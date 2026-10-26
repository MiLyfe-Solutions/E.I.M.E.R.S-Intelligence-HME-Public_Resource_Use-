import V185TrunkScan23Chunk0607

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3595001 : List Nat := [1, 2, 1, 3, 1, 1, 1, 4, 1, 3, 5]
def baseStart_3595001 : Nat := 118140960795 + 3595001 * 2 ^ 59
def prefixEnd_3595001 : Nat := 4983230072969 + 3 ^ 40 * 3595001 * 2
def baseEnd_3595001 : Nat := 1845963466394194275754397

theorem tailTrace_3595001 : CollatzResearch.WordTrace tailWord_3595001 prefixEnd_3595001 1845963466394194275754397 := by
  unfold tailWord_3595001
  simp only [CollatzResearch.WordTrace]
  refine ⟨131120458448932829134680857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87413638965955219423120571 131120458448932829134680857)
  ·
    refine ⟨98340343836699621851010643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131120458448932829134680857 98340343836699621851010643)
    ·
      refine ⟨147510515755049432776515965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98340343836699621851010643 147510515755049432776515965)
      ·
        refine ⟨55316443408143537291193487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147510515755049432776515965 55316443408143537291193487)
        ·
          refine ⟨82974665112215305936790231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55316443408143537291193487 82974665112215305936790231)
          ·
            refine ⟨124461997668322958905185347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82974665112215305936790231 124461997668322958905185347)
            ·
              refine ⟨186692996502484438357778021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124461997668322958905185347 186692996502484438357778021)
              ·
                refine ⟨35004936844215832192083379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 186692996502484438357778021 35004936844215832192083379)
                ·
                  refine ⟨52507405266323748288125069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35004936844215832192083379 52507405266323748288125069)
                  ·
                    refine ⟨19690276974871405608046901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52507405266323748288125069 19690276974871405608046901)
                    ·
                      refine ⟨1845963466394194275754397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19690276974871405608046901 1845963466394194275754397)
                      ·
                        rfl

theorem cell23_3595001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 4, 1, 3, 5].length) (baseStart_3595001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3595001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3595001 prefixEnd_3595001 := by exact prefixLift 3595001
  have htrace : WordTrace (prefixWord ++ tailWord_3595001) baseStart_3595001 baseEnd_3595001 := by
    simpa [prefixWord, tailWord_3595001, baseEnd_3595001] using wordTrace_append hprefix tailTrace_3595001
  have hstable : (prefixWord ++ tailWord_3595001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3595001).length < 2 ^ (prefixWord ++ tailWord_3595001).sum := by decide
  have hdescent : baseEnd_3595001 < baseStart_3595001 := by decide
  rcases family_descends (prefixWord ++ tailWord_3595001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3595018 : List Nat := [3, 1, 2, 2, 1, 2, 1, 2, 2, 4, 3]
def baseStart_3595018 : Nat := 118140960795 + 3595018 * 2 ^ 59
def prefixEnd_3595018 : Nat := 4983230072969 + 3 ^ 40 * 3595018 * 2
def baseEnd_3595018 : Nat := 1845972195565320709241819

theorem tailTrace_3595018 : CollatzResearch.WordTrace tailWord_3595018 prefixEnd_3595018 1845972195565320709241819 := by
  unfold tailWord_3595018
  simp only [CollatzResearch.WordTrace]
  refine ⟨32780269622467810259512427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87414052326580827358699805 32780269622467810259512427)
  ·
    refine ⟨49170404433701715389268641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32780269622467810259512427 49170404433701715389268641)
    ·
      refine ⟨36877803325276286541951481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49170404433701715389268641 36877803325276286541951481)
      ·
        refine ⟨27658352493957214906463611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36877803325276286541951481 27658352493957214906463611)
        ·
          refine ⟨41487528740935822359695417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27658352493957214906463611 41487528740935822359695417)
          ·
            refine ⟨31115646555701866769771563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41487528740935822359695417 31115646555701866769771563)
            ·
              refine ⟨46673469833552800154657345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31115646555701866769771563 46673469833552800154657345)
              ·
                refine ⟨35005102375164600115993009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46673469833552800154657345 35005102375164600115993009)
                ·
                  refine ⟨26253826781373450086994757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35005102375164600115993009 26253826781373450086994757)
                  ·
                    refine ⟨4922592521507521891311517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26253826781373450086994757 4922592521507521891311517)
                    ·
                      refine ⟨1845972195565320709241819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4922592521507521891311517 1845972195565320709241819)
                      ·
                        rfl

theorem cell23_3595018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 2, 2, 4, 3].length) (baseStart_3595018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3595018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3595018 prefixEnd_3595018 := by exact prefixLift 3595018
  have htrace : WordTrace (prefixWord ++ tailWord_3595018) baseStart_3595018 baseEnd_3595018 := by
    simpa [prefixWord, tailWord_3595018, baseEnd_3595018] using wordTrace_append hprefix tailTrace_3595018
  have hstable : (prefixWord ++ tailWord_3595018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3595018).length < 2 ^ (prefixWord ++ tailWord_3595018).sum := by decide
  have hdescent : baseEnd_3595018 < baseStart_3595018 := by decide
  rcases family_descends (prefixWord ++ tailWord_3595018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3595051 : List Nat := [1, 1, 1, 1, 2, 1, 2, 4, 3, 7]
def baseStart_3595051 : Nat := 118140960795 + 3595051 * 2 ^ 59
def prefixEnd_3595051 : Nat := 4983230072969 + 3 ^ 40 * 3595051 * 2
def baseEnd_3595051 : Nat := 615329713475639693376389

theorem tailTrace_3595051 : CollatzResearch.WordTrace tailWord_3595051 prefixEnd_3595051 615329713475639693376389 := by
  unfold tailWord_3595051
  simp only [CollatzResearch.WordTrace]
  refine ⟨131122282098751687674001007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87414854732501125116000671 131122282098751687674001007)
  ·
    refine ⟨196683423148127531511001511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131122282098751687674001007 196683423148127531511001511)
    ·
      refine ⟨295025134722191297266502267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196683423148127531511001511 295025134722191297266502267)
      ·
        refine ⟨442537702083286945899753401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295025134722191297266502267 442537702083286945899753401)
        ·
          refine ⟨331903276562465209424815051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 442537702083286945899753401 331903276562465209424815051)
          ·
            refine ⟨497854914843697814137222577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 331903276562465209424815051 497854914843697814137222577)
            ·
              refine ⟨373391186132773360602916933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 497854914843697814137222577 373391186132773360602916933)
              ·
                refine ⟨70010847399895005113046925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 373391186132773360602916933 70010847399895005113046925)
                ·
                  refine ⟨26254067774960626917392597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70010847399895005113046925 26254067774960626917392597)
                  ·
                    refine ⟨615329713475639693376389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26254067774960626917392597 615329713475639693376389)
                    ·
                      rfl

theorem cell23_3595051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 3, 7].length) (baseStart_3595051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3595051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3595051 prefixEnd_3595051 := by exact prefixLift 3595051
  have htrace : WordTrace (prefixWord ++ tailWord_3595051) baseStart_3595051 baseEnd_3595051 := by
    simpa [prefixWord, tailWord_3595051, baseEnd_3595051] using wordTrace_append hprefix tailTrace_3595051
  have hstable : (prefixWord ++ tailWord_3595051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3595051).length < 2 ^ (prefixWord ++ tailWord_3595051).sum := by decide
  have hdescent : baseEnd_3595051 < baseStart_3595051 := by decide
  rcases family_descends (prefixWord ++ tailWord_3595051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3595066 : List Nat := [3, 1, 1, 1, 6, 1, 3, 1, 2, 2, 2]
def baseStart_3595066 : Nat := 118140960795 + 3595066 * 2 ^ 59
def prefixEnd_3595066 : Nat := 4983230072969 + 3 ^ 40 * 3595066 * 2
def baseEnd_3595066 : Nat := 1845996842636736521441599

theorem tailTrace_3595066 : CollatzResearch.WordTrace tailWord_3595066 prefixEnd_3595066 1845996842636736521441599 := by
  unfold tailWord_3595066
  simp only [CollatzResearch.WordTrace]
  refine ⟨32780707298424336308949263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87415219462464896823864701 32780707298424336308949263)
  ·
    refine ⟨49171060947636504463423895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32780707298424336308949263 49171060947636504463423895)
    ·
      refine ⟨73756591421454756695135843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49171060947636504463423895 73756591421454756695135843)
      ·
        refine ⟨110634887132182135042703765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73756591421454756695135843 110634887132182135042703765)
        ·
          refine ⟨5186010334321037580126739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 110634887132182135042703765 5186010334321037580126739)
          ·
            refine ⟨7779015501481556370190109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5186010334321037580126739 7779015501481556370190109)
            ·
              refine ⟨2917130813055583638821291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7779015501481556370190109 2917130813055583638821291)
              ·
                refine ⟨4375696219583375458231937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2917130813055583638821291 4375696219583375458231937)
                ·
                  refine ⟨3281772164687531593673953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4375696219583375458231937 3281772164687531593673953)
                  ·
                    refine ⟨2461329123515648695255465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3281772164687531593673953 2461329123515648695255465)
                    ·
                      refine ⟨1845996842636736521441599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2461329123515648695255465 1845996842636736521441599)
                      ·
                        rfl

theorem cell23_3595066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 3, 1, 2, 2, 2].length) (baseStart_3595066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3595066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3595066 prefixEnd_3595066 := by exact prefixLift 3595066
  have htrace : WordTrace (prefixWord ++ tailWord_3595066) baseStart_3595066 baseEnd_3595066 := by
    simpa [prefixWord, tailWord_3595066, baseEnd_3595066] using wordTrace_append hprefix tailTrace_3595066
  have hstable : (prefixWord ++ tailWord_3595066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3595066).length < 2 ^ (prefixWord ++ tailWord_3595066).sum := by decide
  have hdescent : baseEnd_3595066 < baseStart_3595066 := by decide
  rcases family_descends (prefixWord ++ tailWord_3595066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3595088 : List Nat := [2, 1, 1, 1, 1, 4, 4, 1, 1, 3, 4]
def baseStart_3595088 : Nat := 118140960795 + 3595088 * 2 ^ 59
def prefixEnd_3595088 : Nat := 4983230072969 + 3 ^ 40 * 3595088 * 2
def baseEnd_3595088 : Nat := 1846008139211135435366497

theorem tailTrace_3595088 : CollatzResearch.WordTrace tailWord_3595088 prefixEnd_3595088 1846008139211135435366497 := by
  unfold tailWord_3595088
  simp only [CollatzResearch.WordTrace]
  refine ⟨65561815799808821496548959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87415754399745095328731945 65561815799808821496548959)
  ·
    refine ⟨98342723699713232244823439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65561815799808821496548959 98342723699713232244823439)
    ·
      refine ⟨147514085549569848367235159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98342723699713232244823439 147514085549569848367235159)
      ·
        refine ⟨221271128324354772550852739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147514085549569848367235159 221271128324354772550852739)
        ·
          refine ⟨331906692486532158826279109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221271128324354772550852739 331906692486532158826279109)
          ·
            refine ⟨62232504841224779779927333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 331906692486532158826279109 62232504841224779779927333)
            ·
              refine ⟨11668594657729646208736375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62232504841224779779927333 11668594657729646208736375)
              ·
                refine ⟨17502891986594469313104563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11668594657729646208736375 17502891986594469313104563)
                ·
                  refine ⟨26254337979891703969656845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17502891986594469313104563 26254337979891703969656845)
                  ·
                    refine ⟨9845376742459388988621317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26254337979891703969656845 9845376742459388988621317)
                    ·
                      refine ⟨1846008139211135435366497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9845376742459388988621317 1846008139211135435366497)
                      ·
                        rfl

theorem cell23_3595088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 1, 1, 3, 4].length) (baseStart_3595088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3595088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3595088 prefixEnd_3595088 := by exact prefixLift 3595088
  have htrace : WordTrace (prefixWord ++ tailWord_3595088) baseStart_3595088 baseEnd_3595088 := by
    simpa [prefixWord, tailWord_3595088, baseEnd_3595088] using wordTrace_append hprefix tailTrace_3595088
  have hstable : (prefixWord ++ tailWord_3595088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3595088).length < 2 ^ (prefixWord ++ tailWord_3595088).sum := by decide
  have hdescent : baseEnd_3595088 < baseStart_3595088 := by decide
  rcases family_descends (prefixWord ++ tailWord_3595088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3595089 : List Nat := [1, 2, 2, 1, 7, 1, 1, 3, 5]
def baseStart_3595089 : Nat := 118140960795 + 3595089 * 2 ^ 59
def prefixEnd_3595089 : Nat := 4983230072969 + 3 ^ 40 * 3595089 * 2
def baseEnd_3595089 : Nat := 205112072521309992383777

theorem tailTrace_3595089 : CollatzResearch.WordTrace tailWord_3595089 prefixEnd_3595089 205112072521309992383777 := by
  unfold tailWord_3595089
  simp only [CollatzResearch.WordTrace]
  refine ⟨131123668072614020163884321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87415778715076013442589547 131123668072614020163884321)
  ·
    refine ⟨98342751054460515122913241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131123668072614020163884321 98342751054460515122913241)
    ·
      refine ⟨73757063290845386342184931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98342751054460515122913241 73757063290845386342184931)
      ·
        refine ⟨110635594936268079513277397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73757063290845386342184931 110635594936268079513277397)
        ·
          refine ⟨2593021756318783113592439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 110635594936268079513277397 2593021756318783113592439)
          ·
            refine ⟨3889532634478174670388659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2593021756318783113592439 3889532634478174670388659)
            ·
              refine ⟨5834298951717262005582989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3889532634478174670388659 5834298951717262005582989)
              ·
                refine ⟨2187862106893973252093621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5834298951717262005582989 2187862106893973252093621)
                ·
                  refine ⟨205112072521309992383777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2187862106893973252093621 205112072521309992383777)
                  ·
                    rfl

theorem cell23_3595089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 1, 3, 5].length) (baseStart_3595089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3595089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3595089 prefixEnd_3595089 := by exact prefixLift 3595089
  have htrace : WordTrace (prefixWord ++ tailWord_3595089) baseStart_3595089 baseEnd_3595089 := by
    simpa [prefixWord, tailWord_3595089, baseEnd_3595089] using wordTrace_append hprefix tailTrace_3595089
  have hstable : (prefixWord ++ tailWord_3595089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3595089).length < 2 ^ (prefixWord ++ tailWord_3595089).sum := by decide
  have hdescent : baseEnd_3595089 < baseStart_3595089 := by decide
  rcases family_descends (prefixWord ++ tailWord_3595089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3595105 : List Nat := [1, 2, 3, 1, 1, 1, 2, 4, 2, 4, 2]
def baseStart_3595105 : Nat := 118140960795 + 3595105 * 2 ^ 59
def prefixEnd_3595105 : Nat := 4983230072969 + 3 ^ 40 * 3595105 * 2
def baseEnd_3595105 : Nat := 1846016868382261868853919

theorem tailTrace_3595105 : CollatzResearch.WordTrace tailWord_3595105 prefixEnd_3595105 1846016868382261868853919 := by
  unfold tailWord_3595105
  simp only [CollatzResearch.WordTrace]
  refine ⟨131124251640556054896466769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87416167760370703264311179 131124251640556054896466769)
  ·
    refine ⟨98343188730417041172350077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131124251640556054896466769 98343188730417041172350077)
    ·
      refine ⟨36878695773906390439631279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98343188730417041172350077 36878695773906390439631279)
      ·
        refine ⟨55318043660859585659446919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36878695773906390439631279 55318043660859585659446919)
        ·
          refine ⟨82977065491289378489170379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55318043660859585659446919 82977065491289378489170379)
          ·
            refine ⟨124465598236934067733755569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82977065491289378489170379 124465598236934067733755569)
            ·
              refine ⟨93349198677700550800316677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124465598236934067733755569 93349198677700550800316677)
              ·
                refine ⟨17502974752068853275059377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 93349198677700550800316677 17502974752068853275059377)
                ·
                  refine ⟨13127231064051639956294533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17502974752068853275059377 13127231064051639956294533)
                  ·
                    refine ⟨2461355824509682491805225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13127231064051639956294533 2461355824509682491805225)
                    ·
                      refine ⟨1846016868382261868853919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2461355824509682491805225 1846016868382261868853919)
                      ·
                        rfl

theorem cell23_3595105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 4, 2, 4, 2].length) (baseStart_3595105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3595105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3595105 prefixEnd_3595105 := by exact prefixLift 3595105
  have htrace : WordTrace (prefixWord ++ tailWord_3595105) baseStart_3595105 baseEnd_3595105 := by
    simpa [prefixWord, tailWord_3595105, baseEnd_3595105] using wordTrace_append hprefix tailTrace_3595105
  have hstable : (prefixWord ++ tailWord_3595105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3595105).length < 2 ^ (prefixWord ++ tailWord_3595105).sum := by decide
  have hdescent : baseEnd_3595105 < baseStart_3595105 := by decide
  rcases family_descends (prefixWord ++ tailWord_3595105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3595115 : List Nat := [1, 1, 1, 1, 2, 2, 7, 1, 3, 4]
def baseStart_3595115 : Nat := 118140960795 + 3595115 * 2 ^ 59
def prefixEnd_3595115 : Nat := 4983230072969 + 3 ^ 40 * 3595115 * 2
def baseEnd_3595115 : Nat := 615340667729602276576291

theorem tailTrace_3595115 : CollatzResearch.WordTrace tailWord_3595115 prefixEnd_3595115 615340667729602276576291 := by
  unfold tailWord_3595115
  simp only [CollatzResearch.WordTrace]
  refine ⟨131124616370519826604330799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87416410913679884402887199 131124616370519826604330799)
  ·
    refine ⟨196686924555779739906496199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131124616370519826604330799 196686924555779739906496199)
    ·
      refine ⟨295030386833669609859744299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196686924555779739906496199 295030386833669609859744299)
      ·
        refine ⟨442545580250504414789616449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295030386833669609859744299 442545580250504414789616449)
        ·
          refine ⟨331909185187878311092212337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 442545580250504414789616449 331909185187878311092212337)
          ·
            refine ⟨248931888890908733319159253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 331909185187878311092212337 248931888890908733319159253)
            ·
              refine ⟨5834341145880673437167795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 248931888890908733319159253 5834341145880673437167795)
              ·
                refine ⟨8751511718821010155751693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5834341145880673437167795 8751511718821010155751693)
                ·
                  refine ⟨3281816894557878808406885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8751511718821010155751693 3281816894557878808406885)
                  ·
                    refine ⟨615340667729602276576291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3281816894557878808406885 615340667729602276576291)
                    ·
                      rfl

theorem cell23_3595115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 7, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 7, 1, 3, 4].length) (baseStart_3595115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3595115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3595115 prefixEnd_3595115 := by exact prefixLift 3595115
  have htrace : WordTrace (prefixWord ++ tailWord_3595115) baseStart_3595115 baseEnd_3595115 := by
    simpa [prefixWord, tailWord_3595115, baseEnd_3595115] using wordTrace_append hprefix tailTrace_3595115
  have hstable : (prefixWord ++ tailWord_3595115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3595115).length < 2 ^ (prefixWord ++ tailWord_3595115).sum := by decide
  have hdescent : baseEnd_3595115 < baseStart_3595115 := by decide
  rcases family_descends (prefixWord ++ tailWord_3595115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3595155 : List Nat := [1, 1, 1, 2, 1, 2, 1, 3, 7, 1, 3]
def baseStart_3595155 : Nat := 118140960795 + 3595155 * 2 ^ 59
def prefixEnd_3595155 : Nat := 4983230072969 + 3 ^ 40 * 3595155 * 2
def baseEnd_3595155 : Nat := 1846042542414986673228689

theorem tailTrace_3595155 : CollatzResearch.WordTrace tailWord_3595155 prefixEnd_3595155 1846042542414986673228689 := by
  unfold tailWord_3595155
  simp only [CollatzResearch.WordTrace]
  refine ⟨131126075290374913435786919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87417383526916608957191279 131126075290374913435786919)
  ·
    refine ⟨196689112935562370153680379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131126075290374913435786919 196689112935562370153680379)
    ·
      refine ⟨295033669403343555230520569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196689112935562370153680379 295033669403343555230520569)
      ·
        refine ⟨221275252052507666422890427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 295033669403343555230520569 221275252052507666422890427)
        ·
          refine ⟨331912878078761499634335641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221275252052507666422890427 331912878078761499634335641)
          ·
            refine ⟨248934658559071124725751731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 331912878078761499634335641 248934658559071124725751731)
            ·
              refine ⟨373401987838606687088627597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 248934658559071124725751731 373401987838606687088627597)
              ·
                refine ⟨140025745439477507658235349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 373401987838606687088627597 140025745439477507658235349)
                ·
                  refine ⟨3281853408737754085739891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 140025745439477507658235349 3281853408737754085739891)
                  ·
                    refine ⟨4922780113106631128609837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3281853408737754085739891 4922780113106631128609837)
                    ·
                      refine ⟨1846042542414986673228689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4922780113106631128609837 1846042542414986673228689)
                      ·
                        rfl

theorem cell23_3595155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 7, 1, 3].length) (baseStart_3595155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3595155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3595155 prefixEnd_3595155 := by exact prefixLift 3595155
  have htrace : WordTrace (prefixWord ++ tailWord_3595155) baseStart_3595155 baseEnd_3595155 := by
    simpa [prefixWord, tailWord_3595155, baseEnd_3595155] using wordTrace_append hprefix tailTrace_3595155
  have hstable : (prefixWord ++ tailWord_3595155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3595155).length < 2 ^ (prefixWord ++ tailWord_3595155).sum := by decide
  have hdescent : baseEnd_3595155 < baseStart_3595155 := by decide
  rcases family_descends (prefixWord ++ tailWord_3595155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3595162 : List Nat := [3, 1, 1, 4, 3, 1, 2, 2, 6]
def baseStart_3595162 : Nat := 118140960795 + 3595162 * 2 ^ 59
def prefixEnd_3595162 : Nat := 4983230072969 + 3 ^ 40 * 3595162 * 2
def baseEnd_3595162 : Nat := 205116237419952016204573

theorem tailTrace_3595162 : CollatzResearch.WordTrace tailWord_3595162 prefixEnd_3595162 205116237419952016204573 := by
  unfold tailWord_3595162
  simp only [CollatzResearch.WordTrace]
  refine ⟨32781582650337388407822935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87417553734233035754194493 32781582650337388407822935)
  ·
    refine ⟨49172373975506082611734403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32781582650337388407822935 49172373975506082611734403)
    ·
      refine ⟨73758560963259123917601605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49172373975506082611734403 73758560963259123917601605)
      ·
        refine ⟨13829730180611085734550301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73758560963259123917601605 13829730180611085734550301)
        ·
          refine ⟨5186148817729157150456363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13829730180611085734550301 5186148817729157150456363)
          ·
            refine ⟨7779223226593735725684545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5186148817729157150456363 7779223226593735725684545)
            ·
              refine ⟨5834417419945301794263409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7779223226593735725684545 5834417419945301794263409)
              ·
                refine ⟨4375813064958976345697557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5834417419945301794263409 4375813064958976345697557)
                ·
                  refine ⟨205116237419952016204573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4375813064958976345697557 205116237419952016204573)
                  ·
                    rfl

theorem cell23_3595162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 2, 2, 6].length) (baseStart_3595162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3595162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3595162 prefixEnd_3595162 := by exact prefixLift 3595162
  have htrace : WordTrace (prefixWord ++ tailWord_3595162) baseStart_3595162 baseEnd_3595162 := by
    simpa [prefixWord, tailWord_3595162, baseEnd_3595162] using wordTrace_append hprefix tailTrace_3595162
  have hstable : (prefixWord ++ tailWord_3595162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3595162).length < 2 ^ (prefixWord ++ tailWord_3595162).sum := by decide
  have hdescent : baseEnd_3595162 < baseStart_3595162 := by decide
  rcases family_descends (prefixWord ++ tailWord_3595162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3595172 : List Nat := [2, 3, 1, 2, 1, 2, 2, 3, 3, 1, 3]
def baseStart_3595172 : Nat := 118140960795 + 3595172 * 2 ^ 59
def prefixEnd_3595172 : Nat := 4983230072969 + 3 ^ 40 * 3595172 * 2
def baseEnd_3595172 : Nat := 1846051271586113106716111

theorem tailTrace_3595172 : CollatzResearch.WordTrace tailWord_3595172 prefixEnd_3595172 1846051271586113106716111 := by
  unfold tailWord_3595172
  simp only [CollatzResearch.WordTrace]
  refine ⟨65563347665656662669577885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87417796887542216892770513 65563347665656662669577885)
  ·
    refine ⟨24586255374621248501091707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65563347665656662669577885 24586255374621248501091707)
    ·
      refine ⟨36879383061931872751637561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24586255374621248501091707 36879383061931872751637561)
      ·
        refine ⟨27659537296448904563728171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36879383061931872751637561 27659537296448904563728171)
        ·
          refine ⟨41489305944673356845592257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27659537296448904563728171 41489305944673356845592257)
          ·
            refine ⟨31116979458505017634194193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41489305944673356845592257 31116979458505017634194193)
            ·
              refine ⟨23337734593878763225645645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31116979458505017634194193 23337734593878763225645645)
              ·
                refine ⟨8751650472704536209617117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23337734593878763225645645 8751650472704536209617117)
                ·
                  refine ⟨3281868927264201078606419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8751650472704536209617117 3281868927264201078606419)
                  ·
                    refine ⟨4922803390896301617909629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3281868927264201078606419 4922803390896301617909629)
                    ·
                      refine ⟨1846051271586113106716111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4922803390896301617909629 1846051271586113106716111)
                      ·
                        rfl

theorem cell23_3595172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 3, 3, 1, 3].length) (baseStart_3595172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3595172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3595172 prefixEnd_3595172 := by exact prefixLift 3595172
  have htrace : WordTrace (prefixWord ++ tailWord_3595172) baseStart_3595172 baseEnd_3595172 := by
    simpa [prefixWord, tailWord_3595172, baseEnd_3595172] using wordTrace_append hprefix tailTrace_3595172
  have hstable : (prefixWord ++ tailWord_3595172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3595172).length < 2 ^ (prefixWord ++ tailWord_3595172).sum := by decide
  have hdescent : baseEnd_3595172 < baseStart_3595172 := by decide
  rcases family_descends (prefixWord ++ tailWord_3595172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3595190 : List Nat := [5, 1, 4, 1, 2, 1, 1, 1, 2, 1, 4]
def baseStart_3595190 : Nat := 118140960795 + 3595190 * 2 ^ 59
def prefixEnd_3595190 : Nat := 4983230072969 + 3 ^ 40 * 3595190 * 2
def baseEnd_3595190 : Nat := 1846060514237894036291029

theorem tailTrace_3595190 : CollatzResearch.WordTrace tailWord_3595190 prefixEnd_3595190 1846060514237894036291029 := by
  unfold tailWord_3595190
  simp only [CollatzResearch.WordTrace]
  refine ⟨8195459490328007150831939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 87418234563498742942207349 8195459490328007150831939)
  ·
    refine ⟨12293189235492010726247909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8195459490328007150831939 12293189235492010726247909)
    ·
      refine ⟨2304972981654752011171483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12293189235492010726247909 2304972981654752011171483)
      ·
        refine ⟨3457459472482128016757225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2304972981654752011171483 3457459472482128016757225)
        ·
          refine ⟨2593094604361596012567919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3457459472482128016757225 2593094604361596012567919)
          ·
            refine ⟨3889641906542394018851879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2593094604361596012567919 3889641906542394018851879)
            ·
              refine ⟨5834462859813591028277819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3889641906542394018851879 5834462859813591028277819)
              ·
                refine ⟨8751694289720386542416729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5834462859813591028277819 8751694289720386542416729)
                ·
                  refine ⟨6563770717290289906812547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8751694289720386542416729 6563770717290289906812547)
                  ·
                    refine ⟨9845656075935434860218821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6563770717290289906812547 9845656075935434860218821)
                    ·
                      refine ⟨1846060514237894036291029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9845656075935434860218821 1846060514237894036291029)
                      ·
                        rfl

theorem cell23_3595190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_3595190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3595190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3595190 prefixEnd_3595190 := by exact prefixLift 3595190
  have htrace : WordTrace (prefixWord ++ tailWord_3595190) baseStart_3595190 baseEnd_3595190 := by
    simpa [prefixWord, tailWord_3595190, baseEnd_3595190] using wordTrace_append hprefix tailTrace_3595190
  have hstable : (prefixWord ++ tailWord_3595190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3595190).length < 2 ^ (prefixWord ++ tailWord_3595190).sum := by decide
  have hdescent : baseEnd_3595190 < baseStart_3595190 := by decide
  rcases family_descends (prefixWord ++ tailWord_3595190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3595212 : List Nat := [2, 2, 1, 4, 1, 1, 3, 3, 1, 1, 4]
def baseStart_3595212 : Nat := 118140960795 + 3595212 * 2 ^ 59
def prefixEnd_3595212 : Nat := 4983230072969 + 3 ^ 40 * 3595212 * 2
def baseEnd_3595212 : Nat := 1846071810812292950215927

theorem tailTrace_3595212 : CollatzResearch.WordTrace tailWord_3595212 prefixEnd_3595212 1846071810812292950215927 := by
  unfold tailWord_3595212
  simp only [CollatzResearch.WordTrace]
  refine ⟨65564077125584206085305945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87418769500778941447074593 65564077125584206085305945)
  ·
    refine ⟨49173057844188154563979459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65564077125584206085305945 49173057844188154563979459)
    ·
      refine ⟨73759586766282231845969189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49173057844188154563979459 73759586766282231845969189)
      ·
        refine ⟨13829922518677918471119223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73759586766282231845969189 13829922518677918471119223)
        ·
          refine ⟨20744883778016877706678835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13829922518677918471119223 20744883778016877706678835)
          ·
            refine ⟨31117325667025316560018253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20744883778016877706678835 31117325667025316560018253)
            ·
              refine ⟨11668997125134493710006845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31117325667025316560018253 11668997125134493710006845)
              ·
                refine ⟨4375873921925435141252567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11668997125134493710006845 4375873921925435141252567)
                ·
                  refine ⟨6563810882888152711878851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4375873921925435141252567 6563810882888152711878851)
                  ·
                    refine ⟨9845716324332229067818277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6563810882888152711878851 9845716324332229067818277)
                    ·
                      refine ⟨1846071810812292950215927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9845716324332229067818277 1846071810812292950215927)
                      ·
                        rfl

theorem cell23_3595212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 3, 1, 1, 4].length) (baseStart_3595212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3595212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3595212 prefixEnd_3595212 := by exact prefixLift 3595212
  have htrace : WordTrace (prefixWord ++ tailWord_3595212) baseStart_3595212 baseEnd_3595212 := by
    simpa [prefixWord, tailWord_3595212, baseEnd_3595212] using wordTrace_append hprefix tailTrace_3595212
  have hstable : (prefixWord ++ tailWord_3595212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3595212).length < 2 ^ (prefixWord ++ tailWord_3595212).sum := by decide
  have hdescent : baseEnd_3595212 < baseStart_3595212 := by decide
  rcases family_descends (prefixWord ++ tailWord_3595212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3595213 : List Nat := [1, 6, 3, 1, 1, 2, 1, 2, 6]
def baseStart_3595213 : Nat := 118140960795 + 3595213 * 2 ^ 59
def prefixEnd_3595213 : Nat := 4983230072969 + 3 ^ 40 * 3595213 * 2
def baseEnd_3595213 : Nat := 205119147143660827367047

theorem tailTrace_3595213 : CollatzResearch.WordTrace tailWord_3595213 prefixEnd_3595213 205119147143660827367047 := by
  unfold tailWord_3595213
  simp only [CollatzResearch.WordTrace]
  refine ⟨131128190724164789341398293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87418793816109859560932195 131128190724164789341398293)
  ·
    refine ⟨6146633940195224500378045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 131128190724164789341398293 6146633940195224500378045)
    ·
      refine ⟨2304987727573209187641767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6146633940195224500378045 2304987727573209187641767)
      ·
        refine ⟨3457481591359813781462651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2304987727573209187641767 3457481591359813781462651)
        ·
          refine ⟨5186222387039720672193977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3457481591359813781462651 5186222387039720672193977)
          ·
            refine ⟨3889666790279790504145483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5186222387039720672193977 3889666790279790504145483)
            ·
              refine ⟨5834500185419685756218225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3889666790279790504145483 5834500185419685756218225)
              ·
                refine ⟨4375875139064764317163669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5834500185419685756218225 4375875139064764317163669)
                ·
                  refine ⟨205119147143660827367047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4375875139064764317163669 205119147143660827367047)
                  ·
                    rfl

theorem cell23_3595213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 1, 2, 6].length) (baseStart_3595213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3595213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3595213 prefixEnd_3595213 := by exact prefixLift 3595213
  have htrace : WordTrace (prefixWord ++ tailWord_3595213) baseStart_3595213 baseEnd_3595213 := by
    simpa [prefixWord, tailWord_3595213, baseEnd_3595213] using wordTrace_append hprefix tailTrace_3595213
  have hstable : (prefixWord ++ tailWord_3595213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3595213).length < 2 ^ (prefixWord ++ tailWord_3595213).sum := by decide
  have hdescent : baseEnd_3595213 < baseStart_3595213 := by decide
  rcases family_descends (prefixWord ++ tailWord_3595213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3595242 : List Nat := [3, 1, 3, 1, 2, 2, 3, 1, 1, 2, 4]
def baseStart_3595242 : Nat := 118140960795 + 3595242 * 2 ^ 59
def prefixEnd_3595242 : Nat := 4983230072969 + 3 ^ 40 * 3595242 * 2
def baseEnd_3595242 : Nat := 1846087215231927832840789

theorem tailTrace_3595242 : CollatzResearch.WordTrace tailWord_3595242 prefixEnd_3595242 1846087215231927832840789 := by
  unfold tailWord_3595242
  simp only [CollatzResearch.WordTrace]
  refine ⟨32782312110264931823550995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87419498960706484862802653 32782312110264931823550995)
  ·
    refine ⟨49173468165397397735326493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32782312110264931823550995 49173468165397397735326493)
    ·
      refine ⟨18440050562024024150747435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49173468165397397735326493 18440050562024024150747435)
      ·
        refine ⟨27660075843036036226121153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18440050562024024150747435 27660075843036036226121153)
        ·
          refine ⟨20745056882277027169590865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27660075843036036226121153 20745056882277027169590865)
          ·
            refine ⟨15558792661707770377193149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20745056882277027169590865 15558792661707770377193149)
            ·
              refine ⟨5834547248140413891447431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15558792661707770377193149 5834547248140413891447431)
              ·
                refine ⟨8751820872210620837171147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5834547248140413891447431 8751820872210620837171147)
                ·
                  refine ⟨13127731308315931255756721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8751820872210620837171147 13127731308315931255756721)
                  ·
                    refine ⟨9845798481236948441817541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13127731308315931255756721 9845798481236948441817541)
                    ·
                      refine ⟨1846087215231927832840789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9845798481236948441817541 1846087215231927832840789)
                      ·
                        rfl

theorem cell23_3595242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 3, 1, 1, 2, 4].length) (baseStart_3595242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3595242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3595242 prefixEnd_3595242 := by exact prefixLift 3595242
  have htrace : WordTrace (prefixWord ++ tailWord_3595242) baseStart_3595242 baseEnd_3595242 := by
    simpa [prefixWord, tailWord_3595242, baseEnd_3595242] using wordTrace_append hprefix tailTrace_3595242
  have hstable : (prefixWord ++ tailWord_3595242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3595242).length < 2 ^ (prefixWord ++ tailWord_3595242).sum := by decide
  have hdescent : baseEnd_3595242 < baseStart_3595242 := by decide
  rcases family_descends (prefixWord ++ tailWord_3595242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3595249 : List Nat := [1, 2, 2, 2, 4, 2, 2, 2, 1, 2, 3]
def baseStart_3595249 : Nat := 118140960795 + 3595249 * 2 ^ 59
def prefixEnd_3595249 : Nat := 4983230072969 + 3 ^ 40 * 3595249 * 2
def baseEnd_3595249 : Nat := 1846090809596509305453257

theorem tailTrace_3595249 : CollatzResearch.WordTrace tailWord_3595249 prefixEnd_3595249 1846090809596509305453257 := by
  unfold tailWord_3595249
  simp only [CollatzResearch.WordTrace]
  refine ⟨131129503752034367489708801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87419669168022911659805867 131129503752034367489708801)
  ·
    refine ⟨98347127814025775617281601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131129503752034367489708801 98347127814025775617281601)
    ·
      refine ⟨73760345860519331712961201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98347127814025775617281601 73760345860519331712961201)
      ·
        refine ⟨55320259395389498784720901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73760345860519331712961201 55320259395389498784720901)
        ·
          refine ⟨10372548636635531022135169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55320259395389498784720901 10372548636635531022135169)
          ·
            refine ⟨7779411477476648266601377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10372548636635531022135169 7779411477476648266601377)
            ·
              refine ⟨5834558608107486199951033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7779411477476648266601377 5834558608107486199951033)
              ·
                refine ⟨4375918956080614649963275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5834558608107486199951033 4375918956080614649963275)
                ·
                  refine ⟨6563878434120921974944913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4375918956080614649963275 6563878434120921974944913)
                  ·
                    refine ⟨4922908825590691481208685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6563878434120921974944913 4922908825590691481208685)
                    ·
                      refine ⟨1846090809596509305453257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4922908825590691481208685 1846090809596509305453257)
                      ·
                        rfl

theorem cell23_3595249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 2, 2, 1, 2, 3].length) (baseStart_3595249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3595249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3595249 prefixEnd_3595249 := by exact prefixLift 3595249
  have htrace : WordTrace (prefixWord ++ tailWord_3595249) baseStart_3595249 baseEnd_3595249 := by
    simpa [prefixWord, tailWord_3595249, baseEnd_3595249] using wordTrace_append hprefix tailTrace_3595249
  have hstable : (prefixWord ++ tailWord_3595249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3595249).length < 2 ^ (prefixWord ++ tailWord_3595249).sum := by decide
  have hdescent : baseEnd_3595249 < baseStart_3595249 := by decide
  rcases family_descends (prefixWord ++ tailWord_3595249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3595266 : List Nat := [3, 4, 1, 3, 1, 1, 2, 1, 1, 1, 5]
def baseStart_3595266 : Nat := 118140960795 + 3595266 * 2 ^ 59
def prefixEnd_3595266 : Nat := 4983230072969 + 3 ^ 40 * 3595266 * 2
def baseEnd_3595266 : Nat := 1846099538767635738940679

theorem tailTrace_3595266 : CollatzResearch.WordTrace tailWord_3595266 prefixEnd_3595266 1846099538767635738940679 := by
  unfold tailWord_3595266
  simp only [CollatzResearch.WordTrace]
  refine ⟨32782530948243194848269413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87420082528648519595385101 32782530948243194848269413)
  ·
    refine ⟨6146724552795599034050515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32782530948243194848269413 6146724552795599034050515)
    ·
      refine ⟨9220086829193398551075773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6146724552795599034050515 9220086829193398551075773)
      ·
        refine ⟨3457532560947524456653415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9220086829193398551075773 3457532560947524456653415)
        ·
          refine ⟨5186298841421286684980123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3457532560947524456653415 5186298841421286684980123)
          ·
            refine ⟨7779448262131930027470185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5186298841421286684980123 7779448262131930027470185)
            ·
              refine ⟨5834586196598947520602639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7779448262131930027470185 5834586196598947520602639)
              ·
                refine ⟨8751879294898421280903959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5834586196598947520602639 8751879294898421280903959)
                ·
                  refine ⟨13127818942347631921355939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8751879294898421280903959 13127818942347631921355939)
                  ·
                    refine ⟨19691728413521447882033909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13127818942347631921355939 19691728413521447882033909)
                    ·
                      refine ⟨1846099538767635738940679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19691728413521447882033909 1846099538767635738940679)
                      ·
                        rfl

theorem cell23_3595266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_3595266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3595266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3595266 prefixEnd_3595266 := by exact prefixLift 3595266
  have htrace : WordTrace (prefixWord ++ tailWord_3595266) baseStart_3595266 baseEnd_3595266 := by
    simpa [prefixWord, tailWord_3595266, baseEnd_3595266] using wordTrace_append hprefix tailTrace_3595266
  have hstable : (prefixWord ++ tailWord_3595266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3595266).length < 2 ^ (prefixWord ++ tailWord_3595266).sum := by decide
  have hdescent : baseEnd_3595266 < baseStart_3595266 := by decide
  rcases family_descends (prefixWord ++ tailWord_3595266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3595306 : List Nat := [3, 1, 4, 1, 3, 1, 1, 1, 3, 3, 2]
def baseStart_3595306 : Nat := 118140960795 + 3595306 * 2 ^ 59
def prefixEnd_3595306 : Nat := 4983230072969 + 3 ^ 40 * 3595306 * 2
def baseEnd_3595306 : Nat := 1846120077993815582440495

theorem tailTrace_3595306 : CollatzResearch.WordTrace tailWord_3595306 prefixEnd_3595306 1846120077993815582440495 := by
  unfold tailWord_3595306
  simp only [CollatzResearch.WordTrace]
  refine ⟨32782895678206966556133443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87421055141885244149689181 32782895678206966556133443)
  ·
    refine ⟨49174343517310449834200165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32782895678206966556133443 49174343517310449834200165)
    ·
      refine ⟨9220189409495709343912531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49174343517310449834200165 9220189409495709343912531)
      ·
        refine ⟨13830284114243564015868797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9220189409495709343912531 13830284114243564015868797)
        ·
          refine ⟨5186356542841336505950799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13830284114243564015868797 5186356542841336505950799)
          ·
            refine ⟨7779534814262004758926199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5186356542841336505950799 7779534814262004758926199)
            ·
              refine ⟨11669302221393007138389299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7779534814262004758926199 11669302221393007138389299)
              ·
                refine ⟨17503953332089510707583949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11669302221393007138389299 17503953332089510707583949)
                ·
                  refine ⟨6563982499533566515343981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17503953332089510707583949 6563982499533566515343981)
                  ·
                    refine ⟨2461493437325087443253993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6563982499533566515343981 2461493437325087443253993)
                    ·
                      refine ⟨1846120077993815582440495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2461493437325087443253993 1846120077993815582440495)
                      ·
                        rfl

theorem cell23_3595306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 1, 3, 3, 2].length) (baseStart_3595306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3595306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3595306 prefixEnd_3595306 := by exact prefixLift 3595306
  have htrace : WordTrace (prefixWord ++ tailWord_3595306) baseStart_3595306 baseEnd_3595306 := by
    simpa [prefixWord, tailWord_3595306, baseEnd_3595306] using wordTrace_append hprefix tailTrace_3595306
  have hstable : (prefixWord ++ tailWord_3595306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3595306).length < 2 ^ (prefixWord ++ tailWord_3595306).sum := by decide
  have hdescent : baseEnd_3595306 < baseStart_3595306 := by decide
  rcases family_descends (prefixWord ++ tailWord_3595306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3595315 : List Nat := [1, 1, 1, 2, 4, 1, 1, 2, 4, 2, 4]
def baseStart_3595315 : Nat := 118140960795 + 3595315 * 2 ^ 59
def prefixEnd_3595315 : Nat := 4983230072969 + 3 ^ 40 * 3595315 * 2
def baseEnd_3595315 : Nat := 1846124699319706047227953

theorem tailTrace_3595315 : CollatzResearch.WordTrace tailWord_3595315 prefixEnd_3595315 1846124699319706047227953 := by
  unfold tailWord_3595315
  simp only [CollatzResearch.WordTrace]
  refine ⟨131131910969795260761611399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87421273979863507174407599 131131910969795260761611399)
  ·
    refine ⟨196697866454692891142417099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131131910969795260761611399 196697866454692891142417099)
    ·
      refine ⟨295046799682039336713625649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196697866454692891142417099 295046799682039336713625649)
      ·
        refine ⟨221285099761529502535219237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 295046799682039336713625649 221285099761529502535219237)
        ·
          refine ⟨41490956205286781725353607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 221285099761529502535219237 41490956205286781725353607)
          ·
            refine ⟨62236434307930172588030411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41490956205286781725353607 62236434307930172588030411)
            ·
              refine ⟨93354651461895258882045617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62236434307930172588030411 93354651461895258882045617)
              ·
                refine ⟨70015988596421444161534213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93354651461895258882045617 70015988596421444161534213)
                ·
                  refine ⟨13127997861829020780287665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70015988596421444161534213 13127997861829020780287665)
                  ·
                    refine ⟨9845998396371765585215749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13127997861829020780287665 9845998396371765585215749)
                    ·
                      refine ⟨1846124699319706047227953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9845998396371765585215749 1846124699319706047227953)
                      ·
                        rfl

theorem cell23_3595315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 4, 2, 4].length) (baseStart_3595315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3595315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3595315 prefixEnd_3595315 := by exact prefixLift 3595315
  have htrace : WordTrace (prefixWord ++ tailWord_3595315) baseStart_3595315 baseEnd_3595315 := by
    simpa [prefixWord, tailWord_3595315, baseEnd_3595315] using wordTrace_append hprefix tailTrace_3595315
  have hstable : (prefixWord ++ tailWord_3595315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3595315).length < 2 ^ (prefixWord ++ tailWord_3595315).sum := by decide
  have hdescent : baseEnd_3595315 < baseStart_3595315 := by decide
  rcases family_descends (prefixWord ++ tailWord_3595315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3595336 : List Nat := [2, 1, 3, 1, 1, 1, 6, 2, 2, 2, 2]
def baseStart_3595336 : Nat := 118140960795 + 3595336 * 2 ^ 59
def prefixEnd_3595336 : Nat := 4983230072969 + 3 ^ 40 * 3595336 * 2
def baseEnd_3595336 : Nat := 1846135482413450465065357

theorem tailTrace_3595336 : CollatzResearch.WordTrace tailWord_3595336 prefixEnd_3595336 1846135482413450465065357 := by
  unfold tailWord_3595336
  simp only [CollatzResearch.WordTrace]
  refine ⟨65566338451359590674062931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87421784601812787565417241 65566338451359590674062931)
  ·
    refine ⟨98349507677039386011094397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65566338451359590674062931 98349507677039386011094397)
    ·
      refine ⟨36881065378889769754160399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98349507677039386011094397 36881065378889769754160399)
      ·
        refine ⟨55321598068334654631240599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36881065378889769754160399 55321598068334654631240599)
        ·
          refine ⟨82982397102501981946860899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55321598068334654631240599 82982397102501981946860899)
          ·
            refine ⟨124473595653752972920291349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82982397102501981946860899 124473595653752972920291349)
            ·
              refine ⟨5834699796269670605638657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 124473595653752972920291349 5834699796269670605638657)
              ·
                refine ⟨4376024847202252954228993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5834699796269670605638657 4376024847202252954228993)
                ·
                  refine ⟨3282018635401689715671745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4376024847202252954228993 3282018635401689715671745)
                  ·
                    refine ⟨2461513976551267286753809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3282018635401689715671745 2461513976551267286753809)
                    ·
                      refine ⟨1846135482413450465065357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2461513976551267286753809 1846135482413450465065357)
                      ·
                        rfl

theorem cell23_3595336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 6, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 6, 2, 2, 2, 2].length) (baseStart_3595336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3595336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3595336 prefixEnd_3595336 := by exact prefixLift 3595336
  have htrace : WordTrace (prefixWord ++ tailWord_3595336) baseStart_3595336 baseEnd_3595336 := by
    simpa [prefixWord, tailWord_3595336, baseEnd_3595336] using wordTrace_append hprefix tailTrace_3595336
  have hstable : (prefixWord ++ tailWord_3595336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3595336).length < 2 ^ (prefixWord ++ tailWord_3595336).sum := by decide
  have hdescent : baseEnd_3595336 < baseStart_3595336 := by decide
  rcases family_descends (prefixWord ++ tailWord_3595336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3595352 : List Nat := [2, 1, 2, 2, 1, 3, 3, 1, 2, 3, 3]
def baseStart_3595352 : Nat := 118140960795 + 3595352 * 2 ^ 59
def prefixEnd_3595352 : Nat := 4983230072969 + 3 ^ 40 * 3595352 * 2
def baseEnd_3595352 : Nat := 1846143698103922402465283

theorem tailTrace_3595352 : CollatzResearch.WordTrace tailWord_3595352 prefixEnd_3595352 1846143698103922402465283 := by
  unfold tailWord_3595352
  simp only [CollatzResearch.WordTrace]
  refine ⟨65566630235330608040354155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87422173647107477387138873 65566630235330608040354155)
  ·
    refine ⟨98349945352995912060531233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65566630235330608040354155 98349945352995912060531233)
    ·
      refine ⟨73762459014746934045398425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98349945352995912060531233 73762459014746934045398425)
      ·
        refine ⟨55321844261060200534048819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73762459014746934045398425 55321844261060200534048819)
        ·
          refine ⟨82982766391590300801073229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55321844261060200534048819 82982766391590300801073229)
          ·
            refine ⟨31118537396846362800402461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82982766391590300801073229 31118537396846362800402461)
            ·
              refine ⟨11669451523817386050150923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31118537396846362800402461 11669451523817386050150923)
              ·
                refine ⟨17504177285726079075226385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11669451523817386050150923 17504177285726079075226385)
                ·
                  refine ⟨13128132964294559306419789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17504177285726079075226385 13128132964294559306419789)
                  ·
                    refine ⟨4923049861610459739907421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13128132964294559306419789 4923049861610459739907421)
                    ·
                      refine ⟨1846143698103922402465283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4923049861610459739907421 1846143698103922402465283)
                      ·
                        rfl

theorem cell23_3595352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 1, 2, 3, 3].length) (baseStart_3595352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3595352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3595352 prefixEnd_3595352 := by exact prefixLift 3595352
  have htrace : WordTrace (prefixWord ++ tailWord_3595352) baseStart_3595352 baseEnd_3595352 := by
    simpa [prefixWord, tailWord_3595352, baseEnd_3595352] using wordTrace_append hprefix tailTrace_3595352
  have hstable : (prefixWord ++ tailWord_3595352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3595352).length < 2 ^ (prefixWord ++ tailWord_3595352).sum := by decide
  have hdescent : baseEnd_3595352 < baseStart_3595352 := by decide
  rcases family_descends (prefixWord ++ tailWord_3595352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3595392 : List Nat := [2, 1, 1, 2, 1, 3, 2, 4, 2, 1, 4]
def baseStart_3595392 : Nat := 118140960795 + 3595392 * 2 ^ 59
def prefixEnd_3595392 : Nat := 4983230072969 + 3 ^ 40 * 3595392 * 2
def baseEnd_3595392 : Nat := 1846164237330102245965099

theorem tailTrace_3595392 : CollatzResearch.WordTrace tailWord_3595392 prefixEnd_3595392 1846164237330102245965099 := by
  unfold tailWord_3595392
  simp only [CollatzResearch.WordTrace]
  refine ⟨65567359695258151456082215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87423146260344201941442953 65567359695258151456082215)
  ·
    refine ⟨98351039542887227184123323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65567359695258151456082215 98351039542887227184123323)
    ·
      refine ⟨147526559314330840776184985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98351039542887227184123323 147526559314330840776184985)
      ·
        refine ⟨110644919485748130582138739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147526559314330840776184985 110644919485748130582138739)
        ·
          refine ⟨165967379228622195873208109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110644919485748130582138739 165967379228622195873208109)
          ·
            refine ⟨62237767210733323452453041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 165967379228622195873208109 62237767210733323452453041)
            ·
              refine ⟨46678325408049992589339781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62237767210733323452453041 46678325408049992589339781)
              ·
                refine ⟨8752186014009373610501209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46678325408049992589339781 8752186014009373610501209)
                ·
                  refine ⟨6564139510507030207875907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8752186014009373610501209 6564139510507030207875907)
                  ·
                    refine ⟨9846209265760545311813861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6564139510507030207875907 9846209265760545311813861)
                    ·
                      refine ⟨1846164237330102245965099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9846209265760545311813861 1846164237330102245965099)
                      ·
                        rfl

theorem cell23_3595392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 4, 2, 1, 4].length) (baseStart_3595392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3595392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3595392 prefixEnd_3595392 := by exact prefixLift 3595392
  have htrace : WordTrace (prefixWord ++ tailWord_3595392) baseStart_3595392 baseEnd_3595392 := by
    simpa [prefixWord, tailWord_3595392, baseEnd_3595392] using wordTrace_append hprefix tailTrace_3595392
  have hstable : (prefixWord ++ tailWord_3595392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3595392).length < 2 ^ (prefixWord ++ tailWord_3595392).sum := by decide
  have hdescent : baseEnd_3595392 < baseStart_3595392 := by decide
  rcases family_descends (prefixWord ++ tailWord_3595392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3595435 : List Nat := [1, 1, 1, 1, 2, 1, 1, 1, 2, 6, 6]
def baseStart_3595435 : Nat := 118140960795 + 3595435 * 2 ^ 59
def prefixEnd_3595435 : Nat := 4983230072969 + 3 ^ 40 * 3595435 * 2
def baseEnd_3595435 : Nat := 1846186316998245577727401

theorem tailTrace_3595435 : CollatzResearch.WordTrace tailWord_3595435 prefixEnd_3595435 1846186316998245577727401 := by
  unfold tailWord_3595435
  simp only [CollatzResearch.WordTrace]
  refine ⟨131136287729360521255979759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87424191819573680837319839 131136287729360521255979759)
  ·
    refine ⟨196704431594040781883969639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131136287729360521255979759 196704431594040781883969639)
    ·
      refine ⟨295056647391061172825954459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196704431594040781883969639 295056647391061172825954459)
      ·
        refine ⟨442584971086591759238931689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295056647391061172825954459 442584971086591759238931689)
        ·
          refine ⟨331938728314943819429198767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 442584971086591759238931689 331938728314943819429198767)
          ·
            refine ⟨497908092472415729143798151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 331938728314943819429198767 497908092472415729143798151)
            ·
              refine ⟨746862138708623593715697227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 497908092472415729143798151 746862138708623593715697227)
              ·
                refine ⟨1120293208062935390573545841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 746862138708623593715697227 1120293208062935390573545841)
                ·
                  refine ⟨840219906047201542930159381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1120293208062935390573545841 840219906047201542930159381)
                  ·
                    refine ⟨39385308095962572324851221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 840219906047201542930159381 39385308095962572324851221)
                    ·
                      refine ⟨1846186316998245577727401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39385308095962572324851221 1846186316998245577727401)
                      ·
                        rfl

theorem cell23_3595435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 6, 6].length) (baseStart_3595435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3595435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3595435 prefixEnd_3595435 := by exact prefixLift 3595435
  have htrace : WordTrace (prefixWord ++ tailWord_3595435) baseStart_3595435 baseEnd_3595435 := by
    simpa [prefixWord, tailWord_3595435, baseEnd_3595435] using wordTrace_append hprefix tailTrace_3595435
  have hstable : (prefixWord ++ tailWord_3595435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3595435).length < 2 ^ (prefixWord ++ tailWord_3595435).sum := by decide
  have hdescent : baseEnd_3595435 < baseStart_3595435 := by decide
  rcases family_descends (prefixWord ++ tailWord_3595435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3595459 : List Nat := [1, 1, 1, 3, 1, 1, 1, 7, 3, 1, 3]
def baseStart_3595459 : Nat := 118140960795 + 3595459 * 2 ^ 59
def prefixEnd_3595459 : Nat := 4983230072969 + 3 ^ 40 * 3595459 * 2
def baseEnd_3595459 : Nat := 1846198640533953483827291

theorem tailTrace_3595459 : CollatzResearch.WordTrace tailWord_3595459 prefixEnd_3595459 1846198640533953483827291 := by
  unfold tailWord_3595459
  simp only [CollatzResearch.WordTrace]
  refine ⟨131137163081273573354853431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87424775387515715569902287 131137163081273573354853431)
  ·
    refine ⟨196705744621910360032280147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131137163081273573354853431 196705744621910360032280147)
    ·
      refine ⟨295058616932865540048420221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196705744621910360032280147 295058616932865540048420221)
      ·
        refine ⟨110646981349824577518157583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 295058616932865540048420221 110646981349824577518157583)
        ·
          refine ⟨165970472024736866277236375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110646981349824577518157583 165970472024736866277236375)
          ·
            refine ⟨248955708037105299415854563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165970472024736866277236375 248955708037105299415854563)
            ·
              refine ⟨373433562055657949123781845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 248955708037105299415854563 373433562055657949123781845)
              ·
                refine ⟨8752349110679483182588637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 373433562055657949123781845 8752349110679483182588637)
                ·
                  refine ⟨3282130916504806193470739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8752349110679483182588637 3282130916504806193470739)
                  ·
                    refine ⟨4923196374757209290206109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3282130916504806193470739 4923196374757209290206109)
                    ·
                      refine ⟨1846198640533953483827291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4923196374757209290206109 1846198640533953483827291)
                      ·
                        rfl

theorem cell23_3595459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 7, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 7, 3, 1, 3].length) (baseStart_3595459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3595459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3595459 prefixEnd_3595459 := by exact prefixLift 3595459
  have htrace : WordTrace (prefixWord ++ tailWord_3595459) baseStart_3595459 baseEnd_3595459 := by
    simpa [prefixWord, tailWord_3595459, baseEnd_3595459] using wordTrace_append hprefix tailTrace_3595459
  have hstable : (prefixWord ++ tailWord_3595459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3595459).length < 2 ^ (prefixWord ++ tailWord_3595459).sum := by decide
  have hdescent : baseEnd_3595459 < baseStart_3595459 := by decide
  rcases family_descends (prefixWord ++ tailWord_3595459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3595466 : List Nat := [3, 1, 2, 1, 3, 4, 2, 1, 6]
def baseStart_3595466 : Nat := 118140960795 + 3595466 * 2 ^ 59
def prefixEnd_3595466 : Nat := 4983230072969 + 3 ^ 40 * 3595466 * 2
def baseEnd_3595466 : Nat := 205133581655392772937751

theorem tailTrace_3595466 : CollatzResearch.WordTrace tailWord_3595466 prefixEnd_3595466 205133581655392772937751 := by
  unfold tailWord_3595466
  simp only [CollatzResearch.WordTrace]
  refine ⟨32784354598062053387589563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87424945594832142366905501 32784354598062053387589563)
  ·
    refine ⟨49176531897093080081384345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32784354598062053387589563 49176531897093080081384345)
    ·
      refine ⟨36882398922819810061038259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49176531897093080081384345 36882398922819810061038259)
      ·
        refine ⟨55323598384229715091557389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36882398922819810061038259 55323598384229715091557389)
        ·
          refine ⟨20746349394086143159334021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55323598384229715091557389 20746349394086143159334021)
          ·
            refine ⟨3889940511391151842375129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20746349394086143159334021 3889940511391151842375129)
            ·
              refine ⟨2917455383543363881781347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3889940511391151842375129 2917455383543363881781347)
              ·
                refine ⟨4376183075315045822672021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2917455383543363881781347 4376183075315045822672021)
                ·
                  refine ⟨205133581655392772937751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4376183075315045822672021 205133581655392772937751)
                  ·
                    rfl

theorem cell23_3595466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 2, 1, 6].length) (baseStart_3595466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3595466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3595466 prefixEnd_3595466 := by exact prefixLift 3595466
  have htrace : WordTrace (prefixWord ++ tailWord_3595466) baseStart_3595466 baseEnd_3595466 := by
    simpa [prefixWord, tailWord_3595466, baseEnd_3595466] using wordTrace_append hprefix tailTrace_3595466
  have hstable : (prefixWord ++ tailWord_3595466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3595466).length < 2 ^ (prefixWord ++ tailWord_3595466).sum := by decide
  have hdescent : baseEnd_3595466 < baseStart_3595466 := by decide
  rcases family_descends (prefixWord ++ tailWord_3595466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3595479 : List Nat := [1, 1, 3, 2, 1, 2, 5, 2, 1, 5]
def baseStart_3595479 : Nat := 118140960795 + 3595479 * 2 ^ 59
def prefixEnd_3595479 : Nat := 4983230072969 + 3 ^ 40 * 3595479 * 2
def baseEnd_3595479 : Nat := 615402970049014468525733

theorem tailTrace_3595479 : CollatzResearch.WordTrace tailWord_3595479 prefixEnd_3595479 615402970049014468525733 := by
  unfold tailWord_3595479
  simp only [CollatzResearch.WordTrace]
  refine ⟨131137892541201116770581491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87425261694134077847054327 131137892541201116770581491)
  ·
    refine ⟨196706838811801675155872237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131137892541201116770581491 196706838811801675155872237)
    ·
      refine ⟨73765064554425628183452089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196706838811801675155872237 73765064554425628183452089)
      ·
        refine ⟨55323798415819221137589067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73765064554425628183452089 55323798415819221137589067)
        ·
          refine ⟨82985697623728831706383601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55323798415819221137589067 82985697623728831706383601)
          ·
            refine ⟨62239273217796623779787701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82985697623728831706383601 62239273217796623779787701)
            ·
              refine ⟨5834931864168433479355097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62239273217796623779787701 5834931864168433479355097)
              ·
                refine ⟨4376198898126325109516323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5834931864168433479355097 4376198898126325109516323)
                ·
                  refine ⟨6564298347189487664274485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4376198898126325109516323 6564298347189487664274485)
                  ·
                    refine ⟨615402970049014468525733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6564298347189487664274485 615402970049014468525733)
                    ·
                      rfl

theorem cell23_3595479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 5, 2, 1, 5].length) (baseStart_3595479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3595479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3595479 prefixEnd_3595479 := by exact prefixLift 3595479
  have htrace : WordTrace (prefixWord ++ tailWord_3595479) baseStart_3595479 baseEnd_3595479 := by
    simpa [prefixWord, tailWord_3595479, baseEnd_3595479] using wordTrace_append hprefix tailTrace_3595479
  have hstable : (prefixWord ++ tailWord_3595479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3595479).length < 2 ^ (prefixWord ++ tailWord_3595479).sum := by decide
  have hdescent : baseEnd_3595479 < baseStart_3595479 := by decide
  rcases family_descends (prefixWord ++ tailWord_3595479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3595492 : List Nat := [2, 3, 1, 1, 1, 2, 3, 1, 3, 6]
def baseStart_3595492 : Nat := 118140960795 + 3595492 * 2 ^ 59
def prefixEnd_3595492 : Nat := 4983230072969 + 3 ^ 40 * 3595492 * 2
def baseEnd_3595492 : Nat := 615405195131850618238213

theorem tailTrace_3595492 : CollatzResearch.WordTrace tailWord_3595492 prefixEnd_3595492 615405195131850618238213 := by
  unfold tailWord_3595492
  simp only [CollatzResearch.WordTrace]
  refine ⟨65569183345077009995402365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87425577793436013327203153 65569183345077009995402365)
  ·
    refine ⟨24588443754403878748275887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65569183345077009995402365 24588443754403878748275887)
    ·
      refine ⟨36882665631605818122413831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24588443754403878748275887 36882665631605818122413831)
      ·
        refine ⟨55323998447408727183620747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36882665631605818122413831 55323998447408727183620747)
        ·
          refine ⟨82985997671113090775431121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55323998447408727183620747 82985997671113090775431121)
          ·
            refine ⟨62239498253334818081573341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82985997671113090775431121 62239498253334818081573341)
            ·
              refine ⟨23339811845000556780590003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62239498253334818081573341 23339811845000556780590003)
              ·
                refine ⟨35009717767500835170885005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23339811845000556780590003 35009717767500835170885005)
                ·
                  refine ⟨13128644162812813189081877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35009717767500835170885005 13128644162812813189081877)
                  ·
                    refine ⟨615405195131850618238213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13128644162812813189081877 615405195131850618238213)
                    ·
                      rfl

theorem cell23_3595492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 1, 3, 6].length) (baseStart_3595492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3595492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3595492 prefixEnd_3595492 := by exact prefixLift 3595492
  have htrace : WordTrace (prefixWord ++ tailWord_3595492) baseStart_3595492 baseEnd_3595492 := by
    simpa [prefixWord, tailWord_3595492, baseEnd_3595492] using wordTrace_append hprefix tailTrace_3595492
  have hstable : (prefixWord ++ tailWord_3595492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3595492).length < 2 ^ (prefixWord ++ tailWord_3595492).sum := by decide
  have hdescent : baseEnd_3595492 < baseStart_3595492 := by decide
  rcases family_descends (prefixWord ++ tailWord_3595492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3595496 : List Nat := [2, 1, 4, 1, 2, 1, 5, 1, 1, 5]
def baseStart_3595496 : Nat := 118140960795 + 3595496 * 2 ^ 59
def prefixEnd_3595496 : Nat := 4983230072969 + 3 ^ 40 * 3595496 * 2
def baseEnd_3595496 : Nat := 615405879772723279688207

theorem tailTrace_3595496 : CollatzResearch.WordTrace tailWord_3595496 prefixEnd_3595496 615405879772723279688207 := by
  unfold tailWord_3595496
  simp only [CollatzResearch.WordTrace]
  refine ⟨65569256291069764336975171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87425675054759685782633561 65569256291069764336975171)
  ·
    refine ⟨98353884436604646505462757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65569256291069764336975171 98353884436604646505462757)
    ·
      refine ⟨18441353331863371219774267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98353884436604646505462757 18441353331863371219774267)
      ·
        refine ⟨27662029997795056829661401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18441353331863371219774267 27662029997795056829661401)
        ·
          refine ⟨20746522498346292622246051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27662029997795056829661401 20746522498346292622246051)
          ·
            refine ⟨31119783747519438933369077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20746522498346292622246051 31119783747519438933369077)
            ·
              refine ⟨2917479726329947400003351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31119783747519438933369077 2917479726329947400003351)
              ·
                refine ⟨4376219589494921100005027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2917479726329947400003351 4376219589494921100005027)
                ·
                  refine ⟨6564329384242381650007541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4376219589494921100005027 6564329384242381650007541)
                  ·
                    refine ⟨615405879772723279688207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6564329384242381650007541 615405879772723279688207)
                    ·
                      rfl

theorem cell23_3595496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 5, 1, 1, 5].length) (baseStart_3595496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3595496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3595496 prefixEnd_3595496 := by exact prefixLift 3595496
  have htrace : WordTrace (prefixWord ++ tailWord_3595496) baseStart_3595496 baseEnd_3595496 := by
    simpa [prefixWord, tailWord_3595496, baseEnd_3595496] using wordTrace_append hprefix tailTrace_3595496
  have hstable : (prefixWord ++ tailWord_3595496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3595496).length < 2 ^ (prefixWord ++ tailWord_3595496).sum := by decide
  have hdescent : baseEnd_3595496 < baseStart_3595496 := by decide
  rcases family_descends (prefixWord ++ tailWord_3595496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3595519 : List Nat := [1, 1, 2, 2, 1, 5, 1, 2, 3, 2, 3]
def baseStart_3595519 : Nat := 118140960795 + 3595519 * 2 ^ 59
def prefixEnd_3595519 : Nat := 4983230072969 + 3 ^ 40 * 3595519 * 2
def baseEnd_3595519 : Nat := 1846229449373223249077015

theorem tailTrace_3595519 : CollatzResearch.WordTrace tailWord_3595519 prefixEnd_3595519 1846229449373223249077015 := by
  unfold tailWord_3595519
  simp only [CollatzResearch.WordTrace]
  refine ⟨131139351461056203602037611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87426234307370802401358407 131139351461056203602037611)
  ·
    refine ⟨196709027191584305403056417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131139351461056203602037611 196709027191584305403056417)
    ·
      refine ⟨147531770393688229052292313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196709027191584305403056417 147531770393688229052292313)
      ·
        refine ⟨110648827795266171789219235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147531770393688229052292313 110648827795266171789219235)
        ·
          refine ⟨165973241692899257683828853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110648827795266171789219235 165973241692899257683828853)
          ·
            refine ⟨15559991408709305407858955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 165973241692899257683828853 15559991408709305407858955)
            ·
              refine ⟨23339987113063958111788433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15559991408709305407858955 23339987113063958111788433)
              ·
                refine ⟨17504990334797968583841325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23339987113063958111788433 17504990334797968583841325)
                ·
                  refine ⟨6564371375549238218940497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17504990334797968583841325 6564371375549238218940497)
                  ·
                    refine ⟨4923278531661928664205373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6564371375549238218940497 4923278531661928664205373)
                    ·
                      refine ⟨1846229449373223249077015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4923278531661928664205373 1846229449373223249077015)
                      ·
                        rfl

theorem cell23_3595519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 2, 3, 2, 3].length) (baseStart_3595519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3595519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3595519 prefixEnd_3595519 := by exact prefixLift 3595519
  have htrace : WordTrace (prefixWord ++ tailWord_3595519) baseStart_3595519 baseEnd_3595519 := by
    simpa [prefixWord, tailWord_3595519, baseEnd_3595519] using wordTrace_append hprefix tailTrace_3595519
  have hstable : (prefixWord ++ tailWord_3595519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3595519).length < 2 ^ (prefixWord ++ tailWord_3595519).sum := by decide
  have hdescent : baseEnd_3595519 < baseStart_3595519 := by decide
  rcases family_descends (prefixWord ++ tailWord_3595519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3595529 : List Nat := [1, 2, 1, 1, 3, 3, 4, 1, 1, 2, 4]
def baseStart_3595529 : Nat := 118140960795 + 3595529 * 2 ^ 59
def prefixEnd_3595529 : Nat := 4983230072969 + 3 ^ 40 * 3595529 * 2
def baseEnd_3595529 : Nat := 1846234584179768209951969

theorem tailTrace_3595529 : CollatzResearch.WordTrace tailWord_3595529 prefixEnd_3595529 1846234584179768209951969 := by
  unfold tailWord_3595529
  simp only [CollatzResearch.WordTrace]
  refine ⟨131139716191019975309901641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87426477460679983539934427 131139716191019975309901641)
  ·
    refine ⟨98354787143264981482426231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131139716191019975309901641 98354787143264981482426231)
    ·
      refine ⟨147532180714897472223639347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98354787143264981482426231 147532180714897472223639347)
      ·
        refine ⟨221298271072346208335459021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147532180714897472223639347 221298271072346208335459021)
        ·
          refine ⟨82986851652129828125797133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 221298271072346208335459021 82986851652129828125797133)
          ·
            refine ⟨31120069369548685547173925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82986851652129828125797133 31120069369548685547173925)
            ·
              refine ⟨5835013006790378540095111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31120069369548685547173925 5835013006790378540095111)
              ·
                refine ⟨8752519510185567810142667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5835013006790378540095111 8752519510185567810142667)
                ·
                  refine ⟨13128779265278351715214001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8752519510185567810142667 13128779265278351715214001)
                  ·
                    refine ⟨9846584448958763786410501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13128779265278351715214001 9846584448958763786410501)
                    ·
                      refine ⟨1846234584179768209951969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9846584448958763786410501 1846234584179768209951969)
                      ·
                        rfl

theorem cell23_3595529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 4, 1, 1, 2, 4].length) (baseStart_3595529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3595529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3595529 prefixEnd_3595529 := by exact prefixLift 3595529
  have htrace : WordTrace (prefixWord ++ tailWord_3595529) baseStart_3595529 baseEnd_3595529 := by
    simpa [prefixWord, tailWord_3595529, baseEnd_3595529] using wordTrace_append hprefix tailTrace_3595529
  have hstable : (prefixWord ++ tailWord_3595529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3595529).length < 2 ^ (prefixWord ++ tailWord_3595529).sum := by decide
  have hdescent : baseEnd_3595529 < baseStart_3595529 := by decide
  rcases family_descends (prefixWord ++ tailWord_3595529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3595550 : List Nat := [4, 3, 2, 1, 2, 1, 1, 3, 1, 1, 4]
def baseStart_3595550 : Nat := 118140960795 + 3595550 * 2 ^ 59
def prefixEnd_3595550 : Nat := 4983230072969 + 3 ^ 40 * 3595550 * 2
def baseEnd_3595550 : Nat := 1846245367273512627789373

theorem tailTrace_3595550 : CollatzResearch.WordTrace tailWord_3595550 prefixEnd_3595550 1846245367273512627789373 := by
  unfold tailWord_3595550
  simp only [CollatzResearch.WordTrace]
  refine ⟨16392560265492986987052013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87426988082629263930944069 16392560265492986987052013)
  ·
    refine ⟨6147210099559870120144505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16392560265492986987052013 6147210099559870120144505)
    ·
      refine ⟨4610407574669902590108379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6147210099559870120144505 4610407574669902590108379)
      ·
        refine ⟨6915611362004853885162569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4610407574669902590108379 6915611362004853885162569)
        ·
          refine ⟨5186708521503640413871927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6915611362004853885162569 5186708521503640413871927)
          ·
            refine ⟨7780062782255460620807891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5186708521503640413871927 7780062782255460620807891)
            ·
              refine ⟨11670094173383190931211837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7780062782255460620807891 11670094173383190931211837)
              ·
                refine ⟨4376285315018696599204439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11670094173383190931211837 4376285315018696599204439)
                ·
                  refine ⟨6564427972528044898806659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4376285315018696599204439 6564427972528044898806659)
                  ·
                    refine ⟨9846641958792067348209989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6564427972528044898806659 9846641958792067348209989)
                    ·
                      refine ⟨1846245367273512627789373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9846641958792067348209989 1846245367273512627789373)
                      ·
                        rfl

theorem cell23_3595550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_3595550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3595550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3595550 prefixEnd_3595550 := by exact prefixLift 3595550
  have htrace : WordTrace (prefixWord ++ tailWord_3595550) baseStart_3595550 baseEnd_3595550 := by
    simpa [prefixWord, tailWord_3595550, baseEnd_3595550] using wordTrace_append hprefix tailTrace_3595550
  have hstable : (prefixWord ++ tailWord_3595550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3595550).length < 2 ^ (prefixWord ++ tailWord_3595550).sum := by decide
  have hdescent : baseEnd_3595550 < baseStart_3595550 := by decide
  rcases family_descends (prefixWord ++ tailWord_3595550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3595639 : List Nat := [1, 1, 3, 1, 1, 2, 4, 1, 1, 5, 3]
def baseStart_3595639 : Nat := 118140960795 + 3595639 * 2 ^ 59
def prefixEnd_3595639 : Nat := 4983230072969 + 3 ^ 40 * 3595639 * 2
def baseEnd_3595639 : Nat := 1846291067051762779576463

theorem tailTrace_3595639 : CollatzResearch.WordTrace tailWord_3595639 prefixEnd_3595639 1846291067051762779576463 := by
  unfold tailWord_3595639
  simp only [CollatzResearch.WordTrace]
  refine ⟨131143728220621464096405971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87429152147080976064270647 131143728220621464096405971)
  ·
    refine ⟨196715592330932196144608957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131143728220621464096405971 196715592330932196144608957)
    ·
      refine ⟨73768347124099573554228359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196715592330932196144608957 73768347124099573554228359)
      ·
        refine ⟨110652520686149360331342539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73768347124099573554228359 110652520686149360331342539)
        ·
          refine ⟨165978781029224040497013809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110652520686149360331342539 165978781029224040497013809)
          ·
            refine ⟨124484085771918030372760357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165978781029224040497013809 124484085771918030372760357)
            ·
              refine ⟨23340766082234630694892567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 124484085771918030372760357 23340766082234630694892567)
              ·
                refine ⟨35011149123351946042338851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23340766082234630694892567 35011149123351946042338851)
                ·
                  refine ⟨52516723685027919063508277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35011149123351946042338851 52516723685027919063508277)
                  ·
                    refine ⟨4923442845471367412203901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52516723685027919063508277 4923442845471367412203901)
                    ·
                      refine ⟨1846291067051762779576463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4923442845471367412203901 1846291067051762779576463)
                      ·
                        rfl

theorem cell23_3595639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 1, 1, 5, 3].length) (baseStart_3595639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3595639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3595639 prefixEnd_3595639 := by exact prefixLift 3595639
  have htrace : WordTrace (prefixWord ++ tailWord_3595639) baseStart_3595639 baseEnd_3595639 := by
    simpa [prefixWord, tailWord_3595639, baseEnd_3595639] using wordTrace_append hprefix tailTrace_3595639
  have hstable : (prefixWord ++ tailWord_3595639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3595639).length < 2 ^ (prefixWord ++ tailWord_3595639).sum := by decide
  have hdescent : baseEnd_3595639 < baseStart_3595639 := by decide
  rcases family_descends (prefixWord ++ tailWord_3595639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3595669 : List Nat := [1, 3, 2, 1, 1, 2, 3, 2, 1, 2, 5]
def baseStart_3595669 : Nat := 118140960795 + 3595669 * 2 ^ 59
def prefixEnd_3595669 : Nat := 4983230072969 + 3 ^ 40 * 3595669 * 2
def baseEnd_3595669 : Nat := 1846306471471397662201325

theorem tailTrace_3595669 : CollatzResearch.WordTrace tailWord_3595669 prefixEnd_3595669 1846306471471397662201325 := by
  unfold tailWord_3595669
  simp only [CollatzResearch.WordTrace]
  refine ⟨131144822410512779219998061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87429881607008519479998707 131144822410512779219998061)
  ·
    refine ⟨49179308403942292207499273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131144822410512779219998061 49179308403942292207499273)
    ·
      refine ⟨36884481302956719155624455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49179308403942292207499273 36884481302956719155624455)
      ·
        refine ⟨55326721954435078733436683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36884481302956719155624455 55326721954435078733436683)
        ·
          refine ⟨82990082931652618100155025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55326721954435078733436683 82990082931652618100155025)
          ·
            refine ⟨62242562198739463575116269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82990082931652618100155025 62242562198739463575116269)
            ·
              refine ⟨23340960824527298840668601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62242562198739463575116269 23340960824527298840668601)
              ·
                refine ⟨17505720618395474130501451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23340960824527298840668601 17505720618395474130501451)
                ·
                  refine ⟨26258580927593211195752177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17505720618395474130501451 26258580927593211195752177)
                  ·
                    refine ⟨19693935695694908396814133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26258580927593211195752177 19693935695694908396814133)
                    ·
                      refine ⟨1846306471471397662201325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19693935695694908396814133 1846306471471397662201325)
                      ·
                        rfl

theorem cell23_3595669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 2, 1, 2, 5].length) (baseStart_3595669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3595669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3595669 prefixEnd_3595669 := by exact prefixLift 3595669
  have htrace : WordTrace (prefixWord ++ tailWord_3595669) baseStart_3595669 baseEnd_3595669 := by
    simpa [prefixWord, tailWord_3595669, baseEnd_3595669] using wordTrace_append hprefix tailTrace_3595669
  have hstable : (prefixWord ++ tailWord_3595669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3595669).length < 2 ^ (prefixWord ++ tailWord_3595669).sum := by decide
  have hdescent : baseEnd_3595669 < baseStart_3595669 := by decide
  rcases family_descends (prefixWord ++ tailWord_3595669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3595719 : List Nat := [1, 1, 4, 1, 1, 3, 2, 2, 8]
def baseStart_3595719 : Nat := 118140960795 + 3595719 * 2 ^ 59
def prefixEnd_3595719 : Nat := 4983230072969 + 3 ^ 40 * 3595719 * 2
def baseEnd_3595719 : Nat := 205148016167124718508455

theorem tailTrace_3595719 : CollatzResearch.WordTrace tailWord_3595719 prefixEnd_3595719 205148016167124718508455 := by
  unfold tailWord_3595719
  simp only [CollatzResearch.WordTrace]
  refine ⟨131146646060331637759318211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87431097373554425172878807 131146646060331637759318211)
  ·
    refine ⟨196719969090497456638977317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131146646060331637759318211 196719969090497456638977317)
    ·
      refine ⟨36884994204468273119808247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 196719969090497456638977317 36884994204468273119808247)
      ·
        refine ⟨55327491306702409679712371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36884994204468273119808247 55327491306702409679712371)
        ·
          refine ⟨82991236960053614519568557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55327491306702409679712371 82991236960053614519568557)
          ·
            refine ⟨31121713860020105444838209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82991236960053614519568557 31121713860020105444838209)
            ·
              refine ⟨23341285395015079083628657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31121713860020105444838209 23341285395015079083628657)
              ·
                refine ⟨17505964046261309312721493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23341285395015079083628657 17505964046261309312721493)
                ·
                  refine ⟨205148016167124718508455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17505964046261309312721493 205148016167124718508455)
                  ·
                    rfl

theorem cell23_3595719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 2, 8].length) (baseStart_3595719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3595719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3595719 prefixEnd_3595719 := by exact prefixLift 3595719
  have htrace : WordTrace (prefixWord ++ tailWord_3595719) baseStart_3595719 baseEnd_3595719 := by
    simpa [prefixWord, tailWord_3595719, baseEnd_3595719] using wordTrace_append hprefix tailTrace_3595719
  have hstable : (prefixWord ++ tailWord_3595719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3595719).length < 2 ^ (prefixWord ++ tailWord_3595719).sum := by decide
  have hdescent : baseEnd_3595719 < baseStart_3595719 := by decide
  rcases family_descends (prefixWord ++ tailWord_3595719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3595723 : List Nat := [1, 1, 1, 1, 3, 3, 3, 5, 1, 4]
def baseStart_3595723 : Nat := 118140960795 + 3595723 * 2 ^ 59
def prefixEnd_3595723 : Nat := 4983230072969 + 3 ^ 40 * 3595723 * 2
def baseEnd_3595723 : Nat := 615444733142246816975359

theorem tailTrace_3595723 : CollatzResearch.WordTrace tailWord_3595723 prefixEnd_3595723 615444733142246816975359 := by
  unfold tailWord_3595723
  simp only [CollatzResearch.WordTrace]
  refine ⟨131146791952317146442463823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87431194634878097628309215 131146791952317146442463823)
  ·
    refine ⟨196720187928475719663695735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131146791952317146442463823 196720187928475719663695735)
    ·
      refine ⟨295080281892713579495543603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196720187928475719663695735 295080281892713579495543603)
      ·
        refine ⟨442620422839070369243315405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295080281892713579495543603 442620422839070369243315405)
        ·
          refine ⟨165982658564651388466243277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 442620422839070369243315405 165982658564651388466243277)
          ·
            refine ⟨62243496961744270674841229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 165982658564651388466243277 62243496961744270674841229)
            ·
              refine ⟨23341311360654101503065461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62243496961744270674841229 23341311360654101503065461)
              ·
                refine ⟨2188247940061322015912387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23341311360654101503065461 2188247940061322015912387)
                ·
                  refine ⟨3282371910091983023868581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2188247940061322015912387 3282371910091983023868581)
                  ·
                    refine ⟨615444733142246816975359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3282371910091983023868581 615444733142246816975359)
                    ·
                      rfl

theorem cell23_3595723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 5, 1, 4].length) (baseStart_3595723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3595723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3595723 prefixEnd_3595723 := by exact prefixLift 3595723
  have htrace : WordTrace (prefixWord ++ tailWord_3595723) baseStart_3595723 baseEnd_3595723 := by
    simpa [prefixWord, tailWord_3595723, baseEnd_3595723] using wordTrace_append hprefix tailTrace_3595723
  have hstable : (prefixWord ++ tailWord_3595723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3595723).length < 2 ^ (prefixWord ++ tailWord_3595723).sum := by decide
  have hdescent : baseEnd_3595723 < baseStart_3595723 := by decide
  rcases family_descends (prefixWord ++ tailWord_3595723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3595736 : List Nat := [2, 1, 2, 2, 2, 1, 5, 2, 6]
def baseStart_3595736 : Nat := 118140960795 + 3595736 * 2 ^ 59
def prefixEnd_3595736 : Nat := 4983230072969 + 3 ^ 40 * 3595736 * 2
def baseEnd_3595736 : Nat := 205148986075027655562613

theorem tailTrace_3595736 : CollatzResearch.WordTrace tailWord_3595736 prefixEnd_3595736 205148986075027655562613 := by
  unfold tailWord_3595736
  simp only [CollatzResearch.WordTrace]
  refine ⟨65573633050635024831343531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87431510734180033108458041 65573633050635024831343531)
  ·
    refine ⟨98360449575952537247015297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65573633050635024831343531 98360449575952537247015297)
    ·
      refine ⟨73770337181964402935261473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98360449575952537247015297 73770337181964402935261473)
      ·
        refine ⟨55327752886473302201446105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73770337181964402935261473 55327752886473302201446105)
        ·
          refine ⟨41495814664854976651084579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55327752886473302201446105 41495814664854976651084579)
          ·
            refine ⟨62243721997282464976626869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41495814664854976651084579 62243721997282464976626869)
            ·
              refine ⟨5835348937245231091558769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62243721997282464976626869 5835348937245231091558769)
              ·
                refine ⟨4376511702933923318669077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5835348937245231091558769 4376511702933923318669077)
                ·
                  refine ⟨205148986075027655562613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4376511702933923318669077 205148986075027655562613)
                  ·
                    rfl

theorem cell23_3595736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 5, 2, 6].length) (baseStart_3595736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3595736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3595736 prefixEnd_3595736 := by exact prefixLift 3595736
  have htrace : WordTrace (prefixWord ++ tailWord_3595736) baseStart_3595736 baseEnd_3595736 := by
    simpa [prefixWord, tailWord_3595736, baseEnd_3595736] using wordTrace_append hprefix tailTrace_3595736
  have hstable : (prefixWord ++ tailWord_3595736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3595736).length < 2 ^ (prefixWord ++ tailWord_3595736).sum := by decide
  have hdescent : baseEnd_3595736 < baseStart_3595736 := by decide
  rcases family_descends (prefixWord ++ tailWord_3595736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3595759 : List Nat := [1, 1, 2, 1, 4, 1, 2, 1, 2, 1, 7]
def baseStart_3595759 : Nat := 118140960795 + 3595759 * 2 ^ 59
def prefixEnd_3595759 : Nat := 4983230072969 + 3 ^ 40 * 3595759 * 2
def baseEnd_3595759 : Nat := 1846352684730302310075911

theorem tailTrace_3595759 : CollatzResearch.WordTrace tailWord_3595759 prefixEnd_3595759 1846352684730302310075911 := by
  unfold tailWord_3595759
  simp only [CollatzResearch.WordTrace]
  refine ⟨131148104980186724590774331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87432069986791149727182887 131148104980186724590774331)
  ·
    refine ⟨196722157470280086886161497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131148104980186724590774331 196722157470280086886161497)
    ·
      refine ⟨147541618102710065164621123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196722157470280086886161497 147541618102710065164621123)
      ·
        refine ⟨221312427154065097746931685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147541618102710065164621123 221312427154065097746931685)
        ·
          refine ⟨41496080091387205827549691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 221312427154065097746931685 41496080091387205827549691)
          ·
            refine ⟨62244120137080808741324537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41496080091387205827549691 62244120137080808741324537)
            ·
              refine ⟨46683090102810606555993403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62244120137080808741324537 46683090102810606555993403)
              ·
                refine ⟨70024635154215909833990105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46683090102810606555993403 70024635154215909833990105)
                ·
                  refine ⟨52518476365661932375492579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70024635154215909833990105 52518476365661932375492579)
                  ·
                    refine ⟨78777714548492898563238869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52518476365661932375492579 78777714548492898563238869)
                    ·
                      refine ⟨1846352684730302310075911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 78777714548492898563238869 1846352684730302310075911)
                      ·
                        rfl

theorem cell23_3595759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 2, 1, 7].length) (baseStart_3595759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3595759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3595759 prefixEnd_3595759 := by exact prefixLift 3595759
  have htrace : WordTrace (prefixWord ++ tailWord_3595759) baseStart_3595759 baseEnd_3595759 := by
    simpa [prefixWord, tailWord_3595759, baseEnd_3595759] using wordTrace_append hprefix tailTrace_3595759
  have hstable : (prefixWord ++ tailWord_3595759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3595759).length < 2 ^ (prefixWord ++ tailWord_3595759).sum := by decide
  have hdescent : baseEnd_3595759 < baseStart_3595759 := by decide
  rcases family_descends (prefixWord ++ tailWord_3595759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3595773 : List Nat := [1, 4, 1, 1, 1, 4, 2, 1, 1, 5, 2]
def baseStart_3595773 : Nat := 118140960795 + 3595773 * 2 ^ 59
def prefixEnd_3595773 : Nat := 4983230072969 + 3 ^ 40 * 3595773 * 2
def baseEnd_3595773 : Nat := 1846359873459465255300847

theorem tailTrace_3595773 : CollatzResearch.WordTrace tailWord_3595773 prefixEnd_3595773 1846359873459465255300847 := by
  unfold tailWord_3595773
  simp only [CollatzResearch.WordTrace]
  refine ⟨131148615602136004981783973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87432410401424003321189315 131148615602136004981783973)
  ·
    refine ⟨24590365425400500934084495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 131148615602136004981783973 24590365425400500934084495)
    ·
      refine ⟨36885548138100751401126743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24590365425400500934084495 36885548138100751401126743)
      ·
        refine ⟨55328322207151127101690115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36885548138100751401126743 55328322207151127101690115)
        ·
          refine ⟨82992483310726690652535173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55328322207151127101690115 82992483310726690652535173)
          ·
            refine ⟨15561090620761254497350345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82992483310726690652535173 15561090620761254497350345)
            ·
              refine ⟨11670817965570940873012759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15561090620761254497350345 11670817965570940873012759)
              ·
                refine ⟨17506226948356411309519139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11670817965570940873012759 17506226948356411309519139)
                ·
                  refine ⟨26259340422534616964278709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17506226948356411309519139 26259340422534616964278709)
                  ·
                    refine ⟨2461813164612620340401129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26259340422534616964278709 2461813164612620340401129)
                    ·
                      refine ⟨1846359873459465255300847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2461813164612620340401129 1846359873459465255300847)
                      ·
                        rfl

theorem cell23_3595773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 1, 1, 5, 2].length) (baseStart_3595773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3595773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3595773 prefixEnd_3595773 := by exact prefixLift 3595773
  have htrace : WordTrace (prefixWord ++ tailWord_3595773) baseStart_3595773 baseEnd_3595773 := by
    simpa [prefixWord, tailWord_3595773, baseEnd_3595773] using wordTrace_append hprefix tailTrace_3595773
  have hstable : (prefixWord ++ tailWord_3595773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3595773).length < 2 ^ (prefixWord ++ tailWord_3595773).sum := by decide
  have hdescent : baseEnd_3595773 < baseStart_3595773 := by decide
  rcases family_descends (prefixWord ++ tailWord_3595773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3595783 : List Nat := [1, 1, 4, 3, 2, 1, 2, 3, 1, 5]
def baseStart_3595783 : Nat := 118140960795 + 3595783 * 2 ^ 59
def prefixEnd_3595783 : Nat := 4983230072969 + 3 ^ 40 * 3595783 * 2
def baseEnd_3595783 : Nat := 615455002755336738725267

theorem tailTrace_3595783 : CollatzResearch.WordTrace tailWord_3595783 prefixEnd_3595783 615455002755336738725267 := by
  unfold tailWord_3595783
  simp only [CollatzResearch.WordTrace]
  refine ⟨131148980332099776689648003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87432653554733184459765335 131148980332099776689648003)
  ·
    refine ⟨196723470498149665034472005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131148980332099776689648003 196723470498149665034472005)
    ·
      refine ⟨36885650718403062193963501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 196723470498149665034472005 36885650718403062193963501)
      ·
        refine ⟨13832119019401148322736313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36885650718403062193963501 13832119019401148322736313)
        ·
          refine ⟨10374089264550861242052235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13832119019401148322736313 10374089264550861242052235)
          ·
            refine ⟨15561133896826291863078353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10374089264550861242052235 15561133896826291863078353)
            ·
              refine ⟨11670850422619718897308765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15561133896826291863078353 11670850422619718897308765)
              ·
                refine ⟨4376568908482394586490787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11670850422619718897308765 4376568908482394586490787)
                ·
                  refine ⟨6564853362723591879736181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4376568908482394586490787 6564853362723591879736181)
                  ·
                    refine ⟨615455002755336738725267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6564853362723591879736181 615455002755336738725267)
                    ·
                      rfl

theorem cell23_3595783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 3, 1, 5].length) (baseStart_3595783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3595783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3595783 prefixEnd_3595783 := by exact prefixLift 3595783
  have htrace : WordTrace (prefixWord ++ tailWord_3595783) baseStart_3595783 baseEnd_3595783 := by
    simpa [prefixWord, tailWord_3595783, baseEnd_3595783] using wordTrace_append hprefix tailTrace_3595783
  have hstable : (prefixWord ++ tailWord_3595783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3595783).length < 2 ^ (prefixWord ++ tailWord_3595783).sum := by decide
  have hdescent : baseEnd_3595783 < baseStart_3595783 := by decide
  rcases family_descends (prefixWord ++ tailWord_3595783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3595830 : List Nat := [5, 1, 2, 1, 3, 1, 1, 2, 1, 6]
def baseStart_3595830 : Nat := 118140960795 + 3595830 * 2 ^ 59
def prefixEnd_3595830 : Nat := 4983230072969 + 3 ^ 40 * 3595830 * 2
def baseEnd_3595830 : Nat := 615463047285590510762695

theorem tailTrace_3595830 : CollatzResearch.WordTrace tailWord_3595830 prefixEnd_3595830 615463047285590510762695 := by
  unfold tailWord_3595830
  simp only [CollatzResearch.WordTrace]
  refine ⟨8196918410183093982288059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 87433796375286335811072629 8196918410183093982288059)
  ·
    refine ⟨12295377615274640973432089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8196918410183093982288059 12295377615274640973432089)
    ·
      refine ⟨9221533211455980730074067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12295377615274640973432089 9221533211455980730074067)
      ·
        refine ⟨13832299817183971095111101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9221533211455980730074067 13832299817183971095111101)
        ·
          refine ⟨5187112431443989160666663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13832299817183971095111101 5187112431443989160666663)
          ·
            refine ⟨7780668647165983740999995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5187112431443989160666663 7780668647165983740999995)
            ·
              refine ⟨11671002970748975611499993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7780668647165983740999995 11671002970748975611499993)
              ·
                refine ⟨8753252228061731708624995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11671002970748975611499993 8753252228061731708624995)
                ·
                  refine ⟨13129878342092597562937493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8753252228061731708624995 13129878342092597562937493)
                  ·
                    refine ⟨615463047285590510762695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13129878342092597562937493 615463047285590510762695)
                    ·
                      rfl

theorem cell23_3595830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 2, 1, 6].length) (baseStart_3595830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3595830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3595830 prefixEnd_3595830 := by exact prefixLift 3595830
  have htrace : WordTrace (prefixWord ++ tailWord_3595830) baseStart_3595830 baseEnd_3595830 := by
    simpa [prefixWord, tailWord_3595830, baseEnd_3595830] using wordTrace_append hprefix tailTrace_3595830
  have hstable : (prefixWord ++ tailWord_3595830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3595830).length < 2 ^ (prefixWord ++ tailWord_3595830).sum := by decide
  have hdescent : baseEnd_3595830 < baseStart_3595830 := by decide
  rcases family_descends (prefixWord ++ tailWord_3595830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3595833 : List Nat := [1, 2, 1, 5, 1, 3, 1, 2, 1, 2, 4]
def baseStart_3595833 : Nat := 118140960795 + 3595833 * 2 ^ 59
def prefixEnd_3595833 : Nat := 4983230072969 + 3 ^ 40 * 3595833 * 2
def baseEnd_3595833 : Nat := 1846390682298735020550571

theorem tailTrace_3595833 : CollatzResearch.WordTrace tailWord_3595833 prefixEnd_3595833 1846390682298735020550571 := by
  unfold tailWord_3595833
  simp only [CollatzResearch.WordTrace]
  refine ⟨131150803981918635228968153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87433869321279090152645435 131150803981918635228968153)
  ·
    refine ⟨98363102986438976421726115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131150803981918635228968153 98363102986438976421726115)
    ·
      refine ⟨147544654479658464632589173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98363102986438976421726115 147544654479658464632589173)
      ·
        refine ⟨13832311357467981059305235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 147544654479658464632589173 13832311357467981059305235)
        ·
          refine ⟨20748467036201971588957853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13832311357467981059305235 20748467036201971588957853)
          ·
            refine ⟨7780675138575739345859195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20748467036201971588957853 7780675138575739345859195)
            ·
              refine ⟨11671012707863609018788793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7780675138575739345859195 11671012707863609018788793)
              ·
                refine ⟨8753259530897706764091595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11671012707863609018788793 8753259530897706764091595)
                ·
                  refine ⟨13129889296346560146137393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8753259530897706764091595 13129889296346560146137393)
                  ·
                    refine ⟨9847416972259920109603045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13129889296346560146137393 9847416972259920109603045)
                    ·
                      refine ⟨1846390682298735020550571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9847416972259920109603045 1846390682298735020550571)
                      ·
                        rfl

theorem cell23_3595833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_3595833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3595833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3595833 prefixEnd_3595833 := by exact prefixLift 3595833
  have htrace : WordTrace (prefixWord ++ tailWord_3595833) baseStart_3595833 baseEnd_3595833 := by
    simpa [prefixWord, tailWord_3595833, baseEnd_3595833] using wordTrace_append hprefix tailTrace_3595833
  have hstable : (prefixWord ++ tailWord_3595833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3595833).length < 2 ^ (prefixWord ++ tailWord_3595833).sum := by decide
  have hdescent : baseEnd_3595833 < baseStart_3595833 := by decide
  rcases family_descends (prefixWord ++ tailWord_3595833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3595837 : List Nat := [1, 4, 1, 3, 3, 1, 3, 1, 1, 1, 4]
def baseStart_3595837 : Nat := 118140960795 + 3595837 * 2 ^ 59
def prefixEnd_3595837 : Nat := 4983230072969 + 3 ^ 40 * 3595837 * 2
def baseEnd_3595837 : Nat := 1846392736221353004900553

theorem tailTrace_3595837 : CollatzResearch.WordTrace tailWord_3595837 prefixEnd_3595837 1846392736221353004900553 := by
  unfold tailWord_3595837
  simp only [CollatzResearch.WordTrace]
  refine ⟨131150949873904143912113765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87433966582602762608075843 131150949873904143912113765)
  ·
    refine ⟨24590803101357026983521331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 131150949873904143912113765 24590803101357026983521331)
    ·
      refine ⟨36886204652035540475281997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24590803101357026983521331 36886204652035540475281997)
      ·
        refine ⟨13832326744513327678230749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36886204652035540475281997 13832326744513327678230749)
        ·
          refine ⟨5187122529192497879336531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13832326744513327678230749 5187122529192497879336531)
          ·
            refine ⟨7780683793788746819004797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5187122529192497879336531 7780683793788746819004797)
            ·
              refine ⟨2917756422670780057126799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7780683793788746819004797 2917756422670780057126799)
              ·
                refine ⟨4376634634006170085690199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2917756422670780057126799 4376634634006170085690199)
                ·
                  refine ⟨6564951951009255128535299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4376634634006170085690199 6564951951009255128535299)
                  ·
                    refine ⟨9847427926513882692802949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6564951951009255128535299 9847427926513882692802949)
                    ·
                      refine ⟨1846392736221353004900553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9847427926513882692802949 1846392736221353004900553)
                      ·
                        rfl

theorem cell23_3595837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 3, 1, 1, 1, 4].length) (baseStart_3595837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3595837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3595837 prefixEnd_3595837 := by exact prefixLift 3595837
  have htrace : WordTrace (prefixWord ++ tailWord_3595837) baseStart_3595837 baseEnd_3595837 := by
    simpa [prefixWord, tailWord_3595837, baseEnd_3595837] using wordTrace_append hprefix tailTrace_3595837
  have hstable : (prefixWord ++ tailWord_3595837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3595837).length < 2 ^ (prefixWord ++ tailWord_3595837).sum := by decide
  have hdescent : baseEnd_3595837 < baseStart_3595837 := by decide
  rcases family_descends (prefixWord ++ tailWord_3595837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3595927 : List Nat := [1, 1, 3, 3, 2, 4, 1, 1, 1, 4, 2]
def baseStart_3595927 : Nat := 118140960795 + 3595927 * 2 ^ 59
def prefixEnd_3595927 : Nat := 4983230072969 + 3 ^ 40 * 3595927 * 2
def baseEnd_3595927 : Nat := 1846438949480257652775139

theorem tailTrace_3595927 : CollatzResearch.WordTrace tailWord_3595927 prefixEnd_3595927 1846438949480257652775139 := by
  unfold tailWord_3595927
  simp only [CollatzResearch.WordTrace]
  refine ⟨131154232443578089282890035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87436154962385392855260023 131154232443578089282890035)
  ·
    refine ⟨196731348665367133924335053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131154232443578089282890035 196731348665367133924335053)
    ·
      refine ⟨73774255749512675221625645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196731348665367133924335053 73774255749512675221625645)
      ·
        refine ⟨27665345906067253208109617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73774255749512675221625645 27665345906067253208109617)
        ·
          refine ⟨20749009429550439906082213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27665345906067253208109617 20749009429550439906082213)
          ·
            refine ⟨3890439268040707482390415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20749009429550439906082213 3890439268040707482390415)
            ·
              refine ⟨5835658902061061223585623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3890439268040707482390415 5835658902061061223585623)
              ·
                refine ⟨8753488353091591835378435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5835658902061061223585623 8753488353091591835378435)
                ·
                  refine ⟨13130232529637387753067653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8753488353091591835378435 13130232529637387753067653)
                  ·
                    refine ⟨2461918599307010203700185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13130232529637387753067653 2461918599307010203700185)
                    ·
                      refine ⟨1846438949480257652775139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2461918599307010203700185 1846438949480257652775139)
                      ·
                        rfl

theorem cell23_3595927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 1, 1, 1, 4, 2].length) (baseStart_3595927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3595927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3595927 prefixEnd_3595927 := by exact prefixLift 3595927
  have htrace : WordTrace (prefixWord ++ tailWord_3595927) baseStart_3595927 baseEnd_3595927 := by
    simpa [prefixWord, tailWord_3595927, baseEnd_3595927] using wordTrace_append hprefix tailTrace_3595927
  have hstable : (prefixWord ++ tailWord_3595927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3595927).length < 2 ^ (prefixWord ++ tailWord_3595927).sum := by decide
  have hdescent : baseEnd_3595927 < baseStart_3595927 := by decide
  rcases family_descends (prefixWord ++ tailWord_3595927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3595978 : List Nat := [3, 1, 2, 1, 6, 1, 2, 1, 2, 2, 2]
def baseStart_3595978 : Nat := 118140960795 + 3595978 * 2 ^ 59
def prefixEnd_3595978 : Nat := 4983230072969 + 3 ^ 40 * 3595978 * 2
def baseEnd_3595978 : Nat := 1846465136993636953237405

theorem tailTrace_3595978 : CollatzResearch.WordTrace tailWord_3595978 prefixEnd_3595978 1846465136993636953237405 := by
  unfold tailWord_3595978
  simp only [CollatzResearch.WordTrace]
  refine ⟨32789023141598331248249147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87437395044262216661997725 32789023141598331248249147)
  ·
    refine ⟨49183534712397496872373721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32789023141598331248249147 49183534712397496872373721)
    ·
      refine ⟨36887651034298122654280291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49183534712397496872373721 36887651034298122654280291)
      ·
        refine ⟨55331476551447183981420437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36887651034298122654280291 55331476551447183981420437)
        ·
          refine ⟨2593662963349086749129083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 55331476551447183981420437 2593662963349086749129083)
          ·
            refine ⟨3890494445023630123693625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2593662963349086749129083 3890494445023630123693625)
            ·
              refine ⟨2917870833767722592770219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3890494445023630123693625 2917870833767722592770219)
              ·
                refine ⟨4376806250651583889155329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2917870833767722592770219 4376806250651583889155329)
                ·
                  refine ⟨3282604687988687916866497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4376806250651583889155329 3282604687988687916866497)
                  ·
                    refine ⟨2461953515991515937649873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3282604687988687916866497 2461953515991515937649873)
                    ·
                      refine ⟨1846465136993636953237405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2461953515991515937649873 1846465136993636953237405)
                      ·
                        rfl

theorem cell23_3595978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 2, 1, 2, 2, 2].length) (baseStart_3595978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3595978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3595978 prefixEnd_3595978 := by exact prefixLift 3595978
  have htrace : WordTrace (prefixWord ++ tailWord_3595978) baseStart_3595978 baseEnd_3595978 := by
    simpa [prefixWord, tailWord_3595978, baseEnd_3595978] using wordTrace_append hprefix tailTrace_3595978
  have hstable : (prefixWord ++ tailWord_3595978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3595978).length < 2 ^ (prefixWord ++ tailWord_3595978).sum := by decide
  have hdescent : baseEnd_3595978 < baseStart_3595978 := by decide
  rcases family_descends (prefixWord ++ tailWord_3595978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3596023 : List Nat := [1, 1, 3, 1, 1, 1, 5, 4, 6]
def baseStart_3596023 : Nat := 118140960795 + 3596023 * 2 ^ 59
def prefixEnd_3596023 : Nat := 4983230072969 + 3 ^ 40 * 3596023 * 2
def baseEnd_3596023 : Nat := 205165360402565475241633

theorem tailTrace_3596023 : CollatzResearch.WordTrace tailWord_3596023 prefixEnd_3596023 205165360402565475241633 := by
  unfold tailWord_3596023
  simp only [CollatzResearch.WordTrace]
  refine ⟨131157733851230297678384723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87438489234153531785589815 131157733851230297678384723)
  ·
    refine ⟨196736600776845446517577085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131157733851230297678384723 196736600776845446517577085)
    ·
      refine ⟨73776225291317042444091407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196736600776845446517577085 73776225291317042444091407)
      ·
        refine ⟨110664337936975563666137111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73776225291317042444091407 110664337936975563666137111)
        ·
          refine ⟨165996506905463345499205667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110664337936975563666137111 165996506905463345499205667)
          ·
            refine ⟨248994760358195018248808501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165996506905463345499205667 248994760358195018248808501)
            ·
              refine ⟨23343258783580782960825797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 248994760358195018248808501 23343258783580782960825797)
              ·
                refine ⟨4376861021921396805154837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23343258783580782960825797 4376861021921396805154837)
                ·
                  refine ⟨205165360402565475241633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4376861021921396805154837 205165360402565475241633)
                  ·
                    rfl

theorem cell23_3596023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 4, 6].length) (baseStart_3596023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3596023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3596023 prefixEnd_3596023 := by exact prefixLift 3596023
  have htrace : WordTrace (prefixWord ++ tailWord_3596023) baseStart_3596023 baseEnd_3596023 := by
    simpa [prefixWord, tailWord_3596023, baseEnd_3596023] using wordTrace_append hprefix tailTrace_3596023
  have hstable : (prefixWord ++ tailWord_3596023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3596023).length < 2 ^ (prefixWord ++ tailWord_3596023).sum := by decide
  have hdescent : baseEnd_3596023 < baseStart_3596023 := by decide
  rcases family_descends (prefixWord ++ tailWord_3596023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3596084 : List Nat := [2, 5, 1, 1, 2, 1, 1, 3, 3, 1, 3]
def baseStart_3596084 : Nat := 118140960795 + 3596084 * 2 ^ 59
def prefixEnd_3596084 : Nat := 4983230072969 + 3 ^ 40 * 3596084 * 2
def baseEnd_3596084 : Nat := 1846519565943013538511917

theorem tailTrace_3596084 : CollatzResearch.WordTrace tailWord_3596084 prefixEnd_3596084 1846519565943013538511917 := by
  unfold tailWord_3596084
  simp only [CollatzResearch.WordTrace]
  refine ⟨65579979352004652548177653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87439972469339536730903537 65579979352004652548177653)
  ·
    refine ⟨6148123064250436176391655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 65579979352004652548177653 6148123064250436176391655)
    ·
      refine ⟨9222184596375654264587483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6148123064250436176391655 9222184596375654264587483)
      ·
        refine ⟨13833276894563481396881225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9222184596375654264587483 13833276894563481396881225)
        ·
          refine ⟨10374957670922611047660919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13833276894563481396881225 10374957670922611047660919)
          ·
            refine ⟨15562436506383916571491379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10374957670922611047660919 15562436506383916571491379)
            ·
              refine ⟨23343654759575874857237069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15562436506383916571491379 23343654759575874857237069)
              ·
                refine ⟨8753870534840953071463901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23343654759575874857237069 8753870534840953071463901)
                ·
                  refine ⟨3282701450565357401798963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8753870534840953071463901 3282701450565357401798963)
                  ·
                    refine ⟨4924052175848036102698445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3282701450565357401798963 4924052175848036102698445)
                    ·
                      refine ⟨1846519565943013538511917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4924052175848036102698445 1846519565943013538511917)
                      ·
                        rfl

theorem cell23_3596084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 3, 3, 1, 3].length) (baseStart_3596084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3596084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3596084 prefixEnd_3596084 := by exact prefixLift 3596084
  have htrace : WordTrace (prefixWord ++ tailWord_3596084) baseStart_3596084 baseEnd_3596084 := by
    simpa [prefixWord, tailWord_3596084, baseEnd_3596084] using wordTrace_append hprefix tailTrace_3596084
  have hstable : (prefixWord ++ tailWord_3596084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3596084).length < 2 ^ (prefixWord ++ tailWord_3596084).sum := by decide
  have hdescent : baseEnd_3596084 < baseStart_3596084 := by decide
  rcases family_descends (prefixWord ++ tailWord_3596084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3596127 : List Nat := [1, 1, 2, 3, 1, 4, 2, 3, 1, 2, 3]
def baseStart_3596127 : Nat := 118140960795 + 3596127 * 2 ^ 59
def prefixEnd_3596127 : Nat := 4983230072969 + 3 ^ 40 * 3596127 * 2
def baseEnd_3596127 : Nat := 1846541645611156870274219

theorem tailTrace_3596127 : CollatzResearch.WordTrace tailWord_3596127 prefixEnd_3596127 1846541645611156870274219 := by
  unfold tailWord_3596127
  simp only [CollatzResearch.WordTrace]
  refine ⟨131161527042853523440170635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87441018028569015626780423 131161527042853523440170635)
  ·
    refine ⟨196742290564280285160255953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131161527042853523440170635 196742290564280285160255953)
    ·
      refine ⟨147556717923210213870191965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196742290564280285160255953 147556717923210213870191965)
      ·
        refine ⟨55333769221203830201321987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147556717923210213870191965 55333769221203830201321987)
        ·
          refine ⟨83000653831805745301982981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55333769221203830201321987 83000653831805745301982981)
          ·
            refine ⟨15562622593463577244121809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83000653831805745301982981 15562622593463577244121809)
            ·
              refine ⟨11671966945097682933091357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15562622593463577244121809 11671966945097682933091357)
              ·
                refine ⟨4376987604411631099909259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11671966945097682933091357 4376987604411631099909259)
                ·
                  refine ⟨6565481406617446649863889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4376987604411631099909259 6565481406617446649863889)
                  ·
                    refine ⟨4924111054963084987397917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6565481406617446649863889 4924111054963084987397917)
                    ·
                      refine ⟨1846541645611156870274219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4924111054963084987397917 1846541645611156870274219)
                      ·
                        rfl

theorem cell23_3596127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 3, 1, 2, 3].length) (baseStart_3596127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3596127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3596127 prefixEnd_3596127 := by exact prefixLift 3596127
  have htrace : WordTrace (prefixWord ++ tailWord_3596127) baseStart_3596127 baseEnd_3596127 := by
    simpa [prefixWord, tailWord_3596127, baseEnd_3596127] using wordTrace_append hprefix tailTrace_3596127
  have hstable : (prefixWord ++ tailWord_3596127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3596127).length < 2 ^ (prefixWord ++ tailWord_3596127).sum := by decide
  have hdescent : baseEnd_3596127 < baseStart_3596127 := by decide
  rcases family_descends (prefixWord ++ tailWord_3596127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3596130 : List Nat := [3, 3, 2, 1, 2, 1, 11]
def baseStart_3596130 : Nat := 118140960795 + 3596130 * 2 ^ 59
def prefixEnd_3596130 : Nat := 4983230072969 + 3 ^ 40 * 3596130 * 2
def baseEnd_3596130 : Nat := 22796829457445930352305

theorem tailTrace_3596130 : CollatzResearch.WordTrace tailWord_3596130 prefixEnd_3596130 22796829457445930352305 := by
  unfold tailWord_3596130
  simp only [CollatzResearch.WordTrace]
  refine ⟨32790409115460663738132461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87441090974561769968353229 32790409115460663738132461)
  ·
    refine ⟨12296403418297748901799673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32790409115460663738132461 12296403418297748901799673)
    ·
      refine ⟨9222302563723311676349755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12296403418297748901799673 9222302563723311676349755)
      ·
        refine ⟨13833453845584967514524633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9222302563723311676349755 13833453845584967514524633)
        ·
          refine ⟨10375090384188725635893475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13833453845584967514524633 10375090384188725635893475)
          ·
            refine ⟨15562635576283088453840213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10375090384188725635893475 15562635576283088453840213)
            ·
              refine ⟨22796829457445930352305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 15562635576283088453840213 22796829457445930352305)
              ·
                rfl

theorem cell23_3596130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 11].length) (baseStart_3596130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3596130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3596130 prefixEnd_3596130 := by exact prefixLift 3596130
  have htrace : WordTrace (prefixWord ++ tailWord_3596130) baseStart_3596130 baseEnd_3596130 := by
    simpa [prefixWord, tailWord_3596130, baseEnd_3596130] using wordTrace_append hprefix tailTrace_3596130
  have hstable : (prefixWord ++ tailWord_3596130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3596130).length < 2 ^ (prefixWord ++ tailWord_3596130).sum := by decide
  have hdescent : baseEnd_3596130 < baseStart_3596130 := by decide
  rcases family_descends (prefixWord ++ tailWord_3596130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3596141 : List Nat := [1, 5, 1, 1, 1, 1, 2, 6, 1, 2, 2]
def baseStart_3596141 : Nat := 118140960795 + 3596141 * 2 ^ 59
def prefixEnd_3596141 : Nat := 4983230072969 + 3 ^ 40 * 3596141 * 2
def baseEnd_3596141 : Nat := 1846548834340319815499155

theorem tailTrace_3596141 : CollatzResearch.WordTrace tailWord_3596141 prefixEnd_3596141 1846548834340319815499155 := by
  unfold tailWord_3596141
  simp only [CollatzResearch.WordTrace]
  refine ⟨131162037664802803831180277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87441358443201869220786851 131162037664802803831180277)
  ·
    refine ⟨12296441031075262859173151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 131162037664802803831180277 12296441031075262859173151)
    ·
      refine ⟨18444661546612894288759727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12296441031075262859173151 18444661546612894288759727)
      ·
        refine ⟨27666992319919341433139591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18444661546612894288759727 27666992319919341433139591)
        ·
          refine ⟨41500488479879012149709387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27666992319919341433139591 41500488479879012149709387)
          ·
            refine ⟨62250732719818518224564081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41500488479879012149709387 62250732719818518224564081)
            ·
              refine ⟨46688049539863888668423061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62250732719818518224564081 46688049539863888668423061)
              ·
                refine ⟨2188502322181119781332331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 46688049539863888668423061 2188502322181119781332331)
                ·
                  refine ⟨3282753483271679671998497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2188502322181119781332331 3282753483271679671998497)
                  ·
                    refine ⟨2462065112453759753998873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3282753483271679671998497 2462065112453759753998873)
                    ·
                      refine ⟨1846548834340319815499155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2462065112453759753998873 1846548834340319815499155)
                      ·
                        rfl

theorem cell23_3596141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 6, 1, 2, 2].length) (baseStart_3596141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3596141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3596141 prefixEnd_3596141 := by exact prefixLift 3596141
  have htrace : WordTrace (prefixWord ++ tailWord_3596141) baseStart_3596141 baseEnd_3596141 := by
    simpa [prefixWord, tailWord_3596141, baseEnd_3596141] using wordTrace_append hprefix tailTrace_3596141
  have hstable : (prefixWord ++ tailWord_3596141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3596141).length < 2 ^ (prefixWord ++ tailWord_3596141).sum := by decide
  have hdescent : baseEnd_3596141 < baseStart_3596141 := by decide
  rcases family_descends (prefixWord ++ tailWord_3596141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3596191 : List Nat := [1, 1, 2, 5, 3, 1, 2, 2, 2, 1, 3]
def baseStart_3596191 : Nat := 118140960795 + 3596191 * 2 ^ 59
def prefixEnd_3596191 : Nat := 4983230072969 + 3 ^ 40 * 3596191 * 2
def baseEnd_3596191 : Nat := 1846574508373044619873925

theorem tailTrace_3596191 : CollatzResearch.WordTrace tailWord_3596191 prefixEnd_3596191 1846574508373044619873925 := by
  unfold tailWord_3596191
  simp only [CollatzResearch.WordTrace]
  refine ⟨131163861314621662370500427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87442574209747774913666951 131163861314621662370500427)
  ·
    refine ⟨196745791971932493555750641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131163861314621662370500427 196745791971932493555750641)
    ·
      refine ⟨147559343978949370166812981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196745791971932493555750641 147559343978949370166812981)
      ·
        refine ⟨13833688498026503453138717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 147559343978949370166812981 13833688498026503453138717)
        ·
          refine ⟨5187633186759938794927019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13833688498026503453138717 5187633186759938794927019)
          ·
            refine ⟨7781449780139908192390529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5187633186759938794927019 7781449780139908192390529)
            ·
              refine ⟨5836087335104931144292897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7781449780139908192390529 5836087335104931144292897)
              ·
                refine ⟨4377065501328698358219673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5836087335104931144292897 4377065501328698358219673)
                ·
                  refine ⟨3282799125996523768664755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4377065501328698358219673 3282799125996523768664755)
                  ·
                    refine ⟨4924198688994785652997133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3282799125996523768664755 4924198688994785652997133)
                    ·
                      refine ⟨1846574508373044619873925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4924198688994785652997133 1846574508373044619873925)
                      ·
                        rfl

theorem cell23_3596191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 2, 2, 2, 1, 3].length) (baseStart_3596191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3596191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3596191 prefixEnd_3596191 := by exact prefixLift 3596191
  have htrace : WordTrace (prefixWord ++ tailWord_3596191) baseStart_3596191 baseEnd_3596191 := by
    simpa [prefixWord, tailWord_3596191, baseEnd_3596191] using wordTrace_append hprefix tailTrace_3596191
  have hstable : (prefixWord ++ tailWord_3596191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3596191).length < 2 ^ (prefixWord ++ tailWord_3596191).sum := by decide
  have hdescent : baseEnd_3596191 < baseStart_3596191 := by decide
  rcases family_descends (prefixWord ++ tailWord_3596191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3596257 : List Nat := [1, 2, 3, 1, 2, 1, 2, 1, 1, 7, 2]
def baseStart_3596257 : Nat := 118140960795 + 3596257 * 2 ^ 59
def prefixEnd_3596257 : Nat := 4983230072969 + 3 ^ 40 * 3596257 * 2
def baseEnd_3596257 : Nat := 1846608398096241361648621

theorem tailTrace_3596257 : CollatzResearch.WordTrace tailWord_3596257 prefixEnd_3596257 1846608398096241361648621 := by
  unfold tailWord_3596257
  simp only [CollatzResearch.WordTrace]
  refine ⟨131166268532382555642403025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87444179021588370428268683 131166268532382555642403025)
  ·
    refine ⟨98374701399286916731802269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131166268532382555642403025 98374701399286916731802269)
    ·
      refine ⟨36890513024732593774425851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98374701399286916731802269 36890513024732593774425851)
      ·
        refine ⟨55335769537098890661638777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36890513024732593774425851 55335769537098890661638777)
        ·
          refine ⟨41501827152824167996229083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55335769537098890661638777 41501827152824167996229083)
          ·
            refine ⟨62252740729236251994343625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41501827152824167996229083 62252740729236251994343625)
            ·
              refine ⟨46689555546927188995757719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62252740729236251994343625 46689555546927188995757719)
              ·
                refine ⟨70034333320390783493636579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46689555546927188995757719 70034333320390783493636579)
                ·
                  refine ⟨105051499980586175240454869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70034333320390783493636579 105051499980586175240454869)
                  ·
                    refine ⟨2462144530794988482198161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 105051499980586175240454869 2462144530794988482198161)
                    ·
                      refine ⟨1846608398096241361648621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2462144530794988482198161 1846608398096241361648621)
                      ·
                        rfl

theorem cell23_3596257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 7, 2].length) (baseStart_3596257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3596257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3596257 prefixEnd_3596257 := by exact prefixLift 3596257
  have htrace : WordTrace (prefixWord ++ tailWord_3596257) baseStart_3596257 baseEnd_3596257 := by
    simpa [prefixWord, tailWord_3596257, baseEnd_3596257] using wordTrace_append hprefix tailTrace_3596257
  have hstable : (prefixWord ++ tailWord_3596257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3596257).length < 2 ^ (prefixWord ++ tailWord_3596257).sum := by decide
  have hdescent : baseEnd_3596257 < baseStart_3596257 := by decide
  rcases family_descends (prefixWord ++ tailWord_3596257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3596260 : List Nat := [2, 3, 1, 1, 1, 1, 4, 1, 1, 1, 7]
def baseStart_3596260 : Nat := 118140960795 + 3596260 * 2 ^ 59
def prefixEnd_3596260 : Nat := 4983230072969 + 3 ^ 40 * 3596260 * 2
def baseEnd_3596260 : Nat := 1846609938538204849911107

theorem tailTrace_3596260 : CollatzResearch.WordTrace tailWord_3596260 prefixEnd_3596260 1846609938538204849911107 := by
  unfold tailWord_3596260
  simp only [CollatzResearch.WordTrace]
  refine ⟨65583188975685843577381117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87444251967581124769841489 65583188975685843577381117)
  ·
    refine ⟨24593695865882191341517919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65583188975685843577381117 24593695865882191341517919)
    ·
      refine ⟨36890543798823287012276879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24593695865882191341517919 36890543798823287012276879)
      ·
        refine ⟨55335815698234930518415319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36890543798823287012276879 55335815698234930518415319)
        ·
          refine ⟨83003723547352395777622979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55335815698234930518415319 83003723547352395777622979)
          ·
            refine ⟨124505585321028593666434469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83003723547352395777622979 124505585321028593666434469)
            ·
              refine ⟨23344797247692861312456463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 124505585321028593666434469 23344797247692861312456463)
              ·
                refine ⟨35017195871539291968684695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23344797247692861312456463 35017195871539291968684695)
                ·
                  refine ⟨52525793807308937953027043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35017195871539291968684695 52525793807308937953027043)
                  ·
                    refine ⟨78788690710963406929540565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52525793807308937953027043 78788690710963406929540565)
                    ·
                      refine ⟨1846609938538204849911107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 78788690710963406929540565 1846609938538204849911107)
                      ·
                        rfl

theorem cell23_3596260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 1, 1, 1, 7].length) (baseStart_3596260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3596260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3596260 prefixEnd_3596260 := by exact prefixLift 3596260
  have htrace : WordTrace (prefixWord ++ tailWord_3596260) baseStart_3596260 baseEnd_3596260 := by
    simpa [prefixWord, tailWord_3596260, baseEnd_3596260] using wordTrace_append hprefix tailTrace_3596260
  have hstable : (prefixWord ++ tailWord_3596260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3596260).length < 2 ^ (prefixWord ++ tailWord_3596260).sum := by decide
  have hdescent : baseEnd_3596260 < baseStart_3596260 := by decide
  rcases family_descends (prefixWord ++ tailWord_3596260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3596287 : List Nat := [1, 1, 2, 2, 1, 2, 1, 4, 1, 6, 2]
def baseStart_3596287 : Nat := 118140960795 + 3596287 * 2 ^ 59
def prefixEnd_3596287 : Nat := 4983230072969 + 3 ^ 40 * 3596287 * 2
def baseEnd_3596287 : Nat := 1846623802515876244273483

theorem tailTrace_3596287 : CollatzResearch.WordTrace tailWord_3596287 prefixEnd_3596287 1846623802515876244273483 := by
  unfold tailWord_3596287
  simp only [CollatzResearch.WordTrace]
  refine ⟨131167362722273870765995115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87444908481515913843996743 131167362722273870765995115)
  ·
    refine ⟨196751044083410806148992673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131167362722273870765995115 196751044083410806148992673)
    ·
      refine ⟨147563283062558104611744505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196751044083410806148992673 147563283062558104611744505)
      ·
        refine ⟨110672462296918578458808379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147563283062558104611744505 110672462296918578458808379)
        ·
          refine ⟨166008693445377867688212569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110672462296918578458808379 166008693445377867688212569)
          ·
            refine ⟨124506520084033400766159427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166008693445377867688212569 124506520084033400766159427)
            ·
              refine ⟨186759780126050101149239141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124506520084033400766159427 186759780126050101149239141)
              ·
                refine ⟨35017458773634393965482339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 186759780126050101149239141 35017458773634393965482339)
                ·
                  refine ⟨52526188160451590948223509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35017458773634393965482339 52526188160451590948223509)
                  ·
                    refine ⟨2462165070021168325697977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 52526188160451590948223509 2462165070021168325697977)
                    ·
                      refine ⟨1846623802515876244273483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2462165070021168325697977 1846623802515876244273483)
                      ·
                        rfl

theorem cell23_3596287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 4, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 4, 1, 6, 2].length) (baseStart_3596287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3596287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3596287 prefixEnd_3596287 := by exact prefixLift 3596287
  have htrace : WordTrace (prefixWord ++ tailWord_3596287) baseStart_3596287 baseEnd_3596287 := by
    simpa [prefixWord, tailWord_3596287, baseEnd_3596287] using wordTrace_append hprefix tailTrace_3596287
  have hstable : (prefixWord ++ tailWord_3596287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3596287).length < 2 ^ (prefixWord ++ tailWord_3596287).sum := by decide
  have hdescent : baseEnd_3596287 < baseStart_3596287 := by decide
  rcases family_descends (prefixWord ++ tailWord_3596287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3596307 : List Nat := [1, 1, 1, 2, 1, 4, 3, 1, 4, 2, 3]
def baseStart_3596307 : Nat := 118140960795 + 3596307 * 2 ^ 59
def prefixEnd_3596307 : Nat := 4983230072969 + 3 ^ 40 * 3596307 * 2
def baseEnd_3596307 : Nat := 1846634072128966166023391

theorem tailTrace_3596307 : CollatzResearch.WordTrace tailWord_3596307 prefixEnd_3596307 1846634072128966166023391 := by
  unfold tailWord_3596307
  simp only [CollatzResearch.WordTrace]
  refine ⟨131168092182201414181723175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87445394788134276121148783 131168092182201414181723175)
  ·
    refine ⟨196752138273302121272584763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131168092182201414181723175 196752138273302121272584763)
    ·
      refine ⟨295128207409953181908877145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196752138273302121272584763 295128207409953181908877145)
      ·
        refine ⟨221346155557464886431657859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 295128207409953181908877145 221346155557464886431657859)
        ·
          refine ⟨332019233336197329647486789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221346155557464886431657859 332019233336197329647486789)
          ·
            refine ⟨62253606250536999308903773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 332019233336197329647486789 62253606250536999308903773)
            ·
              refine ⟨23345102343951374740838915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62253606250536999308903773 23345102343951374740838915)
              ·
                refine ⟨35017653515927062111258373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23345102343951374740838915 35017653515927062111258373)
                ·
                  refine ⟨6565810034236324145860945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35017653515927062111258373 6565810034236324145860945)
                  ·
                    refine ⟨4924357525677243109395709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6565810034236324145860945 4924357525677243109395709)
                    ·
                      refine ⟨1846634072128966166023391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4924357525677243109395709 1846634072128966166023391)
                      ·
                        rfl

theorem cell23_3596307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 1, 4, 2, 3].length) (baseStart_3596307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3596307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3596307 prefixEnd_3596307 := by exact prefixLift 3596307
  have htrace : WordTrace (prefixWord ++ tailWord_3596307) baseStart_3596307 baseEnd_3596307 := by
    simpa [prefixWord, tailWord_3596307, baseEnd_3596307] using wordTrace_append hprefix tailTrace_3596307
  have hstable : (prefixWord ++ tailWord_3596307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3596307).length < 2 ^ (prefixWord ++ tailWord_3596307).sum := by decide
  have hdescent : baseEnd_3596307 < baseStart_3596307 := by decide
  rcases family_descends (prefixWord ++ tailWord_3596307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3596314 : List Nat := [3, 1, 1, 3, 1, 3, 3, 1, 3, 4]
def baseStart_3596314 : Nat := 118140960795 + 3596314 * 2 ^ 59
def prefixEnd_3596314 : Nat := 4983230072969 + 3 ^ 40 * 3596314 * 2
def baseEnd_3596314 : Nat := 615545888831182546211953

theorem tailTrace_3596314 : CollatzResearch.WordTrace tailWord_3596314 prefixEnd_3596314 615545888831182546211953 := by
  unfold tailWord_3596314
  simp only [CollatzResearch.WordTrace]
  refine ⟨32792086873294013594306999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87445564995450702918151997 32792086873294013594306999)
  ·
    refine ⟨49188130309941020391460499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32792086873294013594306999 49188130309941020391460499)
    ·
      refine ⟨73782195464911530587190749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49188130309941020391460499 73782195464911530587190749)
      ·
        refine ⟨27668323299341823970196531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73782195464911530587190749 27668323299341823970196531)
        ·
          refine ⟨41502484949012735955294797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27668323299341823970196531 41502484949012735955294797)
          ·
            refine ⟨15563431855879775983235549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41502484949012735955294797 15563431855879775983235549)
            ·
              refine ⟨5836286945954915993713331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15563431855879775983235549 5836286945954915993713331)
              ·
                refine ⟨8754430418932373990569997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5836286945954915993713331 8754430418932373990569997)
                ·
                  refine ⟨3282911407099640246463749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8754430418932373990569997 3282911407099640246463749)
                  ·
                    refine ⟨615545888831182546211953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3282911407099640246463749 615545888831182546211953)
                    ·
                      rfl

theorem cell23_3596314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 3, 1, 3, 4].length) (baseStart_3596314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3596314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3596314 prefixEnd_3596314 := by exact prefixLift 3596314
  have htrace : WordTrace (prefixWord ++ tailWord_3596314) baseStart_3596314 baseEnd_3596314 := by
    simpa [prefixWord, tailWord_3596314, baseEnd_3596314] using wordTrace_append hprefix tailTrace_3596314
  have hstable : (prefixWord ++ tailWord_3596314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3596314).length < 2 ^ (prefixWord ++ tailWord_3596314).sum := by decide
  have hdescent : baseEnd_3596314 < baseStart_3596314 := by decide
  rcases family_descends (prefixWord ++ tailWord_3596314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3596377 : List Nat := [1, 2, 1, 2, 2, 1, 3, 1, 5, 1, 4]
def baseStart_3596377 : Nat := 118140960795 + 3596377 * 2 ^ 59
def prefixEnd_3596377 : Nat := 4983230072969 + 3 ^ 40 * 3596377 * 2
def baseEnd_3596377 : Nat := 1846670015774780892148069

theorem tailTrace_3596377 : CollatzResearch.WordTrace tailWord_3596377 prefixEnd_3596377 1846670015774780892148069 := by
  unfold tailWord_3596377
  simp only [CollatzResearch.WordTrace]
  refine ⟨131170645291947816136771385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87447096861298544091180923 131170645291947816136771385)
  ·
    refine ⟨98377983968960862102578539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131170645291947816136771385 98377983968960862102578539)
    ·
      refine ⟨147566975953441293153867809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98377983968960862102578539 147566975953441293153867809)
      ·
        refine ⟨110675231965080969865400857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147566975953441293153867809 110675231965080969865400857)
        ·
          refine ⟨83006423973810727399050643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110675231965080969865400857 83006423973810727399050643)
          ·
            refine ⟨124509635960716091098575965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83006423973810727399050643 124509635960716091098575965)
            ·
              refine ⟨46691113485268534161965987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124509635960716091098575965 46691113485268534161965987)
              ·
                refine ⟨70036670227902801242948981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46691113485268534161965987 70036670227902801242948981)
                ·
                  refine ⟨6565937833865887616526467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70036670227902801242948981 6565937833865887616526467)
                  ·
                    refine ⟨9848906750798831424789701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6565937833865887616526467 9848906750798831424789701)
                    ·
                      refine ⟨1846670015774780892148069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9848906750798831424789701 1846670015774780892148069)
                      ·
                        rfl

theorem cell23_3596377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 5, 1, 4].length) (baseStart_3596377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3596377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3596377 prefixEnd_3596377 := by exact prefixLift 3596377
  have htrace : WordTrace (prefixWord ++ tailWord_3596377) baseStart_3596377 baseEnd_3596377 := by
    simpa [prefixWord, tailWord_3596377, baseEnd_3596377] using wordTrace_append hprefix tailTrace_3596377
  have hstable : (prefixWord ++ tailWord_3596377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3596377).length < 2 ^ (prefixWord ++ tailWord_3596377).sum := by decide
  have hdescent : baseEnd_3596377 < baseStart_3596377 := by decide
  rcases family_descends (prefixWord ++ tailWord_3596377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3596387 : List Nat := [1, 1, 1, 5, 1, 1, 3, 3, 1, 6]
def baseStart_3596387 : Nat := 118140960795 + 3596387 * 2 ^ 59
def prefixEnd_3596387 : Nat := 4983230072969 + 3 ^ 40 * 3596387 * 2
def baseEnd_3596387 : Nat := 615558383527108617674341

theorem tailTrace_3596387 : CollatzResearch.WordTrace tailWord_3596387 prefixEnd_3596387 615558383527108617674341 := by
  unfold tailWord_3596387
  simp only [CollatzResearch.WordTrace]
  refine ⟨131171010021911587844635415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87447340014607725229756943 131171010021911587844635415)
  ·
    refine ⟨196756515032867381766953123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131171010021911587844635415 196756515032867381766953123)
    ·
      refine ⟨295134772549301072650429685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196756515032867381766953123 295134772549301072650429685)
      ·
        refine ⟨27668884926496975560977783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 295134772549301072650429685 27668884926496975560977783)
        ·
          refine ⟨41503327389745463341466675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27668884926496975560977783 41503327389745463341466675)
          ·
            refine ⟨62254991084618195012200013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41503327389745463341466675 62254991084618195012200013)
            ·
              refine ⟨23345621656731823129575005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62254991084618195012200013 23345621656731823129575005)
              ·
                refine ⟨8754608121274433673590627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23345621656731823129575005 8754608121274433673590627)
                ·
                  refine ⟨13131912181911650510385941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8754608121274433673590627 13131912181911650510385941)
                  ·
                    refine ⟨615558383527108617674341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13131912181911650510385941 615558383527108617674341)
                    ·
                      rfl

theorem cell23_3596387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 3, 1, 6].length) (baseStart_3596387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3596387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3596387 prefixEnd_3596387 := by exact prefixLift 3596387
  have htrace : WordTrace (prefixWord ++ tailWord_3596387) baseStart_3596387 baseEnd_3596387 := by
    simpa [prefixWord, tailWord_3596387, baseEnd_3596387] using wordTrace_append hprefix tailTrace_3596387
  have hstable : (prefixWord ++ tailWord_3596387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3596387).length < 2 ^ (prefixWord ++ tailWord_3596387).sum := by decide
  have hdescent : baseEnd_3596387 < baseStart_3596387 := by decide
  rcases family_descends (prefixWord ++ tailWord_3596387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3596421 : List Nat := [1, 3, 1, 1, 5, 1, 3, 2, 2, 4]
def baseStart_3596421 : Nat := 118140960795 + 3596421 * 2 ^ 59
def prefixEnd_3596421 : Nat := 4983230072969 + 3 ^ 40 * 3596421 * 2
def baseEnd_3596421 : Nat := 615564202974526239999289

theorem tailTrace_3596421 : CollatzResearch.WordTrace tailWord_3596421 prefixEnd_3596421 615564202974526239999289 := by
  unfold tailWord_3596421
  simp only [CollatzResearch.WordTrace]
  refine ⟨131172250103788411651373117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87448166735858941100915411 131172250103788411651373117)
  ·
    refine ⟨49189593788920654369264919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131172250103788411651373117 49189593788920654369264919)
    ·
      refine ⟨73784390683380981553897379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49189593788920654369264919 73784390683380981553897379)
      ·
        refine ⟨110676586025071472330846069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73784390683380981553897379 110676586025071472330846069)
        ·
          refine ⟨10375929939850450531016819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 110676586025071472330846069 10375929939850450531016819)
          ·
            refine ⟨15563894909775675796525229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10375929939850450531016819 15563894909775675796525229)
            ·
              refine ⟨5836460591165878423696961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15563894909775675796525229 5836460591165878423696961)
              ·
                refine ⟨4377345443374408817772721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5836460591165878423696961 4377345443374408817772721)
                ·
                  refine ⟨3283009082530806613329541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4377345443374408817772721 3283009082530806613329541)
                  ·
                    refine ⟨615564202974526239999289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3283009082530806613329541 615564202974526239999289)
                    ·
                      rfl

theorem cell23_3596421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 3, 2, 2, 4].length) (baseStart_3596421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3596421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3596421 prefixEnd_3596421 := by exact prefixLift 3596421
  have htrace : WordTrace (prefixWord ++ tailWord_3596421) baseStart_3596421 baseEnd_3596421 := by
    simpa [prefixWord, tailWord_3596421, baseEnd_3596421] using wordTrace_append hprefix tailTrace_3596421
  have hstable : (prefixWord ++ tailWord_3596421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3596421).length < 2 ^ (prefixWord ++ tailWord_3596421).sum := by decide
  have hdescent : baseEnd_3596421 < baseStart_3596421 := by decide
  rcases family_descends (prefixWord ++ tailWord_3596421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3596427 : List Nat := [1, 1, 1, 1, 4, 1, 1, 1, 2, 7, 3]
def baseStart_3596427 : Nat := 118140960795 + 3596427 * 2 ^ 59
def prefixEnd_3596427 : Nat := 4983230072969 + 3 ^ 40 * 3596427 * 2
def baseEnd_3596427 : Nat := 1846695689807505696522839

theorem tailTrace_3596427 : CollatzResearch.WordTrace tailWord_3596427 prefixEnd_3596427 1846695689807505696522839 := by
  unfold tailWord_3596427
  simp only [CollatzResearch.WordTrace]
  refine ⟨131172468941766674676091535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87448312627844449784061023 131172468941766674676091535)
  ·
    refine ⟨196758703412650012014137303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131172468941766674676091535 196758703412650012014137303)
    ·
      refine ⟨295138055118975018021205955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196758703412650012014137303 295138055118975018021205955)
      ·
        refine ⟨442707082678462527031808933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295138055118975018021205955 442707082678462527031808933)
        ·
          refine ⟨83007578002211723818464175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 442707082678462527031808933 83007578002211723818464175)
          ·
            refine ⟨124511367003317585727696263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83007578002211723818464175 124511367003317585727696263)
            ·
              refine ⟨186767050504976378591544395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124511367003317585727696263 186767050504976378591544395)
              ·
                refine ⟨280150575757464567887316593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 186767050504976378591544395 280150575757464567887316593)
                ·
                  refine ⟨210112931818098425915487445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 280150575757464567887316593 210112931818098425915487445)
                  ·
                    refine ⟨4924521839486681857394237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 210112931818098425915487445 4924521839486681857394237)
                    ·
                      refine ⟨1846695689807505696522839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4924521839486681857394237 1846695689807505696522839)
                      ·
                        rfl

theorem cell23_3596427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 7, 3].length) (baseStart_3596427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3596427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3596427 prefixEnd_3596427 := by exact prefixLift 3596427
  have htrace : WordTrace (prefixWord ++ tailWord_3596427) baseStart_3596427 baseEnd_3596427 := by
    simpa [prefixWord, tailWord_3596427, baseEnd_3596427] using wordTrace_append hprefix tailTrace_3596427
  have hstable : (prefixWord ++ tailWord_3596427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3596427).length < 2 ^ (prefixWord ++ tailWord_3596427).sum := by decide
  have hdescent : baseEnd_3596427 < baseStart_3596427 := by decide
  rcases family_descends (prefixWord ++ tailWord_3596427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3596467 : List Nat := [1, 1, 1, 2, 3, 2, 1, 2, 1, 5, 4]
def baseStart_3596467 : Nat := 118140960795 + 3596467 * 2 ^ 59
def prefixEnd_3596467 : Nat := 4983230072969 + 3 ^ 40 * 3596467 * 2
def baseEnd_3596467 : Nat := 1846716229033685540022655

theorem tailTrace_3596467 : CollatzResearch.WordTrace tailWord_3596467 prefixEnd_3596467 1846716229033685540022655 := by
  unfold tailWord_3596467
  simp only [CollatzResearch.WordTrace]
  refine ⟨131173927861621761507547655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87449285241081174338365103 131173927861621761507547655)
  ·
    refine ⟨196760891792432642261321483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131173927861621761507547655 196760891792432642261321483)
    ·
      refine ⟨295141337688648963391982225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196760891792432642261321483 295141337688648963391982225)
      ·
        refine ⟨221356003266486722543986669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 295141337688648963391982225 221356003266486722543986669)
        ·
          refine ⟨83008501224932520953995001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 221356003266486722543986669 83008501224932520953995001)
          ·
            refine ⟨62256375918699390715496251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83008501224932520953995001 62256375918699390715496251)
            ·
              refine ⟨93384563878049086073244377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62256375918699390715496251 93384563878049086073244377)
              ·
                refine ⟨70038422908536814554933283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93384563878049086073244377 70038422908536814554933283)
                ·
                  refine ⟨105057634362805221832399925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70038422908536814554933283 105057634362805221832399925)
                  ·
                    refine ⟨9849153221512989546787493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 105057634362805221832399925 9849153221512989546787493)
                    ·
                      refine ⟨1846716229033685540022655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9849153221512989546787493 1846716229033685540022655)
                      ·
                        rfl

theorem cell23_3596467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 5, 4].length) (baseStart_3596467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3596467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3596467 prefixEnd_3596467 := by exact prefixLift 3596467
  have htrace : WordTrace (prefixWord ++ tailWord_3596467) baseStart_3596467 baseEnd_3596467 := by
    simpa [prefixWord, tailWord_3596467, baseEnd_3596467] using wordTrace_append hprefix tailTrace_3596467
  have hstable : (prefixWord ++ tailWord_3596467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3596467).length < 2 ^ (prefixWord ++ tailWord_3596467).sum := by decide
  have hdescent : baseEnd_3596467 < baseStart_3596467 := by decide
  rcases family_descends (prefixWord ++ tailWord_3596467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3596504 : List Nat := [2, 1, 2, 2, 4, 1, 1, 2, 2, 1, 5]
def baseStart_3596504 : Nat := 118140960795 + 3596504 * 2 ^ 59
def prefixEnd_3596504 : Nat := 4983230072969 + 3 ^ 40 * 3596504 * 2
def baseEnd_3596504 : Nat := 1846735227817901895259985

theorem tailTrace_3596504 : CollatzResearch.WordTrace tailWord_3596504 prefixEnd_3596504 1846735227817901895259985 := by
  unfold tailWord_3596504
  simp only [CollatzResearch.WordTrace]
  refine ⟨65587638681243858413322283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87450184908325144551096377 65587638681243858413322283)
  ·
    refine ⟨98381458021865787619983425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65587638681243858413322283 98381458021865787619983425)
    ·
      refine ⟨73786093516399340714987569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98381458021865787619983425 73786093516399340714987569)
      ·
        refine ⟨55339570137299505536240677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73786093516399340714987569 55339570137299505536240677)
        ·
          refine ⟨10376169400743657288045127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55339570137299505536240677 10376169400743657288045127)
          ·
            refine ⟨15564254101115485932067691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10376169400743657288045127 15564254101115485932067691)
            ·
              refine ⟨23346381151673228898101537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15564254101115485932067691 23346381151673228898101537)
              ·
                refine ⟨17509785863754921673576153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23346381151673228898101537 17509785863754921673576153)
                ·
                  refine ⟨13132339397816191255182115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17509785863754921673576153 13132339397816191255182115)
                  ·
                    refine ⟨19698509096724286882773173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13132339397816191255182115 19698509096724286882773173)
                    ·
                      refine ⟨1846735227817901895259985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19698509096724286882773173 1846735227817901895259985)
                      ·
                        rfl

theorem cell23_3596504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 2, 2, 1, 5].length) (baseStart_3596504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3596504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3596504 prefixEnd_3596504 := by exact prefixLift 3596504
  have htrace : WordTrace (prefixWord ++ tailWord_3596504) baseStart_3596504 baseEnd_3596504 := by
    simpa [prefixWord, tailWord_3596504, baseEnd_3596504] using wordTrace_append hprefix tailTrace_3596504
  have hstable : (prefixWord ++ tailWord_3596504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3596504).length < 2 ^ (prefixWord ++ tailWord_3596504).sum := by decide
  have hdescent : baseEnd_3596504 < baseStart_3596504 := by decide
  rcases family_descends (prefixWord ++ tailWord_3596504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3596534 : List Nat := [5, 1, 1, 1, 1, 1, 2, 1, 1, 2, 7]
def baseStart_3596534 : Nat := 118140960795 + 3596534 * 2 ^ 59
def prefixEnd_3596534 : Nat := 4983230072969 + 3 ^ 40 * 3596534 * 2
def baseEnd_3596534 : Nat := 1846750632237536777884847

theorem tailTrace_3596534 : CollatzResearch.WordTrace tailWord_3596534 prefixEnd_3596534 1846750632237536777884847 := by
  unfold tailWord_3596534
  simp only [CollatzResearch.WordTrace]
  refine ⟨8198523222023689496889791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 87450914368252687966824437 8198523222023689496889791)
  ·
    refine ⟨12297784833035534245334687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8198523222023689496889791 12297784833035534245334687)
    ·
      refine ⟨18446677249553301368002031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12297784833035534245334687 18446677249553301368002031)
      ·
        refine ⟨27670015874329952052003047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18446677249553301368002031 27670015874329952052003047)
        ·
          refine ⟨41505023811494928078004571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27670015874329952052003047 41505023811494928078004571)
          ·
            refine ⟨62257535717242392117006857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41505023811494928078004571 62257535717242392117006857)
            ·
              refine ⟨46693151787931794087755143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62257535717242392117006857 46693151787931794087755143)
              ·
                refine ⟨70039727681897691131632715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46693151787931794087755143 70039727681897691131632715)
                ·
                  refine ⟨105059591522846536697449073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70039727681897691131632715 105059591522846536697449073)
                  ·
                    refine ⟨78794693642134902523086805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 105059591522846536697449073 78794693642134902523086805)
                    ·
                      refine ⟨1846750632237536777884847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 78794693642134902523086805 1846750632237536777884847)
                      ·
                        rfl

theorem cell23_3596534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 1, 2, 7].length) (baseStart_3596534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3596534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3596534 prefixEnd_3596534 := by exact prefixLift 3596534
  have htrace : WordTrace (prefixWord ++ tailWord_3596534) baseStart_3596534 baseEnd_3596534 := by
    simpa [prefixWord, tailWord_3596534, baseEnd_3596534] using wordTrace_append hprefix tailTrace_3596534
  have hstable : (prefixWord ++ tailWord_3596534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3596534).length < 2 ^ (prefixWord ++ tailWord_3596534).sum := by decide
  have hdescent : baseEnd_3596534 < baseStart_3596534 := by decide
  rcases family_descends (prefixWord ++ tailWord_3596534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3596554 : List Nat := [3, 1, 2, 2, 1, 1, 2, 2, 4, 5]
def baseStart_3596554 : Nat := 118140960795 + 3596554 * 2 ^ 59
def prefixEnd_3596554 : Nat := 4983230072969 + 3 ^ 40 * 3596554 * 2
def baseEnd_3596554 : Nat := 615586967283542233211585

theorem tailTrace_3596554 : CollatzResearch.WordTrace tailWord_3596554 prefixEnd_3596554 615586967283542233211585 := by
  unfold tailWord_3596554
  simp only [CollatzResearch.WordTrace]
  refine ⟨32794275253076643841491179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87451400674871050243976477 32794275253076643841491179)
  ·
    refine ⟨49191412879614965762236769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32794275253076643841491179 49191412879614965762236769)
    ·
      refine ⟨36893559659711224321677577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49191412879614965762236769 36893559659711224321677577)
      ·
        refine ⟨27670169744783418241258183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36893559659711224321677577 27670169744783418241258183)
        ·
          refine ⟨41505254617175127361887275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27670169744783418241258183 41505254617175127361887275)
          ·
            refine ⟨62257881925762691042830913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41505254617175127361887275 62257881925762691042830913)
            ·
              refine ⟨46693411444322018282123185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62257881925762691042830913 46693411444322018282123185)
              ·
                refine ⟨35020058583241513711592389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46693411444322018282123185 35020058583241513711592389)
                ·
                  refine ⟨6566260984357783820923573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35020058583241513711592389 6566260984357783820923573)
                  ·
                    refine ⟨615586967283542233211585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6566260984357783820923573 615586967283542233211585)
                    ·
                      rfl

theorem cell23_3596554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 2, 4, 5].length) (baseStart_3596554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3596554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3596554 prefixEnd_3596554 := by exact prefixLift 3596554
  have htrace : WordTrace (prefixWord ++ tailWord_3596554) baseStart_3596554 baseEnd_3596554 := by
    simpa [prefixWord, tailWord_3596554, baseEnd_3596554] using wordTrace_append hprefix tailTrace_3596554
  have hstable : (prefixWord ++ tailWord_3596554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3596554).length < 2 ^ (prefixWord ++ tailWord_3596554).sum := by decide
  have hdescent : baseEnd_3596554 < baseStart_3596554 := by decide
  rcases family_descends (prefixWord ++ tailWord_3596554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3596591 : List Nat := [1, 1, 2, 1, 2, 1, 5, 2, 2, 4, 2]
def baseStart_3596591 : Nat := 118140960795 + 3596591 * 2 ^ 59
def prefixEnd_3596591 : Nat := 4983230072969 + 3 ^ 40 * 3596591 * 2
def baseEnd_3596591 : Nat := 1846779900634843054872085

theorem tailTrace_3596591 : CollatzResearch.WordTrace tailWord_3596591 prefixEnd_3596591 1846779900634843054872085 := by
  unfold tailWord_3596591
  simp only [CollatzResearch.WordTrace]
  refine ⟨131178450513172530685061627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87452300342115020456707751 131178450513172530685061627)
  ·
    refine ⟨196767675769758796027592441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131178450513172530685061627 196767675769758796027592441)
    ·
      refine ⟨147575756827319097020694331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196767675769758796027592441 147575756827319097020694331)
      ·
        refine ⟨221363635240978645531041497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147575756827319097020694331 221363635240978645531041497)
        ·
          refine ⟨166022726430733984148281123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 221363635240978645531041497 166022726430733984148281123)
          ·
            refine ⟨249034089646100976222421685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166022726430733984148281123 249034089646100976222421685)
            ·
              refine ⟨23346945904321966520852033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 249034089646100976222421685 23346945904321966520852033)
              ·
                refine ⟨17510209428241474890639025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23346945904321966520852033 17510209428241474890639025)
                ·
                  refine ⟨13132657071181106167979269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17510209428241474890639025 13132657071181106167979269)
                  ·
                    refine ⟨2462373200846457406496113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13132657071181106167979269 2462373200846457406496113)
                    ·
                      refine ⟨1846779900634843054872085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2462373200846457406496113 1846779900634843054872085)
                      ·
                        rfl

theorem cell23_3596591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 2, 2, 4, 2].length) (baseStart_3596591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3596591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3596591 prefixEnd_3596591 := by exact prefixLift 3596591
  have htrace : WordTrace (prefixWord ++ tailWord_3596591) baseStart_3596591 baseEnd_3596591 := by
    simpa [prefixWord, tailWord_3596591, baseEnd_3596591] using wordTrace_append hprefix tailTrace_3596591
  have hstable : (prefixWord ++ tailWord_3596591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3596591).length < 2 ^ (prefixWord ++ tailWord_3596591).sum := by decide
  have hdescent : baseEnd_3596591 < baseStart_3596591 := by decide
  rcases family_descends (prefixWord ++ tailWord_3596591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3596604 : List Nat := [2, 2, 2, 2, 1, 2, 1, 2, 2, 1, 6]
def baseStart_3596604 : Nat := 118140960795 + 3596604 * 2 ^ 59
def prefixEnd_3596604 : Nat := 4983230072969 + 3 ^ 40 * 3596604 * 2
def baseEnd_3596604 : Nat := 1846786575883351504009525

theorem tailTrace_3596604 : CollatzResearch.WordTrace tailWord_3596604 prefixEnd_3596604 1846786575883351504009525 := by
  unfold tailWord_3596604
  simp only [CollatzResearch.WordTrace]
  refine ⟨65589462331062716952642433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87452616441416955936856577 65589462331062716952642433)
  ·
    refine ⟨49192096748297037714481825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65589462331062716952642433 49192096748297037714481825)
    ·
      refine ⟨36894072561222778285861369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49192096748297037714481825 36894072561222778285861369)
      ·
        refine ⟨27670554420917083714396027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36894072561222778285861369 27670554420917083714396027)
        ·
          refine ⟨41505831631375625571594041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27670554420917083714396027 41505831631375625571594041)
          ·
            refine ⟨31129373723531719178695531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41505831631375625571594041 31129373723531719178695531)
            ·
              refine ⟨46694060585297578768043297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31129373723531719178695531 46694060585297578768043297)
              ·
                refine ⟨35020545438973184076032473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46694060585297578768043297 35020545438973184076032473)
                ·
                  refine ⟨26265409079229888057024355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35020545438973184076032473 26265409079229888057024355)
                  ·
                    refine ⟨39398113618844832085536533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26265409079229888057024355 39398113618844832085536533)
                    ·
                      refine ⟨1846786575883351504009525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39398113618844832085536533 1846786575883351504009525)
                      ·
                        rfl

theorem cell23_3596604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 2, 2, 1, 6].length) (baseStart_3596604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3596604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3596604 prefixEnd_3596604 := by exact prefixLift 3596604
  have htrace : WordTrace (prefixWord ++ tailWord_3596604) baseStart_3596604 baseEnd_3596604 := by
    simpa [prefixWord, tailWord_3596604, baseEnd_3596604] using wordTrace_append hprefix tailTrace_3596604
  have hstable : (prefixWord ++ tailWord_3596604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3596604).length < 2 ^ (prefixWord ++ tailWord_3596604).sum := by decide
  have hdescent : baseEnd_3596604 < baseStart_3596604 := by decide
  rcases family_descends (prefixWord ++ tailWord_3596604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3596652 : List Nat := [2, 2, 1, 1, 6, 1, 3, 2, 1, 4]
def baseStart_3596652 : Nat := 118140960795 + 3596652 * 2 ^ 59
def prefixEnd_3596652 : Nat := 4983230072969 + 3 ^ 40 * 3596652 * 2
def baseEnd_3596652 : Nat := 615603740984922438736435

theorem tailTrace_3596652 : CollatzResearch.WordTrace tailWord_3596652 prefixEnd_3596652 615603740984922438736435 := by
  unfold tailWord_3596652
  simp only [CollatzResearch.WordTrace]
  refine ⟨65590337682975769051516105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87453783577301025402021473 65590337682975769051516105)
  ·
    refine ⟨49192753262231826788637079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65590337682975769051516105 49192753262231826788637079)
    ·
      refine ⟨73789129893347740182955619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49192753262231826788637079 73789129893347740182955619)
      ·
        refine ⟨110683694840021610274433429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73789129893347740182955619 110683694840021610274433429)
        ·
          refine ⟨5188298195626012981614067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 110683694840021610274433429 5188298195626012981614067)
          ·
            refine ⟨7782447293439019472421101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5188298195626012981614067 7782447293439019472421101)
            ·
              refine ⟨2918417735039632302157913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7782447293439019472421101 2918417735039632302157913)
              ·
                refine ⟨2188813301279724226618435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2918417735039632302157913 2188813301279724226618435)
                ·
                  refine ⟨3283219951919586339927653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2188813301279724226618435 3283219951919586339927653)
                  ·
                    refine ⟨615603740984922438736435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3283219951919586339927653 615603740984922438736435)
                    ·
                      rfl

theorem cell23_3596652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 3, 2, 1, 4].length) (baseStart_3596652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3596652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3596652 prefixEnd_3596652 := by exact prefixLift 3596652
  have htrace : WordTrace (prefixWord ++ tailWord_3596652) baseStart_3596652 baseEnd_3596652 := by
    simpa [prefixWord, tailWord_3596652, baseEnd_3596652] using wordTrace_append hprefix tailTrace_3596652
  have hstable : (prefixWord ++ tailWord_3596652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3596652).length < 2 ^ (prefixWord ++ tailWord_3596652).sum := by decide
  have hdescent : baseEnd_3596652 < baseStart_3596652 := by decide
  rcases family_descends (prefixWord ++ tailWord_3596652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3596702 : List Nat := [4, 3, 1, 2, 1, 1, 2, 2, 2, 3, 2]
def baseStart_3596702 : Nat := 118140960795 + 3596702 * 2 ^ 59
def prefixEnd_3596702 : Nat := 4983230072969 + 3 ^ 40 * 3596702 * 2
def baseEnd_3596702 : Nat := 1846836896987492120584075

theorem tailTrace_3596702 : CollatzResearch.WordTrace tailWord_3596702 prefixEnd_3596702 1846836896987492120584075 := by
  unfold tailWord_3596702
  simp only [CollatzResearch.WordTrace]
  refine ⟨16397812376971299580294045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87454999343846931094901573 16397812376971299580294045)
  ·
    refine ⟨6149179641364237342610267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16397812376971299580294045 6149179641364237342610267)
    ·
      refine ⟨9223769462046356013915401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6149179641364237342610267 9223769462046356013915401)
      ·
        refine ⟨6917827096534767010436551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9223769462046356013915401 6917827096534767010436551)
        ·
          refine ⟨10376740644802150515654827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6917827096534767010436551 10376740644802150515654827)
          ·
            refine ⟨15565110967203225773482241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10376740644802150515654827 15565110967203225773482241)
            ·
              refine ⟨11673833225402419330111681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15565110967203225773482241 11673833225402419330111681)
              ·
                refine ⟨8755374919051814497583761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11673833225402419330111681 8755374919051814497583761)
                ·
                  refine ⟨6566531189288860873187821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8755374919051814497583761 6566531189288860873187821)
                  ·
                    refine ⟨2462449195983322827445433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6566531189288860873187821 2462449195983322827445433)
                    ·
                      refine ⟨1846836896987492120584075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2462449195983322827445433 1846836896987492120584075)
                      ·
                        rfl

theorem cell23_3596702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 2, 2, 3, 2].length) (baseStart_3596702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3596702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3596702 prefixEnd_3596702 := by exact prefixLift 3596702
  have htrace : WordTrace (prefixWord ++ tailWord_3596702) baseStart_3596702 baseEnd_3596702 := by
    simpa [prefixWord, tailWord_3596702, baseEnd_3596702] using wordTrace_append hprefix tailTrace_3596702
  have hstable : (prefixWord ++ tailWord_3596702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3596702).length < 2 ^ (prefixWord ++ tailWord_3596702).sum := by decide
  have hdescent : baseEnd_3596702 < baseStart_3596702 := by decide
  rcases family_descends (prefixWord ++ tailWord_3596702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3596704 : List Nat := [2, 1, 1, 4, 1, 14]
def baseStart_3596704 : Nat := 118140960795 + 3596704 * 2 ^ 59
def prefixEnd_3596704 : Nat := 4983230072969 + 3 ^ 40 * 3596704 * 2
def baseEnd_3596704 : Nat := 7600156065632926389955

theorem tailTrace_3596704 : CollatzResearch.WordTrace tailWord_3596704 prefixEnd_3596704 7600156065632926389955 := by
  unfold tailWord_3596704
  simp only [CollatzResearch.WordTrace]
  refine ⟨65591285980881575491962583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87455047974508767322616777 65591285980881575491962583)
  ·
    refine ⟨98386928971322363237943875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65591285980881575491962583 98386928971322363237943875)
    ·
      refine ⟨147580393456983544856915813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98386928971322363237943875 147580393456983544856915813)
      ·
        refine ⟨27671323773184414660671715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 147580393456983544856915813 27671323773184414660671715)
        ·
          refine ⟨41506985659776621991007573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27671323773184414660671715 41506985659776621991007573)
          ·
            refine ⟨7600156065632926389955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 41506985659776621991007573 7600156065632926389955)
            ·
              rfl

theorem cell23_3596704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 14].length) (baseStart_3596704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3596704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3596704 prefixEnd_3596704 := by exact prefixLift 3596704
  have htrace : WordTrace (prefixWord ++ tailWord_3596704) baseStart_3596704 baseEnd_3596704 := by
    simpa [prefixWord, tailWord_3596704, baseEnd_3596704] using wordTrace_append hprefix tailTrace_3596704
  have hstable : (prefixWord ++ tailWord_3596704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3596704).length < 2 ^ (prefixWord ++ tailWord_3596704).sum := by decide
  have hdescent : baseEnd_3596704 < baseStart_3596704 := by decide
  rcases family_descends (prefixWord ++ tailWord_3596704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3596708 : List Nat := [2, 3, 1, 2, 1, 1, 3, 4, 2, 4]
def baseStart_3596708 : Nat := 118140960795 + 3596708 * 2 ^ 59
def prefixEnd_3596708 : Nat := 4983230072969 + 3 ^ 40 * 3596708 * 2
def baseEnd_3596708 : Nat := 615613325957139699036349

theorem tailTrace_3596708 : CollatzResearch.WordTrace tailWord_3596708 prefixEnd_3596708 615613325957139699036349 := by
  unfold tailWord_3596708
  simp only [CollatzResearch.WordTrace]
  refine ⟨65591358926874329833535389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87455145235832439778047185 65591358926874329833535389)
  ·
    refine ⟨24596759597577873687575771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65591358926874329833535389 24596759597577873687575771)
    ·
      refine ⟨36895139396366810531363657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24596759597577873687575771 36895139396366810531363657)
      ·
        refine ⟨27671354547275107898522743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36895139396366810531363657 27671354547275107898522743)
        ·
          refine ⟨41507031820912661847784115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27671354547275107898522743 41507031820912661847784115)
          ·
            refine ⟨62260547731368992771676173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41507031820912661847784115 62260547731368992771676173)
            ·
              refine ⟨23347705399263372289378565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62260547731368992771676173 23347705399263372289378565)
              ·
                refine ⟨4377694762361882304258481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23347705399263372289378565 4377694762361882304258481)
                ·
                  refine ⟨3283271071771411728193861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4377694762361882304258481 3283271071771411728193861)
                  ·
                    refine ⟨615613325957139699036349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3283271071771411728193861 615613325957139699036349)
                    ·
                      rfl

theorem cell23_3596708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 4, 2, 4].length) (baseStart_3596708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3596708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3596708 prefixEnd_3596708 := by exact prefixLift 3596708
  have htrace : WordTrace (prefixWord ++ tailWord_3596708) baseStart_3596708 baseEnd_3596708 := by
    simpa [prefixWord, tailWord_3596708, baseEnd_3596708] using wordTrace_append hprefix tailTrace_3596708
  have hstable : (prefixWord ++ tailWord_3596708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3596708).length < 2 ^ (prefixWord ++ tailWord_3596708).sum := by decide
  have hdescent : baseEnd_3596708 < baseStart_3596708 := by decide
  rcases family_descends (prefixWord ++ tailWord_3596708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3596721 : List Nat := [1, 2, 2, 4, 1, 2, 3, 8]
def baseStart_3596721 : Nat := 118140960795 + 3596721 * 2 ^ 59
def prefixEnd_3596721 : Nat := 4983230072969 + 3 ^ 40 * 3596721 * 2
def baseEnd_3596721 : Nat := 68401727893330649860981

theorem tailTrace_3596721 : CollatzResearch.WordTrace tailWord_3596721 prefixEnd_3596721 68401727893330649860981 := by
  unfold tailWord_3596721
  simp only [CollatzResearch.WordTrace]
  refine ⟨131183192002701562887294017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87455461335134375258196011 131183192002701562887294017)
  ·
    refine ⟨98387394002026172165470513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131183192002701562887294017 98387394002026172165470513)
    ·
      refine ⟨73790545501519629124102885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98387394002026172165470513 73790545501519629124102885)
      ·
        refine ⟨13835727281534930460769291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73790545501519629124102885 13835727281534930460769291)
        ·
          refine ⟨20753590922302395691153937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13835727281534930460769291 20753590922302395691153937)
          ·
            refine ⟨15565193191726796768365453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20753590922302395691153937 15565193191726796768365453)
            ·
              refine ⟨5836947446897548788137045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15565193191726796768365453 5836947446897548788137045)
              ·
                refine ⟨68401727893330649860981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5836947446897548788137045 68401727893330649860981)
                ·
                  rfl

theorem cell23_3596721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 3, 8].length) (baseStart_3596721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3596721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3596721 prefixEnd_3596721 := by exact prefixLift 3596721
  have htrace : WordTrace (prefixWord ++ tailWord_3596721) baseStart_3596721 baseEnd_3596721 := by
    simpa [prefixWord, tailWord_3596721, baseEnd_3596721] using wordTrace_append hprefix tailTrace_3596721
  have hstable : (prefixWord ++ tailWord_3596721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3596721).length < 2 ^ (prefixWord ++ tailWord_3596721).sum := by decide
  have hdescent : baseEnd_3596721 < baseStart_3596721 := by decide
  rcases family_descends (prefixWord ++ tailWord_3596721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3596732 : List Nat := [2, 2, 2, 4, 1, 2, 1, 2, 3, 2, 2]
def baseStart_3596732 : Nat := 118140960795 + 3596732 * 2 ^ 59
def prefixEnd_3596732 : Nat := 4983230072969 + 3 ^ 40 * 3596732 * 2
def baseEnd_3596732 : Nat := 1846852301407127003208937

theorem tailTrace_3596732 : CollatzResearch.WordTrace tailWord_3596732 prefixEnd_3596732 1846852301407127003208937 := by
  unfold tailWord_3596732
  simp only [CollatzResearch.WordTrace]
  refine ⟨65591796602830855882972225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87455728803774474510629633 65591796602830855882972225)
  ·
    refine ⟨49193847452123141912229169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65591796602830855882972225 49193847452123141912229169)
    ·
      refine ⟨36895385589092356434171877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49193847452123141912229169 36895385589092356434171877)
      ·
        refine ⟨6917884797954816831407227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36895385589092356434171877 6917884797954816831407227)
        ·
          refine ⟨10376827196932225247110841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6917884797954816831407227 10376827196932225247110841)
          ·
            refine ⟨7782620397699168935333131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10376827196932225247110841 7782620397699168935333131)
            ·
              refine ⟨11673930596548753402999697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7782620397699168935333131 11673930596548753402999697)
              ·
                refine ⟨8755447947411565052249773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11673930596548753402999697 8755447947411565052249773)
                ·
                  refine ⟨3283292980279336894593665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8755447947411565052249773 3283292980279336894593665)
                  ·
                    refine ⟨2462469735209502670945249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3283292980279336894593665 2462469735209502670945249)
                    ·
                      refine ⟨1846852301407127003208937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2462469735209502670945249 1846852301407127003208937)
                      ·
                        rfl

theorem cell23_3596732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 2, 3, 2, 2].length) (baseStart_3596732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3596732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3596732 prefixEnd_3596732 := by exact prefixLift 3596732
  have htrace : WordTrace (prefixWord ++ tailWord_3596732) baseStart_3596732 baseEnd_3596732 := by
    simpa [prefixWord, tailWord_3596732, baseEnd_3596732] using wordTrace_append hprefix tailTrace_3596732
  have hstable : (prefixWord ++ tailWord_3596732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3596732).length < 2 ^ (prefixWord ++ tailWord_3596732).sum := by decide
  have hdescent : baseEnd_3596732 < baseStart_3596732 := by decide
  rcases family_descends (prefixWord ++ tailWord_3596732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3596765 : List Nat := [1, 4, 3, 1, 1, 1, 3, 1, 4, 1, 3]
def baseStart_3596765 : Nat := 118140960795 + 3596765 * 2 ^ 59
def prefixEnd_3596765 : Nat := 4983230072969 + 3 ^ 40 * 3596765 * 2
def baseEnd_3596765 : Nat := 1846869246268725374096285

theorem tailTrace_3596765 : CollatzResearch.WordTrace tailWord_3596765 prefixEnd_3596765 1846869246268725374096285 := by
  unfold tailWord_3596765
  simp only [CollatzResearch.WordTrace]
  refine ⟨131184796814542158401895749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87456531209694772267930499 131184796814542158401895749)
  ·
    refine ⟨24597149402726654700355453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 131184796814542158401895749 24597149402726654700355453)
    ·
      refine ⟨9223931026022495512633295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24597149402726654700355453 9223931026022495512633295)
      ·
        refine ⟨13835896539033743268949943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9223931026022495512633295 13835896539033743268949943)
        ·
          refine ⟨20753844808550614903424915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13835896539033743268949943 20753844808550614903424915)
          ·
            refine ⟨31130767212825922355137373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20753844808550614903424915 31130767212825922355137373)
            ·
              refine ⟨11674037704809720883176515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31130767212825922355137373 11674037704809720883176515)
              ·
                refine ⟨17511056557214581324764773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11674037704809720883176515 17511056557214581324764773)
                ·
                  refine ⟨3283323104477733998393395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17511056557214581324764773 3283323104477733998393395)
                  ·
                    refine ⟨4924984656716600997590093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3283323104477733998393395 4924984656716600997590093)
                    ·
                      refine ⟨1846869246268725374096285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4924984656716600997590093 1846869246268725374096285)
                      ·
                        rfl

theorem cell23_3596765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 1, 4, 1, 3].length) (baseStart_3596765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3596765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3596765 prefixEnd_3596765 := by exact prefixLift 3596765
  have htrace : WordTrace (prefixWord ++ tailWord_3596765) baseStart_3596765 baseEnd_3596765 := by
    simpa [prefixWord, tailWord_3596765, baseEnd_3596765] using wordTrace_append hprefix tailTrace_3596765
  have hstable : (prefixWord ++ tailWord_3596765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3596765).length < 2 ^ (prefixWord ++ tailWord_3596765).sum := by decide
  have hdescent : baseEnd_3596765 < baseStart_3596765 := by decide
  rcases family_descends (prefixWord ++ tailWord_3596765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3596791 : List Nat := [1, 1, 3, 1, 1, 1, 1, 2, 3, 6, 3]
def baseStart_3596791 : Nat := 118140960795 + 3596791 * 2 ^ 59
def prefixEnd_3596791 : Nat := 4983230072969 + 3 ^ 40 * 3596791 * 2
def baseEnd_3596791 : Nat := 1846882596765742272371165

theorem tailTrace_3596791 : CollatzResearch.WordTrace tailWord_3596791 prefixEnd_3596791 1846882596765742272371165 := by
  unfold tailWord_3596791
  simp only [CollatzResearch.WordTrace]
  refine ⟨131185745112447964842342227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87457163408298643228228151 131185745112447964842342227)
  ·
    refine ⟨196778617668671947263513341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131185745112447964842342227 196778617668671947263513341)
    ·
      refine ⟨73791981625751980223817503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196778617668671947263513341 73791981625751980223817503)
      ·
        refine ⟨110687972438627970335726255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73791981625751980223817503 110687972438627970335726255)
        ·
          refine ⟨166031958657941955503589383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110687972438627970335726255 166031958657941955503589383)
          ·
            refine ⟨249047937986912933255384075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166031958657941955503589383 249047937986912933255384075)
            ·
              refine ⟨373571906980369399883076113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 249047937986912933255384075 373571906980369399883076113)
              ·
                refine ⟨280178930235277049912307085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 373571906980369399883076113 280178930235277049912307085)
                ·
                  refine ⟨105067098838228893717115157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 280178930235277049912307085 105067098838228893717115157)
                  ·
                    refine ⟨4925020258041979392989773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 105067098838228893717115157 4925020258041979392989773)
                    ·
                      refine ⟨1846882596765742272371165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4925020258041979392989773 1846882596765742272371165)
                      ·
                        rfl

theorem cell23_3596791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 6, 3].length) (baseStart_3596791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3596791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3596791 prefixEnd_3596791 := by exact prefixLift 3596791
  have htrace : WordTrace (prefixWord ++ tailWord_3596791) baseStart_3596791 baseEnd_3596791 := by
    simpa [prefixWord, tailWord_3596791, baseEnd_3596791] using wordTrace_append hprefix tailTrace_3596791
  have hstable : (prefixWord ++ tailWord_3596791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3596791).length < 2 ^ (prefixWord ++ tailWord_3596791).sum := by decide
  have hdescent : baseEnd_3596791 < baseStart_3596791 := by decide
  rcases family_descends (prefixWord ++ tailWord_3596791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3596805 : List Nat := [1, 3, 1, 1, 2, 2, 3, 2, 4, 2, 2]
def baseStart_3596805 : Nat := 118140960795 + 3596805 * 2 ^ 59
def prefixEnd_3596805 : Nat := 4983230072969 + 3 ^ 40 * 3596805 * 2
def baseEnd_3596805 : Nat := 1846889785494905217596101

theorem tailTrace_3596805 : CollatzResearch.WordTrace tailWord_3596805 prefixEnd_3596805 1846889785494905217596101 := by
  unfold tailWord_3596805
  simp only [CollatzResearch.WordTrace]
  refine ⟨131186255734397245233351869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87457503822931496822234579 131186255734397245233351869)
  ·
    refine ⟨49194845900398966962506951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131186255734397245233351869 49194845900398966962506951)
    ·
      refine ⟨73792268850598450443760427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49194845900398966962506951 73792268850598450443760427)
      ·
        refine ⟨110688403275897675665640641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73792268850598450443760427 110688403275897675665640641)
        ·
          refine ⟨83016302456923256749230481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110688403275897675665640641 83016302456923256749230481)
          ·
            refine ⟨62262226842692442561922861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83016302456923256749230481 62262226842692442561922861)
            ·
              refine ⟨23348335066009665960721073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62262226842692442561922861 23348335066009665960721073)
              ·
                refine ⟨17511251299507249470540805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23348335066009665960721073 17511251299507249470540805)
                ·
                  refine ⟨3283359618657609275726401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17511251299507249470540805 3283359618657609275726401)
                  ·
                    refine ⟨2462519713993206956794801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3283359618657609275726401 2462519713993206956794801)
                    ·
                      refine ⟨1846889785494905217596101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2462519713993206956794801 1846889785494905217596101)
                      ·
                        rfl

theorem cell23_3596805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 2, 4, 2, 2].length) (baseStart_3596805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3596805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3596805 prefixEnd_3596805 := by exact prefixLift 3596805
  have htrace : WordTrace (prefixWord ++ tailWord_3596805) baseStart_3596805 baseEnd_3596805 := by
    simpa [prefixWord, tailWord_3596805, baseEnd_3596805] using wordTrace_append hprefix tailTrace_3596805
  have hstable : (prefixWord ++ tailWord_3596805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3596805).length < 2 ^ (prefixWord ++ tailWord_3596805).sum := by decide
  have hdescent : baseEnd_3596805 < baseStart_3596805 := by decide
  rcases family_descends (prefixWord ++ tailWord_3596805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3596821 : List Nat := [1, 3, 2, 1, 3, 1, 1, 1, 1, 2, 7]
def baseStart_3596821 : Nat := 118140960795 + 3596821 * 2 ^ 59
def prefixEnd_3596821 : Nat := 4983230072969 + 3 ^ 40 * 3596821 * 2
def baseEnd_3596821 : Nat := 1846898001185377154996027

theorem tailTrace_3596821 : CollatzResearch.WordTrace tailWord_3596821 prefixEnd_3596821 1846898001185377154996027 := by
  unfold tailWord_3596821
  simp only [CollatzResearch.WordTrace]
  refine ⟨131186839302339279965934317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87457892868226186643956211 131186839302339279965934317)
  ·
    refine ⟨49195064738377229987225369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131186839302339279965934317 49195064738377229987225369)
    ·
      refine ⟨36896298553782922490419027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49195064738377229987225369 36896298553782922490419027)
      ·
        refine ⟨55344447830674383735628541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36896298553782922490419027 55344447830674383735628541)
        ·
          refine ⟨20754167936502893900860703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55344447830674383735628541 20754167936502893900860703)
          ·
            refine ⟨31131251904754340851291055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20754167936502893900860703 31131251904754340851291055)
            ·
              refine ⟨46696877857131511276936583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31131251904754340851291055 46696877857131511276936583)
              ·
                refine ⟨70045316785697266915404875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46696877857131511276936583 70045316785697266915404875)
                ·
                  refine ⟨105067975178545900373107313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70045316785697266915404875 105067975178545900373107313)
                  ·
                    refine ⟨78800981383909425279830485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 105067975178545900373107313 78800981383909425279830485)
                    ·
                      refine ⟨1846898001185377154996027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 78800981383909425279830485 1846898001185377154996027)
                      ·
                        rfl

theorem cell23_3596821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 2, 7].length) (baseStart_3596821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3596821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3596821 prefixEnd_3596821 := by exact prefixLift 3596821
  have htrace : WordTrace (prefixWord ++ tailWord_3596821) baseStart_3596821 baseEnd_3596821 := by
    simpa [prefixWord, tailWord_3596821, baseEnd_3596821] using wordTrace_append hprefix tailTrace_3596821
  have hstable : (prefixWord ++ tailWord_3596821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3596821).length < 2 ^ (prefixWord ++ tailWord_3596821).sum := by decide
  have hdescent : baseEnd_3596821 < baseStart_3596821 := by decide
  rcases family_descends (prefixWord ++ tailWord_3596821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3596828 : List Nat := [2, 2, 3, 1, 2, 2, 3, 1, 7]
def baseStart_3596828 : Nat := 118140960795 + 3596828 * 2 ^ 59
def prefixEnd_3596828 : Nat := 4983230072969 + 3 ^ 40 * 3596828 * 2
def baseEnd_3596828 : Nat := 205211288394439847512055

theorem tailTrace_3596828 : CollatzResearch.WordTrace tailWord_3596828 prefixEnd_3596828 205211288394439847512055 := by
  unfold tailWord_3596828
  simp only [CollatzResearch.WordTrace]
  refine ⟨65593547306656960080719569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87458063075542613440959425 65593547306656960080719569)
  ·
    refine ⟨49195160479992720060539677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65593547306656960080719569 49195160479992720060539677)
    ·
      refine ⟨18448185179997270022702379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49195160479992720060539677 18448185179997270022702379)
      ·
        refine ⟨27672277769995905034053569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18448185179997270022702379 27672277769995905034053569)
        ·
          refine ⟨20754208327496928775540177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27672277769995905034053569 20754208327496928775540177)
          ·
            refine ⟨15565656245622696581655133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20754208327496928775540177 15565656245622696581655133)
            ·
              refine ⟨5837121092108511218120675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15565656245622696581655133 5837121092108511218120675)
              ·
                refine ⟨8755681638162766827181013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5837121092108511218120675 8755681638162766827181013)
                ·
                  refine ⟨205211288394439847512055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8755681638162766827181013 205211288394439847512055)
                  ·
                    rfl

theorem cell23_3596828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 3, 1, 7].length) (baseStart_3596828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3596828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3596828 prefixEnd_3596828 := by exact prefixLift 3596828
  have htrace : WordTrace (prefixWord ++ tailWord_3596828) baseStart_3596828 baseEnd_3596828 := by
    simpa [prefixWord, tailWord_3596828, baseEnd_3596828] using wordTrace_append hprefix tailTrace_3596828
  have hstable : (prefixWord ++ tailWord_3596828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3596828).length < 2 ^ (prefixWord ++ tailWord_3596828).sum := by decide
  have hdescent : baseEnd_3596828 < baseStart_3596828 := by decide
  rcases family_descends (prefixWord ++ tailWord_3596828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3596851 : List Nat := [1, 1, 1, 2, 4, 2, 1, 2, 1, 1, 7]
def baseStart_3596851 : Nat := 118140960795 + 3596851 * 2 ^ 59
def prefixEnd_3596851 : Nat := 4983230072969 + 3 ^ 40 * 3596851 * 2
def baseEnd_3596851 : Nat := 1846913405605012037620889

theorem tailTrace_3596851 : CollatzResearch.WordTrace tailWord_3596851 prefixEnd_3596851 1846913405605012037620889 := by
  unfold tailWord_3596851
  simp only [CollatzResearch.WordTrace]
  refine ⟨131187933492230595089526407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87458622328153730059684271 131187933492230595089526407)
  ·
    refine ⟨196781900238345892634289611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131187933492230595089526407 196781900238345892634289611)
    ·
      refine ⟨295172850357518838951434417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196781900238345892634289611 295172850357518838951434417)
      ·
        refine ⟨221379637768139129213575813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 295172850357518838951434417 221379637768139129213575813)
        ·
          refine ⟨41508682081526086727545465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 221379637768139129213575813 41508682081526086727545465)
          ·
            refine ⟨31131511561144565045659099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41508682081526086727545465 31131511561144565045659099)
            ·
              refine ⟨46697267341716847568488649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31131511561144565045659099 46697267341716847568488649)
              ·
                refine ⟨35022950506287635676366487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46697267341716847568488649 35022950506287635676366487)
                ·
                  refine ⟨52534425759431453514549731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35022950506287635676366487 52534425759431453514549731)
                  ·
                    refine ⟨78801638639147180271824597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52534425759431453514549731 78801638639147180271824597)
                    ·
                      refine ⟨1846913405605012037620889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 78801638639147180271824597 1846913405605012037620889)
                      ·
                        rfl

theorem cell23_3596851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 2, 1, 1, 7].length) (baseStart_3596851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3596851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3596851 prefixEnd_3596851 := by exact prefixLift 3596851
  have htrace : WordTrace (prefixWord ++ tailWord_3596851) baseStart_3596851 baseEnd_3596851 := by
    simpa [prefixWord, tailWord_3596851, baseEnd_3596851] using wordTrace_append hprefix tailTrace_3596851
  have hstable : (prefixWord ++ tailWord_3596851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3596851).length < 2 ^ (prefixWord ++ tailWord_3596851).sum := by decide
  have hdescent : baseEnd_3596851 < baseStart_3596851 := by decide
  rcases family_descends (prefixWord ++ tailWord_3596851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3596858 : List Nat := [3, 1, 1, 1, 3, 3, 1, 3, 2, 5]
def baseStart_3596858 : Nat := 118140960795 + 3596858 * 2 ^ 59
def prefixEnd_3596858 : Nat := 4983230072969 + 3 ^ 40 * 3596858 * 2
def baseEnd_3596858 : Nat := 615638999989864503411119

theorem tailTrace_3596858 : CollatzResearch.WordTrace tailWord_3596858 prefixEnd_3596858 615638999989864503411119 := by
  unfold tailWord_3596858
  simp only [CollatzResearch.WordTrace]
  refine ⟨32797047200801308821257807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87458792535470156856687485 32797047200801308821257807)
  ·
    refine ⟨49195570801201963231886711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32797047200801308821257807 49195570801201963231886711)
    ·
      refine ⟨73793356201802944847830067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49195570801201963231886711 73793356201802944847830067)
      ·
        refine ⟨110690034302704417271745101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73793356201802944847830067 110690034302704417271745101)
        ·
          refine ⟨41508762863514156476904413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110690034302704417271745101 41508762863514156476904413)
          ·
            refine ⟨15565786073817808678839155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41508762863514156476904413 15565786073817808678839155)
            ·
              refine ⟨23348679110726713018258733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15565786073817808678839155 23348679110726713018258733)
              ·
                refine ⟨8755754666522517381847025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23348679110726713018258733 8755754666522517381847025)
                ·
                  refine ⟨6566815999891888036385269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8755754666522517381847025 6566815999891888036385269)
                  ·
                    refine ⟨615638999989864503411119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6566815999891888036385269 615638999989864503411119)
                    ·
                      rfl

theorem cell23_3596858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 3, 2, 5].length) (baseStart_3596858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3596858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3596858 prefixEnd_3596858 := by exact prefixLift 3596858
  have htrace : WordTrace (prefixWord ++ tailWord_3596858) baseStart_3596858 baseEnd_3596858 := by
    simpa [prefixWord, tailWord_3596858, baseEnd_3596858] using wordTrace_append hprefix tailTrace_3596858
  have hstable : (prefixWord ++ tailWord_3596858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3596858).length < 2 ^ (prefixWord ++ tailWord_3596858).sum := by decide
  have hdescent : baseEnd_3596858 < baseStart_3596858 := by decide
  rcases family_descends (prefixWord ++ tailWord_3596858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3596912 : List Nat := [2, 1, 1, 1, 7, 2, 1, 1, 2, 1, 4]
def baseStart_3596912 : Nat := 118140960795 + 3596912 * 2 ^ 59
def prefixEnd_3596912 : Nat := 4983230072969 + 3 ^ 40 * 3596912 * 2
def baseEnd_3596912 : Nat := 1846944727924936298958109

theorem tailTrace_3596912 : CollatzResearch.WordTrace tailWord_3596912 prefixEnd_3596912 1846944727924936298958109 := by
  unfold tailWord_3596912
  simp only [CollatzResearch.WordTrace]
  refine ⟨65595079172504801253748495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87460105563339735004997993 65595079172504801253748495)
  ·
    refine ⟨98392618758757201880622743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65595079172504801253748495 98392618758757201880622743)
    ·
      refine ⟨147588928138135802820934115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98392618758757201880622743 147588928138135802820934115)
      ·
        refine ⟨221383392207203704231401173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147588928138135802820934115 221383392207203704231401173)
        ·
          refine ⟨5188673254856336817923465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 221383392207203704231401173 5188673254856336817923465)
          ·
            refine ⟨3891504941142252613442599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5188673254856336817923465 3891504941142252613442599)
            ·
              refine ⟨5837257411713378920163899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3891504941142252613442599 5837257411713378920163899)
              ·
                refine ⟨8755886117570068380245849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5837257411713378920163899 8755886117570068380245849)
                ·
                  refine ⟨6566914588177551285184387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8755886117570068380245849 6566914588177551285184387)
                  ·
                    refine ⟨9850371882266326927776581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6566914588177551285184387 9850371882266326927776581)
                    ·
                      refine ⟨1846944727924936298958109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9850371882266326927776581 1846944727924936298958109)
                      ·
                        rfl

theorem cell23_3596912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 1, 1, 2, 1, 4].length) (baseStart_3596912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3596912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3596912 prefixEnd_3596912 := by exact prefixLift 3596912
  have htrace : WordTrace (prefixWord ++ tailWord_3596912) baseStart_3596912 baseEnd_3596912 := by
    simpa [prefixWord, tailWord_3596912, baseEnd_3596912] using wordTrace_append hprefix tailTrace_3596912
  have hstable : (prefixWord ++ tailWord_3596912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3596912).length < 2 ^ (prefixWord ++ tailWord_3596912).sum := by decide
  have hdescent : baseEnd_3596912 < baseStart_3596912 := by decide
  rcases family_descends (prefixWord ++ tailWord_3596912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3596978 : List Nat := [3, 2, 1, 1, 1, 2, 1, 3, 3, 6]
def baseStart_3596978 : Nat := 118140960795 + 3596978 * 2 ^ 59
def prefixEnd_3596978 : Nat := 4983230072969 + 3 ^ 40 * 3596978 * 2
def baseEnd_3596978 : Nat := 615659539216044346910935

theorem tailTrace_3596978 : CollatzResearch.WordTrace tailWord_3596978 prefixEnd_3596978 615659539216044346910935 := by
  unfold tailWord_3596978
  simp only [CollatzResearch.WordTrace]
  refine ⟨32798141390692623944849897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87461710375180330519599725 32798141390692623944849897)
  ·
    refine ⟨24598606043019467958637423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32798141390692623944849897 24598606043019467958637423)
    ·
      refine ⟨36897909064529201937956135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24598606043019467958637423 36897909064529201937956135)
      ·
        refine ⟨55346863596793802906934203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36897909064529201937956135 55346863596793802906934203)
        ·
          refine ⟨83020295395190704360401305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55346863596793802906934203 83020295395190704360401305)
          ·
            refine ⟨62265221546393028270300979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83020295395190704360401305 62265221546393028270300979)
            ·
              refine ⟨93397832319589542405451469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62265221546393028270300979 93397832319589542405451469)
              ·
                refine ⟨35024187119846078402044301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93397832319589542405451469 35024187119846078402044301)
                ·
                  refine ⟨13134070169942279400766613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35024187119846078402044301 13134070169942279400766613)
                  ·
                    refine ⟨615659539216044346910935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13134070169942279400766613 615659539216044346910935)
                    ·
                      rfl

theorem cell23_3596978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 3, 3, 6].length) (baseStart_3596978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3596978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3596978 prefixEnd_3596978 := by exact prefixLift 3596978
  have htrace : WordTrace (prefixWord ++ tailWord_3596978) baseStart_3596978 baseEnd_3596978 := by
    simpa [prefixWord, tailWord_3596978, baseEnd_3596978] using wordTrace_append hprefix tailTrace_3596978
  have hstable : (prefixWord ++ tailWord_3596978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3596978).length < 2 ^ (prefixWord ++ tailWord_3596978).sum := by decide
  have hdescent : baseEnd_3596978 < baseStart_3596978 := by decide
  rcases family_descends (prefixWord ++ tailWord_3596978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3596979 : List Nat := [1, 1, 1, 2, 3, 4, 3, 3, 1, 1, 3]
def baseStart_3596979 : Nat := 118140960795 + 3596979 * 2 ^ 59
def prefixEnd_3596979 : Nat := 4983230072969 + 3 ^ 40 * 3596979 * 2
def baseEnd_3596979 : Nat := 1846979131128787536820301

theorem tailTrace_3596979 : CollatzResearch.WordTrace tailWord_3596979 prefixEnd_3596979 1846979131128787536820301 := by
  unfold tailWord_3596979
  simp only [CollatzResearch.WordTrace]
  refine ⟨131192602035766872950185991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87461734690511248633457327 131192602035766872950185991)
  ·
    refine ⟨196788903053650309425278987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131192602035766872950185991 196788903053650309425278987)
    ·
      refine ⟨295183354580475464137918481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196788903053650309425278987 295183354580475464137918481)
      ·
        refine ⟨221387515935356598103438861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 295183354580475464137918481 221387515935356598103438861)
        ·
          refine ⟨83020318475758724288789573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 221387515935356598103438861 83020318475758724288789573)
          ·
            refine ⟨15566309714204760804148045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83020318475758724288789573 15566309714204760804148045)
            ·
              refine ⟨5837366142826785301555517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15566309714204760804148045 5837366142826785301555517)
              ·
                refine ⟨2189012303560044488083319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5837366142826785301555517 2189012303560044488083319)
                ·
                  refine ⟨3283518455340066732124979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2189012303560044488083319 3283518455340066732124979)
                  ·
                    refine ⟨4925277683010100098187469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3283518455340066732124979 4925277683010100098187469)
                    ·
                      refine ⟨1846979131128787536820301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4925277683010100098187469 1846979131128787536820301)
                      ·
                        rfl

theorem cell23_3596979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 3, 3, 1, 1, 3].length) (baseStart_3596979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3596979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3596979 prefixEnd_3596979 := by exact prefixLift 3596979
  have htrace : WordTrace (prefixWord ++ tailWord_3596979) baseStart_3596979 baseEnd_3596979 := by
    simpa [prefixWord, tailWord_3596979, baseEnd_3596979] using wordTrace_append hprefix tailTrace_3596979
  have hstable : (prefixWord ++ tailWord_3596979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3596979).length < 2 ^ (prefixWord ++ tailWord_3596979).sum := by decide
  have hdescent : baseEnd_3596979 < baseStart_3596979 := by decide
  rcases family_descends (prefixWord ++ tailWord_3596979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3597032 : List Nat := [2, 1, 4, 1, 4, 1, 1, 2, 1, 2, 4]
def baseStart_3597032 : Nat := 118140960795 + 3597032 * 2 ^ 59
def prefixEnd_3597032 : Nat := 4983230072969 + 3 ^ 40 * 3597032 * 2
def baseEnd_3597032 : Nat := 1847006345603475829457557

theorem tailTrace_3597032 : CollatzResearch.WordTrace tailWord_3597032 prefixEnd_3597032 1847006345603475829457557 := by
  unfold tailWord_3597032
  simp only [CollatzResearch.WordTrace]
  refine ⟨65597267552287431500932675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87463023403049908667910233 65597267552287431500932675)
  ·
    refine ⟨98395901328431147251399013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65597267552287431500932675 98395901328431147251399013)
    ·
      refine ⟨18449231499080840109637315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98395901328431147251399013 18449231499080840109637315)
      ·
        refine ⟨27673847248621260164455973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18449231499080840109637315 27673847248621260164455973)
        ·
          refine ⟨5188846359116486280835495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27673847248621260164455973 5188846359116486280835495)
          ·
            refine ⟨7783269538674729421253243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5188846359116486280835495 7783269538674729421253243)
            ·
              refine ⟨11674904308012094131879865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7783269538674729421253243 11674904308012094131879865)
              ·
                refine ⟨8756178231009070598909899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11674904308012094131879865 8756178231009070598909899)
                ·
                  refine ⟨13134267346513605898364849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8756178231009070598909899 13134267346513605898364849)
                  ·
                    refine ⟨9850700509885204423773637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13134267346513605898364849 9850700509885204423773637)
                    ·
                      refine ⟨1847006345603475829457557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9850700509885204423773637 1847006345603475829457557)
                      ·
                        rfl

theorem cell23_3597032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 2, 1, 2, 4].length) (baseStart_3597032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3597032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3597032 prefixEnd_3597032 := by exact prefixLift 3597032
  have htrace : WordTrace (prefixWord ++ tailWord_3597032) baseStart_3597032 baseEnd_3597032 := by
    simpa [prefixWord, tailWord_3597032, baseEnd_3597032] using wordTrace_append hprefix tailTrace_3597032
  have hstable : (prefixWord ++ tailWord_3597032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3597032).length < 2 ^ (prefixWord ++ tailWord_3597032).sum := by decide
  have hdescent : baseEnd_3597032 < baseStart_3597032 := by decide
  rcases family_descends (prefixWord ++ tailWord_3597032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3597039 : List Nat := [1, 1, 2, 1, 5, 3, 3, 1, 1, 2, 3]
def baseStart_3597039 : Nat := 118140960795 + 3597039 * 2 ^ 59
def prefixEnd_3597039 : Nat := 4983230072969 + 3 ^ 40 * 3597039 * 2
def baseEnd_3597039 : Nat := 1847009939968057302070025

theorem tailTrace_3597039 : CollatzResearch.WordTrace tailWord_3597039 prefixEnd_3597039 1847009939968057302070025 := by
  unfold tailWord_3597039
  simp only [CollatzResearch.WordTrace]
  refine ⟨131194790415549503197370171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87463193610366335464913447 131194790415549503197370171)
  ·
    refine ⟨196792185623324254796055257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131194790415549503197370171 196792185623324254796055257)
    ·
      refine ⟨147594139217493191097041443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196792185623324254796055257 147594139217493191097041443)
      ·
        refine ⟨221391208826239786645562165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147594139217493191097041443 221391208826239786645562165)
        ·
          refine ⟨20755425827459979998021453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 221391208826239786645562165 20755425827459979998021453)
          ·
            refine ⟨7783284685297492499258045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20755425827459979998021453 7783284685297492499258045)
            ·
              refine ⟨2918731756986559687221767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7783284685297492499258045 2918731756986559687221767)
              ·
                refine ⟨4378097635479839530832651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2918731756986559687221767 4378097635479839530832651)
                ·
                  refine ⟨6567146453219759296248977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4378097635479839530832651 6567146453219759296248977)
                  ·
                    refine ⟨4925359839914819472186733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6567146453219759296248977 4925359839914819472186733)
                    ·
                      refine ⟨1847009939968057302070025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4925359839914819472186733 1847009939968057302070025)
                      ·
                        rfl

theorem cell23_3597039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 3, 1, 1, 2, 3].length) (baseStart_3597039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3597039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3597039 prefixEnd_3597039 := by exact prefixLift 3597039
  have htrace : WordTrace (prefixWord ++ tailWord_3597039) baseStart_3597039 baseEnd_3597039 := by
    simpa [prefixWord, tailWord_3597039, baseEnd_3597039] using wordTrace_append hprefix tailTrace_3597039
  have hstable : (prefixWord ++ tailWord_3597039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3597039).length < 2 ^ (prefixWord ++ tailWord_3597039).sum := by decide
  have hdescent : baseEnd_3597039 < baseStart_3597039 := by decide
  rcases family_descends (prefixWord ++ tailWord_3597039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3597102 : List Nat := [4, 1, 3, 2, 1, 1, 1, 2, 2, 6]
def baseStart_3597102 : Nat := 118140960795 + 3597102 * 2 ^ 59
def prefixEnd_3597102 : Nat := 4983230072969 + 3 ^ 40 * 3597102 * 2
def baseEnd_3597102 : Nat := 615680763083096851860745

theorem tailTrace_3597102 : CollatzResearch.WordTrace tailWord_3597102 prefixEnd_3597102 615680763083096851860745 := by
  unfold tailWord_3597102
  simp only [CollatzResearch.WordTrace]
  refine ⟨16399636026790158119614195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87464725476214176637942373 16399636026790158119614195)
  ·
    refine ⟨24599454040185237179421293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16399636026790158119614195 24599454040185237179421293)
    ·
      refine ⟨9224795265069463942282985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24599454040185237179421293 9224795265069463942282985)
      ·
        refine ⟨6918596448802097956712239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9224795265069463942282985 6918596448802097956712239)
        ·
          refine ⟨10377894673203146935068359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6918596448802097956712239 10377894673203146935068359)
          ·
            refine ⟨15566842009804720402602539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10377894673203146935068359 15566842009804720402602539)
            ·
              refine ⟨23350263014707080603903809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15566842009804720402602539 23350263014707080603903809)
              ·
                refine ⟨17512697261030310452927857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23350263014707080603903809 17512697261030310452927857)
                ·
                  refine ⟨13134522945772732839695893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17512697261030310452927857 13134522945772732839695893)
                  ·
                    refine ⟨615680763083096851860745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13134522945772732839695893 615680763083096851860745)
                    ·
                      rfl

theorem cell23_3597102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 2, 2, 6].length) (baseStart_3597102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3597102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3597102 prefixEnd_3597102 := by exact prefixLift 3597102
  have htrace : WordTrace (prefixWord ++ tailWord_3597102) baseStart_3597102 baseEnd_3597102 := by
    simpa [prefixWord, tailWord_3597102, baseEnd_3597102] using wordTrace_append hprefix tailTrace_3597102
  have hstable : (prefixWord ++ tailWord_3597102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3597102).length < 2 ^ (prefixWord ++ tailWord_3597102).sum := by decide
  have hdescent : baseEnd_3597102 < baseStart_3597102 := by decide
  rcases family_descends (prefixWord ++ tailWord_3597102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3597105 : List Nat := [1, 2, 2, 3, 2, 1, 1, 1, 4, 2, 4]
def baseStart_3597105 : Nat := 118140960795 + 3597105 * 2 ^ 59
def prefixEnd_3597105 : Nat := 4983230072969 + 3 ^ 40 * 3597105 * 2
def baseEnd_3597105 : Nat := 1847043829691254043844721

theorem tailTrace_3597105 : CollatzResearch.WordTrace tailWord_3597105 prefixEnd_3597105 1847043829691254043844721 := by
  unfold tailWord_3597105
  simp only [CollatzResearch.WordTrace]
  refine ⟨131197197633310396469272769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87464798422206930979515179 131197197633310396469272769)
  ·
    refine ⟨98397898224982797351954577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131197197633310396469272769 98397898224982797351954577)
    ·
      refine ⟨73798423668737098013965933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98397898224982797351954577 73798423668737098013965933)
      ·
        refine ⟨27674408875776411755237225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73798423668737098013965933 27674408875776411755237225)
        ·
          refine ⟨20755806656832308816427919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27674408875776411755237225 20755806656832308816427919)
          ·
            refine ⟨31133709985248463224641879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20755806656832308816427919 31133709985248463224641879)
            ·
              refine ⟨46700564977872694836962819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31133709985248463224641879 46700564977872694836962819)
              ·
                refine ⟨70050847466809042255444229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46700564977872694836962819 70050847466809042255444229)
                ·
                  refine ⟨13134533900026695422895793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70050847466809042255444229 13134533900026695422895793)
                  ·
                    refine ⟨9850900425020021567171845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13134533900026695422895793 9850900425020021567171845)
                    ·
                      refine ⟨1847043829691254043844721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9850900425020021567171845 1847043829691254043844721)
                      ·
                        rfl

theorem cell23_3597105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 4, 2, 4].length) (baseStart_3597105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3597105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3597105 prefixEnd_3597105 := by exact prefixLift 3597105
  have htrace : WordTrace (prefixWord ++ tailWord_3597105) baseStart_3597105 baseEnd_3597105 := by
    simpa [prefixWord, tailWord_3597105, baseEnd_3597105] using wordTrace_append hprefix tailTrace_3597105
  have hstable : (prefixWord ++ tailWord_3597105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3597105).length < 2 ^ (prefixWord ++ tailWord_3597105).sum := by decide
  have hdescent : baseEnd_3597105 < baseStart_3597105 := by decide
  rcases family_descends (prefixWord ++ tailWord_3597105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3597125 : List Nat := [1, 3, 1, 1, 1, 2, 2, 3, 1, 5, 3]
def baseStart_3597125 : Nat := 118140960795 + 3597125 * 2 ^ 59
def prefixEnd_3597125 : Nat := 4983230072969 + 3 ^ 40 * 3597125 * 2
def baseEnd_3597125 : Nat := 1847054099304343965594629

theorem tailTrace_3597125 : CollatzResearch.WordTrace tailWord_3597125 prefixEnd_3597125 1847054099304343965594629 := by
  unfold tailWord_3597125
  simp only [CollatzResearch.WordTrace]
  refine ⟨131197927093237939885000829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87465284728825293256667219 131197927093237939885000829)
  ·
    refine ⟨49199222659964227456875311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131197927093237939885000829 49199222659964227456875311)
    ·
      refine ⟨73798833989946341185312967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49199222659964227456875311 73798833989946341185312967)
      ·
        refine ⟨110698250984919511777969451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73798833989946341185312967 110698250984919511777969451)
        ·
          refine ⟨166047376477379267666954177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110698250984919511777969451 166047376477379267666954177)
          ·
            refine ⟨124535532358034450750215633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166047376477379267666954177 124535532358034450750215633)
            ·
              refine ⟨93401649268525838062661725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124535532358034450750215633 93401649268525838062661725)
              ·
                refine ⟨35025618475697189273498147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93401649268525838062661725 35025618475697189273498147)
                ·
                  refine ⟨52538427713545783910247221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35025618475697189273498147 52538427713545783910247221)
                  ·
                    refine ⟨4925477598144917241585677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52538427713545783910247221 4925477598144917241585677)
                    ·
                      refine ⟨1847054099304343965594629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4925477598144917241585677 1847054099304343965594629)
                      ·
                        rfl

theorem cell23_3597125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 3, 1, 5, 3].length) (baseStart_3597125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3597125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3597125 prefixEnd_3597125 := by exact prefixLift 3597125
  have htrace : WordTrace (prefixWord ++ tailWord_3597125) baseStart_3597125 baseEnd_3597125 := by
    simpa [prefixWord, tailWord_3597125, baseEnd_3597125] using wordTrace_append hprefix tailTrace_3597125
  have hstable : (prefixWord ++ tailWord_3597125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3597125).length < 2 ^ (prefixWord ++ tailWord_3597125).sum := by decide
  have hdescent : baseEnd_3597125 < baseStart_3597125 := by decide
  rcases family_descends (prefixWord ++ tailWord_3597125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3597145 : List Nat := [1, 2, 1, 2, 2, 4, 2, 1, 1, 7]
def baseStart_3597145 : Nat := 118140960795 + 3597145 * 2 ^ 59
def prefixEnd_3597145 : Nat := 4983230072969 + 3 ^ 40 * 3597145 * 2
def baseEnd_3597145 : Nat := 615688122972477962448179

theorem tailTrace_3597145 : CollatzResearch.WordTrace tailWord_3597145 prefixEnd_3597145 615688122972477962448179 := by
  unfold tailWord_3597145
  simp only [CollatzResearch.WordTrace]
  refine ⟨131198656553165483300728889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87465771035443655533819259 131198656553165483300728889)
  ·
    refine ⟨98398992414874112475546667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131198656553165483300728889 98398992414874112475546667)
    ·
      refine ⟨147598488622311168713320001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98398992414874112475546667 147598488622311168713320001)
      ·
        refine ⟨110698866466733376534990001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147598488622311168713320001 110698866466733376534990001)
        ·
          refine ⟨83024149850050032401242501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110698866466733376534990001 83024149850050032401242501)
          ·
            refine ⟨15567028096884381075232969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83024149850050032401242501 15567028096884381075232969)
            ·
              refine ⟨11675271072663285806424727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15567028096884381075232969 11675271072663285806424727)
              ·
                refine ⟨17512906608994928709637091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11675271072663285806424727 17512906608994928709637091)
                ·
                  refine ⟨26269359913492393064455637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17512906608994928709637091 26269359913492393064455637)
                  ·
                    refine ⟨615688122972477962448179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26269359913492393064455637 615688122972477962448179)
                    ·
                      rfl

theorem cell23_3597145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 1, 1, 7].length) (baseStart_3597145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3597145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3597145 prefixEnd_3597145 := by exact prefixLift 3597145
  have htrace : WordTrace (prefixWord ++ tailWord_3597145) baseStart_3597145 baseEnd_3597145 := by
    simpa [prefixWord, tailWord_3597145, baseEnd_3597145] using wordTrace_append hprefix tailTrace_3597145
  have hstable : (prefixWord ++ tailWord_3597145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3597145).length < 2 ^ (prefixWord ++ tailWord_3597145).sum := by decide
  have hdescent : baseEnd_3597145 < baseStart_3597145 := by decide
  rcases family_descends (prefixWord ++ tailWord_3597145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3597166 : List Nat := [4, 1, 2, 3, 3, 1, 1, 1, 7]
def baseStart_3597166 : Nat := 118140960795 + 3597166 * 2 ^ 59
def prefixEnd_3597166 : Nat := 4983230072969 + 3 ^ 40 * 3597166 * 2
def baseEnd_3597166 : Nat := 205230572445686478353549

theorem tailTrace_3597166 : CollatzResearch.WordTrace tailWord_3597166 prefixEnd_3597166 205230572445686478353549 := by
  unfold tailWord_3597166
  simp only [CollatzResearch.WordTrace]
  refine ⟨16399927810761175485905419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87466281657392935924828901 16399927810761175485905419)
  ·
    refine ⟨24599891716141763228858129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16399927810761175485905419 24599891716141763228858129)
    ·
      refine ⟨18449918787106322421643597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24599891716141763228858129 18449918787106322421643597)
      ·
        refine ⟨6918719545164870908116349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18449918787106322421643597 6918719545164870908116349)
        ·
          refine ⟨2594519829436826590543631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6918719545164870908116349 2594519829436826590543631)
          ·
            refine ⟨3891779744155239885815447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2594519829436826590543631 3891779744155239885815447)
            ·
              refine ⟨5837669616232859828723171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3891779744155239885815447 5837669616232859828723171)
              ·
                refine ⟨8756504424349289743084757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5837669616232859828723171 8756504424349289743084757)
                ·
                  refine ⟨205230572445686478353549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8756504424349289743084757 205230572445686478353549)
                  ·
                    rfl

theorem cell23_3597166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 1, 1, 7].length) (baseStart_3597166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3597166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3597166 prefixEnd_3597166 := by exact prefixLift 3597166
  have htrace : WordTrace (prefixWord ++ tailWord_3597166) baseStart_3597166 baseEnd_3597166 := by
    simpa [prefixWord, tailWord_3597166, baseEnd_3597166] using wordTrace_append hprefix tailTrace_3597166
  have hstable : (prefixWord ++ tailWord_3597166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3597166).length < 2 ^ (prefixWord ++ tailWord_3597166).sum := by decide
  have hdescent : baseEnd_3597166 < baseStart_3597166 := by decide
  rcases family_descends (prefixWord ++ tailWord_3597166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3597195 : List Nat := [1, 1, 1, 1, 4, 2, 2, 1, 2, 4, 4]
def baseStart_3597195 : Nat := 118140960795 + 3597195 * 2 ^ 59
def prefixEnd_3597195 : Nat := 4983230072969 + 3 ^ 40 * 3597195 * 2
def baseEnd_3597195 : Nat := 1847090042950158691719307

theorem tailTrace_3597195 : CollatzResearch.WordTrace tailWord_3597195 prefixEnd_3597195 1847090042950158691719307 := by
  unfold tailWord_3597195
  simp only [CollatzResearch.WordTrace]
  refine ⟨131200480202984341840049039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87466986801989561226699359 131200480202984341840049039)
  ·
    refine ⟨196800720304476512760073559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131200480202984341840049039 196800720304476512760073559)
    ·
      refine ⟨295201080456714769140110339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196800720304476512760073559 295201080456714769140110339)
      ·
        refine ⟨442801620685072153710165509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295201080456714769140110339 442801620685072153710165509)
        ·
          refine ⟨83025303878451028820656033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 442801620685072153710165509 83025303878451028820656033)
          ·
            refine ⟨62268977908838271615492025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83025303878451028820656033 62268977908838271615492025)
            ·
              refine ⟨46701733431628703711619019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62268977908838271615492025 46701733431628703711619019)
              ·
                refine ⟨70052600147443055567428529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46701733431628703711619019 70052600147443055567428529)
                ·
                  refine ⟨52539450110582291675571397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70052600147443055567428529 52539450110582291675571397)
                  ·
                    refine ⟨9851146895734179689169637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52539450110582291675571397 9851146895734179689169637)
                    ·
                      refine ⟨1847090042950158691719307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9851146895734179689169637 1847090042950158691719307)
                      ·
                        rfl

theorem cell23_3597195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 2, 4, 4].length) (baseStart_3597195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3597195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3597195 prefixEnd_3597195 := by exact prefixLift 3597195
  have htrace : WordTrace (prefixWord ++ tailWord_3597195) baseStart_3597195 baseEnd_3597195 := by
    simpa [prefixWord, tailWord_3597195, baseEnd_3597195] using wordTrace_append hprefix tailTrace_3597195
  have hstable : (prefixWord ++ tailWord_3597195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3597195).length < 2 ^ (prefixWord ++ tailWord_3597195).sum := by decide
  have hdescent : baseEnd_3597195 < baseStart_3597195 := by decide
  rcases family_descends (prefixWord ++ tailWord_3597195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3597206 : List Nat := [5, 3, 1, 1, 1, 1, 1, 2, 1, 2, 5]
def baseStart_3597206 : Nat := 118140960795 + 3597206 * 2 ^ 59
def prefixEnd_3597206 : Nat := 4983230072969 + 3 ^ 40 * 3597206 * 2
def baseEnd_3597206 : Nat := 1847095691237358148681757

theorem tailTrace_3597206 : CollatzResearch.WordTrace tailWord_3597206 prefixEnd_3597206 1847095691237358148681757 := by
  unfold tailWord_3597206
  simp only [CollatzResearch.WordTrace]
  refine ⟨8200055087871530669918717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 87467254270629660479132981 8200055087871530669918717)
  ·
    refine ⟨3075020657951824001219519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8200055087871530669918717 3075020657951824001219519)
    ·
      refine ⟨4612530986927736001829279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3075020657951824001219519 4612530986927736001829279)
      ·
        refine ⟨6918796480391604002743919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4612530986927736001829279 6918796480391604002743919)
        ·
          refine ⟨10378194720587406004115879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6918796480391604002743919 10378194720587406004115879)
          ·
            refine ⟨15567292080881109006173819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10378194720587406004115879 15567292080881109006173819)
            ·
              refine ⟨23350938121321663509260729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15567292080881109006173819 23350938121321663509260729)
              ·
                refine ⟨17513203590991247631945547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23350938121321663509260729 17513203590991247631945547)
                ·
                  refine ⟨26269805386486871447918321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17513203590991247631945547 26269805386486871447918321)
                  ·
                    refine ⟨19702354039865153585938741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26269805386486871447918321 19702354039865153585938741)
                    ·
                      refine ⟨1847095691237358148681757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19702354039865153585938741 1847095691237358148681757)
                      ·
                        rfl

theorem cell23_3597206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_3597206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3597206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3597206 prefixEnd_3597206 := by exact prefixLift 3597206
  have htrace : WordTrace (prefixWord ++ tailWord_3597206) baseStart_3597206 baseEnd_3597206 := by
    simpa [prefixWord, tailWord_3597206, baseEnd_3597206] using wordTrace_append hprefix tailTrace_3597206
  have hstable : (prefixWord ++ tailWord_3597206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3597206).length < 2 ^ (prefixWord ++ tailWord_3597206).sum := by decide
  have hdescent : baseEnd_3597206 < baseStart_3597206 := by decide
  rcases family_descends (prefixWord ++ tailWord_3597206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3597209 : List Nat := [1, 2, 1, 2, 1, 3, 1, 7, 1, 4]
def baseStart_3597209 : Nat := 118140960795 + 3597209 * 2 ^ 59
def prefixEnd_3597209 : Nat := 4983230072969 + 3 ^ 40 * 3597209 * 2
def baseEnd_3597209 : Nat := 615699077226440545648081

theorem tailTrace_3597209 : CollatzResearch.WordTrace tailWord_3597209 prefixEnd_3597209 615699077226440545648081 := by
  unfold tailWord_3597209
  simp only [CollatzResearch.WordTrace]
  refine ⟨131200990824933622231058681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87467327216622414820705787 131200990824933622231058681)
  ·
    refine ⟨98400743118700216673294011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131200990824933622231058681 98400743118700216673294011)
    ·
      refine ⟨147601114678050325009941017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98400743118700216673294011 147601114678050325009941017)
      ·
        refine ⟨110700836008537743757455763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147601114678050325009941017 110700836008537743757455763)
        ·
          refine ⟨166051254012806615636183645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110700836008537743757455763 166051254012806615636183645)
          ·
            refine ⟨62269220254802480863568867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 166051254012806615636183645 62269220254802480863568867)
            ·
              refine ⟨93403830382203721295353301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62269220254802480863568867 93403830382203721295353301)
              ·
                refine ⟨2189152274582899717859843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 93403830382203721295353301 2189152274582899717859843)
                ·
                  refine ⟨3283728411874349576789765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2189152274582899717859843 3283728411874349576789765)
                  ·
                    refine ⟨615699077226440545648081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3283728411874349576789765 615699077226440545648081)
                    ·
                      rfl

theorem cell23_3597209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 7, 1, 4].length) (baseStart_3597209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3597209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3597209 prefixEnd_3597209 := by exact prefixLift 3597209
  have htrace : WordTrace (prefixWord ++ tailWord_3597209) baseStart_3597209 baseEnd_3597209 := by
    simpa [prefixWord, tailWord_3597209, baseEnd_3597209] using wordTrace_append hprefix tailTrace_3597209
  have hstable : (prefixWord ++ tailWord_3597209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3597209).length < 2 ^ (prefixWord ++ tailWord_3597209).sum := by decide
  have hdescent : baseEnd_3597209 < baseStart_3597209 := by decide
  rcases family_descends (prefixWord ++ tailWord_3597209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3597225 : List Nat := [1, 2, 1, 1, 1, 1, 6, 1, 1, 2, 6]
def baseStart_3597225 : Nat := 118140960795 + 3597225 * 2 ^ 59
def prefixEnd_3597225 : Nat := 4983230072969 + 3 ^ 40 * 3597225 * 2
def baseEnd_3597225 : Nat := 1847105447369793574344169

theorem tailTrace_3597225 : CollatzResearch.WordTrace tailWord_3597225 prefixEnd_3597225 1847105447369793574344169 := by
  unfold tailWord_3597225
  simp only [CollatzResearch.WordTrace]
  refine ⟨131201574392875656963641129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87467716261917104642427419 131201574392875656963641129)
  ·
    refine ⟨98401180794656742722730847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131201574392875656963641129 98401180794656742722730847)
    ·
      refine ⟨147601771191985114084096271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98401180794656742722730847 147601771191985114084096271)
      ·
        refine ⟨221402656787977671126144407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147601771191985114084096271 221402656787977671126144407)
        ·
          refine ⟨332103985181966506689216611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221402656787977671126144407 332103985181966506689216611)
          ·
            refine ⟨498155977772949760033824917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 332103985181966506689216611 498155977772949760033824917)
            ·
              refine ⟨23351061458107020001585543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 498155977772949760033824917 23351061458107020001585543)
              ·
                refine ⟨35026592187160530002378315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23351061458107020001585543 35026592187160530002378315)
                ·
                  refine ⟨52539888280740795003567473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35026592187160530002378315 52539888280740795003567473)
                  ·
                    refine ⟨39404916210555596252675605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52539888280740795003567473 39404916210555596252675605)
                    ·
                      refine ⟨1847105447369793574344169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39404916210555596252675605 1847105447369793574344169)
                      ·
                        rfl

theorem cell23_3597225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 1, 1, 2, 6].length) (baseStart_3597225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3597225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3597225 prefixEnd_3597225 := by exact prefixLift 3597225
  have htrace : WordTrace (prefixWord ++ tailWord_3597225) baseStart_3597225 baseEnd_3597225 := by
    simpa [prefixWord, tailWord_3597225, baseEnd_3597225] using wordTrace_append hprefix tailTrace_3597225
  have hstable : (prefixWord ++ tailWord_3597225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3597225).length < 2 ^ (prefixWord ++ tailWord_3597225).sum := by decide
  have hdescent : baseEnd_3597225 < baseStart_3597225 := by decide
  rcases family_descends (prefixWord ++ tailWord_3597225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3597259 : List Nat := [1, 1, 1, 1, 3, 6, 1, 1, 1, 5, 2]
def baseStart_3597259 : Nat := 118140960795 + 3597259 * 2 ^ 59
def prefixEnd_3597259 : Nat := 4983230072969 + 3 ^ 40 * 3597259 * 2
def baseEnd_3597259 : Nat := 1847122905712046441319013

theorem tailTrace_3597259 : CollatzResearch.WordTrace tailWord_3597259 prefixEnd_3597259 1847122905712046441319013 := by
  unfold tailWord_3597259
  simp only [CollatzResearch.WordTrace]
  refine ⟨131202814474752480770378831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87468542983168320513585887 131202814474752480770378831)
  ·
    refine ⟨196804221712128721155568247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131202814474752480770378831 196804221712128721155568247)
    ·
      refine ⟨295206332568193081733352371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196804221712128721155568247 295206332568193081733352371)
      ·
        refine ⟨442809498852289622600028557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295206332568193081733352371 442809498852289622600028557)
        ·
          refine ⟨166053562069608608475010709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 442809498852289622600028557 166053562069608608475010709)
          ·
            refine ⟨7783760722012903522266127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 166053562069608608475010709 7783760722012903522266127)
            ·
              refine ⟨11675641083019355283399191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7783760722012903522266127 11675641083019355283399191)
              ·
                refine ⟨17513461624529032925098787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11675641083019355283399191 17513461624529032925098787)
                ·
                  refine ⟨26270192436793549387648181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17513461624529032925098787 26270192436793549387648181)
                  ·
                    refine ⟨2462830540949395255092017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26270192436793549387648181 2462830540949395255092017)
                    ·
                      refine ⟨1847122905712046441319013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2462830540949395255092017 1847122905712046441319013)
                      ·
                        rfl

theorem cell23_3597259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 1, 1, 5, 2].length) (baseStart_3597259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3597259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3597259 prefixEnd_3597259 := by exact prefixLift 3597259
  have htrace : WordTrace (prefixWord ++ tailWord_3597259) baseStart_3597259 baseEnd_3597259 := by
    simpa [prefixWord, tailWord_3597259, baseEnd_3597259] using wordTrace_append hprefix tailTrace_3597259
  have hstable : (prefixWord ++ tailWord_3597259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3597259).length < 2 ^ (prefixWord ++ tailWord_3597259).sum := by decide
  have hdescent : baseEnd_3597259 < baseStart_3597259 := by decide
  rcases family_descends (prefixWord ++ tailWord_3597259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3597326 : List Nat := [4, 1, 1, 2, 2, 2, 2, 3, 1, 2, 3]
def baseStart_3597326 : Nat := 118140960795 + 3597326 * 2 ^ 59
def prefixEnd_3597326 : Nat := 4983230072969 + 3 ^ 40 * 3597326 * 2
def baseEnd_3597326 : Nat := 1847157308915897679181205

theorem tailTrace_3597326 : CollatzResearch.WordTrace tailWord_3597326 prefixEnd_3597326 1847157308915897679181205 := by
  unfold tailWord_3597326
  simp only [CollatzResearch.WordTrace]
  refine ⟨16400657270688718901633479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87470172110339834142045221 16400657270688718901633479)
  ·
    refine ⟨24600985906033078352450219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16400657270688718901633479 24600985906033078352450219)
    ·
      refine ⟨36901478859049617528675329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24600985906033078352450219 36901478859049617528675329)
      ·
        refine ⟨27676109144287213146506497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36901478859049617528675329 27676109144287213146506497)
        ·
          refine ⟨20757081858215409859879873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27676109144287213146506497 20757081858215409859879873)
          ·
            refine ⟨15567811393661557394909905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20757081858215409859879873 15567811393661557394909905)
            ·
              refine ⟨11675858545246168046182429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15567811393661557394909905 11675858545246168046182429)
              ·
                refine ⟨4378446954467313017318411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11675858545246168046182429 4378446954467313017318411)
                ·
                  refine ⟨6567670431700969525977617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4378446954467313017318411 6567670431700969525977617)
                  ·
                    refine ⟨4925752823775727144483213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6567670431700969525977617 4925752823775727144483213)
                    ·
                      refine ⟨1847157308915897679181205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4925752823775727144483213 1847157308915897679181205)
                      ·
                        rfl

theorem cell23_3597326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 3, 1, 2, 3].length) (baseStart_3597326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3597326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3597326 prefixEnd_3597326 := by exact prefixLift 3597326
  have htrace : WordTrace (prefixWord ++ tailWord_3597326) baseStart_3597326 baseEnd_3597326 := by
    simpa [prefixWord, tailWord_3597326, baseEnd_3597326] using wordTrace_append hprefix tailTrace_3597326
  have hstable : (prefixWord ++ tailWord_3597326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3597326).length < 2 ^ (prefixWord ++ tailWord_3597326).sum := by decide
  have hdescent : baseEnd_3597326 < baseStart_3597326 := by decide
  rcases family_descends (prefixWord ++ tailWord_3597326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3597340 : List Nat := [2, 2, 3, 1, 4, 2, 1, 1, 3, 2, 2]
def baseStart_3597340 : Nat := 118140960795 + 3597340 * 2 ^ 59
def prefixEnd_3597340 : Nat := 4983230072969 + 3 ^ 40 * 3597340 * 2
def baseEnd_3597340 : Nat := 1847164497645060624406141

theorem tailTrace_3597340 : CollatzResearch.WordTrace tailWord_3597340 prefixEnd_3597340 1847164497645060624406141 := by
  unfold tailWord_3597340
  simp only [CollatzResearch.WordTrace]
  refine ⟨65602884393729515802038737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87470512524972687736051649 65602884393729515802038737)
  ·
    refine ⟨49202163295297136851529053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65602884393729515802038737 49202163295297136851529053)
    ·
      refine ⟨18450811235736426319323395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49202163295297136851529053 18450811235736426319323395)
      ·
        refine ⟨27676216853604639478985093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18450811235736426319323395 27676216853604639478985093)
        ·
          refine ⟨5189290660050869902309705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27676216853604639478985093 5189290660050869902309705)
          ·
            refine ⟨3891967995038152426732279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5189290660050869902309705 3891967995038152426732279)
            ·
              refine ⟨5837951992557228640098419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3891967995038152426732279 5837951992557228640098419)
              ·
                refine ⟨8756927988835842960147629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5837951992557228640098419 8756927988835842960147629)
                ·
                  refine ⟨3283847995813441110055361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8756927988835842960147629 3283847995813441110055361)
                  ·
                    refine ⟨2462885996860080832541521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3283847995813441110055361 2462885996860080832541521)
                    ·
                      refine ⟨1847164497645060624406141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2462885996860080832541521 1847164497645060624406141)
                      ·
                        rfl

theorem cell23_3597340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 1, 1, 3, 2, 2].length) (baseStart_3597340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3597340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3597340 prefixEnd_3597340 := by exact prefixLift 3597340
  have htrace : WordTrace (prefixWord ++ tailWord_3597340) baseStart_3597340 baseEnd_3597340 := by
    simpa [prefixWord, tailWord_3597340, baseEnd_3597340] using wordTrace_append hprefix tailTrace_3597340
  have hstable : (prefixWord ++ tailWord_3597340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3597340).length < 2 ^ (prefixWord ++ tailWord_3597340).sum := by decide
  have hdescent : baseEnd_3597340 < baseStart_3597340 := by decide
  rcases family_descends (prefixWord ++ tailWord_3597340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3597356 : List Nat := [2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 3]
def baseStart_3597356 : Nat := 118140960795 + 3597356 * 2 ^ 59
def prefixEnd_3597356 : Nat := 4983230072969 + 3 ^ 40 * 3597356 * 2
def baseEnd_3597356 : Nat := 1847172713335532561806067

theorem tailTrace_3597356 : CollatzResearch.WordTrace tailWord_3597356 prefixEnd_3597356 1847172713335532561806067 := by
  unfold tailWord_3597356
  simp only [CollatzResearch.WordTrace]
  refine ⟨65603176177700533168329961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87470901570267377557773281 65603176177700533168329961)
  ·
    refine ⟨49202382133275399876247471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65603176177700533168329961 49202382133275399876247471)
    ·
      refine ⟨73803573199913099814371207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49202382133275399876247471 73803573199913099814371207)
      ·
        refine ⟨110705359799869649721556811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73803573199913099814371207 110705359799869649721556811)
        ·
          refine ⟨166058039699804474582335217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110705359799869649721556811 166058039699804474582335217)
          ·
            refine ⟨124543529774853355936751413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166058039699804474582335217 124543529774853355936751413)
            ·
              refine ⟨11675955916392502119070445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 124543529774853355936751413 11675955916392502119070445)
              ·
                refine ⟨4378483468647188294651417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11675955916392502119070445 4378483468647188294651417)
                ·
                  refine ⟨3283862601485391220988563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4378483468647188294651417 3283862601485391220988563)
                  ·
                    refine ⟨4925793902228086831482845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3283862601485391220988563 4925793902228086831482845)
                    ·
                      refine ⟨1847172713335532561806067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4925793902228086831482845 1847172713335532561806067)
                      ·
                        rfl

theorem cell23_3597356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 3].length) (baseStart_3597356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3597356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3597356 prefixEnd_3597356 := by exact prefixLift 3597356
  have htrace : WordTrace (prefixWord ++ tailWord_3597356) baseStart_3597356 baseEnd_3597356 := by
    simpa [prefixWord, tailWord_3597356, baseEnd_3597356] using wordTrace_append hprefix tailTrace_3597356
  have hstable : (prefixWord ++ tailWord_3597356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3597356).length < 2 ^ (prefixWord ++ tailWord_3597356).sum := by decide
  have hdescent : baseEnd_3597356 < baseStart_3597356 := by decide
  rcases family_descends (prefixWord ++ tailWord_3597356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3597392 : List Nat := [2, 1, 1, 1, 1, 3, 1, 2, 3, 4, 4]
def baseStart_3597392 : Nat := 118140960795 + 3597392 * 2 ^ 59
def prefixEnd_3597392 : Nat := 4983230072969 + 3 ^ 40 * 3597392 * 2
def baseEnd_3597392 : Nat := 1847191198639094420955901

theorem tailTrace_3597392 : CollatzResearch.WordTrace tailWord_3597392 prefixEnd_3597392 1847191198639094420955901 := by
  unfold tailWord_3597392
  simp only [CollatzResearch.WordTrace]
  refine ⟨65603832691635322242485215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87471776922180429656646953 65603832691635322242485215)
  ·
    refine ⟨98405749037452983363727823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65603832691635322242485215 98405749037452983363727823)
    ·
      refine ⟨147608623556179475045591735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98405749037452983363727823 147608623556179475045591735)
      ·
        refine ⟨221412935334269212568387603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147608623556179475045591735 221412935334269212568387603)
        ·
          refine ⟨332119403001403818852581405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221412935334269212568387603 332119403001403818852581405)
          ·
            refine ⟨124544776125526432069718027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 332119403001403818852581405 124544776125526432069718027)
            ·
              refine ⟨186817164188289648104577041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124544776125526432069718027 186817164188289648104577041)
              ·
                refine ⟨140112873141217236078432781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 186817164188289648104577041 140112873141217236078432781)
                ·
                  refine ⟨52542327427956463529412293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 140112873141217236078432781 52542327427956463529412293)
                  ·
                    refine ⟨9851686392741836911764805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52542327427956463529412293 9851686392741836911764805)
                    ·
                      refine ⟨1847191198639094420955901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9851686392741836911764805 1847191198639094420955901)
                      ·
                        rfl

theorem cell23_3597392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 3, 4, 4].length) (baseStart_3597392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3597392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3597392 prefixEnd_3597392 := by exact prefixLift 3597392
  have htrace : WordTrace (prefixWord ++ tailWord_3597392) baseStart_3597392 baseEnd_3597392 := by
    simpa [prefixWord, tailWord_3597392, baseEnd_3597392] using wordTrace_append hprefix tailTrace_3597392
  have hstable : (prefixWord ++ tailWord_3597392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3597392).length < 2 ^ (prefixWord ++ tailWord_3597392).sum := by decide
  have hdescent : baseEnd_3597392 < baseStart_3597392 := by decide
  rcases family_descends (prefixWord ++ tailWord_3597392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3597413 : List Nat := [1, 3, 1, 3, 2, 1, 1, 5, 2, 2, 2]
def baseStart_3597413 : Nat := 118140960795 + 3597413 * 2 ^ 59
def prefixEnd_3597413 : Nat := 4983230072969 + 3 ^ 40 * 3597413 * 2
def baseEnd_3597413 : Nat := 1847201981732838838793305

theorem tailTrace_3597413 : CollatzResearch.WordTrace tailWord_3597413 prefixEnd_3597413 1847201981732838838793305 := by
  unfold tailWord_3597413
  simp only [CollatzResearch.WordTrace]
  refine ⟨131208431316194565071484893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87472287544129710047656595 131208431316194565071484893)
  ·
    refine ⟨49203161743572961901806835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131208431316194565071484893 49203161743572961901806835)
    ·
      refine ⟨73804742615359442852710253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49203161743572961901806835 73804742615359442852710253)
      ·
        refine ⟨27676778480759791069766345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73804742615359442852710253 27676778480759791069766345)
        ·
          refine ⟨20757583860569843302324759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27676778480759791069766345 20757583860569843302324759)
          ·
            refine ⟨31136375790854764953487139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20757583860569843302324759 31136375790854764953487139)
            ·
              refine ⟨46704563686282147430230709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31136375790854764953487139 46704563686282147430230709)
              ·
                refine ⟨4378552845588951321584129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46704563686282147430230709 4378552845588951321584129)
                ·
                  refine ⟨3283914634191713491188097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4378552845588951321584129 3283914634191713491188097)
                  ·
                    refine ⟨2462935975643785118391073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3283914634191713491188097 2462935975643785118391073)
                    ·
                      refine ⟨1847201981732838838793305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2462935975643785118391073 1847201981732838838793305)
                      ·
                        rfl

theorem cell23_3597413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 5, 2, 2, 2].length) (baseStart_3597413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3597413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3597413 prefixEnd_3597413 := by exact prefixLift 3597413
  have htrace : WordTrace (prefixWord ++ tailWord_3597413) baseStart_3597413 baseEnd_3597413 := by
    simpa [prefixWord, tailWord_3597413, baseEnd_3597413] using wordTrace_append hprefix tailTrace_3597413
  have hstable : (prefixWord ++ tailWord_3597413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3597413).length < 2 ^ (prefixWord ++ tailWord_3597413).sum := by decide
  have hdescent : baseEnd_3597413 < baseStart_3597413 := by decide
  rcases family_descends (prefixWord ++ tailWord_3597413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3597436 : List Nat := [2, 2, 2, 1, 1, 3, 4, 3, 5]
def baseStart_3597436 : Nat := 118140960795 + 3597436 * 2 ^ 59
def prefixEnd_3597436 : Nat := 4983230072969 + 3 ^ 40 * 3597436 * 2
def baseEnd_3597436 : Nat := 205245976865321360978411

theorem tailTrace_3597436 : CollatzResearch.WordTrace tailWord_3597436 prefixEnd_3597436 205245976865321360978411 := by
  unfold tailWord_3597436
  simp only [CollatzResearch.WordTrace]
  refine ⟨65604635097555619999786081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87472846796740826666381441 65604635097555619999786081)
  ·
    refine ⟨49203476323166714999839561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65604635097555619999786081 49203476323166714999839561)
    ·
      refine ⟨36902607242375036249879671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49203476323166714999839561 36902607242375036249879671)
      ·
        refine ⟨55353910863562554374819507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36902607242375036249879671 55353910863562554374819507)
        ·
          refine ⟨83030866295343831562229261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55353910863562554374819507 83030866295343831562229261)
          ·
            refine ⟨31136574860753936835835973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83030866295343831562229261 31136574860753936835835973)
            ·
              refine ⟨5838107786391363156719245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31136574860753936835835973 5838107786391363156719245)
              ·
                refine ⟨2189290419896761183769717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5838107786391363156719245 2189290419896761183769717)
                ·
                  refine ⟨205245976865321360978411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2189290419896761183769717 205245976865321360978411)
                  ·
                    rfl

theorem cell23_3597436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 4, 3, 5].length) (baseStart_3597436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3597436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3597436 prefixEnd_3597436 := by exact prefixLift 3597436
  have htrace : WordTrace (prefixWord ++ tailWord_3597436) baseStart_3597436 baseEnd_3597436 := by
    simpa [prefixWord, tailWord_3597436, baseEnd_3597436] using wordTrace_append hprefix tailTrace_3597436
  have hstable : (prefixWord ++ tailWord_3597436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3597436).length < 2 ^ (prefixWord ++ tailWord_3597436).sum := by decide
  have hdescent : baseEnd_3597436 < baseStart_3597436 := by decide
  rcases family_descends (prefixWord ++ tailWord_3597436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3597469 : List Nat := [1, 4, 2, 1, 1, 2, 1, 1, 3, 3, 4]
def baseStart_3597469 : Nat := 118140960795 + 3597469 * 2 ^ 59
def prefixEnd_3597469 : Nat := 4983230072969 + 3 ^ 40 * 3597469 * 2
def baseEnd_3597469 : Nat := 1847230736649490619693047

theorem tailTrace_3597469 : CollatzResearch.WordTrace tailWord_3597469 prefixEnd_3597469 1847230736649490619693047 := by
  unfold tailWord_3597469
  simp only [CollatzResearch.WordTrace]
  refine ⟨131210473803991686635523461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87473649202661124423682307 131210473803991686635523461)
  ·
    refine ⟨24601963838248441244160649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 131210473803991686635523461 24601963838248441244160649)
    ·
      refine ⟨18451472878686330933120487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24601963838248441244160649 18451472878686330933120487)
      ·
        refine ⟨27677209318029496399680731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18451472878686330933120487 27677209318029496399680731)
        ·
          refine ⟨41515813977044244599521097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27677209318029496399680731 41515813977044244599521097)
          ·
            refine ⟨31136860482783183449640823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41515813977044244599521097 31136860482783183449640823)
            ·
              refine ⟨46705290724174775174461235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31136860482783183449640823 46705290724174775174461235)
              ·
                refine ⟨70057936086262162761691853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46705290724174775174461235 70057936086262162761691853)
                ·
                  refine ⟨26271726032348311035634445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70057936086262162761691853 26271726032348311035634445)
                  ·
                    refine ⟨9851897262130616638362917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26271726032348311035634445 9851897262130616638362917)
                    ·
                      refine ⟨1847230736649490619693047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9851897262130616638362917 1847230736649490619693047)
                      ·
                        rfl

theorem cell23_3597469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 3, 3, 4].length) (baseStart_3597469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3597469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3597469 prefixEnd_3597469 := by exact prefixLift 3597469
  have htrace : WordTrace (prefixWord ++ tailWord_3597469) baseStart_3597469 baseEnd_3597469 := by
    simpa [prefixWord, tailWord_3597469, baseEnd_3597469] using wordTrace_append hprefix tailTrace_3597469
  have hstable : (prefixWord ++ tailWord_3597469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3597469).length < 2 ^ (prefixWord ++ tailWord_3597469).sum := by decide
  have hdescent : baseEnd_3597469 < baseStart_3597469 := by decide
  rcases family_descends (prefixWord ++ tailWord_3597469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3597509 : List Nat := [1, 3, 1, 1, 1, 1, 3, 6, 6]
def baseStart_3597509 : Nat := 118140960795 + 3597509 * 2 ^ 59
def prefixEnd_3597509 : Nat := 4983230072969 + 3 ^ 40 * 3597509 * 2
def baseEnd_3597509 : Nat := 205250141763963384799207

theorem tailTrace_3597509 : CollatzResearch.WordTrace tailWord_3597509 prefixEnd_3597509 205250141763963384799207 := by
  unfold tailWord_3597509
  simp only [CollatzResearch.WordTrace]
  refine ⟨131211932723846773466979581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87474621815897848977986387 131211932723846773466979581)
  ·
    refine ⟨49204474771442540050117343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131211932723846773466979581 49204474771442540050117343)
    ·
      refine ⟨73806712157163810075176015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49204474771442540050117343 73806712157163810075176015)
      ·
        refine ⟨110710068235745715112764023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73806712157163810075176015 110710068235745715112764023)
        ·
          refine ⟨166065102353618572669146035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110710068235745715112764023 166065102353618572669146035)
          ·
            refine ⟨249097653530427859003719053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166065102353618572669146035 249097653530427859003719053)
            ·
              refine ⟨93411620073910447126394645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 249097653530427859003719053 93411620073910447126394645)
              ·
                refine ⟨4378669690964552209049749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 93411620073910447126394645 4378669690964552209049749)
                ·
                  refine ⟨205250141763963384799207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4378669690964552209049749 205250141763963384799207)
                  ·
                    rfl

theorem cell23_3597509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 6, 6].length) (baseStart_3597509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3597509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3597509 prefixEnd_3597509 := by exact prefixLift 3597509
  have htrace : WordTrace (prefixWord ++ tailWord_3597509) baseStart_3597509 baseEnd_3597509 := by
    simpa [prefixWord, tailWord_3597509, baseEnd_3597509] using wordTrace_append hprefix tailTrace_3597509
  have hstable : (prefixWord ++ tailWord_3597509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3597509).length < 2 ^ (prefixWord ++ tailWord_3597509).sum := by decide
  have hdescent : baseEnd_3597509 < baseStart_3597509 := by decide
  rcases family_descends (prefixWord ++ tailWord_3597509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3597519 : List Nat := [1, 1, 2, 1, 1, 3, 2, 2, 2, 5, 3]
def baseStart_3597519 : Nat := 118140960795 + 3597519 * 2 ^ 59
def prefixEnd_3597519 : Nat := 4983230072969 + 3 ^ 40 * 3597519 * 2
def baseEnd_3597519 : Nat := 1847256410682215424067817

theorem tailTrace_3597519 : CollatzResearch.WordTrace tailWord_3597519 prefixEnd_3597519 1847256410682215424067817 := by
  unfold tailWord_3597519
  simp only [CollatzResearch.WordTrace]
  refine ⟨131212297453810545174843611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87474864969207030116562407 131212297453810545174843611)
  ·
    refine ⟨196818446180715817762265417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131212297453810545174843611 196818446180715817762265417)
    ·
      refine ⟨147613834635536863321699063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196818446180715817762265417 147613834635536863321699063)
      ·
        refine ⟨221420751953305294982548595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147613834635536863321699063 221420751953305294982548595)
        ·
          refine ⟨332131127929957942473822893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221420751953305294982548595 332131127929957942473822893)
          ·
            refine ⟨124549172973734228427683585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 332131127929957942473822893 124549172973734228427683585)
            ·
              refine ⟨93411879730300671320762689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124549172973734228427683585 93411879730300671320762689)
              ·
                refine ⟨70058909797725503490572017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93411879730300671320762689 70058909797725503490572017)
                ·
                  refine ⟨52544182348294127617929013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70058909797725503490572017 52544182348294127617929013)
                  ·
                    refine ⟨4926017095152574464180845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52544182348294127617929013 4926017095152574464180845)
                    ·
                      refine ⟨1847256410682215424067817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4926017095152574464180845 1847256410682215424067817)
                      ·
                        rfl

theorem cell23_3597519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 2, 5, 3].length) (baseStart_3597519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3597519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3597519 prefixEnd_3597519 := by exact prefixLift 3597519
  have htrace : WordTrace (prefixWord ++ tailWord_3597519) baseStart_3597519 baseEnd_3597519 := by
    simpa [prefixWord, tailWord_3597519, baseEnd_3597519] using wordTrace_append hprefix tailTrace_3597519
  have hstable : (prefixWord ++ tailWord_3597519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3597519).length < 2 ^ (prefixWord ++ tailWord_3597519).sum := by decide
  have hdescent : baseEnd_3597519 < baseStart_3597519 := by decide
  rcases family_descends (prefixWord ++ tailWord_3597519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3597564 : List Nat := [2, 2, 2, 1, 6, 1, 2, 2, 1, 4]
def baseStart_3597564 : Nat := 118140960795 + 3597564 * 2 ^ 59
def prefixEnd_3597564 : Nat := 4983230072969 + 3 ^ 40 * 3597564 * 2
def baseEnd_3597564 : Nat := 615759839103889249335037

theorem tailTrace_3597564 : CollatzResearch.WordTrace tailWord_3597564 prefixEnd_3597564 615759839103889249335037 := by
  unfold tailWord_3597564
  simp only [CollatzResearch.WordTrace]
  refine ⟨65606969369323758930115873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87475959159098345240154497 65606969369323758930115873)
  ·
    refine ⟨49205227026992819197586905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65606969369323758930115873 49205227026992819197586905)
    ·
      refine ⟨36903920270244614398190179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49205227026992819197586905 36903920270244614398190179)
      ·
        refine ⟨55355880405366921597285269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36903920270244614398190179 55355880405366921597285269)
        ·
          refine ⟨2594806894001574449872747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 55355880405366921597285269 2594806894001574449872747)
          ·
            refine ⟨3892210341002361674809121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2594806894001574449872747 3892210341002361674809121)
            ·
              refine ⟨2919157755751771256106841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3892210341002361674809121 2919157755751771256106841)
              ·
                refine ⟨2189368316813828442080131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2919157755751771256106841 2189368316813828442080131)
                ·
                  refine ⟨3284052475220742663120197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2189368316813828442080131 3284052475220742663120197)
                  ·
                    refine ⟨615759839103889249335037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3284052475220742663120197 615759839103889249335037)
                    ·
                      rfl

theorem cell23_3597564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 2, 2, 1, 4].length) (baseStart_3597564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3597564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3597564 prefixEnd_3597564 := by exact prefixLift 3597564
  have htrace : WordTrace (prefixWord ++ tailWord_3597564) baseStart_3597564 baseEnd_3597564 := by
    simpa [prefixWord, tailWord_3597564, baseEnd_3597564] using wordTrace_append hprefix tailTrace_3597564
  have hstable : (prefixWord ++ tailWord_3597564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3597564).length < 2 ^ (prefixWord ++ tailWord_3597564).sum := by decide
  have hdescent : baseEnd_3597564 < baseStart_3597564 := by decide
  rcases family_descends (prefixWord ++ tailWord_3597564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3597597 : List Nat := [1, 4, 2, 3, 1, 3, 1, 1, 2, 3, 2]
def baseStart_3597597 : Nat := 118140960795 + 3597597 * 2 ^ 59
def prefixEnd_3597597 : Nat := 4983230072969 + 3 ^ 40 * 3597597 * 2
def baseEnd_3597597 : Nat := 1847296462173266118892459

theorem tailTrace_3597597 : CollatzResearch.WordTrace tailWord_3597597 prefixEnd_3597597 1847296462173266118892459 := by
  unfold tailWord_3597597
  simp only [CollatzResearch.WordTrace]
  refine ⟨131215142347527964496183045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87476761565018642997455363 131215142347527964496183045)
  ·
    refine ⟨24602839190161493343034321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 131215142347527964496183045 24602839190161493343034321)
    ·
      refine ⟨18452129392621120007275741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24602839190161493343034321 18452129392621120007275741)
      ·
        refine ⟨6919548522232920002728403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18452129392621120007275741 6919548522232920002728403)
        ·
          refine ⟨10379322783349380004092605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6919548522232920002728403 10379322783349380004092605)
          ·
            refine ⟨3892246043756017501534727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10379322783349380004092605 3892246043756017501534727)
            ·
              refine ⟨5838369065634026252302091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3892246043756017501534727 5838369065634026252302091)
              ·
                refine ⟨8757553598451039378453137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5838369065634026252302091 8757553598451039378453137)
                ·
                  refine ⟨6568165198838279533839853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8757553598451039378453137 6568165198838279533839853)
                  ·
                    refine ⟨2463061949564354825189945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6568165198838279533839853 2463061949564354825189945)
                    ·
                      refine ⟨1847296462173266118892459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2463061949564354825189945 1847296462173266118892459)
                      ·
                        rfl

theorem cell23_3597597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 1, 1, 2, 3, 2].length) (baseStart_3597597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3597597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3597597 prefixEnd_3597597 := by exact prefixLift 3597597
  have htrace : WordTrace (prefixWord ++ tailWord_3597597) baseStart_3597597 baseEnd_3597597 := by
    simpa [prefixWord, tailWord_3597597, baseEnd_3597597] using wordTrace_append hprefix tailTrace_3597597
  have hstable : (prefixWord ++ tailWord_3597597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3597597).length < 2 ^ (prefixWord ++ tailWord_3597597).sum := by decide
  have hdescent : baseEnd_3597597 < baseStart_3597597 := by decide
  rcases family_descends (prefixWord ++ tailWord_3597597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3597610 : List Nat := [3, 1, 4, 2, 1, 2, 1, 3, 1, 1, 4]
def baseStart_3597610 : Nat := 118140960795 + 3597610 * 2 ^ 59
def prefixEnd_3597610 : Nat := 4983230072969 + 3 ^ 40 * 3597610 * 2
def baseEnd_3597610 : Nat := 1847303137421774568029899

theorem tailTrace_3597610 : CollatzResearch.WordTrace tailWord_3597610 prefixEnd_3597610 1847303137421774568029899 := by
  unfold tailWord_3597610
  simp only [CollatzResearch.WordTrace]
  refine ⟨32803904124120216929101571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87477077664320578477604189 32803904124120216929101571)
  ·
    refine ⟨49205856186180325393652357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32803904124120216929101571 49205856186180325393652357)
    ·
      refine ⟨9226098034908811011309817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49205856186180325393652357 9226098034908811011309817)
      ·
        refine ⟨6919573526181608258482363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9226098034908811011309817 6919573526181608258482363)
        ·
          refine ⟨10379360289272412387723545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6919573526181608258482363 10379360289272412387723545)
          ·
            refine ⟨7784520216954309290792659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10379360289272412387723545 7784520216954309290792659)
            ·
              refine ⟨11676780325431463936188989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7784520216954309290792659 11676780325431463936188989)
              ·
                refine ⟨4378792622036798976070871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11676780325431463936188989 4378792622036798976070871)
                ·
                  refine ⟨6568188933055198464106307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4378792622036798976070871 6568188933055198464106307)
                  ·
                    refine ⟨9852283399582797696159461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6568188933055198464106307 9852283399582797696159461)
                    ·
                      refine ⟨1847303137421774568029899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9852283399582797696159461 1847303137421774568029899)
                      ·
                        rfl

theorem cell23_3597610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_3597610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3597610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3597610 prefixEnd_3597610 := by exact prefixLift 3597610
  have htrace : WordTrace (prefixWord ++ tailWord_3597610) baseStart_3597610 baseEnd_3597610 := by
    simpa [prefixWord, tailWord_3597610, baseEnd_3597610] using wordTrace_append hprefix tailTrace_3597610
  have hstable : (prefixWord ++ tailWord_3597610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3597610).length < 2 ^ (prefixWord ++ tailWord_3597610).sum := by decide
  have hdescent : baseEnd_3597610 < baseStart_3597610 := by decide
  rcases family_descends (prefixWord ++ tailWord_3597610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3597678 : List Nat := [4, 1, 2, 4, 1, 1, 3, 2, 1, 2, 2]
def baseStart_3597678 : Nat := 118140960795 + 3597678 * 2 ^ 59
def prefixEnd_3597678 : Nat := 4983230072969 + 3 ^ 40 * 3597678 * 2
def baseEnd_3597678 : Nat := 1847338054106280301979587

theorem tailTrace_3597678 : CollatzResearch.WordTrace tailWord_3597678 prefixEnd_3597678 1847338054106280301979587 := by
  unfold tailWord_3597678
  simp only [CollatzResearch.WordTrace]
  refine ⟨16402262082529314416235211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87478731106823010219921125 16402262082529314416235211)
  ·
    refine ⟨24603393123793971624352817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16402262082529314416235211 24603393123793971624352817)
    ·
      refine ⟨18452544842845478718264613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24603393123793971624352817 18452544842845478718264613)
      ·
        refine ⟨3459852158033527259674615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18452544842845478718264613 3459852158033527259674615)
        ·
          refine ⟨5189778237050290889511923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3459852158033527259674615 5189778237050290889511923)
          ·
            refine ⟨7784667355575436334267885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5189778237050290889511923 7784667355575436334267885)
            ·
              refine ⟨2919250258340788625350457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7784667355575436334267885 2919250258340788625350457)
              ·
                refine ⟨2189437693755591469012843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2919250258340788625350457 2189437693755591469012843)
                ·
                  refine ⟨3284156540633387203519265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2189437693755591469012843 3284156540633387203519265)
                  ·
                    refine ⟨2463117405475040402639449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3284156540633387203519265 2463117405475040402639449)
                    ·
                      refine ⟨1847338054106280301979587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2463117405475040402639449 1847338054106280301979587)
                      ·
                        rfl

theorem cell23_3597678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_3597678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3597678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3597678 prefixEnd_3597678 := by exact prefixLift 3597678
  have htrace : WordTrace (prefixWord ++ tailWord_3597678) baseStart_3597678 baseEnd_3597678 := by
    simpa [prefixWord, tailWord_3597678, baseEnd_3597678] using wordTrace_append hprefix tailTrace_3597678
  have hstable : (prefixWord ++ tailWord_3597678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3597678).length < 2 ^ (prefixWord ++ tailWord_3597678).sum := by decide
  have hdescent : baseEnd_3597678 < baseStart_3597678 := by decide
  rcases family_descends (prefixWord ++ tailWord_3597678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3597696 : List Nat := [2, 1, 1, 2, 1, 2, 1, 5, 2, 2, 4]
def baseStart_3597696 : Nat := 118140960795 + 3597696 * 2 ^ 59
def prefixEnd_3597696 : Nat := 4983230072969 + 3 ^ 40 * 3597696 * 2
def baseEnd_3597696 : Nat := 1847347296758061231554503

theorem tailTrace_3597696 : CollatzResearch.WordTrace tailWord_3597696 prefixEnd_3597696 1847347296758061231554503 := by
  unfold tailWord_3597696
  simp only [CollatzResearch.WordTrace]
  refine ⟨65609376587084652202018471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87479168782779536269357961 65609376587084652202018471)
  ·
    refine ⟨98414064880626978303027707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65609376587084652202018471 98414064880626978303027707)
    ·
      refine ⟨147621097320940467454541561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98414064880626978303027707 147621097320940467454541561)
      ·
        refine ⟨110715822990705350590906171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147621097320940467454541561 110715822990705350590906171)
        ·
          refine ⟨166073734486058025886359257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110715822990705350590906171 166073734486058025886359257)
          ·
            refine ⟨124555300864543519414769443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166073734486058025886359257 124555300864543519414769443)
            ·
              refine ⟨186832951296815279122154165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124555300864543519414769443 186832951296815279122154165)
              ·
                refine ⟨17515589184076432417701953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 186832951296815279122154165 17515589184076432417701953)
                ·
                  refine ⟨13136691888057324313276465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17515589184076432417701953 13136691888057324313276465)
                  ·
                    refine ⟨9852518916042993234957349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13136691888057324313276465 9852518916042993234957349)
                    ·
                      refine ⟨1847347296758061231554503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9852518916042993234957349 1847347296758061231554503)
                      ·
                        rfl

theorem cell23_3597696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 5, 2, 2, 4].length) (baseStart_3597696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3597696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3597696 prefixEnd_3597696 := by exact prefixLift 3597696
  have htrace : WordTrace (prefixWord ++ tailWord_3597696) baseStart_3597696 baseEnd_3597696 := by
    simpa [prefixWord, tailWord_3597696, baseEnd_3597696] using wordTrace_append hprefix tailTrace_3597696
  have hstable : (prefixWord ++ tailWord_3597696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3597696).length < 2 ^ (prefixWord ++ tailWord_3597696).sum := by decide
  have hdescent : baseEnd_3597696 < baseStart_3597696 := by decide
  rcases family_descends (prefixWord ++ tailWord_3597696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3597740 : List Nat := [2, 2, 1, 1, 1, 1, 8, 2, 5]
def baseStart_3597740 : Nat := 118140960795 + 3597740 * 2 ^ 59
def prefixEnd_3597740 : Nat := 4983230072969 + 3 ^ 40 * 3597740 * 2
def baseEnd_3597740 : Nat := 205263321100762117711589

theorem tailTrace_3597740 : CollatzResearch.WordTrace tailWord_3597740 prefixEnd_3597740 205263321100762117711589 := by
  unfold tailWord_3597740
  simp only [CollatzResearch.WordTrace]
  refine ⟨65610178993004949959319337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87480238657339933279092449 65610178993004949959319337)
  ·
    refine ⟨49207634244753712469489503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65610178993004949959319337 49207634244753712469489503)
    ·
      refine ⟨73811451367130568704234255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49207634244753712469489503 73811451367130568704234255)
      ·
        refine ⟨110717177050695853056351383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73811451367130568704234255 110717177050695853056351383)
        ·
          refine ⟨166075765576043779584527075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110717177050695853056351383 166075765576043779584527075)
          ·
            refine ⟨249113648364065669376790613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166075765576043779584527075 249113648364065669376790613)
            ·
              refine ⟨2919300566766394563009265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 249113648364065669376790613 2919300566766394563009265)
              ·
                refine ⟨2189475425074795922256949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2919300566766394563009265 2189475425074795922256949)
                ·
                  refine ⟨205263321100762117711589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2189475425074795922256949 205263321100762117711589)
                  ·
                    rfl

theorem cell23_3597740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 8, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 8, 2, 5].length) (baseStart_3597740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3597740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3597740 prefixEnd_3597740 := by exact prefixLift 3597740
  have htrace : WordTrace (prefixWord ++ tailWord_3597740) baseStart_3597740 baseEnd_3597740 := by
    simpa [prefixWord, tailWord_3597740, baseEnd_3597740] using wordTrace_append hprefix tailTrace_3597740
  have hstable : (prefixWord ++ tailWord_3597740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3597740).length < 2 ^ (prefixWord ++ tailWord_3597740).sum := by decide
  have hdescent : baseEnd_3597740 < baseStart_3597740 := by decide
  rcases family_descends (prefixWord ++ tailWord_3597740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3597746 : List Nat := [3, 2, 1, 1, 1, 1, 2, 3, 1, 1, 7]
def baseStart_3597746 : Nat := 118140960795 + 3597746 * 2 ^ 59
def prefixEnd_3597746 : Nat := 4983230072969 + 3 ^ 40 * 3597746 * 2
def baseEnd_3597746 : Nat := 1847372970790786035929273

theorem tailTrace_3597746 : CollatzResearch.WordTrace tailWord_3597746 prefixEnd_3597746 1847372970790786035929273 := by
  unfold tailWord_3597746
  simp only [CollatzResearch.WordTrace]
  refine ⟨32805144205997040735839273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87480384549325441962238061 32805144205997040735839273)
  ·
    refine ⟨24603858154497780551879455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32805144205997040735839273 24603858154497780551879455)
    ·
      refine ⟨36905787231746670827819183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24603858154497780551879455 36905787231746670827819183)
      ·
        refine ⟨55358680847620006241728775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36905787231746670827819183 55358680847620006241728775)
        ·
          refine ⟨83038021271430009362593163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55358680847620006241728775 83038021271430009362593163)
          ·
            refine ⟨124557031907145014043889745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83038021271430009362593163 124557031907145014043889745)
            ·
              refine ⟨93417773930358760532917309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124557031907145014043889745 93417773930358760532917309)
              ·
                refine ⟨35031665223884535199843991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93417773930358760532917309 35031665223884535199843991)
                ·
                  refine ⟨52547497835826802799765987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35031665223884535199843991 52547497835826802799765987)
                  ·
                    refine ⟨78821246753740204199648981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52547497835826802799765987 78821246753740204199648981)
                    ·
                      refine ⟨1847372970790786035929273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 78821246753740204199648981 1847372970790786035929273)
                      ·
                        rfl

theorem cell23_3597746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 3, 1, 1, 7].length) (baseStart_3597746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3597746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3597746 prefixEnd_3597746 := by exact prefixLift 3597746
  have htrace : WordTrace (prefixWord ++ tailWord_3597746) baseStart_3597746 baseEnd_3597746 := by
    simpa [prefixWord, tailWord_3597746, baseEnd_3597746] using wordTrace_append hprefix tailTrace_3597746
  have hstable : (prefixWord ++ tailWord_3597746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3597746).length < 2 ^ (prefixWord ++ tailWord_3597746).sum := by decide
  have hdescent : baseEnd_3597746 < baseStart_3597746 := by decide
  rcases family_descends (prefixWord ++ tailWord_3597746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3597770 : List Nat := [3, 1, 2, 1, 2, 5, 1, 1, 2, 5]
def baseStart_3597770 : Nat := 118140960795 + 3597770 * 2 ^ 59
def prefixEnd_3597770 : Nat := 4983230072969 + 3 ^ 40 * 3597770 * 2
def baseEnd_3597770 : Nat := 615795098108831314009721

theorem tailTrace_3597770 : CollatzResearch.WordTrace tailWord_3597770 prefixEnd_3597770 615795098108831314009721 := by
  unfold tailWord_3597770
  simp only [CollatzResearch.WordTrace]
  refine ⟨32805363043975303760557691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87480968117267476694820509 32805363043975303760557691)
  ·
    refine ⟨49208044565962955640836537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32805363043975303760557691 49208044565962955640836537)
    ·
      refine ⟨36906033424472216730627403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49208044565962955640836537 36906033424472216730627403)
      ·
        refine ⟨55359050136708325095941105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36906033424472216730627403 55359050136708325095941105)
        ·
          refine ⟨41519287602531243821955829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55359050136708325095941105 41519287602531243821955829)
          ·
            refine ⟨3892433212737304108308359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41519287602531243821955829 3892433212737304108308359)
            ·
              refine ⟨5838649819105956162462539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3892433212737304108308359 5838649819105956162462539)
              ·
                refine ⟨8757974728658934243693809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5838649819105956162462539 8757974728658934243693809)
                ·
                  refine ⟨6568481046494200682770357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8757974728658934243693809 6568481046494200682770357)
                  ·
                    refine ⟨615795098108831314009721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6568481046494200682770357 615795098108831314009721)
                    ·
                      rfl

theorem cell23_3597770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 1, 1, 2, 5].length) (baseStart_3597770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3597770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3597770 prefixEnd_3597770 := by exact prefixLift 3597770
  have htrace : WordTrace (prefixWord ++ tailWord_3597770) baseStart_3597770 baseEnd_3597770 := by
    simpa [prefixWord, tailWord_3597770, baseEnd_3597770] using wordTrace_append hprefix tailTrace_3597770
  have hstable : (prefixWord ++ tailWord_3597770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3597770).length < 2 ^ (prefixWord ++ tailWord_3597770).sum := by decide
  have hdescent : baseEnd_3597770 < baseStart_3597770 := by decide
  rcases family_descends (prefixWord ++ tailWord_3597770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3597800 : List Nat := [2, 1, 4, 1, 1, 2, 4, 1, 3, 4]
def baseStart_3597800 : Nat := 118140960795 + 3597800 * 2 ^ 59
def prefixEnd_3597800 : Nat := 4983230072969 + 3 ^ 40 * 3597800 * 2
def baseEnd_3597800 : Nat := 615800232915376274884675

theorem tailTrace_3597800 : CollatzResearch.WordTrace tailWord_3597800 prefixEnd_3597800 615800232915376274884675 := by
  unfold tailWord_3597800
  simp only [CollatzResearch.WordTrace]
  refine ⟨65611273182896265082911427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87481697577195020110548569 65611273182896265082911427)
  ·
    refine ⟨98416909774344397624367141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65611273182896265082911427 98416909774344397624367141)
    ·
      refine ⟨18453170582689574554568839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98416909774344397624367141 18453170582689574554568839)
      ·
        refine ⟨27679755874034361831853259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18453170582689574554568839 27679755874034361831853259)
        ·
          refine ⟨41519633811051542747779889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27679755874034361831853259 41519633811051542747779889)
          ·
            refine ⟨31139725358288657060834917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41519633811051542747779889 31139725358288657060834917)
            ·
              refine ⟨5838698504679123198906547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31139725358288657060834917 5838698504679123198906547)
              ·
                refine ⟨8758047757018684798359821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5838698504679123198906547 8758047757018684798359821)
                ·
                  refine ⟨3284267908882006799384933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8758047757018684798359821 3284267908882006799384933)
                  ·
                    refine ⟨615800232915376274884675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3284267908882006799384933 615800232915376274884675)
                    ·
                      rfl

theorem cell23_3597800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 4, 1, 3, 4].length) (baseStart_3597800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3597800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3597800 prefixEnd_3597800 := by exact prefixLift 3597800
  have htrace : WordTrace (prefixWord ++ tailWord_3597800) baseStart_3597800 baseEnd_3597800 := by
    simpa [prefixWord, tailWord_3597800, baseEnd_3597800] using wordTrace_append hprefix tailTrace_3597800
  have hstable : (prefixWord ++ tailWord_3597800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3597800).length < 2 ^ (prefixWord ++ tailWord_3597800).sum := by decide
  have hdescent : baseEnd_3597800 < baseStart_3597800 := by decide
  rcases family_descends (prefixWord ++ tailWord_3597800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3597810 : List Nat := [3, 2, 1, 4, 1, 1, 1, 2, 1, 4, 3]
def baseStart_3597810 : Nat := 118140960795 + 3597810 * 2 ^ 59
def prefixEnd_3597810 : Nat := 4983230072969 + 3 ^ 40 * 3597810 * 2
def baseEnd_3597810 : Nat := 1847405833552673785528979

theorem tailTrace_3597810 : CollatzResearch.WordTrace tailWord_3597810 prefixEnd_3597810 1847405833552673785528979 := by
  unfold tailWord_3597810
  simp only [CollatzResearch.WordTrace]
  refine ⟨32805727773939075468421721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87481940730504201249124589 32805727773939075468421721)
  ·
    refine ⟨24604295830454306601316291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32805727773939075468421721 24604295830454306601316291)
    ·
      refine ⟨36906443745681459901974437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24604295830454306601316291 36906443745681459901974437)
      ·
        refine ⟨6919958202315273731620207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36906443745681459901974437 6919958202315273731620207)
        ·
          refine ⟨10379937303472910597430311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6919958202315273731620207 10379937303472910597430311)
          ·
            refine ⟨15569905955209365896145467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10379937303472910597430311 15569905955209365896145467)
            ·
              refine ⟨23354858932814048844218201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15569905955209365896145467 23354858932814048844218201)
              ·
                refine ⟨17516144199610536633163651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23354858932814048844218201 17516144199610536633163651)
                ·
                  refine ⟨26274216299415804949745477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17516144199610536633163651 26274216299415804949745477)
                  ·
                    refine ⟨4926415556140463428077277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26274216299415804949745477 4926415556140463428077277)
                    ·
                      refine ⟨1847405833552673785528979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4926415556140463428077277 1847405833552673785528979)
                      ·
                        rfl

theorem cell23_3597810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_3597810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3597810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3597810 prefixEnd_3597810 := by exact prefixLift 3597810
  have htrace : WordTrace (prefixWord ++ tailWord_3597810) baseStart_3597810 baseEnd_3597810 := by
    simpa [prefixWord, tailWord_3597810, baseEnd_3597810] using wordTrace_append hprefix tailTrace_3597810
  have hstable : (prefixWord ++ tailWord_3597810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3597810).length < 2 ^ (prefixWord ++ tailWord_3597810).sum := by decide
  have hdescent : baseEnd_3597810 < baseStart_3597810 := by decide
  rcases family_descends (prefixWord ++ tailWord_3597810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3597834 : List Nat := [3, 1, 2, 2, 2, 4, 1, 3, 1, 4]
def baseStart_3597834 : Nat := 118140960795 + 3597834 * 2 ^ 59
def prefixEnd_3597834 : Nat := 4983230072969 + 3 ^ 40 * 3597834 * 2
def baseEnd_3597834 : Nat := 615806052362793897209623

theorem tailTrace_3597834 : CollatzResearch.WordTrace tailWord_3597834 prefixEnd_3597834 615806052362793897209623 := by
  unfold tailWord_3597834
  simp only [CollatzResearch.WordTrace]
  refine ⟨32805946611917338493140139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87482524298446235981707037 32805946611917338493140139)
  ·
    refine ⟨49208919917876007739710209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32805946611917338493140139 49208919917876007739710209)
    ·
      refine ⟨36906689938407005804782657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49208919917876007739710209 36906689938407005804782657)
      ·
        refine ⟨27680017453805254353586993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36906689938407005804782657 27680017453805254353586993)
        ·
          refine ⟨20760013090353940765190245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27680017453805254353586993 20760013090353940765190245)
          ·
            refine ⟨3892502454441363893473171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20760013090353940765190245 3892502454441363893473171)
            ·
              refine ⟨5838753681662045840209757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3892502454441363893473171 5838753681662045840209757)
              ·
                refine ⟨2189532630623267190078659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5838753681662045840209757 2189532630623267190078659)
                ·
                  refine ⟨3284298945934900785117989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2189532630623267190078659 3284298945934900785117989)
                  ·
                    refine ⟨615806052362793897209623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3284298945934900785117989 615806052362793897209623)
                    ·
                      rfl

theorem cell23_3597834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 1, 3, 1, 4].length) (baseStart_3597834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3597834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3597834 prefixEnd_3597834 := by exact prefixLift 3597834
  have htrace : WordTrace (prefixWord ++ tailWord_3597834) baseStart_3597834 baseEnd_3597834 := by
    simpa [prefixWord, tailWord_3597834, baseEnd_3597834] using wordTrace_append hprefix tailTrace_3597834
  have hstable : (prefixWord ++ tailWord_3597834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3597834).length < 2 ^ (prefixWord ++ tailWord_3597834).sum := by decide
  have hdescent : baseEnd_3597834 < baseStart_3597834 := by decide
  rcases family_descends (prefixWord ++ tailWord_3597834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3597844 : List Nat := [2, 4, 3, 1, 2, 1, 1, 2, 2, 2, 3]
def baseStart_3597844 : Nat := 118140960795 + 3597844 * 2 ^ 59
def prefixEnd_3597844 : Nat := 4983230072969 + 3 ^ 40 * 3597844 * 2
def baseEnd_3597844 : Nat := 1847423291894926652503823

theorem tailTrace_3597844 : CollatzResearch.WordTrace tailWord_3597844 prefixEnd_3597844 1847423291894926652503823 := by
  unfold tailWord_3597844
  simp only [CollatzResearch.WordTrace]
  refine ⟨65612075588816562840212293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87482767451755417120283057 65612075588816562840212293)
  ·
    refine ⟨12302264172903105532539805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65612075588816562840212293 12302264172903105532539805)
    ·
      refine ⟨4613349064838664574702427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12302264172903105532539805 4613349064838664574702427)
      ·
        refine ⟨6920023597257996862053641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4613349064838664574702427 6920023597257996862053641)
        ·
          refine ⟨5190017697943497646540231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6920023597257996862053641 5190017697943497646540231)
          ·
            refine ⟨7785026546915246469810347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5190017697943497646540231 7785026546915246469810347)
            ·
              refine ⟨11677539820372869704715521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7785026546915246469810347 11677539820372869704715521)
              ·
                refine ⟨8758154865279652278536641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11677539820372869704715521 8758154865279652278536641)
                ·
                  refine ⟨6568616148959739208902481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8758154865279652278536641 6568616148959739208902481)
                  ·
                    refine ⟨4926462111719804406676861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6568616148959739208902481 4926462111719804406676861)
                    ·
                      refine ⟨1847423291894926652503823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4926462111719804406676861 1847423291894926652503823)
                      ·
                        rfl

theorem cell23_3597844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_3597844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3597844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3597844 prefixEnd_3597844 := by exact prefixLift 3597844
  have htrace : WordTrace (prefixWord ++ tailWord_3597844) baseStart_3597844 baseEnd_3597844 := by
    simpa [prefixWord, tailWord_3597844, baseEnd_3597844] using wordTrace_append hprefix tailTrace_3597844
  have hstable : (prefixWord ++ tailWord_3597844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3597844).length < 2 ^ (prefixWord ++ tailWord_3597844).sum := by decide
  have hdescent : baseEnd_3597844 < baseStart_3597844 := by decide
  rcases family_descends (prefixWord ++ tailWord_3597844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3597857 : List Nat := [1, 2, 3, 2, 2, 2, 3, 1, 3, 1, 3]
def baseStart_3597857 : Nat := 118140960795 + 3597857 * 2 ^ 59
def prefixEnd_3597857 : Nat := 4983230072969 + 3 ^ 40 * 3597857 * 2
def baseEnd_3597857 : Nat := 1847429967143435101641263

theorem tailTrace_3597857 : CollatzResearch.WordTrace tailWord_3597857 prefixEnd_3597857 1847429967143435101641263 := by
  unfold tailWord_3597857
  simp only [CollatzResearch.WordTrace]
  refine ⟨131224625326586028900647825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87483083551057352600431883 131224625326586028900647825)
  ·
    refine ⟨98418468994939521675485869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131224625326586028900647825 98418468994939521675485869)
    ·
      refine ⟨36906925873102320628307201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98418468994939521675485869 36906925873102320628307201)
      ·
        refine ⟨27680194404826740471230401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36906925873102320628307201 27680194404826740471230401)
        ·
          refine ⟨20760145803620055353422801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27680194404826740471230401 20760145803620055353422801)
          ·
            refine ⟨15570109352715041515067101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20760145803620055353422801 15570109352715041515067101)
            ·
              refine ⟨5838791007268140568150163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15570109352715041515067101 5838791007268140568150163)
              ·
                refine ⟨8758186510902210852225245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5838791007268140568150163 8758186510902210852225245)
                ·
                  refine ⟨3284319941588329069584467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8758186510902210852225245 3284319941588329069584467)
                  ·
                    refine ⟨4926479912382493604376701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3284319941588329069584467 4926479912382493604376701)
                    ·
                      refine ⟨1847429967143435101641263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4926479912382493604376701 1847429967143435101641263)
                      ·
                        rfl

theorem cell23_3597857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 3, 1, 3, 1, 3].length) (baseStart_3597857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3597857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3597857 prefixEnd_3597857 := by exact prefixLift 3597857
  have htrace : WordTrace (prefixWord ++ tailWord_3597857) baseStart_3597857 baseEnd_3597857 := by
    simpa [prefixWord, tailWord_3597857, baseEnd_3597857] using wordTrace_append hprefix tailTrace_3597857
  have hstable : (prefixWord ++ tailWord_3597857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3597857).length < 2 ^ (prefixWord ++ tailWord_3597857).sum := by decide
  have hdescent : baseEnd_3597857 < baseStart_3597857 := by decide
  rcases family_descends (prefixWord ++ tailWord_3597857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3597864 : List Nat := [2, 1, 5, 2, 2, 2, 2, 1, 6]
def baseStart_3597864 : Nat := 118140960795 + 3597864 * 2 ^ 59
def prefixEnd_3597864 : Nat := 4983230072969 + 3 ^ 40 * 3597864 * 2
def baseEnd_3597864 : Nat := 205270395723112952694859

theorem tailTrace_3597864 : CollatzResearch.WordTrace tailWord_3597864 prefixEnd_3597864 205270395723112952694859 := by
  unfold tailWord_3597864
  simp only [CollatzResearch.WordTrace]
  refine ⟨65612440318780334548076323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87483253758373779397435097 65612440318780334548076323)
  ·
    refine ⟨98418660478170501822114485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65612440318780334548076323 98418660478170501822114485)
    ·
      refine ⟨9226749419828484545823233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 98418660478170501822114485 9226749419828484545823233)
      ·
        refine ⟨6920062064871363409367425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9226749419828484545823233 6920062064871363409367425)
        ·
          refine ⟨5190046548653522557025569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6920062064871363409367425 5190046548653522557025569)
          ·
            refine ⟨3892534911490141917769177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5190046548653522557025569 3892534911490141917769177)
            ·
              refine ⟨2919401183617606438326883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3892534911490141917769177 2919401183617606438326883)
              ·
                refine ⟨4379101775426409657490325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2919401183617606438326883 4379101775426409657490325)
                ·
                  refine ⟨205270395723112952694859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4379101775426409657490325 205270395723112952694859)
                  ·
                    rfl

theorem cell23_3597864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 2, 1, 6].length) (baseStart_3597864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3597864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3597864 prefixEnd_3597864 := by exact prefixLift 3597864
  have htrace : WordTrace (prefixWord ++ tailWord_3597864) baseStart_3597864 baseEnd_3597864 := by
    simpa [prefixWord, tailWord_3597864, baseEnd_3597864] using wordTrace_append hprefix tailTrace_3597864
  have hstable : (prefixWord ++ tailWord_3597864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3597864).length < 2 ^ (prefixWord ++ tailWord_3597864).sum := by decide
  have hdescent : baseEnd_3597864 < baseStart_3597864 := by decide
  rcases family_descends (prefixWord ++ tailWord_3597864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3597873 : List Nat := [1, 2, 2, 3, 1, 1, 1, 5, 1, 6]
def baseStart_3597873 : Nat := 118140960795 + 3597873 * 2 ^ 59
def prefixEnd_3597873 : Nat := 4983230072969 + 3 ^ 40 * 3597873 * 2
def baseEnd_3597873 : Nat := 615812727611302346347063

theorem tailTrace_3597873 : CollatzResearch.WordTrace tailWord_3597873 prefixEnd_3597873 615812727611302346347063 := by
  unfold tailWord_3597873
  simp only [CollatzResearch.WordTrace]
  refine ⟨131225208894528063633230273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87483472596352042422153515 131225208894528063633230273)
  ·
    refine ⟨98418906670896047724922705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131225208894528063633230273 98418906670896047724922705)
    ·
      refine ⟨73814180003172035793692029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98418906670896047724922705 73814180003172035793692029)
      ·
        refine ⟨27680317501189513422634511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73814180003172035793692029 27680317501189513422634511)
        ·
          refine ⟨41520476251784270133951767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27680317501189513422634511 41520476251784270133951767)
          ·
            refine ⟨62280714377676405200927651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41520476251784270133951767 62280714377676405200927651)
            ·
              refine ⟨93421071566514607801391477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62280714377676405200927651 93421071566514607801391477)
              ·
                refine ⟨8758225459360744481380451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 93421071566514607801391477 8758225459360744481380451)
                ·
                  refine ⟨13137338189041116722070677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8758225459360744481380451 13137338189041116722070677)
                  ·
                    refine ⟨615812727611302346347063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13137338189041116722070677 615812727611302346347063)
                    ·
                      rfl

theorem cell23_3597873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 5, 1, 6].length) (baseStart_3597873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3597873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3597873 prefixEnd_3597873 := by exact prefixLift 3597873
  have htrace : WordTrace (prefixWord ++ tailWord_3597873) baseStart_3597873 baseEnd_3597873 := by
    simpa [prefixWord, tailWord_3597873, baseEnd_3597873] using wordTrace_append hprefix tailTrace_3597873
  have hstable : (prefixWord ++ tailWord_3597873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3597873).length < 2 ^ (prefixWord ++ tailWord_3597873).sum := by decide
  have hdescent : baseEnd_3597873 < baseStart_3597873 := by decide
  rcases family_descends (prefixWord ++ tailWord_3597873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3597877 : List Nat := [1, 3, 3, 1, 1, 5, 1, 2, 1, 5]
def baseStart_3597877 : Nat := 118140960795 + 3597877 * 2 ^ 59
def prefixEnd_3597877 : Nat := 4983230072969 + 3 ^ 40 * 3597877 * 2
def baseEnd_3597877 : Nat := 615813412252175007797057

theorem tailTrace_3597877 : CollatzResearch.WordTrace tailWord_3597877 prefixEnd_3597877 615813412252175007797057 := by
  unfold tailWord_3597877
  simp only [CollatzResearch.WordTrace]
  refine ⟨131225354786513572316375885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87483569857675714877583923 131225354786513572316375885)
  ·
    refine ⟨49209508044942589618640957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131225354786513572316375885 49209508044942589618640957)
    ·
      refine ⟨18453565516853471106990359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49209508044942589618640957 18453565516853471106990359)
      ·
        refine ⟨27680348275280206660485539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18453565516853471106990359 27680348275280206660485539)
        ·
          refine ⟨41520522412920309990728309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27680348275280206660485539 41520522412920309990728309)
          ·
            refine ⟨3892548976211279061630779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41520522412920309990728309 3892548976211279061630779)
            ·
              refine ⟨5838823464316918592446169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3892548976211279061630779 5838823464316918592446169)
              ·
                refine ⟨4379117598237688944334627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5838823464316918592446169 4379117598237688944334627)
                ·
                  refine ⟨6568676397356533416501941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4379117598237688944334627 6568676397356533416501941)
                  ·
                    refine ⟨615813412252175007797057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6568676397356533416501941 615813412252175007797057)
                    ·
                      rfl

theorem cell23_3597877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 1, 2, 1, 5].length) (baseStart_3597877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3597877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3597877 prefixEnd_3597877 := by exact prefixLift 3597877
  have htrace : WordTrace (prefixWord ++ tailWord_3597877) baseStart_3597877 baseEnd_3597877 := by
    simpa [prefixWord, tailWord_3597877, baseEnd_3597877] using wordTrace_append hprefix tailTrace_3597877
  have hstable : (prefixWord ++ tailWord_3597877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3597877).length < 2 ^ (prefixWord ++ tailWord_3597877).sum := by decide
  have hdescent : baseEnd_3597877 < baseStart_3597877 := by decide
  rcases family_descends (prefixWord ++ tailWord_3597877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3597880 : List Nat := [2, 1, 2, 1, 4, 3, 1, 1, 3, 1, 4]
def baseStart_3597880 : Nat := 118140960795 + 3597880 * 2 ^ 59
def prefixEnd_3597880 : Nat := 4983230072969 + 3 ^ 40 * 3597880 * 2
def baseEnd_3597880 : Nat := 1847441777198488511653657

theorem tailTrace_3597880 : CollatzResearch.WordTrace tailWord_3597880 prefixEnd_3597880 1847441777198488511653657 := by
  unfold tailWord_3597880
  simp only [CollatzResearch.WordTrace]
  refine ⟨65612732102751351914367547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87483642803668469219156729 65612732102751351914367547)
  ·
    refine ⟨98419098154127027871551321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65612732102751351914367547 98419098154127027871551321)
    ·
      refine ⟨73814323615595270903663491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98419098154127027871551321 73814323615595270903663491)
      ·
        refine ⟨110721485423392906355495237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73814323615595270903663491 110721485423392906355495237)
        ·
          refine ⟨20760278516886169941655357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110721485423392906355495237 20760278516886169941655357)
          ·
            refine ⟨7785104443832313728120759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20760278516886169941655357 7785104443832313728120759)
            ·
              refine ⟨11677656665748470592181139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7785104443832313728120759 11677656665748470592181139)
              ·
                refine ⟨17516484998622705888271709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11677656665748470592181139 17516484998622705888271709)
                ·
                  refine ⟨6568681874483514708101891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17516484998622705888271709 6568681874483514708101891)
                  ·
                    refine ⟨9853022811725272062152837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6568681874483514708101891 9853022811725272062152837)
                    ·
                      refine ⟨1847441777198488511653657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9853022811725272062152837 1847441777198488511653657)
                      ·
                        rfl

theorem cell23_3597880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 1, 3, 1, 4].length) (baseStart_3597880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3597880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3597880 prefixEnd_3597880 := by exact prefixLift 3597880
  have htrace : WordTrace (prefixWord ++ tailWord_3597880) baseStart_3597880 baseEnd_3597880 := by
    simpa [prefixWord, tailWord_3597880, baseEnd_3597880] using wordTrace_append hprefix tailTrace_3597880
  have hstable : (prefixWord ++ tailWord_3597880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3597880).length < 2 ^ (prefixWord ++ tailWord_3597880).sum := by decide
  have hdescent : baseEnd_3597880 < baseStart_3597880 := by decide
  rcases family_descends (prefixWord ++ tailWord_3597880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3597884 : List Nat := [2, 2, 2, 2, 4, 1, 2, 1, 2, 3, 2]
def baseStart_3597884 : Nat := 118140960795 + 3597884 * 2 ^ 59
def prefixEnd_3597884 : Nat := 4983230072969 + 3 ^ 40 * 3597884 * 2
def baseEnd_3597884 : Nat := 1847443831121106496003639

theorem tailTrace_3597884 : CollatzResearch.WordTrace tailWord_3597884 prefixEnd_3597884 1847443831121106496003639 := by
  unfold tailWord_3597884
  simp only [CollatzResearch.WordTrace]
  refine ⟨65612805048744106255940353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87483740064992141674587137 65612805048744106255940353)
  ·
    refine ⟨49209603786558079691955265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65612805048744106255940353 49209603786558079691955265)
    ·
      refine ⟨36907202839918559768966449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49209603786558079691955265 36907202839918559768966449)
      ·
        refine ⟨27680402129938919826724837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36907202839918559768966449 27680402129938919826724837)
        ·
          refine ⟨5190075399363547467510907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27680402129938919826724837 5190075399363547467510907)
          ·
            refine ⟨7785113099045321201266361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5190075399363547467510907 7785113099045321201266361)
            ·
              refine ⟨5838834824283990900949771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7785113099045321201266361 5838834824283990900949771)
              ·
                refine ⟨8758252236425986351424657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5838834824283990900949771 8758252236425986351424657)
                ·
                  refine ⟨6568689177319489763568493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8758252236425986351424657 6568689177319489763568493)
                  ·
                    refine ⟨2463258441494808661338185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6568689177319489763568493 2463258441494808661338185)
                    ·
                      refine ⟨1847443831121106496003639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2463258441494808661338185 1847443831121106496003639)
                      ·
                        rfl

theorem cell23_3597884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 2, 1, 2, 3, 2].length) (baseStart_3597884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3597884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3597884 prefixEnd_3597884 := by exact prefixLift 3597884
  have htrace : WordTrace (prefixWord ++ tailWord_3597884) baseStart_3597884 baseEnd_3597884 := by
    simpa [prefixWord, tailWord_3597884, baseEnd_3597884] using wordTrace_append hprefix tailTrace_3597884
  have hstable : (prefixWord ++ tailWord_3597884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3597884).length < 2 ^ (prefixWord ++ tailWord_3597884).sum := by decide
  have hdescent : baseEnd_3597884 < baseStart_3597884 := by decide
  rcases family_descends (prefixWord ++ tailWord_3597884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3597900 : List Nat := [2, 2, 1, 3, 1, 3, 3, 1, 1, 1, 5]
def baseStart_3597900 : Nat := 118140960795 + 3597900 * 2 ^ 59
def prefixEnd_3597900 : Nat := 4983230072969 + 3 ^ 40 * 3597900 * 2
def baseEnd_3597900 : Nat := 1847452046811578433403565

theorem tailTrace_3597900 : CollatzResearch.WordTrace tailWord_3597900 prefixEnd_3597900 1847452046811578433403565 := by
  unfold tailWord_3597900
  simp only [CollatzResearch.WordTrace]
  refine ⟨65613096832715123622231577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87484129110286831496308769 65613096832715123622231577)
  ·
    refine ⟨49209822624536342716673683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65613096832715123622231577 49209822624536342716673683)
    ·
      refine ⟨73814733936804514075010525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49209822624536342716673683 73814733936804514075010525)
      ·
        refine ⟨27680525226301692778128947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73814733936804514075010525 27680525226301692778128947)
        ·
          refine ⟨41520787839452539167193421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27680525226301692778128947 41520787839452539167193421)
          ·
            refine ⟨15570295439794702187697533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41520787839452539167193421 15570295439794702187697533)
            ·
              refine ⟨5838860789923013320386575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15570295439794702187697533 5838860789923013320386575)
              ·
                refine ⟨8758291184884519980579863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5838860789923013320386575 8758291184884519980579863)
                ·
                  refine ⟨13137436777326779970869795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8758291184884519980579863 13137436777326779970869795)
                  ·
                    refine ⟨19706155165990169956304693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13137436777326779970869795 19706155165990169956304693)
                    ·
                      refine ⟨1847452046811578433403565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19706155165990169956304693 1847452046811578433403565)
                      ·
                        rfl

theorem cell23_3597900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 3, 1, 1, 1, 5].length) (baseStart_3597900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3597900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3597900 prefixEnd_3597900 := by exact prefixLift 3597900
  have htrace : WordTrace (prefixWord ++ tailWord_3597900) baseStart_3597900 baseEnd_3597900 := by
    simpa [prefixWord, tailWord_3597900, baseEnd_3597900] using wordTrace_append hprefix tailTrace_3597900
  have hstable : (prefixWord ++ tailWord_3597900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3597900).length < 2 ^ (prefixWord ++ tailWord_3597900).sum := by decide
  have hdescent : baseEnd_3597900 < baseStart_3597900 := by decide
  rcases family_descends (prefixWord ++ tailWord_3597900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3597943 : List Nat := [1, 1, 3, 1, 1, 3, 1, 3, 2, 2, 5]
def baseStart_3597943 : Nat := 118140960795 + 3597943 * 2 ^ 59
def prefixEnd_3597943 : Nat := 4983230072969 + 3 ^ 40 * 3597943 * 2
def baseEnd_3597943 : Nat := 1847474126479721765165867

theorem tailTrace_3597943 : CollatzResearch.WordTrace tailWord_3597943 prefixEnd_3597943 1847474126479721765165867 := by
  unfold tailWord_3597943
  simp only [CollatzResearch.WordTrace]
  refine ⟨131227762004274465588278483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87485174669516310392185655 131227762004274465588278483)
  ·
    refine ⟨196841643006411698382417725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131227762004274465588278483 196841643006411698382417725)
    ·
      refine ⟨73815616127404386893406647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196841643006411698382417725 73815616127404386893406647)
      ·
        refine ⟨110723424191106580340109971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73815616127404386893406647 110723424191106580340109971)
        ·
          refine ⟨166085136286659870510164957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110723424191106580340109971 166085136286659870510164957)
          ·
            refine ⟨62281926107497451441311859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 166085136286659870510164957 62281926107497451441311859)
            ·
              refine ⟨93422889161246177161967789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62281926107497451441311859 93422889161246177161967789)
              ·
                refine ⟨35033583435467316435737921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93422889161246177161967789 35033583435467316435737921)
                ·
                  refine ⟨26275187576600487326803441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35033583435467316435737921 26275187576600487326803441)
                  ·
                    refine ⟨19706390682450365495102581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26275187576600487326803441 19706390682450365495102581)
                    ·
                      refine ⟨1847474126479721765165867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19706390682450365495102581 1847474126479721765165867)
                      ·
                        rfl

theorem cell23_3597943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 3, 2, 2, 5].length) (baseStart_3597943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3597943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3597943 prefixEnd_3597943 := by exact prefixLift 3597943
  have htrace : WordTrace (prefixWord ++ tailWord_3597943) baseStart_3597943 baseEnd_3597943 := by
    simpa [prefixWord, tailWord_3597943, baseEnd_3597943] using wordTrace_append hprefix tailTrace_3597943
  have hstable : (prefixWord ++ tailWord_3597943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3597943).length < 2 ^ (prefixWord ++ tailWord_3597943).sum := by decide
  have hdescent : baseEnd_3597943 < baseStart_3597943 := by decide
  rcases family_descends (prefixWord ++ tailWord_3597943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3597963 : List Nat := [1, 1, 1, 1, 4, 1, 3, 1, 4, 6]
def baseStart_3597963 : Nat := 118140960795 + 3597963 * 2 ^ 59
def prefixEnd_3597963 : Nat := 4983230072969 + 3 ^ 40 * 3597963 * 2
def baseEnd_3597963 : Nat := 615828132030937228971925

theorem tailTrace_3597963 : CollatzResearch.WordTrace tailWord_3597963 prefixEnd_3597963 615828132030937228971925 := by
  unfold tailWord_3597963
  simp only [CollatzResearch.WordTrace]
  refine ⟨131228491464202009004006543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87485660976134672669337695 131228491464202009004006543)
  ·
    refine ⟨196842737196303013506009815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131228491464202009004006543 196842737196303013506009815)
    ·
      refine ⟨295264105794454520259014723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196842737196303013506009815 295264105794454520259014723)
      ·
        refine ⟨442896158691681780388522085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295264105794454520259014723 442896158691681780388522085)
        ·
          refine ⟨83043029754690333822847891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 442896158691681780388522085 83043029754690333822847891)
          ·
            refine ⟨124564544632035500734271837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83043029754690333822847891 124564544632035500734271837)
            ·
              refine ⟨46711704237013312775351939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124564544632035500734271837 46711704237013312775351939)
              ·
                refine ⟨70067556355519969163027909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46711704237013312775351939 70067556355519969163027909)
                ·
                  refine ⟨13137666816659994218067733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70067556355519969163027909 13137666816659994218067733)
                  ·
                    refine ⟨615828132030937228971925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13137666816659994218067733 615828132030937228971925)
                    ·
                      rfl

theorem cell23_3597963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 4, 6].length) (baseStart_3597963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3597963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3597963 prefixEnd_3597963 := by exact prefixLift 3597963
  have htrace : WordTrace (prefixWord ++ tailWord_3597963) baseStart_3597963 baseEnd_3597963 := by
    simpa [prefixWord, tailWord_3597963, baseEnd_3597963] using wordTrace_append hprefix tailTrace_3597963
  have hstable : (prefixWord ++ tailWord_3597963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3597963).length < 2 ^ (prefixWord ++ tailWord_3597963).sum := by decide
  have hdescent : baseEnd_3597963 < baseStart_3597963 := by decide
  rcases family_descends (prefixWord ++ tailWord_3597963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3598020 : List Nat := [2, 3, 3, 1, 1, 1, 1, 1, 1, 2, 7]
def baseStart_3598020 : Nat := 118140960795 + 3598020 * 2 ^ 59
def prefixEnd_3598020 : Nat := 4983230072969 + 3 ^ 40 * 3598020 * 2
def baseEnd_3598020 : Nat := 1847513664490117963903013

theorem tailTrace_3598020 : CollatzResearch.WordTrace tailWord_3598020 prefixEnd_3598020 1847513664490117963903013 := by
  unfold tailWord_3598020
  simp only [CollatzResearch.WordTrace]
  refine ⟨65615285212497753869415757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87487046949997005159221009 65615285212497753869415757)
  ·
    refine ⟨24605731954686657701030909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65615285212497753869415757 24605731954686657701030909)
    ·
      refine ⟨9227149483007496637886591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24605731954686657701030909 9227149483007496637886591)
      ·
        refine ⟨13840724224511244956829887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9227149483007496637886591 13840724224511244956829887)
        ·
          refine ⟨20761086336766867435244831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13840724224511244956829887 20761086336766867435244831)
          ·
            refine ⟨31141629505150301152867247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20761086336766867435244831 31141629505150301152867247)
            ·
              refine ⟨46712444257725451729300871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31141629505150301152867247 46712444257725451729300871)
              ·
                refine ⟨70068666386588177593951307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46712444257725451729300871 70068666386588177593951307)
                ·
                  refine ⟨105102999579882266390926961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70068666386588177593951307 105102999579882266390926961)
                  ·
                    refine ⟨78827249684911699793195221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 105102999579882266390926961 78827249684911699793195221)
                    ·
                      refine ⟨1847513664490117963903013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 78827249684911699793195221 1847513664490117963903013)
                      ·
                        rfl

theorem cell23_3598020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_3598020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3598020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3598020 prefixEnd_3598020 := by exact prefixLift 3598020
  have htrace : WordTrace (prefixWord ++ tailWord_3598020) baseStart_3598020 baseEnd_3598020 := by
    simpa [prefixWord, tailWord_3598020, baseEnd_3598020] using wordTrace_append hprefix tailTrace_3598020
  have hstable : (prefixWord ++ tailWord_3598020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3598020).length < 2 ^ (prefixWord ++ tailWord_3598020).sum := by decide
  have hdescent : baseEnd_3598020 < baseStart_3598020 := by decide
  rcases family_descends (prefixWord ++ tailWord_3598020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3598040 : List Nat := [2, 1, 2, 2, 3, 1, 1, 2, 4, 5]
def baseStart_3598040 : Nat := 118140960795 + 3598040 * 2 ^ 59
def prefixEnd_3598040 : Nat := 4983230072969 + 3 ^ 40 * 3598040 * 2
def baseEnd_3598040 : Nat := 615841311367735961884307

theorem tailTrace_3598040 : CollatzResearch.WordTrace tailWord_3598040 prefixEnd_3598040 615841311367735961884307 := by
  unfold tailWord_3598040
  simp only [CollatzResearch.WordTrace]
  refine ⟨65615649942461525577279787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87487533256615367436373049 65615649942461525577279787)
  ·
    refine ⟨98423474913692288365919681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65615649942461525577279787 98423474913692288365919681)
    ·
      refine ⟨73817606185269216274439761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98423474913692288365919681 73817606185269216274439761)
      ·
        refine ⟨55363204638951912205829821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73817606185269216274439761 55363204638951912205829821)
        ·
          refine ⟨20761201739606967077186183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55363204638951912205829821 20761201739606967077186183)
          ·
            refine ⟨31141802609410450615779275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20761201739606967077186183 31141802609410450615779275)
            ·
              refine ⟨46712703914115675923668913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31141802609410450615779275 46712703914115675923668913)
              ·
                refine ⟨35034527935586756942751685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46712703914115675923668913 35034527935586756942751685)
                ·
                  refine ⟨6568973987922516926765941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35034527935586756942751685 6568973987922516926765941)
                  ·
                    refine ⟨615841311367735961884307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6568973987922516926765941 615841311367735961884307)
                    ·
                      rfl

theorem cell23_3598040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 2, 4, 5].length) (baseStart_3598040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3598040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3598040 prefixEnd_3598040 := by exact prefixLift 3598040
  have htrace : WordTrace (prefixWord ++ tailWord_3598040) baseStart_3598040 baseEnd_3598040 := by
    simpa [prefixWord, tailWord_3598040, baseEnd_3598040] using wordTrace_append hprefix tailTrace_3598040
  have hstable : (prefixWord ++ tailWord_3598040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3598040).length < 2 ^ (prefixWord ++ tailWord_3598040).sum := by decide
  have hdescent : baseEnd_3598040 < baseStart_3598040 := by decide
  rcases family_descends (prefixWord ++ tailWord_3598040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3598060 : List Nat := [2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 4]
def baseStart_3598060 : Nat := 118140960795 + 3598060 * 2 ^ 59
def prefixEnd_3598060 : Nat := 4983230072969 + 3 ^ 40 * 3598060 * 2
def baseEnd_3598060 : Nat := 1847534203716297807402829

theorem tailTrace_3598060 : CollatzResearch.WordTrace tailWord_3598060 prefixEnd_3598060 1847534203716297807402829 := by
  unfold tailWord_3598060
  simp only [CollatzResearch.WordTrace]
  refine ⟨65616014672425297285143817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87488019563233729713525089 65616014672425297285143817)
  ·
    refine ⟨49212011004318972963857863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65616014672425297285143817 49212011004318972963857863)
    ·
      refine ⟨73818016506478459445786795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49212011004318972963857863 73818016506478459445786795)
      ·
        refine ⟨110727024759717689168680193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73818016506478459445786795 110727024759717689168680193)
        ·
          refine ⟨83045268569788266876510145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110727024759717689168680193 83045268569788266876510145)
          ·
            refine ⟨62283951427341200157382609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83045268569788266876510145 62283951427341200157382609)
            ·
              refine ⟨46712963570505900118036957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62283951427341200157382609 46712963570505900118036957)
              ·
                refine ⟨17517361338939712544263859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46712963570505900118036957 17517361338939712544263859)
                ·
                  refine ⟨26276042008409568816395789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17517361338939712544263859 26276042008409568816395789)
                  ·
                    refine ⟨9853515753153588306148421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26276042008409568816395789 9853515753153588306148421)
                    ·
                      refine ⟨1847534203716297807402829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9853515753153588306148421 1847534203716297807402829)
                      ·
                        rfl

theorem cell23_3598060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 4].length) (baseStart_3598060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3598060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3598060 prefixEnd_3598060 := by exact prefixLift 3598060
  have htrace : WordTrace (prefixWord ++ tailWord_3598060) baseStart_3598060 baseEnd_3598060 := by
    simpa [prefixWord, tailWord_3598060, baseEnd_3598060] using wordTrace_append hprefix tailTrace_3598060
  have hstable : (prefixWord ++ tailWord_3598060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3598060).length < 2 ^ (prefixWord ++ tailWord_3598060).sum := by decide
  have hdescent : baseEnd_3598060 < baseStart_3598060 := by decide
  rcases family_descends (prefixWord ++ tailWord_3598060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3598078 : List Nat := [4, 2, 2, 1, 3, 2, 2, 2, 5]
def baseStart_3598078 : Nat := 118140960795 + 3598078 * 2 ^ 59
def prefixEnd_3598078 : Nat := 4983230072969 + 3 ^ 40 * 3598078 * 2
def baseEnd_3598078 : Nat := 205282605152008748553083

theorem tailTrace_3598078 : CollatzResearch.WordTrace tailWord_3598078 prefixEnd_3598078 205282605152008748553083 := by
  unfold tailWord_3598078
  simp only [CollatzResearch.WordTrace]
  refine ⟨16404085732348172955555361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87488457239190255762961925 16404085732348172955555361)
  ·
    refine ⟨12303064299261129716666521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16404085732348172955555361 12303064299261129716666521)
    ·
      refine ⟨9227298224445847287499891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12303064299261129716666521 9227298224445847287499891)
      ·
        refine ⟨13840947336668770931249837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9227298224445847287499891 13840947336668770931249837)
        ·
          refine ⟨5190355251250789099218689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13840947336668770931249837 5190355251250789099218689)
          ·
            refine ⟨3892766438438091824414017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5190355251250789099218689 3892766438438091824414017)
            ·
              refine ⟨2919574828828568868310513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3892766438438091824414017 2919574828828568868310513)
              ·
                refine ⟨2189681121621426651232885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2919574828828568868310513 2189681121621426651232885)
                ·
                  refine ⟨205282605152008748553083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2189681121621426651232885 205282605152008748553083)
                  ·
                    rfl

theorem cell23_3598078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 2, 2, 5].length) (baseStart_3598078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3598078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3598078 prefixEnd_3598078 := by exact prefixLift 3598078
  have htrace : WordTrace (prefixWord ++ tailWord_3598078) baseStart_3598078 baseEnd_3598078 := by
    simpa [prefixWord, tailWord_3598078, baseEnd_3598078] using wordTrace_append hprefix tailTrace_3598078
  have hstable : (prefixWord ++ tailWord_3598078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3598078).length < 2 ^ (prefixWord ++ tailWord_3598078).sum := by decide
  have hdescent : baseEnd_3598078 < baseStart_3598078 := by decide
  rcases family_descends (prefixWord ++ tailWord_3598078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3598134 : List Nat := [5, 1, 2, 2, 1, 2, 1, 1, 8]
def baseStart_3598134 : Nat := 118140960795 + 3598134 * 2 ^ 59
def prefixEnd_3598134 : Nat := 4983230072969 + 3 ^ 40 * 3598134 * 2
def baseEnd_3598134 : Nat := 205285800142747835319721

theorem tailTrace_3598134 : CollatzResearch.WordTrace tailWord_3598134 prefixEnd_3598134 205285800142747835319721 := by
  unfold tailWord_3598134
  simp only [CollatzResearch.WordTrace]
  refine ⟨8202170521661406575530091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 87489818897721670138987637 8202170521661406575530091)
  ·
    refine ⟨12303255782492109863295137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8202170521661406575530091 12303255782492109863295137)
    ·
      refine ⟨9227441836869082397471353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12303255782492109863295137 9227441836869082397471353)
      ·
        refine ⟨6920581377651811798103515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9227441836869082397471353 6920581377651811798103515)
        ·
          refine ⟨10380872066477717697155273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6920581377651811798103515 10380872066477717697155273)
          ·
            refine ⟨7785654049858288272866455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10380872066477717697155273 7785654049858288272866455)
            ·
              refine ⟨11678481074787432409299683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7785654049858288272866455 11678481074787432409299683)
              ·
                refine ⟨17517721612181148613949525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11678481074787432409299683 17517721612181148613949525)
                ·
                  refine ⟨205285800142747835319721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17517721612181148613949525 205285800142747835319721)
                  ·
                    rfl

theorem cell23_3598134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 1, 8].length) (baseStart_3598134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3598134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3598134 prefixEnd_3598134 := by exact prefixLift 3598134
  have htrace : WordTrace (prefixWord ++ tailWord_3598134) baseStart_3598134 baseEnd_3598134 := by
    simpa [prefixWord, tailWord_3598134, baseEnd_3598134] using wordTrace_append hprefix tailTrace_3598134
  have hstable : (prefixWord ++ tailWord_3598134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3598134).length < 2 ^ (prefixWord ++ tailWord_3598134).sum := by decide
  have hdescent : baseEnd_3598134 < baseStart_3598134 := by decide
  rcases family_descends (prefixWord ++ tailWord_3598134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3598164 : List Nat := [2, 4, 1, 1, 3, 1, 1, 4, 1, 5]
def baseStart_3598164 : Nat := 118140960795 + 3598164 * 2 ^ 59
def prefixEnd_3598164 : Nat := 4983230072969 + 3 ^ 40 * 3598164 * 2
def baseEnd_3598164 : Nat := 615862535234788466834117

theorem tailTrace_3598164 : CollatzResearch.WordTrace tailWord_3598164 prefixEnd_3598164 615862535234788466834117 := by
  unfold tailWord_3598164
  simp only [CollatzResearch.WordTrace]
  refine ⟨65617911268236910166036773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87490548357649213554715697 65617911268236910166036773)
  ·
    refine ⟨12303358362794420656131895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65617911268236910166036773 12303358362794420656131895)
    ·
      refine ⟨18455037544191630984197843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12303358362794420656131895 18455037544191630984197843)
      ·
        refine ⟨27682556316287446476296765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18455037544191630984197843 27682556316287446476296765)
        ·
          refine ⟨10380958618607792428611287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27682556316287446476296765 10380958618607792428611287)
          ·
            refine ⟨15571437927911688642916931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10380958618607792428611287 15571437927911688642916931)
            ·
              refine ⟨23357156891867532964375397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15571437927911688642916931 23357156891867532964375397)
              ·
                refine ⟨4379466917225162430820387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23357156891867532964375397 4379466917225162430820387)
                ·
                  refine ⟨6569200375837743646230581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4379466917225162430820387 6569200375837743646230581)
                  ·
                    refine ⟨615862535234788466834117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6569200375837743646230581 615862535234788466834117)
                    ·
                      rfl

theorem cell23_3598164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 4, 1, 5].length) (baseStart_3598164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3598164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3598164 prefixEnd_3598164 := by exact prefixLift 3598164
  have htrace : WordTrace (prefixWord ++ tailWord_3598164) baseStart_3598164 baseEnd_3598164 := by
    simpa [prefixWord, tailWord_3598164, baseEnd_3598164] using wordTrace_append hprefix tailTrace_3598164
  have hstable : (prefixWord ++ tailWord_3598164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3598164).length < 2 ^ (prefixWord ++ tailWord_3598164).sum := by decide
  have hdescent : baseEnd_3598164 < baseStart_3598164 := by decide
  rcases family_descends (prefixWord ++ tailWord_3598164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3598177 : List Nat := [1, 2, 3, 1, 1, 1, 3, 1, 6, 4]
def baseStart_3598177 : Nat := 118140960795 + 3598177 * 2 ^ 59
def prefixEnd_3598177 : Nat := 4983230072969 + 3 ^ 40 * 3598177 * 2
def baseEnd_3598177 : Nat := 615864760317624616546597

theorem tailTrace_3598177 : CollatzResearch.WordTrace tailWord_3598177 prefixEnd_3598177 615864760317624616546597 := by
  unfold tailWord_3598177
  simp only [CollatzResearch.WordTrace]
  refine ⟨131236296685426723552296785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87490864456951149034864523 131236296685426723552296785)
  ·
    refine ⟨98427222514070042664222589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131236296685426723552296785 98427222514070042664222589)
    ·
      refine ⟨36910208442776265999083471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98427222514070042664222589 36910208442776265999083471)
      ·
        refine ⟨55365312664164398998625207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36910208442776265999083471 55365312664164398998625207)
        ·
          refine ⟨83047968996246598497937811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55365312664164398998625207 83047968996246598497937811)
          ·
            refine ⟨124571953494369897746906717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83047968996246598497937811 124571953494369897746906717)
            ·
              refine ⟨46714482560388711655090019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124571953494369897746906717 46714482560388711655090019)
              ·
                refine ⟨70071723840583067482635029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46714482560388711655090019 70071723840583067482635029)
                ·
                  refine ⟨3284612055027331288248517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 70071723840583067482635029 3284612055027331288248517)
                  ·
                    refine ⟨615864760317624616546597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3284612055027331288248517 615864760317624616546597)
                    ·
                      rfl

theorem cell23_3598177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 6, 4].length) (baseStart_3598177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3598177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3598177 prefixEnd_3598177 := by exact prefixLift 3598177
  have htrace : WordTrace (prefixWord ++ tailWord_3598177) baseStart_3598177 baseEnd_3598177 := by
    simpa [prefixWord, tailWord_3598177, baseEnd_3598177] using wordTrace_append hprefix tailTrace_3598177
  have hstable : (prefixWord ++ tailWord_3598177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3598177).length < 2 ^ (prefixWord ++ tailWord_3598177).sum := by decide
  have hdescent : baseEnd_3598177 < baseStart_3598177 := by decide
  rcases family_descends (prefixWord ++ tailWord_3598177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3598184 : List Nat := [2, 1, 4, 2, 1, 1, 1, 5, 1, 1, 4]
def baseStart_3598184 : Nat := 118140960795 + 3598184 * 2 ^ 59
def prefixEnd_3598184 : Nat := 4983230072969 + 3 ^ 40 * 3598184 * 2
def baseEnd_3598184 : Nat := 1847597875317455322252259

theorem tailTrace_3598184 : CollatzResearch.WordTrace tailWord_3598184 prefixEnd_3598184 1847597875317455322252259 := by
  unfold tailWord_3598184
  simp only [CollatzResearch.WordTrace]
  refine ⟨65618275998200681873900803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87491034664267575831867737 65618275998200681873900803)
  ·
    refine ⟨98427413997301022810851205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65618275998200681873900803 98427413997301022810851205)
    ·
      refine ⟨18455140124493941777034601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98427413997301022810851205 18455140124493941777034601)
      ·
        refine ⟨13841355093370456332775951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18455140124493941777034601 13841355093370456332775951)
        ·
          refine ⟨20762032640055684499163927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13841355093370456332775951 20762032640055684499163927)
          ·
            refine ⟨31143048960083526748745891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20762032640055684499163927 31143048960083526748745891)
            ·
              refine ⟨46714573440125290123118837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31143048960083526748745891 46714573440125290123118837)
              ·
                refine ⟨4379491260011745949042391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46714573440125290123118837 4379491260011745949042391)
                ·
                  refine ⟨6569236890017618923563587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4379491260011745949042391 6569236890017618923563587)
                  ·
                    refine ⟨9853855335026428385345381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6569236890017618923563587 9853855335026428385345381)
                    ·
                      refine ⟨1847597875317455322252259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9853855335026428385345381 1847597875317455322252259)
                      ·
                        rfl

theorem cell23_3598184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 5, 1, 1, 4].length) (baseStart_3598184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3598184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3598184 prefixEnd_3598184 := by exact prefixLift 3598184
  have htrace : WordTrace (prefixWord ++ tailWord_3598184) baseStart_3598184 baseEnd_3598184 := by
    simpa [prefixWord, tailWord_3598184, baseEnd_3598184] using wordTrace_append hprefix tailTrace_3598184
  have hstable : (prefixWord ++ tailWord_3598184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3598184).length < 2 ^ (prefixWord ++ tailWord_3598184).sum := by decide
  have hdescent : baseEnd_3598184 < baseStart_3598184 := by decide
  rcases family_descends (prefixWord ++ tailWord_3598184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3598187 : List Nat := [1, 1, 1, 1, 2, 2, 3, 2, 5, 2, 3]
def baseStart_3598187 : Nat := 118140960795 + 3598187 * 2 ^ 59
def prefixEnd_3598187 : Nat := 4983230072969 + 3 ^ 40 * 3598187 * 2
def baseEnd_3598187 : Nat := 1847599415759418810514745

theorem tailTrace_3598187 : CollatzResearch.WordTrace tailWord_3598187 prefixEnd_3598187 1847599415759418810514745 := by
  unfold tailWord_3598187
  simp only [CollatzResearch.WordTrace]
  refine ⟨131236661415390495260160815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87491107610260330173440543 131236661415390495260160815)
  ·
    refine ⟨196854992123085742890241223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131236661415390495260160815 196854992123085742890241223)
    ·
      refine ⟨295282488184628614335361835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196854992123085742890241223 295282488184628614335361835)
      ·
        refine ⟨442923732276942921503042753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295282488184628614335361835 442923732276942921503042753)
        ·
          refine ⟨332192799207707191127282065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 442923732276942921503042753 332192799207707191127282065)
          ·
            refine ⟨249144599405780393345461549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 332192799207707191127282065 249144599405780393345461549)
            ·
              refine ⟨93429224777167647504548081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 249144599405780393345461549 93429224777167647504548081)
              ·
                refine ⟨70071918582875735628411061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93429224777167647504548081 70071918582875735628411061)
                ·
                  refine ⟨6569242367144600215163537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70071918582875735628411061 6569242367144600215163537)
                  ·
                    refine ⟨4926931775358450161372653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6569242367144600215163537 4926931775358450161372653)
                    ·
                      refine ⟨1847599415759418810514745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4926931775358450161372653 1847599415759418810514745)
                      ·
                        rfl

theorem cell23_3598187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 5, 2, 3].length) (baseStart_3598187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3598187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3598187 prefixEnd_3598187 := by exact prefixLift 3598187
  have htrace : WordTrace (prefixWord ++ tailWord_3598187) baseStart_3598187 baseEnd_3598187 := by
    simpa [prefixWord, tailWord_3598187, baseEnd_3598187] using wordTrace_append hprefix tailTrace_3598187
  have hstable : (prefixWord ++ tailWord_3598187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3598187).length < 2 ^ (prefixWord ++ tailWord_3598187).sum := by decide
  have hdescent : baseEnd_3598187 < baseStart_3598187 := by decide
  rcases family_descends (prefixWord ++ tailWord_3598187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3598194 : List Nat := [3, 2, 1, 2, 1, 1, 1, 6, 2, 4]
def baseStart_3598194 : Nat := 118140960795 + 3598194 * 2 ^ 59
def prefixEnd_3598194 : Nat := 4983230072969 + 3 ^ 40 * 3598194 * 2
def baseEnd_3598194 : Nat := 615867670041333427709071

theorem tailTrace_3598194 : CollatzResearch.WordTrace tailWord_3598194 prefixEnd_3598194 615867670041333427709071 := by
  unfold tailWord_3598194
  simp only [CollatzResearch.WordTrace]
  refine ⟨32809229181591283863916409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87491277817576756970443757 32809229181591283863916409)
  ·
    refine ⟨24606921886193462897937307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32809229181591283863916409 24606921886193462897937307)
    ·
      refine ⟨36910382829290194346905961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24606921886193462897937307 36910382829290194346905961)
      ·
        refine ⟨27682787121967645760179471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36910382829290194346905961 27682787121967645760179471)
        ·
          refine ⟨41524180682951468640269207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27682787121967645760179471 41524180682951468640269207)
          ·
            refine ⟨62286271024427202960403811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41524180682951468640269207 62286271024427202960403811)
            ·
              refine ⟨93429406536640804440605717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62286271024427202960403811 93429406536640804440605717)
              ·
                refine ⟨4379503431405037708153393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 93429406536640804440605717 4379503431405037708153393)
                ·
                  refine ⟨3284627573553778281115045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4379503431405037708153393 3284627573553778281115045)
                  ·
                    refine ⟨615867670041333427709071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3284627573553778281115045 615867670041333427709071)
                    ·
                      rfl

theorem cell23_3598194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 6, 2, 4].length) (baseStart_3598194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3598194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3598194 prefixEnd_3598194 := by exact prefixLift 3598194
  have htrace : WordTrace (prefixWord ++ tailWord_3598194) baseStart_3598194 baseEnd_3598194 := by
    simpa [prefixWord, tailWord_3598194, baseEnd_3598194] using wordTrace_append hprefix tailTrace_3598194
  have hstable : (prefixWord ++ tailWord_3598194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3598194).length < 2 ^ (prefixWord ++ tailWord_3598194).sum := by decide
  have hdescent : baseEnd_3598194 < baseStart_3598194 := by decide
  rcases family_descends (prefixWord ++ tailWord_3598194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3598197 : List Nat := [1, 3, 4, 1, 1, 1, 1, 1, 3, 1, 6]
def baseStart_3598197 : Nat := 118140960795 + 3598197 * 2 ^ 59
def prefixEnd_3598197 : Nat := 4983230072969 + 3 ^ 40 * 3598197 * 2
def baseEnd_3598197 : Nat := 1847604550565963771389699

theorem tailTrace_3598197 : CollatzResearch.WordTrace tailWord_3598197 prefixEnd_3598197 1847604550565963771389699 := by
  unfold tailWord_3598197
  simp only [CollatzResearch.WordTrace]
  refine ⟨131237026145354266968024845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87491350763569511312016563 131237026145354266968024845)
  ·
    refine ⟨49213884804507850113009317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131237026145354266968024845 49213884804507850113009317)
    ·
      refine ⟨9227603400845221896189247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49213884804507850113009317 9227603400845221896189247)
      ·
        refine ⟨13841405101267832844283871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9227603400845221896189247 13841405101267832844283871)
        ·
          refine ⟨20762107651901749266425807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13841405101267832844283871 20762107651901749266425807)
          ·
            refine ⟨31143161477852623899638711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20762107651901749266425807 31143161477852623899638711)
            ·
              refine ⟨46714742216778935849458067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31143161477852623899638711 46714742216778935849458067)
              ·
                refine ⟨70072113325168403774187101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46714742216778935849458067 70072113325168403774187101)
                ·
                  refine ⟨26277042496938151415320163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70072113325168403774187101 26277042496938151415320163)
                  ·
                    refine ⟨39415563745407227122980245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26277042496938151415320163 39415563745407227122980245)
                    ·
                      refine ⟨1847604550565963771389699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39415563745407227122980245 1847604550565963771389699)
                      ·
                        rfl

theorem cell23_3598197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_3598197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3598197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3598197 prefixEnd_3598197 := by exact prefixLift 3598197
  have htrace : WordTrace (prefixWord ++ tailWord_3598197) baseStart_3598197 baseEnd_3598197 := by
    simpa [prefixWord, tailWord_3598197, baseEnd_3598197] using wordTrace_append hprefix tailTrace_3598197
  have hstable : (prefixWord ++ tailWord_3598197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3598197).length < 2 ^ (prefixWord ++ tailWord_3598197).sum := by decide
  have hdescent : baseEnd_3598197 < baseStart_3598197 := by decide
  rcases family_descends (prefixWord ++ tailWord_3598197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3598211 : List Nat := [1, 1, 1, 3, 4, 2, 4, 1, 2, 4]
def baseStart_3598211 : Nat := 118140960795 + 3598211 * 2 ^ 59
def prefixEnd_3598211 : Nat := 4983230072969 + 3 ^ 40 * 3598211 * 2
def baseEnd_3598211 : Nat := 615870579765042238871545

theorem tailTrace_3598211 : CollatzResearch.WordTrace tailWord_3598211 prefixEnd_3598211 615870579765042238871545 := by
  unfold tailWord_3598211
  simp only [CollatzResearch.WordTrace]
  refine ⟨131237536767303547359034487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87491691178202364906022991 131237536767303547359034487)
  ·
    refine ⟨196856305150955321038551731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131237536767303547359034487 196856305150955321038551731)
    ·
      refine ⟨295284457726432981557827597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196856305150955321038551731 295284457726432981557827597)
      ·
        refine ⟨110731671647412368084185349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 295284457726432981557827597 110731671647412368084185349)
        ·
          refine ⟨20762188433889819015784753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110731671647412368084185349 20762188433889819015784753)
          ·
            refine ⟨15571641325417364261838565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20762188433889819015784753 15571641325417364261838565)
            ·
              refine ⟨2919682748515755799094731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15571641325417364261838565 2919682748515755799094731)
              ·
                refine ⟨4379524122773633698642097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2919682748515755799094731 4379524122773633698642097)
                ·
                  refine ⟨3284643092080225273981573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4379524122773633698642097 3284643092080225273981573)
                  ·
                    refine ⟨615870579765042238871545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3284643092080225273981573 615870579765042238871545)
                    ·
                      rfl

theorem cell23_3598211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 4, 1, 2, 4].length) (baseStart_3598211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3598211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3598211 prefixEnd_3598211 := by exact prefixLift 3598211
  have htrace : WordTrace (prefixWord ++ tailWord_3598211) baseStart_3598211 baseEnd_3598211 := by
    simpa [prefixWord, tailWord_3598211, baseEnd_3598211] using wordTrace_append hprefix tailTrace_3598211
  have hstable : (prefixWord ++ tailWord_3598211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3598211).length < 2 ^ (prefixWord ++ tailWord_3598211).sum := by decide
  have hdescent : baseEnd_3598211 < baseStart_3598211 := by decide
  rcases family_descends (prefixWord ++ tailWord_3598211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3598218 : List Nat := [3, 1, 2, 4, 2, 2, 1, 2, 1, 1, 4]
def baseStart_3598218 : Nat := 118140960795 + 3598218 * 2 ^ 59
def prefixEnd_3598218 : Nat := 4983230072969 + 3 ^ 40 * 3598218 * 2
def baseEnd_3598218 : Nat := 1847615333659708189227103

theorem tailTrace_3598218 : CollatzResearch.WordTrace tailWord_3598218 prefixEnd_3598218 1847615333659708189227103 := by
  unfold tailWord_3598218
  simp only [CollatzResearch.WordTrace]
  refine ⟨32809448019569546888634827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87491861385518791703026205 32809448019569546888634827)
  ·
    refine ⟨49214172029354320332952241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32809448019569546888634827 49214172029354320332952241)
    ·
      refine ⟨36910629022015740249714181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49214172029354320332952241 36910629022015740249714181)
      ·
        refine ⟨6920742941627951296821409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36910629022015740249714181 6920742941627951296821409)
        ·
          refine ⟨5190557206220963472616057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6920742941627951296821409 5190557206220963472616057)
          ·
            refine ⟨3892917904665722604462043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5190557206220963472616057 3892917904665722604462043)
            ·
              refine ⟨5839376856998583906693065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3892917904665722604462043 5839376856998583906693065)
              ·
                refine ⟨4379532642748937930019799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5839376856998583906693065 4379532642748937930019799)
                ·
                  refine ⟨6569298964123406895029699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4379532642748937930019799 6569298964123406895029699)
                  ·
                    refine ⟨9853948446185110342544549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6569298964123406895029699 9853948446185110342544549)
                    ·
                      refine ⟨1847615333659708189227103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9853948446185110342544549 1847615333659708189227103)
                      ·
                        rfl

theorem cell23_3598218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_3598218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3598218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3598218 prefixEnd_3598218 := by exact prefixLift 3598218
  have htrace : WordTrace (prefixWord ++ tailWord_3598218) baseStart_3598218 baseEnd_3598218 := by
    simpa [prefixWord, tailWord_3598218, baseEnd_3598218] using wordTrace_append hprefix tailTrace_3598218
  have hstable : (prefixWord ++ tailWord_3598218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3598218).length < 2 ^ (prefixWord ++ tailWord_3598218).sum := by decide
  have hdescent : baseEnd_3598218 < baseStart_3598218 := by decide
  rcases family_descends (prefixWord ++ tailWord_3598218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3598234 : List Nat := [3, 1, 1, 4, 2, 1, 1, 1, 3, 3, 3]
def baseStart_3598234 : Nat := 118140960795 + 3598234 * 2 ^ 59
def prefixEnd_3598234 : Nat := 4983230072969 + 3 ^ 40 * 3598234 * 2
def baseEnd_3598234 : Nat := 1847623549350180126627029

theorem tailTrace_3598234 : CollatzResearch.WordTrace tailWord_3598234 prefixEnd_3598234 1847623549350180126627029 := by
  unfold tailWord_3598234
  simp only [CollatzResearch.WordTrace]
  refine ⟨32809593911555055571780439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87492250430813481524747837 32809593911555055571780439)
  ·
    refine ⟨49214390867332583357670659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32809593911555055571780439 49214390867332583357670659)
    ·
      refine ⟨73821586300998875036505989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49214390867332583357670659 73821586300998875036505989)
      ·
        refine ⟨13841547431437289069344873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73821586300998875036505989 13841547431437289069344873)
        ·
          refine ⟨10381160573577966802008655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13841547431437289069344873 10381160573577966802008655)
          ·
            refine ⟨15571740860366950203012983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10381160573577966802008655 15571740860366950203012983)
            ·
              refine ⟨23357611290550425304519475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15571740860366950203012983 23357611290550425304519475)
              ·
                refine ⟨35036416935825637956779213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23357611290550425304519475 35036416935825637956779213)
                ·
                  refine ⟨13138656350934614233792205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35036416935825637956779213 13138656350934614233792205)
                  ·
                    refine ⟨4926996131600480337672077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13138656350934614233792205 4926996131600480337672077)
                    ·
                      refine ⟨1847623549350180126627029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4926996131600480337672077 1847623549350180126627029)
                      ·
                        rfl

theorem cell23_3598234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 1, 3, 3, 3].length) (baseStart_3598234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3598234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3598234 prefixEnd_3598234 := by exact prefixLift 3598234
  have htrace : WordTrace (prefixWord ++ tailWord_3598234) baseStart_3598234 baseEnd_3598234 := by
    simpa [prefixWord, tailWord_3598234, baseEnd_3598234] using wordTrace_append hprefix tailTrace_3598234
  have hstable : (prefixWord ++ tailWord_3598234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3598234).length < 2 ^ (prefixWord ++ tailWord_3598234).sum := by decide
  have hdescent : baseEnd_3598234 < baseStart_3598234 := by decide
  rcases family_descends (prefixWord ++ tailWord_3598234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3598261 : List Nat := [1, 3, 3, 2, 1, 2, 1, 2, 3, 3, 2]
def baseStart_3598261 : Nat := 118140960795 + 3598261 * 2 ^ 59
def prefixEnd_3598261 : Nat := 4983230072969 + 3 ^ 40 * 3598261 * 2
def baseEnd_3598261 : Nat := 1847637413327851520989405

theorem tailTrace_3598261 : CollatzResearch.WordTrace tailWord_3598261 prefixEnd_3598261 1847637413327851520989405 := by
  unfold tailWord_3598261
  simp only [CollatzResearch.WordTrace]
  refine ⟨131239360417122405898354637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87492906944748270598903091 131239360417122405898354637)
  ·
    refine ⟨49214760156420902211882989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131239360417122405898354637 49214760156420902211882989)
    ·
      refine ⟨18455535058657838329456121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49214760156420902211882989 18455535058657838329456121)
      ·
        refine ⟨13841651293993378747092091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18455535058657838329456121 13841651293993378747092091)
        ·
          refine ⟨20762476940990068120638137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13841651293993378747092091 20762476940990068120638137)
          ·
            refine ⟨15571857705742551090478603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20762476940990068120638137 15571857705742551090478603)
            ·
              refine ⟨23357786558613826635717905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15571857705742551090478603 23357786558613826635717905)
              ·
                refine ⟨17518339918960369976788429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23357786558613826635717905 17518339918960369976788429)
                ·
                  refine ⟨6569377469610138741295661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17518339918960369976788429 6569377469610138741295661)
                  ·
                    refine ⟨2463516551103802027985873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6569377469610138741295661 2463516551103802027985873)
                    ·
                      refine ⟨1847637413327851520989405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2463516551103802027985873 1847637413327851520989405)
                      ·
                        rfl

theorem cell23_3598261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 2, 3, 3, 2].length) (baseStart_3598261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3598261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3598261 prefixEnd_3598261 := by exact prefixLift 3598261
  have htrace : WordTrace (prefixWord ++ tailWord_3598261) baseStart_3598261 baseEnd_3598261 := by
    simpa [prefixWord, tailWord_3598261, baseEnd_3598261] using wordTrace_append hprefix tailTrace_3598261
  have hstable : (prefixWord ++ tailWord_3598261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3598261).length < 2 ^ (prefixWord ++ tailWord_3598261).sum := by decide
  have hdescent : baseEnd_3598261 < baseStart_3598261 := by decide
  rcases family_descends (prefixWord ++ tailWord_3598261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3598268 : List Nat := [2, 2, 2, 5, 1, 1, 2, 1, 1, 3, 3]
def baseStart_3598268 : Nat := 118140960795 + 3598268 * 2 ^ 59
def prefixEnd_3598268 : Nat := 4983230072969 + 3 ^ 40 * 3598268 * 2
def baseEnd_3598268 : Nat := 1847641007692432993601873

theorem tailTrace_3598268 : CollatzResearch.WordTrace tailWord_3598268 prefixEnd_3598268 1847641007692432993601873 := by
  unfold tailWord_3598268
  simp only [CollatzResearch.WordTrace]
  refine ⟨65619807864048523046929729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87493077152064697395906305 65619807864048523046929729)
  ·
    refine ⟨49214855898036392285197297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65619807864048523046929729 49214855898036392285197297)
    ·
      refine ⟨36911141923527294213897973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49214855898036392285197297 36911141923527294213897973)
      ·
        refine ⟨3460419555330683832552935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36911141923527294213897973 3460419555330683832552935)
        ·
          refine ⟨5190629332996025748829403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3460419555330683832552935 5190629332996025748829403)
          ·
            refine ⟨7785943999494038623244105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5190629332996025748829403 7785943999494038623244105)
            ·
              refine ⟨5839457999620528967433079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7785943999494038623244105 5839457999620528967433079)
              ·
                refine ⟨8759186999430793451149619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5839457999620528967433079 8759186999430793451149619)
                ·
                  refine ⟨13138780499146190176724429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8759186999430793451149619 13138780499146190176724429)
                  ·
                    refine ⟨4927042687179821316271661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13138780499146190176724429 4927042687179821316271661)
                    ·
                      refine ⟨1847641007692432993601873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4927042687179821316271661 1847641007692432993601873)
                      ·
                        rfl

theorem cell23_3598268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_3598268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3598268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3598268 prefixEnd_3598268 := by exact prefixLift 3598268
  have htrace : WordTrace (prefixWord ++ tailWord_3598268) baseStart_3598268 baseEnd_3598268 := by
    simpa [prefixWord, tailWord_3598268, baseEnd_3598268] using wordTrace_append hprefix tailTrace_3598268
  have hstable : (prefixWord ++ tailWord_3598268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3598268).length < 2 ^ (prefixWord ++ tailWord_3598268).sum := by decide
  have hdescent : baseEnd_3598268 < baseStart_3598268 := by decide
  rcases family_descends (prefixWord ++ tailWord_3598268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3598277 : List Nat := [1, 3, 1, 1, 1, 1, 1, 6, 2, 1, 5]
def baseStart_3598277 : Nat := 118140960795 + 3598277 * 2 ^ 59
def prefixEnd_3598277 : Nat := 4983230072969 + 3 ^ 40 * 3598277 * 2
def baseEnd_3598277 : Nat := 1847645629018323458389331

theorem tailTrace_3598277 : CollatzResearch.WordTrace tailWord_3598277 prefixEnd_3598277 1847645629018323458389331 := by
  unfold tailWord_3598277
  simp only [CollatzResearch.WordTrace]
  refine ⟨131239943985064440630937085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87493295990042960420624723 131239943985064440630937085)
  ·
    refine ⟨49214978994399165236601407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131239943985064440630937085 49214978994399165236601407)
    ·
      refine ⟨73822468491598747854902111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49214978994399165236601407 73822468491598747854902111)
      ·
        refine ⟨110733702737398121782353167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73822468491598747854902111 110733702737398121782353167)
        ·
          refine ⟨166100554106097182673529751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110733702737398121782353167 166100554106097182673529751)
          ·
            refine ⟨249150831159145774010294627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166100554106097182673529751 249150831159145774010294627)
            ·
              refine ⟨373726246738718661015441941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 249150831159145774010294627 373726246738718661015441941)
              ·
                refine ⟨17518417815877437235098841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 373726246738718661015441941 17518417815877437235098841)
                ·
                  refine ⟨13138813361908077926324131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17518417815877437235098841 13138813361908077926324131)
                  ·
                    refine ⟨19708220042862116889486197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13138813361908077926324131 19708220042862116889486197)
                    ·
                      refine ⟨1847645629018323458389331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19708220042862116889486197 1847645629018323458389331)
                      ·
                        rfl

theorem cell23_3598277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 6, 2, 1, 5].length) (baseStart_3598277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3598277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3598277 prefixEnd_3598277 := by exact prefixLift 3598277
  have htrace : WordTrace (prefixWord ++ tailWord_3598277) baseStart_3598277 baseEnd_3598277 := by
    simpa [prefixWord, tailWord_3598277, baseEnd_3598277] using wordTrace_append hprefix tailTrace_3598277
  have hstable : (prefixWord ++ tailWord_3598277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3598277).length < 2 ^ (prefixWord ++ tailWord_3598277).sum := by decide
  have hdescent : baseEnd_3598277 < baseStart_3598277 := by decide
  rcases family_descends (prefixWord ++ tailWord_3598277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3598287 : List Nat := [1, 1, 2, 1, 1, 5, 1, 2, 1, 4, 4]
def baseStart_3598287 : Nat := 118140960795 + 3598287 * 2 ^ 59
def prefixEnd_3598287 : Nat := 4983230072969 + 3 ^ 40 * 3598287 * 2
def baseEnd_3598287 : Nat := 1847650763824868419264285

theorem tailTrace_3598287 : CollatzResearch.WordTrace tailWord_3598287 prefixEnd_3598287 1847650763824868419264285 := by
  unfold tailWord_3598287
  simp only [CollatzResearch.WordTrace]
  refine ⟨131240308715028212338801115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87493539143352141559200743 131240308715028212338801115)
  ·
    refine ⟨196860463072542318508201673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131240308715028212338801115 196860463072542318508201673)
    ·
      refine ⟨147645347304406738881151255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196860463072542318508201673 147645347304406738881151255)
      ·
        refine ⟨221468020956610108321726883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147645347304406738881151255 221468020956610108321726883)
        ·
          refine ⟨332202031434915162482590325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221468020956610108321726883 332202031434915162482590325)
          ·
            refine ⟨31143940447023296482742843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 332202031434915162482590325 31143940447023296482742843)
            ·
              refine ⟨46715910670534944724114265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31143940447023296482742843 46715910670534944724114265)
              ·
                refine ⟨35036933002901208543085699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46715910670534944724114265 35036933002901208543085699)
                ·
                  refine ⟨52555399504351812814628549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35036933002901208543085699 52555399504351812814628549)
                  ·
                    refine ⟨9854137407065964902742853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52555399504351812814628549 9854137407065964902742853)
                    ·
                      refine ⟨1847650763824868419264285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9854137407065964902742853 1847650763824868419264285)
                      ·
                        rfl

theorem cell23_3598287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 2, 1, 4, 4].length) (baseStart_3598287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3598287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3598287 prefixEnd_3598287 := by exact prefixLift 3598287
  have htrace : WordTrace (prefixWord ++ tailWord_3598287) baseStart_3598287 baseEnd_3598287 := by
    simpa [prefixWord, tailWord_3598287, baseEnd_3598287] using wordTrace_append hprefix tailTrace_3598287
  have hstable : (prefixWord ++ tailWord_3598287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3598287).length < 2 ^ (prefixWord ++ tailWord_3598287).sum := by decide
  have hdescent : baseEnd_3598287 < baseStart_3598287 := by decide
  rcases family_descends (prefixWord ++ tailWord_3598287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3598314 : List Nat := [3, 1, 3, 1, 2, 1, 4, 1, 7]
def baseStart_3598314 : Nat := 118140960795 + 3598314 * 2 ^ 59
def prefixEnd_3598314 : Nat := 4983230072969 + 3 ^ 40 * 3598314 * 2
def baseEnd_3598314 : Nat := 205296069755837757069629

theorem tailTrace_3598314 : CollatzResearch.WordTrace tailWord_3598314 prefixEnd_3598314 205296069755837757069629 := by
  unfold tailWord_3598314
  simp only [CollatzResearch.WordTrace]
  refine ⟨32810323371482598987508499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87494195657286930633355997 32810323371482598987508499)
  ·
    refine ⟨49215485057223898481262749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32810323371482598987508499 49215485057223898481262749)
    ·
      refine ⟨18455806896458961930473531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49215485057223898481262749 18455806896458961930473531)
      ·
        refine ⟨27683710344688442895710297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18455806896458961930473531 27683710344688442895710297)
        ·
          refine ⟨20762782758516332171782723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27683710344688442895710297 20762782758516332171782723)
          ·
            refine ⟨31144174137774498257674085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20762782758516332171782723 31144174137774498257674085)
            ·
              refine ⟨5839532650832718423313891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31144174137774498257674085 5839532650832718423313891)
              ·
                refine ⟨8759298976249077634970837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5839532650832718423313891 8759298976249077634970837)
                ·
                  refine ⟨205296069755837757069629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8759298976249077634970837 205296069755837757069629)
                  ·
                    rfl

theorem cell23_3598314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 4, 1, 7].length) (baseStart_3598314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3598314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3598314 prefixEnd_3598314 := by exact prefixLift 3598314
  have htrace : WordTrace (prefixWord ++ tailWord_3598314) baseStart_3598314 baseEnd_3598314 := by
    simpa [prefixWord, tailWord_3598314, baseEnd_3598314] using wordTrace_append hprefix tailTrace_3598314
  have hstable : (prefixWord ++ tailWord_3598314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3598314).length < 2 ^ (prefixWord ++ tailWord_3598314).sum := by decide
  have hdescent : baseEnd_3598314 < baseStart_3598314 := by decide
  rcases family_descends (prefixWord ++ tailWord_3598314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3598344 : List Nat := [2, 1, 3, 2, 1, 2, 2, 3, 2, 5]
def baseStart_3598344 : Nat := 118140960795 + 3598344 * 2 ^ 59
def prefixEnd_3598344 : Nat := 4983230072969 + 3 ^ 40 * 3598344 * 2
def baseEnd_3598344 : Nat := 615893344074058232083841

theorem tailTrace_3598344 : CollatzResearch.WordTrace tailWord_3598344 prefixEnd_3598344 615893344074058232083841 := by
  unfold tailWord_3598344
  simp only [CollatzResearch.WordTrace]
  refine ⟨65621193837910855536813043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87494925117214474049084057 65621193837910855536813043)
  ·
    refine ⟨98431790756866283305219565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65621193837910855536813043 98431790756866283305219565)
    ·
      refine ⟨36911921533824856239457337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98431790756866283305219565 36911921533824856239457337)
      ·
        refine ⟨27683941150368642179593003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36911921533824856239457337 27683941150368642179593003)
        ·
          refine ⟨41525911725552963269389505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27683941150368642179593003 41525911725552963269389505)
          ·
            refine ⟨31144433794164722452042129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41525911725552963269389505 31144433794164722452042129)
            ·
              refine ⟨23358325345623541839031597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31144433794164722452042129 23358325345623541839031597)
              ·
                refine ⟨8759372004608828189636849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23358325345623541839031597 8759372004608828189636849)
                ·
                  refine ⟨6569529003456621142227637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8759372004608828189636849 6569529003456621142227637)
                  ·
                    refine ⟨615893344074058232083841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6569529003456621142227637 615893344074058232083841)
                    ·
                      rfl

theorem cell23_3598344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 3, 2, 5].length) (baseStart_3598344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3598344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3598344 prefixEnd_3598344 := by exact prefixLift 3598344
  have htrace : WordTrace (prefixWord ++ tailWord_3598344) baseStart_3598344 baseEnd_3598344 := by
    simpa [prefixWord, tailWord_3598344, baseEnd_3598344] using wordTrace_append hprefix tailTrace_3598344
  have hstable : (prefixWord ++ tailWord_3598344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3598344).length < 2 ^ (prefixWord ++ tailWord_3598344).sum := by decide
  have hdescent : baseEnd_3598344 < baseStart_3598344 := by decide
  rcases family_descends (prefixWord ++ tailWord_3598344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3598376 : List Nat := [2, 1, 5, 3, 2, 1, 2, 1, 2, 2, 2]
def baseStart_3598376 : Nat := 118140960795 + 3598376 * 2 ^ 59
def prefixEnd_3598376 : Nat := 4983230072969 + 3 ^ 40 * 3598376 * 2
def baseEnd_3598376 : Nat := 1847696463603118571051377

theorem tailTrace_3598376 : CollatzResearch.WordTrace tailWord_3598376 prefixEnd_3598376 1847696463603118571051377 := by
  unfold tailWord_3598376
  simp only [CollatzResearch.WordTrace]
  refine ⟨65621777405852890269395491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87495703207803853692527321 65621777405852890269395491)
  ·
    refine ⟨98432666108779335404093237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65621777405852890269395491 98432666108779335404093237)
    ·
      refine ⟨9228062447698062694133741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 98432666108779335404093237 9228062447698062694133741)
      ·
        refine ⟨3460523417886773510300153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9228062447698062694133741 3460523417886773510300153)
        ·
          refine ⟨2595392563415080132725115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3460523417886773510300153 2595392563415080132725115)
          ·
            refine ⟨3893088845122620199087673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2595392563415080132725115 3893088845122620199087673)
            ·
              refine ⟨2919816633841965149315755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3893088845122620199087673 2919816633841965149315755)
              ·
                refine ⟨4379724950762947723973633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2919816633841965149315755 4379724950762947723973633)
                ·
                  refine ⟨3284793713072210792980225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4379724950762947723973633 3284793713072210792980225)
                  ·
                    refine ⟨2463595284804158094735169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3284793713072210792980225 2463595284804158094735169)
                    ·
                      refine ⟨1847696463603118571051377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2463595284804158094735169 1847696463603118571051377)
                      ·
                        rfl

theorem cell23_3598376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_3598376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3598376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3598376 prefixEnd_3598376 := by exact prefixLift 3598376
  have htrace : WordTrace (prefixWord ++ tailWord_3598376) baseStart_3598376 baseEnd_3598376 := by
    simpa [prefixWord, tailWord_3598376, baseEnd_3598376] using wordTrace_append hprefix tailTrace_3598376
  have hstable : (prefixWord ++ tailWord_3598376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3598376).length < 2 ^ (prefixWord ++ tailWord_3598376).sum := by decide
  have hdescent : baseEnd_3598376 < baseStart_3598376 := by decide
  rcases family_descends (prefixWord ++ tailWord_3598376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3598377 : List Nat := [1, 2, 1, 1, 1, 1, 1, 1, 5, 3, 6]
def baseStart_3598377 : Nat := 118140960795 + 3598377 * 2 ^ 59
def prefixEnd_3598377 : Nat := 4983230072969 + 3 ^ 40 * 3598377 * 2
def baseEnd_3598377 : Nat := 1847696977083773067138871

theorem tailTrace_3598377 : CollatzResearch.WordTrace tailWord_3598377 prefixEnd_3598377 1847696977083773067138871 := by
  unfold tailWord_3598377
  simp only [CollatzResearch.WordTrace]
  refine ⟨131243591284702157709577385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87495727523134771806384923 131243591284702157709577385)
  ·
    refine ⟨98432693463526618282183039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131243591284702157709577385 98432693463526618282183039)
    ·
      refine ⟨147649040195289927423274559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98432693463526618282183039 147649040195289927423274559)
      ·
        refine ⟨221473560292934891134911839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147649040195289927423274559 221473560292934891134911839)
        ·
          refine ⟨332210340439402336702367759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221473560292934891134911839 332210340439402336702367759)
          ·
            refine ⟨498315510659103505053551639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 332210340439402336702367759 498315510659103505053551639)
            ·
              refine ⟨747473265988655257580327459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 498315510659103505053551639 747473265988655257580327459)
              ·
                refine ⟨1121209898982982886370491189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 747473265988655257580327459 1121209898982982886370491189)
                ·
                  refine ⟨105113428029654645597233549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1121209898982982886370491189 105113428029654645597233549)
                  ·
                    refine ⟨39417535511120492098962581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 105113428029654645597233549 39417535511120492098962581)
                    ·
                      refine ⟨1847696977083773067138871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39417535511120492098962581 1847696977083773067138871)
                      ·
                        rfl

theorem cell23_3598377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 3, 6].length) (baseStart_3598377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3598377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3598377 prefixEnd_3598377 := by exact prefixLift 3598377
  have htrace : WordTrace (prefixWord ++ tailWord_3598377) baseStart_3598377 baseEnd_3598377 := by
    simpa [prefixWord, tailWord_3598377, baseEnd_3598377] using wordTrace_append hprefix tailTrace_3598377
  have hstable : (prefixWord ++ tailWord_3598377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3598377).length < 2 ^ (prefixWord ++ tailWord_3598377).sum := by decide
  have hdescent : baseEnd_3598377 < baseStart_3598377 := by decide
  rcases family_descends (prefixWord ++ tailWord_3598377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3598421 : List Nat := [1, 3, 2, 2, 1, 4, 2, 2, 6]
def baseStart_3598421 : Nat := 118140960795 + 3598421 * 2 ^ 59
def prefixEnd_3598421 : Nat := 4983230072969 + 3 ^ 40 * 3598421 * 2
def baseEnd_3598421 : Nat := 205302174470285654998741

theorem tailTrace_3598421 : CollatzResearch.WordTrace tailWord_3598421 prefixEnd_3598421 205302174470285654998741 := by
  unfold tailWord_3598421
  simp only [CollatzResearch.WordTrace]
  refine ⟨131245196096542753224179117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87496797397695168816119411 131245196096542753224179117)
  ·
    refine ⟨49216948536203532459067169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131245196096542753224179117 49216948536203532459067169)
    ·
      refine ⟨36912711402152649344300377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49216948536203532459067169 36912711402152649344300377)
      ·
        refine ⟨27684533551614487008225283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36912711402152649344300377 27684533551614487008225283)
        ·
          refine ⟨41526800327421730512337925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27684533551614487008225283 41526800327421730512337925)
          ·
            refine ⟨7786275061391574471063361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41526800327421730512337925 7786275061391574471063361)
            ·
              refine ⟨5839706296043680853297521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7786275061391574471063361 5839706296043680853297521)
              ·
                refine ⟨4379779722032760639973141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5839706296043680853297521 4379779722032760639973141)
                ·
                  refine ⟨205302174470285654998741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4379779722032760639973141 205302174470285654998741)
                  ·
                    rfl

theorem cell23_3598421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 2, 2, 6].length) (baseStart_3598421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3598421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3598421 prefixEnd_3598421 := by exact prefixLift 3598421
  have htrace : WordTrace (prefixWord ++ tailWord_3598421) baseStart_3598421 baseEnd_3598421 := by
    simpa [prefixWord, tailWord_3598421, baseEnd_3598421] using wordTrace_append hprefix tailTrace_3598421
  have hstable : (prefixWord ++ tailWord_3598421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3598421).length < 2 ^ (prefixWord ++ tailWord_3598421).sum := by decide
  have hdescent : baseEnd_3598421 < baseStart_3598421 := by decide
  rcases family_descends (prefixWord ++ tailWord_3598421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3598441 : List Nat := [1, 2, 1, 1, 1, 5, 2, 2, 1, 5, 2]
def baseStart_3598441 : Nat := 118140960795 + 3598441 * 2 ^ 59
def prefixEnd_3598441 : Nat := 4983230072969 + 3 ^ 40 * 3598441 * 2
def baseEnd_3598441 : Nat := 1847729839845660816738577

theorem tailTrace_3598441 : CollatzResearch.WordTrace tailWord_3598441 prefixEnd_3598441 1847729839845660816738577 := by
  unfold tailWord_3598441
  simp only [CollatzResearch.WordTrace]
  refine ⟨131245925556470296639907177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87497283704313531093271451 131245925556470296639907177)
  ·
    refine ⟨98434444167352722479930383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131245925556470296639907177 98434444167352722479930383)
    ·
      refine ⟨147651666251029083719895575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98434444167352722479930383 147651666251029083719895575)
      ·
        refine ⟨221477499376543625579843363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147651666251029083719895575 221477499376543625579843363)
        ·
          refine ⟨332216249064815438369765045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221477499376543625579843363 332216249064815438369765045)
          ·
            refine ⟨31145273349826447347165473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 332216249064815438369765045 31145273349826447347165473)
            ·
              refine ⟨23358955012369835510374105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31145273349826447347165473 23358955012369835510374105)
              ·
                refine ⟨17519216259277376632780579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23358955012369835510374105 17519216259277376632780579)
                ·
                  refine ⟨26278824388916064949170869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17519216259277376632780579 26278824388916064949170869)
                  ·
                    refine ⟨2463639786460881088984769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26278824388916064949170869 2463639786460881088984769)
                    ·
                      refine ⟨1847729839845660816738577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2463639786460881088984769 1847729839845660816738577)
                      ·
                        rfl

theorem cell23_3598441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 2, 1, 5, 2].length) (baseStart_3598441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3598441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3598441 prefixEnd_3598441 := by exact prefixLift 3598441
  have htrace : WordTrace (prefixWord ++ tailWord_3598441) baseStart_3598441 baseEnd_3598441 := by
    simpa [prefixWord, tailWord_3598441, baseEnd_3598441] using wordTrace_append hprefix tailTrace_3598441
  have hstable : (prefixWord ++ tailWord_3598441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3598441).length < 2 ^ (prefixWord ++ tailWord_3598441).sum := by decide
  have hdescent : baseEnd_3598441 < baseStart_3598441 := by decide
  rcases family_descends (prefixWord ++ tailWord_3598441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3598448 : List Nat := [2, 1, 1, 1, 5, 3, 1, 2, 3, 1, 3]
def baseStart_3598448 : Nat := 118140960795 + 3598448 * 2 ^ 59
def prefixEnd_3598448 : Nat := 4983230072969 + 3 ^ 40 * 3598448 * 2
def baseEnd_3598448 : Nat := 1847733434210242289351045

theorem tailTrace_3598448 : CollatzResearch.WordTrace tailWord_3598448 prefixEnd_3598448 1847733434210242289351045 := by
  unfold tailWord_3598448
  simp only [CollatzResearch.WordTrace]
  refine ⟨65623090433722468417705999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87497453911629957890274665 65623090433722468417705999)
  ·
    refine ⟨98434635650583702626558999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65623090433722468417705999 98434635650583702626558999)
    ·
      refine ⟨147651953475875553939838499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98434635650583702626558999 147651953475875553939838499)
      ·
        refine ⟨221477930213813330909757749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147651953475875553939838499 221477930213813330909757749)
        ·
          refine ⟨20763555957544999772789789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 221477930213813330909757749 20763555957544999772789789)
          ·
            refine ⟨7786333484079374914796171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20763555957544999772789789 7786333484079374914796171)
            ·
              refine ⟨11679500226119062372194257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7786333484079374914796171 11679500226119062372194257)
              ·
                refine ⟨8759625169589296779145693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11679500226119062372194257 8759625169589296779145693)
                ·
                  refine ⟨3284859438595986292179635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8759625169589296779145693 3284859438595986292179635)
                  ·
                    refine ⟨4927289157893979438269453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3284859438595986292179635 4927289157893979438269453)
                    ·
                      refine ⟨1847733434210242289351045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4927289157893979438269453 1847733434210242289351045)
                      ·
                        rfl

theorem cell23_3598448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 2, 3, 1, 3].length) (baseStart_3598448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3598448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3598448 prefixEnd_3598448 := by exact prefixLift 3598448
  have htrace : WordTrace (prefixWord ++ tailWord_3598448) baseStart_3598448 baseEnd_3598448 := by
    simpa [prefixWord, tailWord_3598448, baseEnd_3598448] using wordTrace_append hprefix tailTrace_3598448
  have hstable : (prefixWord ++ tailWord_3598448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3598448).length < 2 ^ (prefixWord ++ tailWord_3598448).sum := by decide
  have hdescent : baseEnd_3598448 < baseStart_3598448 := by decide
  rcases family_descends (prefixWord ++ tailWord_3598448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3598498 : List Nat := [3, 3, 1, 3, 1, 1, 3, 1, 1, 6]
def baseStart_3598498 : Nat := 118140960795 + 3598498 * 2 ^ 59
def prefixEnd_3598498 : Nat := 4983230072969 + 3 ^ 40 * 3598498 * 2
def baseEnd_3598498 : Nat := 615919702747655697908605

theorem tailTrace_3598498 : CollatzResearch.WordTrace tailWord_3598498 prefixEnd_3598498 615919702747655697908605 := by
  unfold tailWord_3598498
  simp only [CollatzResearch.WordTrace]
  refine ⟨32812001129315948843683037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87498669678175863583154765 32812001129315948843683037)
  ·
    refine ⟨12304500423493480816381139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32812001129315948843683037 12304500423493480816381139)
    ·
      refine ⟨18456750635240221224571709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12304500423493480816381139 18456750635240221224571709)
      ·
        refine ⟨6921281488215082959214391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18456750635240221224571709 6921281488215082959214391)
        ·
          refine ⟨10381922232322624438821587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6921281488215082959214391 10381922232322624438821587)
          ·
            refine ⟨15572883348483936658232381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10381922232322624438821587 15572883348483936658232381)
            ·
              refine ⟨5839831255681476246837143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15572883348483936658232381 5839831255681476246837143)
              ·
                refine ⟨8759746883522214370255715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5839831255681476246837143 8759746883522214370255715)
                ·
                  refine ⟨13139620325283321555383573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8759746883522214370255715 13139620325283321555383573)
                  ·
                    refine ⟨615919702747655697908605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13139620325283321555383573 615919702747655697908605)
                    ·
                      rfl

theorem cell23_3598498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 3, 1, 1, 6].length) (baseStart_3598498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3598498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3598498 prefixEnd_3598498 := by exact prefixLift 3598498
  have htrace : WordTrace (prefixWord ++ tailWord_3598498) baseStart_3598498 baseEnd_3598498 := by
    simpa [prefixWord, tailWord_3598498, baseEnd_3598498] using wordTrace_append hprefix tailTrace_3598498
  have hstable : (prefixWord ++ tailWord_3598498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3598498).length < 2 ^ (prefixWord ++ tailWord_3598498).sum := by decide
  have hdescent : baseEnd_3598498 < baseStart_3598498 := by decide
  rcases family_descends (prefixWord ++ tailWord_3598498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3598521 : List Nat := [1, 2, 1, 4, 1, 2, 2, 1, 3, 3, 3]
def baseStart_3598521 : Nat := 118140960795 + 3598521 * 2 ^ 59
def prefixEnd_3598521 : Nat := 4983230072969 + 3 ^ 40 * 3598521 * 2
def baseEnd_3598521 : Nat := 1847770918298020503738209

theorem tailTrace_3598521 : CollatzResearch.WordTrace tailWord_3598521 prefixEnd_3598521 1847770918298020503738209 := by
  unfold tailWord_3598521
  simp only [CollatzResearch.WordTrace]
  refine ⟨131248843396180470302819417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87499228930786980201879611 131248843396180470302819417)
  ·
    refine ⟨98436632547135352727114563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131248843396180470302819417 98436632547135352727114563)
    ·
      refine ⟨147654948820703029090671845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98436632547135352727114563 147654948820703029090671845)
      ·
        refine ⟨27685302903881817954500971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 147654948820703029090671845 27685302903881817954500971)
        ·
          refine ⟨41527954355822726931751457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27685302903881817954500971 41527954355822726931751457)
          ·
            refine ⟨31145965766867045198813593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41527954355822726931751457 31145965766867045198813593)
            ·
              refine ⟨23359474325150283899110195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31145965766867045198813593 23359474325150283899110195)
              ·
                refine ⟨35039211487725425848665293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23359474325150283899110195 35039211487725425848665293)
                ·
                  refine ⟨13139704307897034693249485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35039211487725425848665293 13139704307897034693249485)
                  ·
                    refine ⟨4927389115461388009968557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13139704307897034693249485 4927389115461388009968557)
                    ·
                      refine ⟨1847770918298020503738209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4927389115461388009968557 1847770918298020503738209)
                      ·
                        rfl

theorem cell23_3598521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 1, 3, 3, 3].length) (baseStart_3598521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3598521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3598521 prefixEnd_3598521 := by exact prefixLift 3598521
  have htrace : WordTrace (prefixWord ++ tailWord_3598521) baseStart_3598521 baseEnd_3598521 := by
    simpa [prefixWord, tailWord_3598521, baseEnd_3598521] using wordTrace_append hprefix tailTrace_3598521
  have hstable : (prefixWord ++ tailWord_3598521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3598521).length < 2 ^ (prefixWord ++ tailWord_3598521).sum := by decide
  have hdescent : baseEnd_3598521 < baseStart_3598521 := by decide
  rcases family_descends (prefixWord ++ tailWord_3598521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3598522 : List Nat := [3, 1, 1, 1, 2, 2, 5, 3, 1, 2, 2]
def baseStart_3598522 : Nat := 118140960795 + 3598522 * 2 ^ 59
def prefixEnd_3598522 : Nat := 4983230072969 + 3 ^ 40 * 3598522 * 2
def baseEnd_3598522 : Nat := 1847771431778674999825705

theorem tailTrace_3598522 : CollatzResearch.WordTrace tailWord_3598522 prefixEnd_3598522 1847771431778674999825705 := by
  unfold tailWord_3598522
  simp only [CollatzResearch.WordTrace]
  refine ⟨32812219967294211868401455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87499253246117898315737213 32812219967294211868401455)
  ·
    refine ⟨49218329950941317802602183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32812219967294211868401455 49218329950941317802602183)
    ·
      refine ⟨73827494926411976703903275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49218329950941317802602183 73827494926411976703903275)
      ·
        refine ⟨110741242389617965055854913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73827494926411976703903275 110741242389617965055854913)
        ·
          refine ⟨83055931792213473791891185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110741242389617965055854913 83055931792213473791891185)
          ·
            refine ⟨62291948844160105343918389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83055931792213473791891185 62291948844160105343918389)
            ·
              refine ⟨5839870204140009875992349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62291948844160105343918389 5839870204140009875992349)
              ·
                refine ⟨2189951326552503703497131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5839870204140009875992349 2189951326552503703497131)
                ·
                  refine ⟨3284926989828755555245697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2189951326552503703497131 3284926989828755555245697)
                  ·
                    refine ⟨2463695242371566666434273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3284926989828755555245697 2463695242371566666434273)
                    ·
                      refine ⟨1847771431778674999825705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2463695242371566666434273 1847771431778674999825705)
                      ·
                        rfl

theorem cell23_3598522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 5, 3, 1, 2, 2].length) (baseStart_3598522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3598522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3598522 prefixEnd_3598522 := by exact prefixLift 3598522
  have htrace : WordTrace (prefixWord ++ tailWord_3598522) baseStart_3598522 baseEnd_3598522 := by
    simpa [prefixWord, tailWord_3598522, baseEnd_3598522] using wordTrace_append hprefix tailTrace_3598522
  have hstable : (prefixWord ++ tailWord_3598522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3598522).length < 2 ^ (prefixWord ++ tailWord_3598522).sum := by decide
  have hdescent : baseEnd_3598522 < baseStart_3598522 := by decide
  rcases family_descends (prefixWord ++ tailWord_3598522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3598531 : List Nat := [1, 1, 1, 3, 1, 1, 1, 2, 1, 9, 2]
def baseStart_3598531 : Nat := 118140960795 + 3598531 * 2 ^ 59
def prefixEnd_3598531 : Nat := 4983230072969 + 3 ^ 40 * 3598531 * 2
def baseEnd_3598531 : Nat := 1847776053104565464613163

theorem tailTrace_3598531 : CollatzResearch.WordTrace tailWord_3598531 prefixEnd_3598531 1847776053104565464613163 := by
  unfold tailWord_3598531
  simp only [CollatzResearch.WordTrace]
  refine ⟨131249208126144242010683447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87499472084096161340455631 131249208126144242010683447)
  ·
    refine ⟨196873812189216363016025171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131249208126144242010683447 196873812189216363016025171)
    ·
      refine ⟨295310718283824544524037757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196873812189216363016025171 295310718283824544524037757)
      ·
        refine ⟨110741519356434204196514159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 295310718283824544524037757 110741519356434204196514159)
        ·
          refine ⟨166112279034651306294771239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110741519356434204196514159 166112279034651306294771239)
          ·
            refine ⟨249168418551976959442156859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166112279034651306294771239 249168418551976959442156859)
            ·
              refine ⟨373752627827965439163235289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 249168418551976959442156859 373752627827965439163235289)
              ·
                refine ⟨280314470870974079372426467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 373752627827965439163235289 280314470870974079372426467)
                ·
                  refine ⟨420471706306461119058639701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 280314470870974079372426467 420471706306461119058639701)
                  ·
                    refine ⟨2463701404139420619484217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 420471706306461119058639701 2463701404139420619484217)
                    ·
                      refine ⟨1847776053104565464613163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2463701404139420619484217 1847776053104565464613163)
                      ·
                        rfl

theorem cell23_3598531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 9, 2].length) (baseStart_3598531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3598531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3598531 prefixEnd_3598531 := by exact prefixLift 3598531
  have htrace : WordTrace (prefixWord ++ tailWord_3598531) baseStart_3598531 baseEnd_3598531 := by
    simpa [prefixWord, tailWord_3598531, baseEnd_3598531] using wordTrace_append hprefix tailTrace_3598531
  have hstable : (prefixWord ++ tailWord_3598531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3598531).length < 2 ^ (prefixWord ++ tailWord_3598531).sum := by decide
  have hdescent : baseEnd_3598531 < baseStart_3598531 := by decide
  rcases family_descends (prefixWord ++ tailWord_3598531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3598538 : List Nat := [3, 1, 2, 1, 3, 1, 1, 3, 4, 1, 3]
def baseStart_3598538 : Nat := 118140960795 + 3598538 * 2 ^ 59
def prefixEnd_3598538 : Nat := 4983230072969 + 3 ^ 40 * 3598538 * 2
def baseEnd_3598538 : Nat := 1847779647469146937225631

theorem tailTrace_3598538 : CollatzResearch.WordTrace tailWord_3598538 prefixEnd_3598538 1847779647469146937225631 := by
  unfold tailWord_3598538
  simp only [CollatzResearch.WordTrace]
  refine ⟨32812365859279720551547067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87499642291412588137458845 32812365859279720551547067)
  ·
    refine ⟨49218548788919580827320601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32812365859279720551547067 49218548788919580827320601)
    ·
      refine ⟨36913911591689685620490451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49218548788919580827320601 36913911591689685620490451)
      ·
        refine ⟨55370867387534528430735677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36913911591689685620490451 55370867387534528430735677)
        ·
          refine ⟨20764075270325448161525879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55370867387534528430735677 20764075270325448161525879)
          ·
            refine ⟨31146112905488172242288819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20764075270325448161525879 31146112905488172242288819)
            ·
              refine ⟨46719169358232258363433229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31146112905488172242288819 46719169358232258363433229)
              ·
                refine ⟨17519688509337096886287461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46719169358232258363433229 17519688509337096886287461)
                ·
                  refine ⟨3284941595500705666178899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17519688509337096886287461 3284941595500705666178899)
                  ·
                    refine ⟨4927412393251058499268349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3284941595500705666178899 4927412393251058499268349)
                    ·
                      refine ⟨1847779647469146937225631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4927412393251058499268349 1847779647469146937225631)
                      ·
                        rfl

theorem cell23_3598538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 3, 4, 1, 3].length) (baseStart_3598538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3598538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3598538 prefixEnd_3598538 := by exact prefixLift 3598538
  have htrace : WordTrace (prefixWord ++ tailWord_3598538) baseStart_3598538 baseEnd_3598538 := by
    simpa [prefixWord, tailWord_3598538, baseEnd_3598538] using wordTrace_append hprefix tailTrace_3598538
  have hstable : (prefixWord ++ tailWord_3598538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3598538).length < 2 ^ (prefixWord ++ tailWord_3598538).sum := by decide
  have hdescent : baseEnd_3598538 < baseStart_3598538 := by decide
  rcases family_descends (prefixWord ++ tailWord_3598538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3598549 : List Nat := [1, 3, 2, 4, 3, 1, 2, 1, 2, 4]
def baseStart_3598549 : Nat := 118140960795 + 3598549 * 2 ^ 59
def prefixEnd_3598549 : Nat := 4983230072969 + 3 ^ 40 * 3598549 * 2
def baseEnd_3598549 : Nat := 615928431918782131396027

theorem tailTrace_3598549 : CollatzResearch.WordTrace tailWord_3598549 prefixEnd_3598549 615928431918782131396027 := by
  unfold tailWord_3598549
  simp only [CollatzResearch.WordTrace]
  refine ⟨131249864640079031084838701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87499909760052687389892467 131249864640079031084838701)
  ·
    refine ⟨49218699240029636656814513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131249864640079031084838701 49218699240029636656814513)
    ·
      refine ⟨36914024430022227492610885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49218699240029636656814513 36914024430022227492610885)
      ·
        refine ⟨6921379580629167654864541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36914024430022227492610885 6921379580629167654864541)
        ·
          refine ⟨2595517342735937870574203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6921379580629167654864541 2595517342735937870574203)
          ·
            refine ⟨3893276014103906805861305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2595517342735937870574203 3893276014103906805861305)
            ·
              refine ⟨2919957010577930104395979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3893276014103906805861305 2919957010577930104395979)
              ·
                refine ⟨4379935515866895156593969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2919957010577930104395979 4379935515866895156593969)
                ·
                  refine ⟨3284951636900171367445477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4379935515866895156593969 3284951636900171367445477)
                  ·
                    refine ⟨615928431918782131396027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3284951636900171367445477 615928431918782131396027)
                    ·
                      rfl

theorem cell23_3598549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 2, 1, 2, 4].length) (baseStart_3598549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3598549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3598549 prefixEnd_3598549 := by exact prefixLift 3598549
  have htrace : WordTrace (prefixWord ++ tailWord_3598549) baseStart_3598549 baseEnd_3598549 := by
    simpa [prefixWord, tailWord_3598549, baseEnd_3598549] using wordTrace_append hprefix tailTrace_3598549
  have hstable : (prefixWord ++ tailWord_3598549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3598549).length < 2 ^ (prefixWord ++ tailWord_3598549).sum := by decide
  have hdescent : baseEnd_3598549 < baseStart_3598549 := by decide
  rcases family_descends (prefixWord ++ tailWord_3598549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3598565 : List Nat := [1, 3, 1, 4, 2, 2, 1, 1, 3, 3, 2]
def baseStart_3598565 : Nat := 118140960795 + 3598565 * 2 ^ 59
def prefixEnd_3598565 : Nat := 4983230072969 + 3 ^ 40 * 3598565 * 2
def baseEnd_3598565 : Nat := 1847793511446818331588007

theorem tailTrace_3598565 : CollatzResearch.WordTrace tailWord_3598565 prefixEnd_3598565 1847793511446818331588007 := by
  unfold tailWord_3598565
  simp only [CollatzResearch.WordTrace]
  refine ⟨131250448208021065817421149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87500298805347377211614099 131250448208021065817421149)
  ·
    refine ⟨49218918078007899681532931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131250448208021065817421149 49218918078007899681532931)
    ·
      refine ⟨73828377117011849522299397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49218918078007899681532931 73828377117011849522299397)
      ·
        refine ⟨13842820709439721785431137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73828377117011849522299397 13842820709439721785431137)
        ·
          refine ⟨10382115532079791339073353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13842820709439721785431137 10382115532079791339073353)
          ·
            refine ⟨7786586649059843504305015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10382115532079791339073353 7786586649059843504305015)
            ·
              refine ⟨11679879973589765256457523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7786586649059843504305015 11679879973589765256457523)
              ·
                refine ⟨17519819960384647884686285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11679879973589765256457523 17519819960384647884686285)
                ·
                  refine ⟨6569932485144242956757357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17519819960384647884686285 6569932485144242956757357)
                  ·
                    refine ⟨2463724681929091108784009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6569932485144242956757357 2463724681929091108784009)
                    ·
                      refine ⟨1847793511446818331588007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2463724681929091108784009 1847793511446818331588007)
                      ·
                        rfl

theorem cell23_3598565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 1, 3, 3, 2].length) (baseStart_3598565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3598565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3598565 prefixEnd_3598565 := by exact prefixLift 3598565
  have htrace : WordTrace (prefixWord ++ tailWord_3598565) baseStart_3598565 baseEnd_3598565 := by
    simpa [prefixWord, tailWord_3598565, baseEnd_3598565] using wordTrace_append hprefix tailTrace_3598565
  have hstable : (prefixWord ++ tailWord_3598565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3598565).length < 2 ^ (prefixWord ++ tailWord_3598565).sum := by decide
  have hdescent : baseEnd_3598565 < baseStart_3598565 := by decide
  rcases family_descends (prefixWord ++ tailWord_3598565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3598591 : List Nat := [1, 1, 2, 2, 1, 4, 2, 2, 2, 2, 4]
def baseStart_3598591 : Nat := 118140960795 + 3598591 * 2 ^ 59
def prefixEnd_3598591 : Nat := 4983230072969 + 3 ^ 40 * 3598591 * 2
def baseEnd_3598591 : Nat := 1847806861943835229862887

theorem tailTrace_3598591 : CollatzResearch.WordTrace tailWord_3598591 prefixEnd_3598591 1847806861943835229862887 := by
  unfold tailWord_3598591
  simp only [CollatzResearch.WordTrace]
  refine ⟨131251396505926872257867627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87500931003951248171911751 131251396505926872257867627)
  ·
    refine ⟨196877094758890308386801441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131251396505926872257867627 196877094758890308386801441)
    ·
      refine ⟨147657821069167731290101081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196877094758890308386801441 147657821069167731290101081)
      ·
        refine ⟨110743365801875798467575811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147657821069167731290101081 110743365801875798467575811)
        ·
          refine ⟨166115048702813697701363717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110743365801875798467575811 166115048702813697701363717)
          ·
            refine ⟨31146571631777568319005697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 166115048702813697701363717 31146571631777568319005697)
            ·
              refine ⟨23359928723833176239254273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31146571631777568319005697 23359928723833176239254273)
              ·
                refine ⟨17519946542874882179440705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23359928723833176239254273 17519946542874882179440705)
                ·
                  refine ⟨13139959907156161634580529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17519946542874882179440705 13139959907156161634580529)
                  ·
                    refine ⟨9854969930367121225935397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13139959907156161634580529 9854969930367121225935397)
                    ·
                      refine ⟨1847806861943835229862887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9854969930367121225935397 1847806861943835229862887)
                      ·
                        rfl

theorem cell23_3598591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 2, 2, 2, 4].length) (baseStart_3598591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3598591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3598591 prefixEnd_3598591 := by exact prefixLift 3598591
  have htrace : WordTrace (prefixWord ++ tailWord_3598591) baseStart_3598591 baseEnd_3598591 := by
    simpa [prefixWord, tailWord_3598591, baseEnd_3598591] using wordTrace_append hprefix tailTrace_3598591
  have hstable : (prefixWord ++ tailWord_3598591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3598591).length < 2 ^ (prefixWord ++ tailWord_3598591).sum := by decide
  have hdescent : baseEnd_3598591 < baseStart_3598591 := by decide
  rcases family_descends (prefixWord ++ tailWord_3598591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3598618 : List Nat := [3, 1, 1, 3, 4, 1, 1, 2, 7]
def baseStart_3598618 : Nat := 118140960795 + 3598618 * 2 ^ 59
def prefixEnd_3598618 : Nat := 4983230072969 + 3 ^ 40 * 3598618 * 2
def baseEnd_3598618 : Nat := 205313413991278513802807

theorem tailTrace_3598618 : CollatzResearch.WordTrace tailWord_3598618 prefixEnd_3598618 205313413991278513802807 := by
  unfold tailWord_3598618
  simp only [CollatzResearch.WordTrace]
  refine ⟨32813095319207263967275127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87501587517886037246067005 32813095319207263967275127)
  ·
    refine ⟨49219642978810895950912691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32813095319207263967275127 49219642978810895950912691)
    ·
      refine ⟨73829464468216343926369037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49219642978810895950912691 73829464468216343926369037)
      ·
        refine ⟨27686049175581128972388389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73829464468216343926369037 27686049175581128972388389)
        ·
          refine ⟨5191134220421461682322823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27686049175581128972388389 5191134220421461682322823)
          ·
            refine ⟨7786701330632192523484235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5191134220421461682322823 7786701330632192523484235)
            ·
              refine ⟨11680051995948288785226353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7786701330632192523484235 11680051995948288785226353)
              ·
                refine ⟨8760038996961216588919765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11680051995948288785226353 8760038996961216588919765)
                ·
                  refine ⟨205313413991278513802807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8760038996961216588919765 205313413991278513802807)
                  ·
                    rfl

theorem cell23_3598618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 2, 7].length) (baseStart_3598618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3598618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3598618 prefixEnd_3598618 := by exact prefixLift 3598618
  have htrace : WordTrace (prefixWord ++ tailWord_3598618) baseStart_3598618 baseEnd_3598618 := by
    simpa [prefixWord, tailWord_3598618, baseEnd_3598618] using wordTrace_append hprefix tailTrace_3598618
  have hstable : (prefixWord ++ tailWord_3598618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3598618).length < 2 ^ (prefixWord ++ tailWord_3598618).sum := by decide
  have hdescent : baseEnd_3598618 < baseStart_3598618 := by decide
  rcases family_descends (prefixWord ++ tailWord_3598618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3598681 : List Nat := [1, 2, 1, 2, 2, 2, 1, 1, 1, 6, 4]
def baseStart_3598681 : Nat := 118140960795 + 3598681 * 2 ^ 59
def prefixEnd_3598681 : Nat := 4983230072969 + 3 ^ 40 * 3598681 * 2
def baseEnd_3598681 : Nat := 1847853075202739877737473

theorem tailTrace_3598681 : CollatzResearch.WordTrace tailWord_3598681 prefixEnd_3598681 1847853075202739877737473 := by
  unfold tailWord_3598681
  simp only [CollatzResearch.WordTrace]
  refine ⟨131254679075600817628643897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87503119383733878419095931 131254679075600817628643897)
  ·
    refine ⟨98441009306700613221482923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131254679075600817628643897 98441009306700613221482923)
    ·
      refine ⟨147661513960050919832224385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98441009306700613221482923 147661513960050919832224385)
      ·
        refine ⟨110746135470038189874168289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147661513960050919832224385 110746135470038189874168289)
        ·
          refine ⟨83059601602528642405626217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110746135470038189874168289 83059601602528642405626217)
          ·
            refine ⟨62294701201896481804219663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83059601602528642405626217 62294701201896481804219663)
            ·
              refine ⟨93442051802844722706329495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62294701201896481804219663 93442051802844722706329495)
              ·
                refine ⟨140163077704267084059494243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93442051802844722706329495 140163077704267084059494243)
                ·
                  refine ⟨210244616556400626089241365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 140163077704267084059494243 210244616556400626089241365)
                  ·
                    refine ⟨9855216401081279347933189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 210244616556400626089241365 9855216401081279347933189)
                    ·
                      refine ⟨1847853075202739877737473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9855216401081279347933189 1847853075202739877737473)
                      ·
                        rfl

theorem cell23_3598681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 6, 4].length) (baseStart_3598681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3598681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3598681 prefixEnd_3598681 := by exact prefixLift 3598681
  have htrace : WordTrace (prefixWord ++ tailWord_3598681) baseStart_3598681 baseEnd_3598681 := by
    simpa [prefixWord, tailWord_3598681, baseEnd_3598681] using wordTrace_append hprefix tailTrace_3598681
  have hstable : (prefixWord ++ tailWord_3598681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3598681).length < 2 ^ (prefixWord ++ tailWord_3598681).sum := by decide
  have hdescent : baseEnd_3598681 < baseStart_3598681 := by decide
  rcases family_descends (prefixWord ++ tailWord_3598681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3598691 : List Nat := [1, 1, 1, 5, 2, 1, 1, 1, 10]
def baseStart_3598691 : Nat := 118140960795 + 3598691 * 2 ^ 59
def prefixEnd_3598691 : Nat := 4983230072969 + 3 ^ 40 * 3598691 * 2
def baseEnd_3598691 : Nat := 205317578889920537623603

theorem tailTrace_3598691 : CollatzResearch.WordTrace tailWord_3598691 prefixEnd_3598691 205317578889920537623603 := by
  unfold tailWord_3598691
  simp only [CollatzResearch.WordTrace]
  refine ⟨131255043805564589336507927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87503362537043059557671951 131255043805564589336507927)
  ·
    refine ⟨196882565708346884004761891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131255043805564589336507927 196882565708346884004761891)
    ·
      refine ⟨295323848562520326007142837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196882565708346884004761891 295323848562520326007142837)
      ·
        refine ⟨27686610802736280563169641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 295323848562520326007142837 27686610802736280563169641)
        ·
          refine ⟨20764958102052210422377231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27686610802736280563169641 20764958102052210422377231)
          ·
            refine ⟨31147437153078315633565847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20764958102052210422377231 31147437153078315633565847)
            ·
              refine ⟨46721155729617473450348771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31147437153078315633565847 46721155729617473450348771)
              ·
                refine ⟨70081733594426210175523157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46721155729617473450348771 70081733594426210175523157)
                ·
                  refine ⟨205317578889920537623603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 70081733594426210175523157 205317578889920537623603)
                  ·
                    rfl

theorem cell23_3598691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 10].length) (baseStart_3598691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3598691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3598691 prefixEnd_3598691 := by exact prefixLift 3598691
  have htrace : WordTrace (prefixWord ++ tailWord_3598691) baseStart_3598691 baseEnd_3598691 := by
    simpa [prefixWord, tailWord_3598691, baseEnd_3598691] using wordTrace_append hprefix tailTrace_3598691
  have hstable : (prefixWord ++ tailWord_3598691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3598691).length < 2 ^ (prefixWord ++ tailWord_3598691).sum := by decide
  have hdescent : baseEnd_3598691 < baseStart_3598691 := by decide
  rcases family_descends (prefixWord ++ tailWord_3598691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3598711 : List Nat := [1, 1, 3, 1, 1, 2, 2, 3, 1, 2, 6]
def baseStart_3598711 : Nat := 118140960795 + 3598711 * 2 ^ 59
def prefixEnd_3598711 : Nat := 4983230072969 + 3 ^ 40 * 3598711 * 2
def baseEnd_3598711 : Nat := 1847868479622374760362335

theorem tailTrace_3598711 : CollatzResearch.WordTrace tailWord_3598711 prefixEnd_3598711 1847868479622374760362335 := by
  unfold tailWord_3598711
  simp only [CollatzResearch.WordTrace]
  refine ⟨131255773265492132752235987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87503848843661421834823991 131255773265492132752235987)
  ·
    refine ⟨196883659898238199128353981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131255773265492132752235987 196883659898238199128353981)
    ·
      refine ⟨73831372461839324673132743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196883659898238199128353981 73831372461839324673132743)
      ·
        refine ⟨110747058692758987009699115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73831372461839324673132743 110747058692758987009699115)
        ·
          refine ⟨166120588039138480514548673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110747058692758987009699115 166120588039138480514548673)
          ·
            refine ⟨124590441029353860385911505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166120588039138480514548673 124590441029353860385911505)
            ·
              refine ⟨93442830772015395289433629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124590441029353860385911505 93442830772015395289433629)
              ·
                refine ⟨35041061539505773233537611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93442830772015395289433629 35041061539505773233537611)
                ·
                  refine ⟨52561592309258659850306417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35041061539505773233537611 52561592309258659850306417)
                  ·
                    refine ⟨39421194231943994887729813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52561592309258659850306417 39421194231943994887729813)
                    ·
                      refine ⟨1847868479622374760362335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39421194231943994887729813 1847868479622374760362335)
                      ·
                        rfl

theorem cell23_3598711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 3, 1, 2, 6].length) (baseStart_3598711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3598711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3598711 prefixEnd_3598711 := by exact prefixLift 3598711
  have htrace : WordTrace (prefixWord ++ tailWord_3598711) baseStart_3598711 baseEnd_3598711 := by
    simpa [prefixWord, tailWord_3598711, baseEnd_3598711] using wordTrace_append hprefix tailTrace_3598711
  have hstable : (prefixWord ++ tailWord_3598711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3598711).length < 2 ^ (prefixWord ++ tailWord_3598711).sum := by decide
  have hdescent : baseEnd_3598711 < baseStart_3598711 := by decide
  rcases family_descends (prefixWord ++ tailWord_3598711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3598768 : List Nat := [2, 1, 1, 1, 2, 1, 1, 2, 8, 4]
def baseStart_3598768 : Nat := 118140960795 + 3598768 * 2 ^ 59
def prefixEnd_3598768 : Nat := 4983230072969 + 3 ^ 40 * 3598768 * 2
def baseEnd_3598768 : Nat := 615965916006560345783191

theorem tailTrace_3598768 : CollatzResearch.WordTrace tailWord_3598768 prefixEnd_3598768 615965916006560345783191 := by
  unfold tailWord_3598768
  simp only [CollatzResearch.WordTrace]
  refine ⟨65628926113142815743530479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87505234817523754324707305 65628926113142815743530479)
  ·
    refine ⟨98443389169714223615295719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65628926113142815743530479 98443389169714223615295719)
    ·
      refine ⟨147665083754571335422943579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98443389169714223615295719 147665083754571335422943579)
      ·
        refine ⟨221497625631857003134415369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147665083754571335422943579 221497625631857003134415369)
        ·
          refine ⟨166123219223892752350811527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 221497625631857003134415369 166123219223892752350811527)
          ·
            refine ⟨249184828835839128526217291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166123219223892752350811527 249184828835839128526217291)
            ·
              refine ⟨373777243253758692789325937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 249184828835839128526217291 373777243253758692789325937)
              ·
                refine ⟨280332932440319019591994453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 373777243253758692789325937 280332932440319019591994453)
                ·
                  refine ⟨3285151552034988510843685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 280332932440319019591994453 3285151552034988510843685)
                  ·
                    refine ⟨615965916006560345783191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3285151552034988510843685 615965916006560345783191)
                    ·
                      rfl

theorem cell23_3598768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 8, 4].length) (baseStart_3598768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3598768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3598768 prefixEnd_3598768 := by exact prefixLift 3598768
  have htrace : WordTrace (prefixWord ++ tailWord_3598768) baseStart_3598768 baseEnd_3598768 := by
    simpa [prefixWord, tailWord_3598768, baseEnd_3598768] using wordTrace_append hprefix tailTrace_3598768
  have hstable : (prefixWord ++ tailWord_3598768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3598768).length < 2 ^ (prefixWord ++ tailWord_3598768).sum := by decide
  have hdescent : baseEnd_3598768 < baseStart_3598768 := by decide
  rcases family_descends (prefixWord ++ tailWord_3598768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3598769 : List Nat := [1, 2, 2, 4, 1, 3, 1, 4, 1, 1, 3]
def baseStart_3598769 : Nat := 118140960795 + 3598769 * 2 ^ 59
def prefixEnd_3598769 : Nat := 4983230072969 + 3 ^ 40 * 3598769 * 2
def baseEnd_3598769 : Nat := 1847898261500335533437069

theorem tailTrace_3598769 : CollatzResearch.WordTrace tailWord_3598769 prefixEnd_3598769 1847898261500335533437069 := by
  unfold tailWord_3598769
  simp only [CollatzResearch.WordTrace]
  refine ⟨131257888699282008657847361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87505259132854672438564907 131257888699282008657847361)
  ·
    refine ⟨98443416524461506493385521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131257888699282008657847361 98443416524461506493385521)
    ·
      refine ⟨73832562393346129870039141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98443416524461506493385521 73832562393346129870039141)
      ·
        refine ⟨13843605448752399350632339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73832562393346129870039141 13843605448752399350632339)
        ·
          refine ⟨20765408173128599025948509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13843605448752399350632339 20765408173128599025948509)
          ·
            refine ⟨7787028064923224634730691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20765408173128599025948509 7787028064923224634730691)
            ·
              refine ⟨11680542097384836952096037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7787028064923224634730691 11680542097384836952096037)
              ·
                refine ⟨2190101643259656928518007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11680542097384836952096037 2190101643259656928518007)
                ·
                  refine ⟨3285152464889485392777011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2190101643259656928518007 3285152464889485392777011)
                  ·
                    refine ⟨4927728697334228089165517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3285152464889485392777011 4927728697334228089165517)
                    ·
                      refine ⟨1847898261500335533437069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4927728697334228089165517 1847898261500335533437069)
                      ·
                        rfl

theorem cell23_3598769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 4, 1, 1, 3].length) (baseStart_3598769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3598769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3598769 prefixEnd_3598769 := by exact prefixLift 3598769
  have htrace : WordTrace (prefixWord ++ tailWord_3598769) baseStart_3598769 baseEnd_3598769 := by
    simpa [prefixWord, tailWord_3598769, baseEnd_3598769] using wordTrace_append hprefix tailTrace_3598769
  have hstable : (prefixWord ++ tailWord_3598769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3598769).length < 2 ^ (prefixWord ++ tailWord_3598769).sum := by decide
  have hdescent : baseEnd_3598769 < baseStart_3598769 := by decide
  rcases family_descends (prefixWord ++ tailWord_3598769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3598778 : List Nat := [3, 1, 1, 1, 2, 1, 1, 6, 1, 1, 5]
def baseStart_3598778 : Nat := 118140960795 + 3598778 * 2 ^ 59
def prefixEnd_3598778 : Nat := 4983230072969 + 3 ^ 40 * 3598778 * 2
def baseEnd_3598778 : Nat := 1847902882826225998224527

theorem tailTrace_3598778 : CollatzResearch.WordTrace tailWord_3598778 prefixEnd_3598778 1847902882826225998224527 := by
  unfold tailWord_3598778
  simp only [CollatzResearch.WordTrace]
  refine ⟨32814554239062350798731247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87505477970832935463283325 32814554239062350798731247)
  ·
    refine ⟨49221831358593526198096871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32814554239062350798731247 49221831358593526198096871)
    ·
      refine ⟨73832747037890289297145307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49221831358593526198096871 73832747037890289297145307)
      ·
        refine ⟨110749120556835433945717961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73832747037890289297145307 110749120556835433945717961)
        ·
          refine ⟨83061840417626575459288471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110749120556835433945717961 83061840417626575459288471)
          ·
            refine ⟨124592760626439863188932707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83061840417626575459288471 124592760626439863188932707)
            ·
              refine ⟨186889140939659794783399061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124592760626439863188932707 186889140939659794783399061)
              ·
                refine ⟨8760428481546552880471831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 186889140939659794783399061 8760428481546552880471831)
                ·
                  refine ⟨13140642722319829320707747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8760428481546552880471831 13140642722319829320707747)
                  ·
                    refine ⟨19710964083479743981061621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13140642722319829320707747 19710964083479743981061621)
                    ·
                      refine ⟨1847902882826225998224527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19710964083479743981061621 1847902882826225998224527)
                      ·
                        rfl

theorem cell23_3598778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 6, 1, 1, 5].length) (baseStart_3598778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3598778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3598778 prefixEnd_3598778 := by exact prefixLift 3598778
  have htrace : WordTrace (prefixWord ++ tailWord_3598778) baseStart_3598778 baseEnd_3598778 := by
    simpa [prefixWord, tailWord_3598778, baseEnd_3598778] using wordTrace_append hprefix tailTrace_3598778
  have hstable : (prefixWord ++ tailWord_3598778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3598778).length < 2 ^ (prefixWord ++ tailWord_3598778).sum := by decide
  have hdescent : baseEnd_3598778 < baseStart_3598778 := by decide
  rcases family_descends (prefixWord ++ tailWord_3598778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3598792 : List Nat := [2, 1, 3, 1, 3, 2, 1, 1, 5, 2, 2]
def baseStart_3598792 : Nat := 118140960795 + 3598792 * 2 ^ 59
def prefixEnd_3598792 : Nat := 4983230072969 + 3 ^ 40 * 3598792 * 2
def baseEnd_3598792 : Nat := 1847910071555388943449463

theorem tailTrace_3598792 : CollatzResearch.WordTrace tailWord_3598792 prefixEnd_3598792 1847910071555388943449463 := by
  unfold tailWord_3598792
  simp only [CollatzResearch.WordTrace]
  refine ⟨65629363789099341792967315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87505818385465789057289753 65629363789099341792967315)
  ·
    refine ⟨98444045683649012689450973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65629363789099341792967315 98444045683649012689450973)
    ·
      refine ⟨36916517131368379758544115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98444045683649012689450973 36916517131368379758544115)
      ·
        refine ⟨55374775697052569637816173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36916517131368379758544115 55374775697052569637816173)
        ·
          refine ⟨20765540886394713614181065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55374775697052569637816173 20765540886394713614181065)
          ·
            refine ⟨15574155664796035210635799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20765540886394713614181065 15574155664796035210635799)
            ·
              refine ⟨23361233497194052815953699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15574155664796035210635799 23361233497194052815953699)
              ·
                refine ⟨35041850245791079223930549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23361233497194052815953699 35041850245791079223930549)
                ·
                  refine ⟨3285173460542913677243489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35041850245791079223930549 3285173460542913677243489)
                  ·
                    refine ⟨2463880095407185257932617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3285173460542913677243489 2463880095407185257932617)
                    ·
                      refine ⟨1847910071555388943449463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2463880095407185257932617 1847910071555388943449463)
                      ·
                        rfl

theorem cell23_3598792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 1, 5, 2, 2].length) (baseStart_3598792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3598792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3598792 prefixEnd_3598792 := by exact prefixLift 3598792
  have htrace : WordTrace (prefixWord ++ tailWord_3598792) baseStart_3598792 baseEnd_3598792 := by
    simpa [prefixWord, tailWord_3598792, baseEnd_3598792] using wordTrace_append hprefix tailTrace_3598792
  have hstable : (prefixWord ++ tailWord_3598792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3598792).length < 2 ^ (prefixWord ++ tailWord_3598792).sum := by decide
  have hdescent : baseEnd_3598792 < baseStart_3598792 := by decide
  rcases family_descends (prefixWord ++ tailWord_3598792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3598795 : List Nat := [1, 1, 1, 1, 3, 3, 1, 6, 1, 2, 3]
def baseStart_3598795 : Nat := 118140960795 + 3598795 * 2 ^ 59
def prefixEnd_3598795 : Nat := 4983230072969 + 3 ^ 40 * 3598795 * 2
def baseEnd_3598795 : Nat := 1847911611997352431711949

theorem tailTrace_3598795 : CollatzResearch.WordTrace tailWord_3598795 prefixEnd_3598795 1847911611997352431711949 := by
  unfold tailWord_3598795
  simp only [CollatzResearch.WordTrace]
  refine ⟨131258836997187815098293839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87505891331458543398862559 131258836997187815098293839)
  ·
    refine ⟨196888255495781722647440759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131258836997187815098293839 196888255495781722647440759)
    ·
      refine ⟨295332383243672583971161139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196888255495781722647440759 295332383243672583971161139)
      ·
        refine ⟨442998574865508875956741709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295332383243672583971161139 442998574865508875956741709)
        ·
          refine ⟨166124465574565828483778141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 442998574865508875956741709 166124465574565828483778141)
          ·
            refine ⟨62296674590462185681416803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 166124465574565828483778141 62296674590462185681416803)
            ·
              refine ⟨93445011885693278522125205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62296674590462185681416803 93445011885693278522125205)
              ·
                refine ⟨4380234932141872430724619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 93445011885693278522125205 4380234932141872430724619)
                ·
                  refine ⟨6570352398212808646086929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4380234932141872430724619 6570352398212808646086929)
                  ·
                    refine ⟨4927764298659606484565197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6570352398212808646086929 4927764298659606484565197)
                    ·
                      refine ⟨1847911611997352431711949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4927764298659606484565197 1847911611997352431711949)
                      ·
                        rfl

theorem cell23_3598795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 6, 1, 2, 3].length) (baseStart_3598795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3598795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3598795 prefixEnd_3598795 := by exact prefixLift 3598795
  have htrace : WordTrace (prefixWord ++ tailWord_3598795) baseStart_3598795 baseEnd_3598795 := by
    simpa [prefixWord, tailWord_3598795, baseEnd_3598795] using wordTrace_append hprefix tailTrace_3598795
  have hstable : (prefixWord ++ tailWord_3598795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3598795).length < 2 ^ (prefixWord ++ tailWord_3598795).sum := by decide
  have hdescent : baseEnd_3598795 < baseStart_3598795 := by decide
  rcases family_descends (prefixWord ++ tailWord_3598795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3598796 : List Nat := [2, 2, 1, 4, 4, 1, 1, 1, 2, 3, 2]
def baseStart_3598796 : Nat := 118140960795 + 3598796 * 2 ^ 59
def prefixEnd_3598796 : Nat := 4983230072969 + 3 ^ 40 * 3598796 * 2
def baseEnd_3598796 : Nat := 1847912125478006927799445

theorem tailTrace_3598796 : CollatzResearch.WordTrace tailWord_3598796 prefixEnd_3598796 1847912125478006927799445 := by
  unfold tailWord_3598796
  simp only [CollatzResearch.WordTrace]
  refine ⟨65629436735092096134540121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87505915646789461512720161 65629436735092096134540121)
  ·
    refine ⟨49222077551319072100905091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65629436735092096134540121 49222077551319072100905091)
    ·
      refine ⟨73833116326978608151357637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49222077551319072100905091 73833116326978608151357637)
      ·
        refine ⟨13843709311308489028379557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73833116326978608151357637 13843709311308489028379557)
        ·
          refine ⟨2595695495870341692821167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13843709311308489028379557 2595695495870341692821167)
          ·
            refine ⟨3893543243805512539231751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2595695495870341692821167 3893543243805512539231751)
            ·
              refine ⟨5840314865708268808847627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3893543243805512539231751 5840314865708268808847627)
              ·
                refine ⟨8760472298562403213271441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5840314865708268808847627 8760472298562403213271441)
                ·
                  refine ⟨6570354223921802409953581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8760472298562403213271441 6570354223921802409953581)
                  ·
                    refine ⟨2463882833970675903732593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6570354223921802409953581 2463882833970675903732593)
                    ·
                      refine ⟨1847912125478006927799445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2463882833970675903732593 1847912125478006927799445)
                      ·
                        rfl

theorem cell23_3598796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 1, 1, 2, 3, 2].length) (baseStart_3598796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3598796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3598796 prefixEnd_3598796 := by exact prefixLift 3598796
  have htrace : WordTrace (prefixWord ++ tailWord_3598796) baseStart_3598796 baseEnd_3598796 := by
    simpa [prefixWord, tailWord_3598796, baseEnd_3598796] using wordTrace_append hprefix tailTrace_3598796
  have hstable : (prefixWord ++ tailWord_3598796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3598796).length < 2 ^ (prefixWord ++ tailWord_3598796).sum := by decide
  have hdescent : baseEnd_3598796 < baseStart_3598796 := by decide
  rcases family_descends (prefixWord ++ tailWord_3598796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3598805 : List Nat := [1, 3, 2, 3, 1, 2, 2, 2, 1, 2, 4]
def baseStart_3598805 : Nat := 118140960795 + 3598805 * 2 ^ 59
def prefixEnd_3598805 : Nat := 4983230072969 + 3 ^ 40 * 3598805 * 2
def baseEnd_3598805 : Nat := 1847916746803897392586903

theorem tailTrace_3598805 : CollatzResearch.WordTrace tailWord_3598805 prefixEnd_3598805 1847916746803897392586903 := by
  unfold tailWord_3598805
  simp only [CollatzResearch.WordTrace]
  refine ⟨131259201727151586806157869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87506134484767724537438579 131259201727151586806157869)
  ·
    refine ⟨49222200647681845052309201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131259201727151586806157869 49222200647681845052309201)
    ·
      refine ⟨36916650485761383789231901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49222200647681845052309201 36916650485761383789231901)
      ·
        refine ⟨13843743932160518920961963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36916650485761383789231901 13843743932160518920961963)
        ·
          refine ⟨20765615898240778381442945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13843743932160518920961963 20765615898240778381442945)
          ·
            refine ⟨15574211923680583786082209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20765615898240778381442945 15574211923680583786082209)
            ·
              refine ⟨11680658942760437839561657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15574211923680583786082209 11680658942760437839561657)
              ·
                refine ⟨8760494207070328379671243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11680658942760437839561657 8760494207070328379671243)
                ·
                  refine ⟨13140741310605492569506865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8760494207070328379671243 13140741310605492569506865)
                  ·
                    refine ⟨9855555982954119427130149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13140741310605492569506865 9855555982954119427130149)
                    ·
                      refine ⟨1847916746803897392586903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9855555982954119427130149 1847916746803897392586903)
                      ·
                        rfl

theorem cell23_3598805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_3598805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3598805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3598805 prefixEnd_3598805 := by exact prefixLift 3598805
  have htrace : WordTrace (prefixWord ++ tailWord_3598805) baseStart_3598805 baseEnd_3598805 := by
    simpa [prefixWord, tailWord_3598805, baseEnd_3598805] using wordTrace_append hprefix tailTrace_3598805
  have hstable : (prefixWord ++ tailWord_3598805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3598805).length < 2 ^ (prefixWord ++ tailWord_3598805).sum := by decide
  have hdescent : baseEnd_3598805 < baseStart_3598805 := by decide
  rcases family_descends (prefixWord ++ tailWord_3598805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3598819 : List Nat := [1, 1, 1, 6, 3, 2, 1, 2, 2, 4]
def baseStart_3598819 : Nat := 118140960795 + 3598819 * 2 ^ 59
def prefixEnd_3598819 : Nat := 4983230072969 + 3 ^ 40 * 3598819 * 2
def baseEnd_3598819 : Nat := 615974645177686779270613

theorem tailTrace_3598819 : CollatzResearch.WordTrace tailWord_3598819 prefixEnd_3598819 615974645177686779270613 := by
  unfold tailWord_3598819
  simp only [CollatzResearch.WordTrace]
  refine ⟨131259712349100867197167511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87506474899400578131445007 131259712349100867197167511)
  ·
    refine ⟨196889568523651300795751267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131259712349100867197167511 196889568523651300795751267)
    ·
      refine ⟨295334352785476951193626901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196889568523651300795751267 295334352785476951193626901)
      ·
        refine ⟨13843797786819232087201261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 295334352785476951193626901 13843797786819232087201261)
        ·
          refine ⟨5191424170057212032700473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13843797786819232087201261 5191424170057212032700473)
          ·
            refine ⟨3893568127542909024525355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5191424170057212032700473 3893568127542909024525355)
            ·
              refine ⟨5840352191314363536788033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3893568127542909024525355 5840352191314363536788033)
              ·
                refine ⟨4380264143485772652591025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5840352191314363536788033 4380264143485772652591025)
                ·
                  refine ⟨3285198107614329489443269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4380264143485772652591025 3285198107614329489443269)
                  ·
                    refine ⟨615974645177686779270613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3285198107614329489443269 615974645177686779270613)
                    ·
                      rfl

theorem cell23_3598819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 1, 2, 2, 4].length) (baseStart_3598819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3598819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3598819 prefixEnd_3598819 := by exact prefixLift 3598819
  have htrace : WordTrace (prefixWord ++ tailWord_3598819) baseStart_3598819 baseEnd_3598819 := by
    simpa [prefixWord, tailWord_3598819, baseEnd_3598819] using wordTrace_append hprefix tailTrace_3598819
  have hstable : (prefixWord ++ tailWord_3598819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3598819).length < 2 ^ (prefixWord ++ tailWord_3598819).sum := by decide
  have hdescent : baseEnd_3598819 < baseStart_3598819 := by decide
  rcases family_descends (prefixWord ++ tailWord_3598819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3598826 : List Nat := [3, 1, 3, 1, 3, 1, 2, 4, 1, 2, 2]
def baseStart_3598826 : Nat := 118140960795 + 3598826 * 2 ^ 59
def prefixEnd_3598826 : Nat := 4983230072969 + 3 ^ 40 * 3598826 * 2
def baseEnd_3598826 : Nat := 1847927529897641810424307

theorem tailTrace_3598826 : CollatzResearch.WordTrace tailWord_3598826 prefixEnd_3598826 1847927529897641810424307 := by
  unfold tailWord_3598826
  simp only [CollatzResearch.WordTrace]
  refine ⟨32814991915018876848168083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87506645106717004928448221 32814991915018876848168083)
  ·
    refine ⟨49222487872528315272252125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32814991915018876848168083 49222487872528315272252125)
    ·
      refine ⟨18458432952198118227094547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49222487872528315272252125 18458432952198118227094547)
      ·
        refine ⟨27687649428297177340641821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18458432952198118227094547 27687649428297177340641821)
        ·
          refine ⟨10382868535611441502740683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27687649428297177340641821 10382868535611441502740683)
          ·
            refine ⟨15574302803417162254111025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10382868535611441502740683 15574302803417162254111025)
            ·
              refine ⟨11680727102562871690583269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15574302803417162254111025 11680727102562871690583269)
              ·
                refine ⟨2190136331730538441984363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11680727102562871690583269 2190136331730538441984363)
                ·
                  refine ⟨3285204497595807662976545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2190136331730538441984363 3285204497595807662976545)
                  ·
                    refine ⟨2463903373196855747232409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3285204497595807662976545 2463903373196855747232409)
                    ·
                      refine ⟨1847927529897641810424307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2463903373196855747232409 1847927529897641810424307)
                      ·
                        rfl

theorem cell23_3598826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 4, 1, 2, 2].length) (baseStart_3598826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3598826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3598826 prefixEnd_3598826 := by exact prefixLift 3598826
  have htrace : WordTrace (prefixWord ++ tailWord_3598826) baseStart_3598826 baseEnd_3598826 := by
    simpa [prefixWord, tailWord_3598826, baseEnd_3598826] using wordTrace_append hprefix tailTrace_3598826
  have hstable : (prefixWord ++ tailWord_3598826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3598826).length < 2 ^ (prefixWord ++ tailWord_3598826).sum := by decide
  have hdescent : baseEnd_3598826 < baseStart_3598826 := by decide
  rcases family_descends (prefixWord ++ tailWord_3598826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3598899 : List Nat := [1, 1, 1, 2, 4, 2, 3, 3, 2, 2, 2]
def baseStart_3598899 : Nat := 118140960795 + 3598899 * 2 ^ 59
def prefixEnd_3598899 : Nat := 4983230072969 + 3 ^ 40 * 3598899 * 2
def baseEnd_3598899 : Nat := 1847965013985420024811471

theorem tailTrace_3598899 : CollatzResearch.WordTrace tailWord_3598899 prefixEnd_3598899 1847965013985420024811471 := by
  unfold tailWord_3598899
  simp only [CollatzResearch.WordTrace]
  refine ⟨131262630188811040860079751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87508420125874027240053167 131262630188811040860079751)
  ·
    refine ⟨196893945283216561290119627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131262630188811040860079751 196893945283216561290119627)
    ·
      refine ⟨295340917924824841935179441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196893945283216561290119627 295340917924824841935179441)
      ·
        refine ⟨221505688443618631451384581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 295340917924824841935179441 221505688443618631451384581)
        ·
          refine ⟨41532316583178493397134609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 221505688443618631451384581 41532316583178493397134609)
          ·
            refine ⟨31149237437383870047850957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41532316583178493397134609 31149237437383870047850957)
            ·
              refine ⟨11680964039018951267944109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31149237437383870047850957 11680964039018951267944109)
              ·
                refine ⟨4380361514632106725479041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11680964039018951267944109 4380361514632106725479041)
                ·
                  refine ⟨3285271135974080044109281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4380361514632106725479041 3285271135974080044109281)
                  ·
                    refine ⟨2463953351980560033081961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3285271135974080044109281 2463953351980560033081961)
                    ·
                      refine ⟨1847965013985420024811471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2463953351980560033081961 1847965013985420024811471)
                      ·
                        rfl

theorem cell23_3598899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 3, 2, 2, 2].length) (baseStart_3598899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3598899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3598899 prefixEnd_3598899 := by exact prefixLift 3598899
  have htrace : WordTrace (prefixWord ++ tailWord_3598899) baseStart_3598899 baseEnd_3598899 := by
    simpa [prefixWord, tailWord_3598899, baseEnd_3598899] using wordTrace_append hprefix tailTrace_3598899
  have hstable : (prefixWord ++ tailWord_3598899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3598899).length < 2 ^ (prefixWord ++ tailWord_3598899).sum := by decide
  have hdescent : baseEnd_3598899 < baseStart_3598899 := by decide
  rcases family_descends (prefixWord ++ tailWord_3598899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3598902 : List Nat := [5, 1, 2, 1, 2, 1, 1, 2, 2, 1, 5]
def baseStart_3598902 : Nat := 118140960795 + 3598902 * 2 ^ 59
def prefixEnd_3598902 : Nat := 4983230072969 + 3 ^ 40 * 3598902 * 2
def baseEnd_3598902 : Nat := 1847966554427383513073957

theorem tailTrace_3598902 : CollatzResearch.WordTrace tailWord_3598902 prefixEnd_3598902 1847966554427383513073957 := by
  unfold tailWord_3598902
  simp only [CollatzResearch.WordTrace]
  refine ⟨8203921225487510773277435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 87508493071866781581625973 8203921225487510773277435)
  ·
    refine ⟨12305881838231266159916153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8203921225487510773277435 12305881838231266159916153)
    ·
      refine ⟨9229411378673449619937115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12305881838231266159916153 9229411378673449619937115)
      ·
        refine ⟨13844117068010174429905673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9229411378673449619937115 13844117068010174429905673)
        ·
          refine ⟨10383087801007630822429255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13844117068010174429905673 10383087801007630822429255)
          ·
            refine ⟨15574631701511446233643883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10383087801007630822429255 15574631701511446233643883)
            ·
              refine ⟨23361947552267169350465825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15574631701511446233643883 23361947552267169350465825)
              ·
                refine ⟨17521460664200377012849369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23361947552267169350465825 17521460664200377012849369)
                ·
                  refine ⟨13141095498150282759637027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17521460664200377012849369 13141095498150282759637027)
                  ·
                    refine ⟨19711643247225424139455541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13141095498150282759637027 19711643247225424139455541)
                    ·
                      refine ⟨1847966554427383513073957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19711643247225424139455541 1847966554427383513073957)
                      ·
                        rfl

theorem cell23_3598902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_3598902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3598902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3598902 prefixEnd_3598902 := by exact prefixLift 3598902
  have htrace : WordTrace (prefixWord ++ tailWord_3598902) baseStart_3598902 baseEnd_3598902 := by
    simpa [prefixWord, tailWord_3598902, baseEnd_3598902] using wordTrace_append hprefix tailTrace_3598902
  have hstable : (prefixWord ++ tailWord_3598902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3598902).length < 2 ^ (prefixWord ++ tailWord_3598902).sum := by decide
  have hdescent : baseEnd_3598902 < baseStart_3598902 := by decide
  rcases family_descends (prefixWord ++ tailWord_3598902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3598935 : List Nat := [1, 1, 3, 2, 2, 2, 1, 4, 2, 5]
def baseStart_3598935 : Nat := 118140960795 + 3598935 * 2 ^ 59
def prefixEnd_3598935 : Nat := 4983230072969 + 3 ^ 40 * 3598935 * 2
def baseEnd_3598935 : Nat := 615994499762993961320435

theorem tailTrace_3598935 : CollatzResearch.WordTrace tailWord_3598935 prefixEnd_3598935 615994499762993961320435 := by
  unfold tailWord_3598935
  simp only [CollatzResearch.WordTrace]
  refine ⟨131263943216680619008390259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87509295477787079338926839 131263943216680619008390259)
  ·
    refine ⟨196895914825020928512585389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131263943216680619008390259 196895914825020928512585389)
    ·
      refine ⟨73835968059382848192219521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196895914825020928512585389 73835968059382848192219521)
      ·
        refine ⟨55376976044537136144164641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73835968059382848192219521 55376976044537136144164641)
        ·
          refine ⟨41532732033402852108123481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55376976044537136144164641 41532732033402852108123481)
          ·
            refine ⟨31149549025052139081092611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41532732033402852108123481 31149549025052139081092611)
            ·
              refine ⟨46724323537578208621638917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31149549025052139081092611 46724323537578208621638917)
              ·
                refine ⟨8760810663295914116557297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46724323537578208621638917 8760810663295914116557297)
                ·
                  refine ⟨6570607997471935587417973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8760810663295914116557297 6570607997471935587417973)
                  ·
                    refine ⟨615994499762993961320435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6570607997471935587417973 615994499762993961320435)
                    ·
                      rfl

theorem cell23_3598935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 4, 2, 5].length) (baseStart_3598935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3598935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3598935 prefixEnd_3598935 := by exact prefixLift 3598935
  have htrace : WordTrace (prefixWord ++ tailWord_3598935) baseStart_3598935 baseEnd_3598935 := by
    simpa [prefixWord, tailWord_3598935, baseEnd_3598935] using wordTrace_append hprefix tailTrace_3598935
  have hstable : (prefixWord ++ tailWord_3598935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3598935).length < 2 ^ (prefixWord ++ tailWord_3598935).sum := by decide
  have hdescent : baseEnd_3598935 < baseStart_3598935 := by decide
  rcases family_descends (prefixWord ++ tailWord_3598935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3598945 : List Nat := [1, 2, 3, 1, 1, 4, 2, 1, 1, 2, 5]
def baseStart_3598945 : Nat := 118140960795 + 3598945 * 2 ^ 59
def prefixEnd_3598945 : Nat := 4983230072969 + 3 ^ 40 * 3598945 * 2
def baseEnd_3598945 : Nat := 1847988634095526844836259

theorem tailTrace_3598945 : CollatzResearch.WordTrace tailWord_3598945 prefixEnd_3598945 1847988634095526844836259 := by
  unfold tailWord_3598945
  simp only [CollatzResearch.WordTrace]
  refine ⟨131264307946644390716254289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87509538631096260477502859 131264307946644390716254289)
  ·
    refine ⟨98448230959983293037190717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131264307946644390716254289 98448230959983293037190717)
    ·
      refine ⟨36918086609993734888946519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98448230959983293037190717 36918086609993734888946519)
      ·
        refine ⟨55377129914990602333419779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36918086609993734888946519 55377129914990602333419779)
        ·
          refine ⟨83065694872485903500129669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55377129914990602333419779 83065694872485903500129669)
          ·
            refine ⟨15574817788591106906274313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83065694872485903500129669 15574817788591106906274313)
            ·
              refine ⟨11681113341443330179705735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15574817788591106906274313 11681113341443330179705735)
              ·
                refine ⟨17521670012164995269558603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11681113341443330179705735 17521670012164995269558603)
                ·
                  refine ⟨26282505018247492904337905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17521670012164995269558603 26282505018247492904337905)
                  ·
                    refine ⟨19711878763685619678253429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26282505018247492904337905 19711878763685619678253429)
                    ·
                      refine ⟨1847988634095526844836259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19711878763685619678253429 1847988634095526844836259)
                      ·
                        rfl

theorem cell23_3598945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 1, 1, 2, 5].length) (baseStart_3598945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3598945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3598945 prefixEnd_3598945 := by exact prefixLift 3598945
  have htrace : WordTrace (prefixWord ++ tailWord_3598945) baseStart_3598945 baseEnd_3598945 := by
    simpa [prefixWord, tailWord_3598945, baseEnd_3598945] using wordTrace_append hprefix tailTrace_3598945
  have hstable : (prefixWord ++ tailWord_3598945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3598945).length < 2 ^ (prefixWord ++ tailWord_3598945).sum := by decide
  have hdescent : baseEnd_3598945 < baseStart_3598945 := by decide
  rcases family_descends (prefixWord ++ tailWord_3598945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3598972 : List Nat := [2, 2, 2, 1, 1, 2, 5, 1, 2, 1, 4]
def baseStart_3598972 : Nat := 118140960795 + 3598972 * 2 ^ 59
def prefixEnd_3598972 : Nat := 4983230072969 + 3 ^ 40 * 3598972 * 2
def baseEnd_3598972 : Nat := 1848002498073198239198635

theorem tailTrace_3598972 : CollatzResearch.WordTrace tailWord_3598972 prefixEnd_3598972 1848002498073198239198635 := by
  unfold tailWord_3598972
  simp only [CollatzResearch.WordTrace]
  refine ⟨65632646358773287163743585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87510195145031049551658113 65632646358773287163743585)
  ·
    refine ⟨49224484769079965372807689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65632646358773287163743585 49224484769079965372807689)
    ·
      refine ⟨36918363576809974029605767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49224484769079965372807689 36918363576809974029605767)
      ·
        refine ⟨55377545365214961044408651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36918363576809974029605767 55377545365214961044408651)
        ·
          refine ⟨83066318047822441566612977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55377545365214961044408651 83066318047822441566612977)
          ·
            refine ⟨62299738535866831174959733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83066318047822441566612977 62299738535866831174959733)
            ·
              refine ⟨5840600487737515422652475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62299738535866831174959733 5840600487737515422652475)
              ·
                refine ⟨8760900731606273133978713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5840600487737515422652475 8760900731606273133978713)
                ·
                  refine ⟨6570675548704704850484035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8760900731606273133978713 6570675548704704850484035)
                  ·
                    refine ⟨9856013323057057275726053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6570675548704704850484035 9856013323057057275726053)
                    ·
                      refine ⟨1848002498073198239198635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9856013323057057275726053 1848002498073198239198635)
                      ·
                        rfl

theorem cell23_3598972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 5, 1, 2, 1, 4].length) (baseStart_3598972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3598972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3598972 prefixEnd_3598972 := by exact prefixLift 3598972
  have htrace : WordTrace (prefixWord ++ tailWord_3598972) baseStart_3598972 baseEnd_3598972 := by
    simpa [prefixWord, tailWord_3598972, baseEnd_3598972] using wordTrace_append hprefix tailTrace_3598972
  have hstable : (prefixWord ++ tailWord_3598972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3598972).length < 2 ^ (prefixWord ++ tailWord_3598972).sum := by decide
  have hdescent : baseEnd_3598972 < baseStart_3598972 := by decide
  rcases family_descends (prefixWord ++ tailWord_3598972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3598999 : List Nat := [1, 1, 3, 3, 2, 1, 1, 6, 1, 4]
def baseStart_3598999 : Nat := 118140960795 + 3598999 * 2 ^ 59
def prefixEnd_3598999 : Nat := 4983230072969 + 3 ^ 40 * 3598999 * 2
def baseEnd_3598999 : Nat := 616005454016956544520337

theorem tailTrace_3598999 : CollatzResearch.WordTrace tailWord_3598999 prefixEnd_3598999 616005454016956544520337 := by
  unfold tailWord_3598999
  simp only [CollatzResearch.WordTrace]
  refine ⟨131266277488448757938720051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87510851658965838625813367 131266277488448757938720051)
  ·
    refine ⟨196899416232673136908080077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131266277488448757938720051 196899416232673136908080077)
    ·
      refine ⟨73837281087252426340530029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196899416232673136908080077 73837281087252426340530029)
      ·
        refine ⟨27688980407719659877698761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73837281087252426340530029 27688980407719659877698761)
        ·
          refine ⟨20766735305789744908274071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27688980407719659877698761 20766735305789744908274071)
          ·
            refine ⟨31150102958684617362411107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20766735305789744908274071 31150102958684617362411107)
            ·
              refine ⟨46725154438026926043616661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31150102958684617362411107 46725154438026926043616661)
              ·
                refine ⟨2190241614282512158294531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 46725154438026926043616661 2190241614282512158294531)
                ·
                  refine ⟨3285362421423768237441797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2190241614282512158294531 3285362421423768237441797)
                  ·
                    refine ⟨616005454016956544520337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3285362421423768237441797 616005454016956544520337)
                    ·
                      rfl

theorem cell23_3598999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 6, 1, 4].length) (baseStart_3598999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3598999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3598999 prefixEnd_3598999 := by exact prefixLift 3598999
  have htrace : WordTrace (prefixWord ++ tailWord_3598999) baseStart_3598999 baseEnd_3598999 := by
    simpa [prefixWord, tailWord_3598999, baseEnd_3598999] using wordTrace_append hprefix tailTrace_3598999
  have hstable : (prefixWord ++ tailWord_3598999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3598999).length < 2 ^ (prefixWord ++ tailWord_3598999).sum := by decide
  have hdescent : baseEnd_3598999 < baseStart_3598999 := by decide
  rcases family_descends (prefixWord ++ tailWord_3598999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3599102 : List Nat := [4, 2, 2, 1, 2, 12]
def baseStart_3599102 : Nat := 118140960795 + 3599102 * 2 ^ 59
def prefixEnd_3599102 : Nat := 4983230072969 + 3 ^ 40 * 3599102 * 2
def baseEnd_3599102 : Nat := 7605223253326266380959

theorem tailTrace_3599102 : CollatzResearch.WordTrace tailWord_3599102 prefixEnd_3599102 7605223253326266380959 := by
  unfold tailWord_3599102
  simp only [CollatzResearch.WordTrace]
  refine ⟨16408754275884450816214945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87513356138050404353146373 16408754275884450816214945)
  ·
    refine ⟨12306565706913338112161209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16408754275884450816214945 12306565706913338112161209)
    ·
      refine ⟨9229924280185003584120907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12306565706913338112161209 9229924280185003584120907)
      ·
        refine ⟨13844886420277505376181361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9229924280185003584120907 13844886420277505376181361)
        ·
          refine ⟨10383664815208129032136021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13844886420277505376181361 10383664815208129032136021)
          ·
            refine ⟨7605223253326266380959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 10383664815208129032136021 7605223253326266380959)
            ·
              rfl

theorem cell23_3599102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 12].length) (baseStart_3599102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3599102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3599102 prefixEnd_3599102 := by exact prefixLift 3599102
  have htrace : WordTrace (prefixWord ++ tailWord_3599102) baseStart_3599102 baseEnd_3599102 := by
    simpa [prefixWord, tailWord_3599102, baseEnd_3599102] using wordTrace_append hprefix tailTrace_3599102
  have hstable : (prefixWord ++ tailWord_3599102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3599102).length < 2 ^ (prefixWord ++ tailWord_3599102).sum := by decide
  have hdescent : baseEnd_3599102 < baseStart_3599102 := by decide
  rcases family_descends (prefixWord ++ tailWord_3599102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3599106 : List Nat := [3, 4, 1, 1, 1, 2, 1, 4, 2, 4]
def baseStart_3599106 : Nat := 118140960795 + 3599106 * 2 ^ 59
def prefixEnd_3599106 : Nat := 4983230072969 + 3 ^ 40 * 3599106 * 2
def baseEnd_3599106 : Nat := 616023768160300238307673

theorem tailTrace_3599106 : CollatzResearch.WordTrace tailWord_3599106 prefixEnd_3599106 616023768160300238307673 := by
  unfold tailWord_3599106
  simp only [CollatzResearch.WordTrace]
  refine ⟨32817545024765278803216293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87513453399374076808576781 32817545024765278803216293)
  ·
    refine ⟨6153289692143489775603055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32817545024765278803216293 6153289692143489775603055)
    ·
      refine ⟨9229934538215234663404583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6153289692143489775603055 9229934538215234663404583)
      ·
        refine ⟨13844901807322851995106875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9229934538215234663404583 13844901807322851995106875)
        ·
          refine ⟨20767352710984277992660313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13844901807322851995106875 20767352710984277992660313)
          ·
            refine ⟨15575514533238208494495235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20767352710984277992660313 15575514533238208494495235)
            ·
              refine ⟨23363271799857312741742853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15575514533238208494495235 23363271799857312741742853)
              ·
                refine ⟨4380613462473246139076785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23363271799857312741742853 4380613462473246139076785)
                ·
                  refine ⟨3285460096854934604307589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4380613462473246139076785 3285460096854934604307589)
                  ·
                    refine ⟨616023768160300238307673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3285460096854934604307589 616023768160300238307673)
                    ·
                      rfl

theorem cell23_3599106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 4, 2, 4].length) (baseStart_3599106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3599106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3599106 prefixEnd_3599106 := by exact prefixLift 3599106
  have htrace : WordTrace (prefixWord ++ tailWord_3599106) baseStart_3599106 baseEnd_3599106 := by
    simpa [prefixWord, tailWord_3599106, baseEnd_3599106] using wordTrace_append hprefix tailTrace_3599106
  have hstable : (prefixWord ++ tailWord_3599106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3599106).length < 2 ^ (prefixWord ++ tailWord_3599106).sum := by decide
  have hdescent : baseEnd_3599106 < baseStart_3599106 := by decide
  rcases family_descends (prefixWord ++ tailWord_3599106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3599150 : List Nat := [4, 1, 3, 2, 1, 3, 2, 1, 1, 2, 3]
def baseStart_3599150 : Nat := 118140960795 + 3599150 * 2 ^ 59
def prefixEnd_3599150 : Nat := 4983230072969 + 3 ^ 40 * 3599150 * 2
def baseEnd_3599150 : Nat := 1848093897629698542772817

theorem tailTrace_3599150 : CollatzResearch.WordTrace tailWord_3599150 prefixEnd_3599150 1848093897629698542772817 := by
  unfold tailWord_3599150
  simp only [CollatzResearch.WordTrace]
  refine ⟨16408973113862713840933363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87514523273934473818311269 16408973113862713840933363)
  ·
    refine ⟨24613459670794070761400045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16408973113862713840933363 24613459670794070761400045)
    ·
      refine ⟨9230047376547776535525017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24613459670794070761400045 9230047376547776535525017)
      ·
        refine ⟨6922535532410832401643763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9230047376547776535525017 6922535532410832401643763)
        ·
          refine ⟨10383803298616248602465645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6922535532410832401643763 10383803298616248602465645)
          ·
            refine ⟨3893926236981093225924617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10383803298616248602465645 3893926236981093225924617)
            ·
              refine ⟨2920444677735819919443463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3893926236981093225924617 2920444677735819919443463)
              ·
                refine ⟨4380667016603729879165195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2920444677735819919443463 4380667016603729879165195)
                ·
                  refine ⟨6571000524905594818747793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4380667016603729879165195 6571000524905594818747793)
                  ·
                    refine ⟨4928250393679196114060845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6571000524905594818747793 4928250393679196114060845)
                    ·
                      refine ⟨1848093897629698542772817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4928250393679196114060845 1848093897629698542772817)
                      ·
                        rfl

theorem cell23_3599150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 2, 1, 1, 2, 3].length) (baseStart_3599150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3599150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3599150 prefixEnd_3599150 := by exact prefixLift 3599150
  have htrace : WordTrace (prefixWord ++ tailWord_3599150) baseStart_3599150 baseEnd_3599150 := by
    simpa [prefixWord, tailWord_3599150, baseEnd_3599150] using wordTrace_append hprefix tailTrace_3599150
  have hstable : (prefixWord ++ tailWord_3599150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3599150).length < 2 ^ (prefixWord ++ tailWord_3599150).sum := by decide
  have hdescent : baseEnd_3599150 < baseStart_3599150 := by decide
  rcases family_descends (prefixWord ++ tailWord_3599150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3599277 : List Nat := [1, 5, 2, 3, 1, 2, 2, 2, 5]
def baseStart_3599277 : Nat := 118140960795 + 3599277 * 2 ^ 59
def prefixEnd_3599277 : Nat := 4983230072969 + 3 ^ 40 * 3599277 * 2
def baseEnd_3599277 : Nat := 205351012185868838431637

theorem tailTrace_3599277 : CollatzResearch.WordTrace tailWord_3599277 prefixEnd_3599277 205351012185868838431637 := by
  unfold tailWord_3599277
  simp only [CollatzResearch.WordTrace]
  refine ⟨131276416981441611417340085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87517611320961074278226723 131276416981441611417340085)
  ·
    refine ⟨12307164092010151070375633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 131276416981441611417340085 12307164092010151070375633)
    ·
      refine ⟨9230373069007613302781725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12307164092010151070375633 9230373069007613302781725)
      ·
        refine ⟨3461389900877854988543147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9230373069007613302781725 3461389900877854988543147)
        ·
          refine ⟨5192084851316782482814721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3461389900877854988543147 5192084851316782482814721)
          ·
            refine ⟨3894063638487586862111041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5192084851316782482814721 3894063638487586862111041)
            ·
              refine ⟨2920547728865690146583281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3894063638487586862111041 2920547728865690146583281)
              ·
                refine ⟨2190410796649267609937461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2920547728865690146583281 2190410796649267609937461)
                ·
                  refine ⟨205351012185868838431637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2190410796649267609937461 205351012185868838431637)
                  ·
                    rfl

theorem cell23_3599277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 2, 2, 5].length) (baseStart_3599277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3599277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3599277 prefixEnd_3599277 := by exact prefixLift 3599277
  have htrace : WordTrace (prefixWord ++ tailWord_3599277) baseStart_3599277 baseEnd_3599277 := by
    simpa [prefixWord, tailWord_3599277, baseEnd_3599277] using wordTrace_append hprefix tailTrace_3599277
  have hstable : (prefixWord ++ tailWord_3599277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3599277).length < 2 ^ (prefixWord ++ tailWord_3599277).sum := by decide
  have hdescent : baseEnd_3599277 < baseStart_3599277 := by decide
  rcases family_descends (prefixWord ++ tailWord_3599277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3599279 : List Nat := [1, 1, 2, 1, 2, 2, 2, 3, 4, 2, 3]
def baseStart_3599279 : Nat := 118140960795 + 3599279 * 2 ^ 59
def prefixEnd_3599279 : Nat := 4983230072969 + 3 ^ 40 * 3599279 * 2
def baseEnd_3599279 : Nat := 1848160136634128538059723

theorem tailTrace_3599279 : CollatzResearch.WordTrace tailWord_3599279 prefixEnd_3599279 1848160136634128538059723 := by
  unfold tailWord_3599279
  simp only [CollatzResearch.WordTrace]
  refine ⟨131276489927434365758912891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87517659951622910505941927 131276489927434365758912891)
  ·
    refine ⟨196914734891151548638369337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131276489927434365758912891 196914734891151548638369337)
    ·
      refine ⟨147686051168363661478777003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196914734891151548638369337 147686051168363661478777003)
      ·
        refine ⟨221529076752545492218165505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147686051168363661478777003 221529076752545492218165505)
        ·
          refine ⟨166146807564409119163624129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 221529076752545492218165505 166146807564409119163624129)
          ·
            refine ⟨124610105673306839372718097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166146807564409119163624129 124610105673306839372718097)
            ·
              refine ⟨93457579254980129529538573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124610105673306839372718097 93457579254980129529538573)
              ·
                refine ⟨35046592220617548573576965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93457579254980129529538573 35046592220617548573576965)
                ·
                  refine ⟨6571236041365790357545681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35046592220617548573576965 6571236041365790357545681)
                  ·
                    refine ⟨4928427031024342768159261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6571236041365790357545681 4928427031024342768159261)
                    ·
                      refine ⟨1848160136634128538059723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4928427031024342768159261 1848160136634128538059723)
                      ·
                        rfl

theorem cell23_3599279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 3, 4, 2, 3].length) (baseStart_3599279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3599279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3599279 prefixEnd_3599279 := by exact prefixLift 3599279
  have htrace : WordTrace (prefixWord ++ tailWord_3599279) baseStart_3599279 baseEnd_3599279 := by
    simpa [prefixWord, tailWord_3599279, baseEnd_3599279] using wordTrace_append hprefix tailTrace_3599279
  have hstable : (prefixWord ++ tailWord_3599279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3599279).length < 2 ^ (prefixWord ++ tailWord_3599279).sum := by decide
  have hdescent : baseEnd_3599279 < baseStart_3599279 := by decide
  rcases family_descends (prefixWord ++ tailWord_3599279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3599293 : List Nat := [1, 4, 1, 2, 4, 1, 1, 1, 2, 4, 2]
def baseStart_3599293 : Nat := 118140960795 + 3599293 * 2 ^ 59
def prefixEnd_3599293 : Nat := 4983230072969 + 3 ^ 40 * 3599293 * 2
def baseEnd_3599293 : Nat := 1848167325363291483284659

theorem tailTrace_3599293 : CollatzResearch.WordTrace tailWord_3599293 prefixEnd_3599293 1848167325363291483284659 := by
  unfold tailWord_3599293
  simp only [CollatzResearch.WordTrace]
  refine ⟨131277000549383646149922533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87518000366255764099948355 131277000549383646149922533)
  ·
    refine ⟨24614437603009433653110475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 131277000549383646149922533 24614437603009433653110475)
    ·
      refine ⟨36921656404514150479665713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24614437603009433653110475 36921656404514150479665713)
      ·
        refine ⟨27691242303385612859749285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36921656404514150479665713 27691242303385612859749285)
        ·
          refine ⟨5192107931884802411202991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27691242303385612859749285 5192107931884802411202991)
          ·
            refine ⟨7788161897827203616804487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5192107931884802411202991 7788161897827203616804487)
            ·
              refine ⟨11682242846740805425206731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7788161897827203616804487 11682242846740805425206731)
              ·
                refine ⟨17523364270111208137810097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11682242846740805425206731 17523364270111208137810097)
                ·
                  refine ⟨13142523202583406103357573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17523364270111208137810097 13142523202583406103357573)
                  ·
                    refine ⟨2464223100484388644379545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13142523202583406103357573 2464223100484388644379545)
                    ·
                      refine ⟨1848167325363291483284659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2464223100484388644379545 1848167325363291483284659)
                      ·
                        rfl

theorem cell23_3599293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 1, 2, 4, 2].length) (baseStart_3599293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3599293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3599293 prefixEnd_3599293 := by exact prefixLift 3599293
  have htrace : WordTrace (prefixWord ++ tailWord_3599293) baseStart_3599293 baseEnd_3599293 := by
    simpa [prefixWord, tailWord_3599293, baseEnd_3599293] using wordTrace_append hprefix tailTrace_3599293
  have hstable : (prefixWord ++ tailWord_3599293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3599293).length < 2 ^ (prefixWord ++ tailWord_3599293).sum := by decide
  have hdescent : baseEnd_3599293 < baseStart_3599293 := by decide
  rcases family_descends (prefixWord ++ tailWord_3599293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3599343 : List Nat := [1, 1, 2, 1, 4, 4, 2, 1, 3, 1, 3]
def baseStart_3599343 : Nat := 118140960795 + 3599343 * 2 ^ 59
def prefixEnd_3599343 : Nat := 4983230072969 + 3 ^ 40 * 3599343 * 2
def baseEnd_3599343 : Nat := 1848192999396016287659429

theorem tailTrace_3599343 : CollatzResearch.WordTrace tailWord_3599343 prefixEnd_3599343 1848192999396016287659429 := by
  unfold tailWord_3599343
  simp only [CollatzResearch.WordTrace]
  refine ⟨131278824199202504689242683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87519216132801669792828455 131278824199202504689242683)
  ·
    refine ⟨196918236298803757033864025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131278824199202504689242683 196918236298803757033864025)
    ·
      refine ⟨147688677224102817775398019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196918236298803757033864025 147688677224102817775398019)
      ·
        refine ⟨221533015836154226663097029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147688677224102817775398019 221533015836154226663097029)
        ·
          refine ⟨41537440469278917499330693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 221533015836154226663097029 41537440469278917499330693)
          ·
            refine ⟨7788270087989797031124505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41537440469278917499330693 7788270087989797031124505)
            ·
              refine ⟨5841202565992347773343379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7788270087989797031124505 5841202565992347773343379)
              ·
                refine ⟨8761803848988521660015069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5841202565992347773343379 8761803848988521660015069)
                ·
                  refine ⟨3285676443370695622505651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8761803848988521660015069 3285676443370695622505651)
                  ·
                    refine ⟨4928514665056043433758477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3285676443370695622505651 4928514665056043433758477)
                    ·
                      refine ⟨1848192999396016287659429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4928514665056043433758477 1848192999396016287659429)
                      ·
                        rfl

theorem cell23_3599343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 2, 1, 3, 1, 3].length) (baseStart_3599343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3599343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3599343 prefixEnd_3599343 := by exact prefixLift 3599343
  have htrace : WordTrace (prefixWord ++ tailWord_3599343) baseStart_3599343 baseEnd_3599343 := by
    simpa [prefixWord, tailWord_3599343, baseEnd_3599343] using wordTrace_append hprefix tailTrace_3599343
  have hstable : (prefixWord ++ tailWord_3599343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3599343).length < 2 ^ (prefixWord ++ tailWord_3599343).sum := by decide
  have hdescent : baseEnd_3599343 < baseStart_3599343 := by decide
  rcases family_descends (prefixWord ++ tailWord_3599343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3599369 : List Nat := [1, 2, 1, 1, 3, 1, 1, 2, 2, 6, 3]
def baseStart_3599369 : Nat := 118140960795 + 3599369 * 2 ^ 59
def prefixEnd_3599369 : Nat := 4983230072969 + 3 ^ 40 * 3599369 * 2
def baseEnd_3599369 : Nat := 1848206349893033185934309

theorem tailTrace_3599369 : CollatzResearch.WordTrace tailWord_3599369 prefixEnd_3599369 1848206349893033185934309 := by
  unfold tailWord_3599369
  simp only [CollatzResearch.WordTrace]
  refine ⟨131279772497108311129689161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87519848331405540753126107 131279772497108311129689161)
  ·
    refine ⟨98459829372831233347266871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131279772497108311129689161 98459829372831233347266871)
    ·
      refine ⟨147689744059246850020900307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98459829372831233347266871 147689744059246850020900307)
      ·
        refine ⟨221534616088870275031350461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147689744059246850020900307 221534616088870275031350461)
        ·
          refine ⟨83075481033326353136756423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 221534616088870275031350461 83075481033326353136756423)
          ·
            refine ⟨124613221549989529705134635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83075481033326353136756423 124613221549989529705134635)
            ·
              refine ⟨186919832324984294557701953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124613221549989529705134635 186919832324984294557701953)
              ·
                refine ⟨140189874243738220918276465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 186919832324984294557701953 140189874243738220918276465)
                ·
                  refine ⟨105142405682803665688707349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 140189874243738220918276465 105142405682803665688707349)
                  ·
                    refine ⟨4928550266381421829158157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 105142405682803665688707349 4928550266381421829158157)
                    ·
                      refine ⟨1848206349893033185934309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4928550266381421829158157 1848206349893033185934309)
                      ·
                        rfl

theorem cell23_3599369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 6, 3].length) (baseStart_3599369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3599369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3599369 prefixEnd_3599369 := by exact prefixLift 3599369
  have htrace : WordTrace (prefixWord ++ tailWord_3599369) baseStart_3599369 baseEnd_3599369 := by
    simpa [prefixWord, tailWord_3599369, baseEnd_3599369] using wordTrace_append hprefix tailTrace_3599369
  have hstable : (prefixWord ++ tailWord_3599369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3599369).length < 2 ^ (prefixWord ++ tailWord_3599369).sum := by decide
  have hdescent : baseEnd_3599369 < baseStart_3599369 := by decide
  rcases family_descends (prefixWord ++ tailWord_3599369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3599379 : List Nat := [1, 1, 1, 2, 1, 4, 1, 3, 3, 2, 4]
def baseStart_3599379 : Nat := 118140960795 + 3599379 * 2 ^ 59
def prefixEnd_3599379 : Nat := 4983230072969 + 3 ^ 40 * 3599379 * 2
def baseEnd_3599379 : Nat := 1848211484699578146809263

theorem tailTrace_3599379 : CollatzResearch.WordTrace tailWord_3599379 prefixEnd_3599379 1848211484699578146809263 := by
  unfold tailWord_3599379
  simp only [CollatzResearch.WordTrace]
  refine ⟨131280137227072082837553191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87520091484714721891702127 131280137227072082837553191)
  ·
    refine ⟨196920205840608124256329787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131280137227072082837553191 196920205840608124256329787)
    ·
      refine ⟨295380308760912186384494681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196920205840608124256329787 295380308760912186384494681)
      ·
        refine ⟨221535231570684139788371011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 295380308760912186384494681 221535231570684139788371011)
        ·
          refine ⟨332302847356026209682556517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221535231570684139788371011 332302847356026209682556517)
          ·
            refine ⟨62306783879254914315479347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 332302847356026209682556517 62306783879254914315479347)
            ·
              refine ⟨93460175818882371473219021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62306783879254914315479347 93460175818882371473219021)
              ·
                refine ⟨35047565932080889302457133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93460175818882371473219021 35047565932080889302457133)
                ·
                  refine ⟨13142837224530333488421425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35047565932080889302457133 13142837224530333488421425)
                  ·
                    refine ⟨9857127918397750116316069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13142837224530333488421425 9857127918397750116316069)
                    ·
                      refine ⟨1848211484699578146809263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9857127918397750116316069 1848211484699578146809263)
                      ·
                        rfl

theorem cell23_3599379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 3, 3, 2, 4].length) (baseStart_3599379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3599379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3599379 prefixEnd_3599379 := by exact prefixLift 3599379
  have htrace : WordTrace (prefixWord ++ tailWord_3599379) baseStart_3599379 baseEnd_3599379 := by
    simpa [prefixWord, tailWord_3599379, baseEnd_3599379] using wordTrace_append hprefix tailTrace_3599379
  have hstable : (prefixWord ++ tailWord_3599379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3599379).length < 2 ^ (prefixWord ++ tailWord_3599379).sum := by decide
  have hdescent : baseEnd_3599379 < baseStart_3599379 := by decide
  rcases family_descends (prefixWord ++ tailWord_3599379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3599383 : List Nat := [1, 1, 3, 5, 1, 1, 2, 3, 1, 1, 4]
def baseStart_3599383 : Nat := 118140960795 + 3599383 * 2 ^ 59
def prefixEnd_3599383 : Nat := 4983230072969 + 3 ^ 40 * 3599383 * 2
def baseEnd_3599383 : Nat := 1848213538622196131159245

theorem tailTrace_3599383 : CollatzResearch.WordTrace tailWord_3599383 prefixEnd_3599383 1848213538622196131159245 := by
  unfold tailWord_3599383
  simp only [CollatzResearch.WordTrace]
  refine ⟨131280283119057591520698803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87520188746038394347132535 131280283119057591520698803)
  ·
    refine ⟨196920424678586387281048205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131280283119057591520698803 196920424678586387281048205)
    ·
      refine ⟨73845159254469895230393077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196920424678586387281048205 73845159254469895230393077)
      ·
        refine ⟨6922983680106552677849351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 73845159254469895230393077 6922983680106552677849351)
        ·
          refine ⟨10384475520159829016774027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6922983680106552677849351 10384475520159829016774027)
          ·
            refine ⟨15576713280239743525161041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10384475520159829016774027 15576713280239743525161041)
            ·
              refine ⟨11682534960179807643870781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15576713280239743525161041 11682534960179807643870781)
              ·
                refine ⟨4380950610067427866451543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11682534960179807643870781 4380950610067427866451543)
                ·
                  refine ⟨6571425915101141799677315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4380950610067427866451543 6571425915101141799677315)
                  ·
                    refine ⟨9857138872651712699515973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6571425915101141799677315 9857138872651712699515973)
                    ·
                      refine ⟨1848213538622196131159245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9857138872651712699515973 1848213538622196131159245)
                      ·
                        rfl

theorem cell23_3599383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_3599383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3599383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3599383 prefixEnd_3599383 := by exact prefixLift 3599383
  have htrace : WordTrace (prefixWord ++ tailWord_3599383) baseStart_3599383 baseEnd_3599383 := by
    simpa [prefixWord, tailWord_3599383, baseEnd_3599383] using wordTrace_append hprefix tailTrace_3599383
  have hstable : (prefixWord ++ tailWord_3599383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3599383).length < 2 ^ (prefixWord ++ tailWord_3599383).sum := by decide
  have hdescent : baseEnd_3599383 < baseStart_3599383 := by decide
  rcases family_descends (prefixWord ++ tailWord_3599383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3599386 : List Nat := [3, 1, 1, 3, 1, 2, 4, 1, 1, 1, 5]
def baseStart_3599386 : Nat := 118140960795 + 3599386 * 2 ^ 59
def prefixEnd_3599386 : Nat := 4983230072969 + 3 ^ 40 * 3599386 * 2
def baseEnd_3599386 : Nat := 1848215079064159619421731

theorem tailTrace_3599386 : CollatzResearch.WordTrace tailWord_3599386 prefixEnd_3599386 1848215079064159619421731 := by
  unfold tailWord_3599386
  simp only [CollatzResearch.WordTrace]
  refine ⟨32820098134511680758264503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87520261692031148688705341 32820098134511680758264503)
  ·
    refine ⟨49230147201767521137396755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32820098134511680758264503 49230147201767521137396755)
    ·
      refine ⟨73845220802651281706095133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49230147201767521137396755 73845220802651281706095133)
      ·
        refine ⟨27691957800994230639785675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73845220802651281706095133 27691957800994230639785675)
        ·
          refine ⟨41537936701491345959678513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27691957800994230639785675 41537936701491345959678513)
          ·
            refine ⟨31153452526118509469758885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41537936701491345959678513 31153452526118509469758885)
            ·
              refine ⟨5841272348647220525579791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31153452526118509469758885 5841272348647220525579791)
              ·
                refine ⟨8761908522970830788369687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5841272348647220525579791 8761908522970830788369687)
                ·
                  refine ⟨13142862784456246182554531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8761908522970830788369687 13142862784456246182554531)
                  ·
                    refine ⟨19714294176684369273831797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13142862784456246182554531 19714294176684369273831797)
                    ·
                      refine ⟨1848215079064159619421731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19714294176684369273831797 1848215079064159619421731)
                      ·
                        rfl

theorem cell23_3599386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 4, 1, 1, 1, 5].length) (baseStart_3599386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3599386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3599386 prefixEnd_3599386 := by exact prefixLift 3599386
  have htrace : WordTrace (prefixWord ++ tailWord_3599386) baseStart_3599386 baseEnd_3599386 := by
    simpa [prefixWord, tailWord_3599386, baseEnd_3599386] using wordTrace_append hprefix tailTrace_3599386
  have hstable : (prefixWord ++ tailWord_3599386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3599386).length < 2 ^ (prefixWord ++ tailWord_3599386).sum := by decide
  have hdescent : baseEnd_3599386 < baseStart_3599386 := by decide
  rcases family_descends (prefixWord ++ tailWord_3599386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3599396 : List Nat := [2, 3, 1, 4, 1, 1, 1, 2, 1, 1, 6]
def baseStart_3599396 : Nat := 118140960795 + 3599396 * 2 ^ 59
def prefixEnd_3599396 : Nat := 4983230072969 + 3 ^ 40 * 3599396 * 2
def baseEnd_3599396 : Nat := 1848220213870704580296685

theorem tailTrace_3599396 : CollatzResearch.WordTrace tailWord_3599396 prefixEnd_3599396 1848220213870704580296685 := by
  unfold tailWord_3599396
  simp only [CollatzResearch.WordTrace]
  refine ⟨65640378634005247370461021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87520504845340329827281361 65640378634005247370461021)
  ·
    refine ⟨24615141987751967763922883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65640378634005247370461021 24615141987751967763922883)
    ·
      refine ⟨36922712981627951645884325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24615141987751967763922883 36922712981627951645884325)
      ·
        refine ⟨6923008684055240933603311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36922712981627951645884325 6923008684055240933603311)
        ·
          refine ⟨10384513026082861400404967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6923008684055240933603311 10384513026082861400404967)
          ·
            refine ⟨15576769539124292100607451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10384513026082861400404967 15576769539124292100607451)
            ·
              refine ⟨23365154308686438150911177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15576769539124292100607451 23365154308686438150911177)
              ·
                refine ⟨17523865731514828613183383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23365154308686438150911177 17523865731514828613183383)
                ·
                  refine ⟨26285798597272242919775075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17523865731514828613183383 26285798597272242919775075)
                  ·
                    refine ⟨39428697895908364379662613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26285798597272242919775075 39428697895908364379662613)
                    ·
                      refine ⟨1848220213870704580296685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39428697895908364379662613 1848220213870704580296685)
                      ·
                        rfl

theorem cell23_3599396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_3599396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3599396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3599396 prefixEnd_3599396 := by exact prefixLift 3599396
  have htrace : WordTrace (prefixWord ++ tailWord_3599396) baseStart_3599396 baseEnd_3599396 := by
    simpa [prefixWord, tailWord_3599396, baseEnd_3599396] using wordTrace_append hprefix tailTrace_3599396
  have hstable : (prefixWord ++ tailWord_3599396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3599396).length < 2 ^ (prefixWord ++ tailWord_3599396).sum := by decide
  have hdescent : baseEnd_3599396 < baseStart_3599396 := by decide
  rcases family_descends (prefixWord ++ tailWord_3599396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3599406 : List Nat := [4, 1, 3, 1, 1, 1, 4, 8]
def baseStart_3599406 : Nat := 118140960795 + 3599406 * 2 ^ 59
def prefixEnd_3599406 : Nat := 4983230072969 + 3 ^ 40 * 3599406 * 2
def baseEnd_3599406 : Nat := 68452790691749983006357

theorem tailTrace_3599406 : CollatzResearch.WordTrace tailWord_3599406 prefixEnd_3599406 68452790691749983006357 := by
  unfold tailWord_3599406
  simp only [CollatzResearch.WordTrace]
  refine ⟨16410140249746783306098259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87520747998649510965857381 16410140249746783306098259)
  ·
    refine ⟨24615210374620174959147389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16410140249746783306098259 24615210374620174959147389)
    ·
      refine ⟨9230703890482565609680271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24615210374620174959147389 9230703890482565609680271)
      ·
        refine ⟨13846055835723848414520407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9230703890482565609680271 13846055835723848414520407)
        ·
          refine ⟨20769083753585772621780611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13846055835723848414520407 20769083753585772621780611)
          ·
            refine ⟨31153625630378658932670917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20769083753585772621780611 31153625630378658932670917)
            ·
              refine ⟨5841304805695998549875797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31153625630378658932670917 5841304805695998549875797)
              ·
                refine ⟨68452790691749983006357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5841304805695998549875797 68452790691749983006357)
                ·
                  rfl

theorem cell23_3599406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 4, 8].length) (baseStart_3599406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3599406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3599406 prefixEnd_3599406 := by exact prefixLift 3599406
  have htrace : WordTrace (prefixWord ++ tailWord_3599406) baseStart_3599406 baseEnd_3599406 := by
    simpa [prefixWord, tailWord_3599406, baseEnd_3599406] using wordTrace_append hprefix tailTrace_3599406
  have hstable : (prefixWord ++ tailWord_3599406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3599406).length < 2 ^ (prefixWord ++ tailWord_3599406).sum := by decide
  have hdescent : baseEnd_3599406 < baseStart_3599406 := by decide
  rcases family_descends (prefixWord ++ tailWord_3599406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3599409 : List Nat := [1, 2, 2, 3, 1, 2, 1, 1, 2, 2, 6]
def baseStart_3599409 : Nat := 118140960795 + 3599409 * 2 ^ 59
def prefixEnd_3599409 : Nat := 4983230072969 + 3 ^ 40 * 3599409 * 2
def baseEnd_3599409 : Nat := 1848226889119213029434125

theorem tailTrace_3599409 : CollatzResearch.WordTrace tailWord_3599409 prefixEnd_3599409 1848226889119213029434125 := by
  unfold tailWord_3599409
  simp only [CollatzResearch.WordTrace]
  refine ⟨131281231416963397961145281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87520820944642265307430187 131281231416963397961145281)
  ·
    refine ⟨98460923562722548470858961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131281231416963397961145281 98460923562722548470858961)
    ·
      refine ⟨73845692672041911353144221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98460923562722548470858961 73845692672041911353144221)
      ·
        refine ⟨27692134752015716757429083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73845692672041911353144221 27692134752015716757429083)
        ·
          refine ⟨41538202128023575136143625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27692134752015716757429083 41538202128023575136143625)
          ·
            refine ⟨31153651596017681352107719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41538202128023575136143625 31153651596017681352107719)
            ·
              refine ⟨46730477394026522028161579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31153651596017681352107719 46730477394026522028161579)
              ·
                refine ⟨70095716091039783042242369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46730477394026522028161579 70095716091039783042242369)
                ·
                  refine ⟨52571787068279837281681777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70095716091039783042242369 52571787068279837281681777)
                  ·
                    refine ⟨39428840301209877961261333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52571787068279837281681777 39428840301209877961261333)
                    ·
                      refine ⟨1848226889119213029434125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39428840301209877961261333 1848226889119213029434125)
                      ·
                        rfl

theorem cell23_3599409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 2, 2, 6].length) (baseStart_3599409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3599409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3599409 prefixEnd_3599409 := by exact prefixLift 3599409
  have htrace : WordTrace (prefixWord ++ tailWord_3599409) baseStart_3599409 baseEnd_3599409 := by
    simpa [prefixWord, tailWord_3599409, baseEnd_3599409] using wordTrace_append hprefix tailTrace_3599409
  have hstable : (prefixWord ++ tailWord_3599409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3599409).length < 2 ^ (prefixWord ++ tailWord_3599409).sum := by decide
  have hdescent : baseEnd_3599409 < baseStart_3599409 := by decide
  rcases family_descends (prefixWord ++ tailWord_3599409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3599420 : List Nat := [2, 2, 2, 2, 2, 4, 1, 2, 1, 2, 3]
def baseStart_3599420 : Nat := 118140960795 + 3599420 * 2 ^ 59
def prefixEnd_3599420 : Nat := 4983230072969 + 3 ^ 40 * 3599420 * 2
def baseEnd_3599420 : Nat := 1848232537406412486396575

theorem tailTrace_3599420 : CollatzResearch.WordTrace tailWord_3599420 prefixEnd_3599420 1848232537406412486396575 := by
  unfold tailWord_3599420
  simp only [CollatzResearch.WordTrace]
  refine ⟨65640816309961773419897857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87521088413282364559863809 65640816309961773419897857)
  ·
    refine ⟨49230612232471330064923393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65640816309961773419897857 49230612232471330064923393)
    ·
      refine ⟨36922959174353497548692545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49230612232471330064923393 36922959174353497548692545)
      ·
        refine ⟨27692219380765123161519409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36922959174353497548692545 27692219380765123161519409)
        ·
          refine ⟨20769164535573842371139557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27692219380765123161519409 20769164535573842371139557)
          ·
            refine ⟨3894218350420095444588667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20769164535573842371139557 3894218350420095444588667)
            ·
              refine ⟨5841327525630143166883001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3894218350420095444588667 5841327525630143166883001)
              ·
                refine ⟨4380995644222607375162251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5841327525630143166883001 4380995644222607375162251)
                ·
                  refine ⟨6571493466333911062743377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4380995644222607375162251 6571493466333911062743377)
                  ·
                    refine ⟨4928620099750433297057533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6571493466333911062743377 4928620099750433297057533)
                    ·
                      refine ⟨1848232537406412486396575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4928620099750433297057533 1848232537406412486396575)
                      ·
                        rfl

theorem cell23_3599420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 1, 2, 1, 2, 3].length) (baseStart_3599420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3599420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3599420 prefixEnd_3599420 := by exact prefixLift 3599420
  have htrace : WordTrace (prefixWord ++ tailWord_3599420) baseStart_3599420 baseEnd_3599420 := by
    simpa [prefixWord, tailWord_3599420, baseEnd_3599420] using wordTrace_append hprefix tailTrace_3599420
  have hstable : (prefixWord ++ tailWord_3599420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3599420).length < 2 ^ (prefixWord ++ tailWord_3599420).sum := by decide
  have hdescent : baseEnd_3599420 < baseStart_3599420 := by decide
  rcases family_descends (prefixWord ++ tailWord_3599420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3599429 : List Nat := [1, 3, 1, 1, 1, 3, 2, 1, 1, 4, 5]
def baseStart_3599429 : Nat := 118140960795 + 3599429 * 2 ^ 59
def prefixEnd_3599429 : Nat := 4983230072969 + 3 ^ 40 * 3599429 * 2
def baseEnd_3599429 : Nat := 1848237158732302951184033

theorem tailTrace_3599429 : CollatzResearch.WordTrace tailWord_3599429 prefixEnd_3599429 1848237158732302951184033 := by
  unfold tailWord_3599429
  simp only [CollatzResearch.WordTrace]
  refine ⟨131281960876890941376873341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87521307251260627584582227 131281960876890941376873341)
  ·
    refine ⟨49230735328834103016327503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131281960876890941376873341 49230735328834103016327503)
    ·
      refine ⟨73846102993251154524491255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49230735328834103016327503 73846102993251154524491255)
      ·
        refine ⟨110769154489876731786736883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73846102993251154524491255 110769154489876731786736883)
        ·
          refine ⟨166153731734815097680105325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110769154489876731786736883 166153731734815097680105325)
          ·
            refine ⟨62307649400555661630039497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 166153731734815097680105325 62307649400555661630039497)
            ·
              refine ⟨46730737050416746222529623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62307649400555661630039497 46730737050416746222529623)
              ·
                refine ⟨70096105575625119333794435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46730737050416746222529623 70096105575625119333794435)
                ·
                  refine ⟨105144158363437679000691653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70096105575625119333794435 105144158363437679000691653)
                  ·
                    refine ⟨19714529693144564812629685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 105144158363437679000691653 19714529693144564812629685)
                    ·
                      refine ⟨1848237158732302951184033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19714529693144564812629685 1848237158732302951184033)
                      ·
                        rfl

theorem cell23_3599429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 4, 5].length) (baseStart_3599429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3599429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3599429 prefixEnd_3599429 := by exact prefixLift 3599429
  have htrace : WordTrace (prefixWord ++ tailWord_3599429) baseStart_3599429 baseEnd_3599429 := by
    simpa [prefixWord, tailWord_3599429, baseEnd_3599429] using wordTrace_append hprefix tailTrace_3599429
  have hstable : (prefixWord ++ tailWord_3599429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3599429).length < 2 ^ (prefixWord ++ tailWord_3599429).sum := by decide
  have hdescent : baseEnd_3599429 < baseStart_3599429 := by decide
  rcases family_descends (prefixWord ++ tailWord_3599429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3599430 : List Nat := [6, 1, 1, 1, 1, 3, 1, 2, 1, 2, 4]
def baseStart_3599430 : Nat := 118140960795 + 3599430 * 2 ^ 59
def prefixEnd_3599430 : Nat := 4983230072969 + 3 ^ 40 * 3599430 * 2
def baseEnd_3599430 : Nat := 1848237672212957447271529

theorem tailTrace_3599430 : CollatzResearch.WordTrace tailWord_3599430 prefixEnd_3599430 1848237672212957447271529 := by
  unfold tailWord_3599430
  simp only [CollatzResearch.WordTrace]
  refine ⟨4102562417183978704614367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 87521331566591545698439829 4102562417183978704614367)
  ·
    refine ⟨6153843625775968056921551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4102562417183978704614367 6153843625775968056921551)
    ·
      refine ⟨9230765438663952085382327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6153843625775968056921551 9230765438663952085382327)
      ·
        refine ⟨13846148157995928128073491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9230765438663952085382327 13846148157995928128073491)
        ·
          refine ⟨20769222236993892192110237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13846148157995928128073491 20769222236993892192110237)
          ·
            refine ⟨7788458338872709572041339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20769222236993892192110237 7788458338872709572041339)
            ·
              refine ⟨11682687508309064358062009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7788458338872709572041339 11682687508309064358062009)
              ·
                refine ⟨8762015631231798268546507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11682687508309064358062009 8762015631231798268546507)
                ·
                  refine ⟨13143023446847697402819761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8762015631231798268546507 13143023446847697402819761)
                  ·
                    refine ⟨9857267585135773052114821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13143023446847697402819761 9857267585135773052114821)
                    ·
                      refine ⟨1848237672212957447271529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9857267585135773052114821 1848237672212957447271529)
                      ·
                        rfl

theorem cell23_3599430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_3599430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3599430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3599430 prefixEnd_3599430 := by exact prefixLift 3599430
  have htrace : WordTrace (prefixWord ++ tailWord_3599430) baseStart_3599430 baseEnd_3599430 := by
    simpa [prefixWord, tailWord_3599430, baseEnd_3599430] using wordTrace_append hprefix tailTrace_3599430
  have hstable : (prefixWord ++ tailWord_3599430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3599430).length < 2 ^ (prefixWord ++ tailWord_3599430).sum := by decide
  have hdescent : baseEnd_3599430 < baseStart_3599430 := by decide
  rcases family_descends (prefixWord ++ tailWord_3599430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3599437 : List Nat := [1, 6, 1, 1, 1, 3, 3, 1, 1, 2, 3]
def baseStart_3599437 : Nat := 118140960795 + 3599437 * 2 ^ 59
def prefixEnd_3599437 : Nat := 4983230072969 + 3 ^ 40 * 3599437 * 2
def baseEnd_3599437 : Nat := 1848241266577538919883997

theorem tailTrace_3599437 : CollatzResearch.WordTrace tailWord_3599437 prefixEnd_3599437 1848241266577538919883997 := by
  unfold tailWord_3599437
  simp only [CollatzResearch.WordTrace]
  refine ⟨131282252660861958743164565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87521501773907972495443043 131282252660861958743164565)
  ·
    refine ⟨6153855593477904316085839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 131282252660861958743164565 6153855593477904316085839)
    ·
      refine ⟨9230783390216856474128759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6153855593477904316085839 9230783390216856474128759)
      ·
        refine ⟨13846175085325284711193139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9230783390216856474128759 13846175085325284711193139)
        ·
          refine ⟨20769262627987927066789709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13846175085325284711193139 20769262627987927066789709)
          ·
            refine ⟨7788473485495472650046141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20769262627987927066789709 7788473485495472650046141)
            ·
              refine ⟨2920677557060802243767303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7788473485495472650046141 2920677557060802243767303)
              ·
                refine ⟨4381016335591203365650955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2920677557060802243767303 4381016335591203365650955)
                ·
                  refine ⟨6571524503386805048476433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4381016335591203365650955 6571524503386805048476433)
                  ·
                    refine ⟨4928643377540103786357325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6571524503386805048476433 4928643377540103786357325)
                    ·
                      refine ⟨1848241266577538919883997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4928643377540103786357325 1848241266577538919883997)
                      ·
                        rfl

theorem cell23_3599437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 3, 1, 1, 2, 3].length) (baseStart_3599437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3599437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3599437 prefixEnd_3599437 := by exact prefixLift 3599437
  have htrace : WordTrace (prefixWord ++ tailWord_3599437) baseStart_3599437 baseEnd_3599437 := by
    simpa [prefixWord, tailWord_3599437, baseEnd_3599437] using wordTrace_append hprefix tailTrace_3599437
  have hstable : (prefixWord ++ tailWord_3599437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3599437).length < 2 ^ (prefixWord ++ tailWord_3599437).sum := by decide
  have hdescent : baseEnd_3599437 < baseStart_3599437 := by decide
  rcases family_descends (prefixWord ++ tailWord_3599437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3599439 : List Nat := [1, 1, 2, 1, 1, 2, 2, 1, 3, 5, 4]
def baseStart_3599439 : Nat := 118140960795 + 3599439 * 2 ^ 59
def prefixEnd_3599439 : Nat := 4983230072969 + 3 ^ 40 * 3599439 * 2
def baseEnd_3599439 : Nat := 1848242293538847912058987

theorem tailTrace_3599439 : CollatzResearch.WordTrace tailWord_3599439 prefixEnd_3599439 1848242293538847912058987 := by
  unfold tailWord_3599439
  simp only [CollatzResearch.WordTrace]
  refine ⟨131282325606854713084737371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87521550404569808723158247 131282325606854713084737371)
  ·
    refine ⟨196923488410282069627106057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131282325606854713084737371 196923488410282069627106057)
    ·
      refine ⟨147692616307711552220329543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196923488410282069627106057 147692616307711552220329543)
      ·
        refine ⟨221538924461567328330494315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147692616307711552220329543 221538924461567328330494315)
        ·
          refine ⟨332308386692350992495741473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221538924461567328330494315 332308386692350992495741473)
          ·
            refine ⟨249231290019263244371806105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 332308386692350992495741473 249231290019263244371806105)
            ·
              refine ⟨186923467514447433278854579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 249231290019263244371806105 186923467514447433278854579)
              ·
                refine ⟨280385201271671149918281869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 186923467514447433278854579 280385201271671149918281869)
                ·
                  refine ⟨105144450476876681219355701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 280385201271671149918281869 105144450476876681219355701)
                  ·
                    refine ⟨9857292232207188864314597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 105144450476876681219355701 9857292232207188864314597)
                    ·
                      refine ⟨1848242293538847912058987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9857292232207188864314597 1848242293538847912058987)
                      ·
                        rfl

theorem cell23_3599439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 5, 4].length) (baseStart_3599439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3599439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3599439 prefixEnd_3599439 := by exact prefixLift 3599439
  have htrace : WordTrace (prefixWord ++ tailWord_3599439) baseStart_3599439 baseEnd_3599439 := by
    simpa [prefixWord, tailWord_3599439, baseEnd_3599439] using wordTrace_append hprefix tailTrace_3599439
  have hstable : (prefixWord ++ tailWord_3599439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3599439).length < 2 ^ (prefixWord ++ tailWord_3599439).sum := by decide
  have hdescent : baseEnd_3599439 < baseStart_3599439 := by decide
  rcases family_descends (prefixWord ++ tailWord_3599439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3599466 : List Nat := [3, 1, 3, 2, 2, 1, 1, 1, 1, 8]
def baseStart_3599466 : Nat := 118140960795 + 3599466 * 2 ^ 59
def prefixEnd_3599466 : Nat := 4983230072969 + 3 ^ 40 * 3599466 * 2
def baseEnd_3599466 : Nat := 616085385838839768807121

theorem tailTrace_3599466 : CollatzResearch.WordTrace tailWord_3599466 prefixEnd_3599466 616085385838839768807121 := by
  unfold tailWord_3599466
  simp only [CollatzResearch.WordTrace]
  refine ⟨32820827594439224173992563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87522206918504597797313501 32820827594439224173992563)
  ·
    refine ⟨49231241391658836260988845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32820827594439224173992563 49231241391658836260988845)
    ·
      refine ⟨18461715521872063597870817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49231241391658836260988845 18461715521872063597870817)
      ·
        refine ⟨13846286641404047698403113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18461715521872063597870817 13846286641404047698403113)
        ·
          refine ⟨10384714981053035773802335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13846286641404047698403113 10384714981053035773802335)
          ·
            refine ⟨15577072471579553660703503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10384714981053035773802335 15577072471579553660703503)
            ·
              refine ⟨23365608707369330491055255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15577072471579553660703503 23365608707369330491055255)
              ·
                refine ⟨35048413061053995736582883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23365608707369330491055255 35048413061053995736582883)
                ·
                  refine ⟨52572619591580993604874325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35048413061053995736582883 52572619591580993604874325)
                  ·
                    refine ⟨616085385838839768807121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 52572619591580993604874325 616085385838839768807121)
                    ·
                      rfl

theorem cell23_3599466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 1, 1, 8].length) (baseStart_3599466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3599466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3599466 prefixEnd_3599466 := by exact prefixLift 3599466
  have htrace : WordTrace (prefixWord ++ tailWord_3599466) baseStart_3599466 baseEnd_3599466 := by
    simpa [prefixWord, tailWord_3599466, baseEnd_3599466] using wordTrace_append hprefix tailTrace_3599466
  have hstable : (prefixWord ++ tailWord_3599466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3599466).length < 2 ^ (prefixWord ++ tailWord_3599466).sum := by decide
  have hdescent : baseEnd_3599466 < baseStart_3599466 := by decide
  rcases family_descends (prefixWord ++ tailWord_3599466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3599524 : List Nat := [2, 3, 1, 2, 3, 2, 3, 1, 2, 2, 2]
def baseStart_3599524 : Nat := 118140960795 + 3599524 * 2 ^ 59
def prefixEnd_3599524 : Nat := 4983230072969 + 3 ^ 40 * 3599524 * 2
def baseEnd_3599524 : Nat := 1848285939394480079496097

theorem tailTrace_3599524 : CollatzResearch.WordTrace tailWord_3599524 prefixEnd_3599524 1848285939394480079496097 := by
  unfold tailWord_3599524
  simp only [CollatzResearch.WordTrace]
  refine ⟨65642712905773386300790813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87523617207697848401054417 65642712905773386300790813)
  ·
    refine ⟨24616017339665019862796555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65642712905773386300790813 24616017339665019862796555)
    ·
      refine ⟨36924026009497529794194833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24616017339665019862796555 36924026009497529794194833)
      ·
        refine ⟨27693019507123147345646125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36924026009497529794194833 27693019507123147345646125)
        ·
          refine ⟨10384882315171180254617297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27693019507123147345646125 10384882315171180254617297)
          ·
            refine ⟨7788661736378385190962973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10384882315171180254617297 7788661736378385190962973)
            ·
              refine ⟨2920748151141894446611115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7788661736378385190962973 2920748151141894446611115)
              ·
                refine ⟨4381122226712841669916673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2920748151141894446611115 4381122226712841669916673)
                ·
                  refine ⟨3285841670034631252437505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4381122226712841669916673 3285841670034631252437505)
                  ·
                    refine ⟨2464381252525973439328129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3285841670034631252437505 2464381252525973439328129)
                    ·
                      refine ⟨1848285939394480079496097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2464381252525973439328129 1848285939394480079496097)
                      ·
                        rfl

theorem cell23_3599524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 3, 1, 2, 2, 2].length) (baseStart_3599524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3599524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3599524 prefixEnd_3599524 := by exact prefixLift 3599524
  have htrace : WordTrace (prefixWord ++ tailWord_3599524) baseStart_3599524 baseEnd_3599524 := by
    simpa [prefixWord, tailWord_3599524, baseEnd_3599524] using wordTrace_append hprefix tailTrace_3599524
  have hstable : (prefixWord ++ tailWord_3599524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3599524).length < 2 ^ (prefixWord ++ tailWord_3599524).sum := by decide
  have hdescent : baseEnd_3599524 < baseStart_3599524 := by decide
  rcases family_descends (prefixWord ++ tailWord_3599524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3599563 : List Nat := [1, 1, 1, 1, 3, 2, 2, 4, 2, 4, 2]
def baseStart_3599563 : Nat := 118140960795 + 3599563 * 2 ^ 59
def prefixEnd_3599563 : Nat := 4983230072969 + 3 ^ 40 * 3599563 * 2
def baseEnd_3599563 : Nat := 1848305965140005426908417

theorem tailTrace_3599563 : CollatzResearch.WordTrace tailWord_3599563 prefixEnd_3599563 1848305965140005426908417 := by
  unfold tailWord_3599563
  simp only [CollatzResearch.WordTrace]
  refine ⟨131286848258405482262251343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87524565505603654841500895 131286848258405482262251343)
  ·
    refine ⟨196930272387608223393377015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131286848258405482262251343 196930272387608223393377015)
    ·
      refine ⟨295395408581412335090065523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196930272387608223393377015 295395408581412335090065523)
      ·
        refine ⟨443093112872118502635098285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295395408581412335090065523 443093112872118502635098285)
        ·
          refine ⟨166159917327044438488161857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 443093112872118502635098285 166159917327044438488161857)
          ·
            refine ⟨124619937995283328866121393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166159917327044438488161857 124619937995283328866121393)
            ·
              refine ⟨93464953496462496649591045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124619937995283328866121393 93464953496462496649591045)
              ·
                refine ⟨17524678780586718121798321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 93464953496462496649591045 17524678780586718121798321)
                ·
                  refine ⟨13143509085440038591348741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17524678780586718121798321 13143509085440038591348741)
                  ·
                    refine ⟨2464407953520007235877889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13143509085440038591348741 2464407953520007235877889)
                    ·
                      refine ⟨1848305965140005426908417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2464407953520007235877889 1848305965140005426908417)
                      ·
                        rfl

theorem cell23_3599563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 4, 2, 4, 2].length) (baseStart_3599563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3599563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3599563 prefixEnd_3599563 := by exact prefixLift 3599563
  have htrace : WordTrace (prefixWord ++ tailWord_3599563) baseStart_3599563 baseEnd_3599563 := by
    simpa [prefixWord, tailWord_3599563, baseEnd_3599563] using wordTrace_append hprefix tailTrace_3599563
  have hstable : (prefixWord ++ tailWord_3599563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3599563).length < 2 ^ (prefixWord ++ tailWord_3599563).sum := by decide
  have hdescent : baseEnd_3599563 < baseStart_3599563 := by decide
  rcases family_descends (prefixWord ++ tailWord_3599563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3599620 : List Nat := [2, 3, 2, 2, 2, 2, 2, 2, 6]
def baseStart_3599620 : Nat := 118140960795 + 3599620 * 2 ^ 59
def prefixEnd_3599620 : Nat := 4983230072969 + 3 ^ 40 * 3599620 * 2
def baseEnd_3599620 : Nat := 205370581504145744877295

theorem tailTrace_3599620 : CollatzResearch.WordTrace tailWord_3599620 prefixEnd_3599620 205370581504145744877295 := by
  unfold tailWord_3599620
  simp only [CollatzResearch.WordTrace]
  refine ⟨65644463609599490498538157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87525951479465987331384209 65644463609599490498538157)
  ·
    refine ⟨24616673853599808936951809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65644463609599490498538157 24616673853599808936951809)
    ·
      refine ⟨18462505390199856702713857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24616673853599808936951809 18462505390199856702713857)
      ·
        refine ⟨13846879042649892527035393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18462505390199856702713857 13846879042649892527035393)
        ·
          refine ⟨10385159281987419395276545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13846879042649892527035393 10385159281987419395276545)
          ·
            refine ⟨7788869461490564546457409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10385159281987419395276545 7788869461490564546457409)
            ·
              refine ⟨5841652096117923409843057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7788869461490564546457409 5841652096117923409843057)
              ·
                refine ⟨4381239072088442557382293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5841652096117923409843057 4381239072088442557382293)
                ·
                  refine ⟨205370581504145744877295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4381239072088442557382293 205370581504145744877295)
                  ·
                    rfl

theorem cell23_3599620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 2, 2, 6].length) (baseStart_3599620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3599620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3599620 prefixEnd_3599620 := by exact prefixLift 3599620
  have htrace : WordTrace (prefixWord ++ tailWord_3599620) baseStart_3599620 baseEnd_3599620 := by
    simpa [prefixWord, tailWord_3599620, baseEnd_3599620] using wordTrace_append hprefix tailTrace_3599620
  have hstable : (prefixWord ++ tailWord_3599620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3599620).length < 2 ^ (prefixWord ++ tailWord_3599620).sum := by decide
  have hdescent : baseEnd_3599620 < baseStart_3599620 := by decide
  rcases family_descends (prefixWord ++ tailWord_3599620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3599647 : List Nat := [1, 1, 2, 4, 4, 1, 1, 2, 3, 1, 3]
def baseStart_3599647 : Nat := 118140960795 + 3599647 * 2 ^ 59
def prefixEnd_3599647 : Nat := 4983230072969 + 3 ^ 40 * 3599647 * 2
def baseEnd_3599647 : Nat := 1848349097514983098258031

theorem tailTrace_3599647 : CollatzResearch.WordTrace tailWord_3599647 prefixEnd_3599647 1848349097514983098258031 := by
  unfold tailWord_3599647
  simp only [CollatzResearch.WordTrace]
  refine ⟨131289911990101164608309195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87526607993400776405539463 131289911990101164608309195)
  ·
    refine ⟨196934867985151746912463793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131289911990101164608309195 196934867985151746912463793)
    ·
      refine ⟨147701150988863810184347845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196934867985151746912463793 147701150988863810184347845)
      ·
        refine ⟨27693965810411964409565221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 147701150988863810184347845 27693965810411964409565221)
        ·
          refine ⟨5192618589452243326793479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27693965810411964409565221 5192618589452243326793479)
          ·
            refine ⟨7788927884178364990190219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5192618589452243326793479 7788927884178364990190219)
            ·
              refine ⟨11683391826267547485285329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7788927884178364990190219 11683391826267547485285329)
              ·
                refine ⟨8762543869700660613963997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11683391826267547485285329 8762543869700660613963997)
                ·
                  refine ⟨3285953951137747730236499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8762543869700660613963997 3285953951137747730236499)
                  ·
                    refine ⟨4928930926706621595354749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3285953951137747730236499 4928930926706621595354749)
                    ·
                      refine ⟨1848349097514983098258031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4928930926706621595354749 1848349097514983098258031)
                      ·
                        rfl

theorem cell23_3599647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 2, 3, 1, 3].length) (baseStart_3599647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3599647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3599647 prefixEnd_3599647 := by exact prefixLift 3599647
  have htrace : WordTrace (prefixWord ++ tailWord_3599647) baseStart_3599647 baseEnd_3599647 := by
    simpa [prefixWord, tailWord_3599647, baseEnd_3599647] using wordTrace_append hprefix tailTrace_3599647
  have hstable : (prefixWord ++ tailWord_3599647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3599647).length < 2 ^ (prefixWord ++ tailWord_3599647).sum := by decide
  have hdescent : baseEnd_3599647 < baseStart_3599647 := by decide
  rcases family_descends (prefixWord ++ tailWord_3599647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3599663 : List Nat := [1, 1, 2, 1, 2, 1, 3, 4, 4, 4]
def baseStart_3599663 : Nat := 118140960795 + 3599663 * 2 ^ 59
def prefixEnd_3599663 : Nat := 4983230072969 + 3 ^ 40 * 3599663 * 2
def baseEnd_3599663 : Nat := 616119104401818345219319

theorem tailTrace_3599663 : CollatzResearch.WordTrace tailWord_3599663 prefixEnd_3599663 616119104401818345219319 := by
  unfold tailWord_3599663
  simp only [CollatzResearch.WordTrace]
  refine ⟨131290495558043199340891643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87526997038695466227261095 131290495558043199340891643)
  ·
    refine ⟨196935743337064799011337465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131290495558043199340891643 196935743337064799011337465)
    ·
      refine ⟨147701807502798599258503099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196935743337064799011337465 147701807502798599258503099)
      ·
        refine ⟨221552711254197898887754649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147701807502798599258503099 221552711254197898887754649)
        ·
          refine ⟨166164533440648424165815987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 221552711254197898887754649 166164533440648424165815987)
          ·
            refine ⟨249246800160972636248723981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166164533440648424165815987 249246800160972636248723981)
            ·
              refine ⟨93467550060364738593271493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 249246800160972636248723981 93467550060364738593271493)
              ·
                refine ⟨17525165636318388486238405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 93467550060364738593271493 17525165636318388486238405)
                ·
                  refine ⟨3285968556809697841169701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17525165636318388486238405 3285968556809697841169701)
                  ·
                    refine ⟨616119104401818345219319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3285968556809697841169701 616119104401818345219319)
                    ·
                      rfl

theorem cell23_3599663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 4, 4, 4].length) (baseStart_3599663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3599663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3599663 prefixEnd_3599663 := by exact prefixLift 3599663
  have htrace : WordTrace (prefixWord ++ tailWord_3599663) baseStart_3599663 baseEnd_3599663 := by
    simpa [prefixWord, tailWord_3599663, baseEnd_3599663] using wordTrace_append hprefix tailTrace_3599663
  have hstable : (prefixWord ++ tailWord_3599663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3599663).length < 2 ^ (prefixWord ++ tailWord_3599663).sum := by decide
  have hdescent : baseEnd_3599663 < baseStart_3599663 := by decide
  rcases family_descends (prefixWord ++ tailWord_3599663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3599667 : List Nat := [1, 1, 1, 2, 5, 4, 2, 1, 1, 5]
def baseStart_3599667 : Nat := 118140960795 + 3599667 * 2 ^ 59
def prefixEnd_3599667 : Nat := 4983230072969 + 3 ^ 40 * 3599667 * 2
def baseEnd_3599667 : Nat := 616119789042691006669313

theorem tailTrace_3599667 : CollatzResearch.WordTrace tailWord_3599667 prefixEnd_3599667 616119789042691006669313 := by
  unfold tailWord_3599667
  simp only [CollatzResearch.WordTrace]
  refine ⟨131290641450028708024037255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87527094300019138682691503 131290641450028708024037255)
  ·
    refine ⟨196935962175043062036055883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131290641450028708024037255 196935962175043062036055883)
    ·
      refine ⟨295403943262564593054083825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196935962175043062036055883 295403943262564593054083825)
      ·
        refine ⟨221552957446923444790562869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 295403943262564593054083825 221552957446923444790562869)
        ·
          refine ⟨20770589760649072949115269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 221552957446923444790562869 20770589760649072949115269)
          ·
            refine ⟨3894485580121701177959113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20770589760649072949115269 3894485580121701177959113)
            ·
              refine ⟨2920864185091275883469335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3894485580121701177959113 2920864185091275883469335)
              ·
                refine ⟨4381296277636913825204003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2920864185091275883469335 4381296277636913825204003)
                ·
                  refine ⟨6571944416455370737806005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4381296277636913825204003 6571944416455370737806005)
                  ·
                    refine ⟨616119789042691006669313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6571944416455370737806005 616119789042691006669313)
                    ·
                      rfl

theorem cell23_3599667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 2, 1, 1, 5].length) (baseStart_3599667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3599667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3599667 prefixEnd_3599667 := by exact prefixLift 3599667
  have htrace : WordTrace (prefixWord ++ tailWord_3599667) baseStart_3599667 baseEnd_3599667 := by
    simpa [prefixWord, tailWord_3599667, baseEnd_3599667] using wordTrace_append hprefix tailTrace_3599667
  have hstable : (prefixWord ++ tailWord_3599667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3599667).length < 2 ^ (prefixWord ++ tailWord_3599667).sum := by decide
  have hdescent : baseEnd_3599667 < baseStart_3599667 := by decide
  rcases family_descends (prefixWord ++ tailWord_3599667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3599687 : List Nat := [1, 1, 4, 1, 2, 3, 1, 3, 3, 2, 2]
def baseStart_3599687 : Nat := 118140960795 + 3599687 * 2 ^ 59
def prefixEnd_3599687 : Nat := 4983230072969 + 3 ^ 40 * 3599687 * 2
def baseEnd_3599687 : Nat := 1848369636741162941757847

theorem tailTrace_3599687 : CollatzResearch.WordTrace tailWord_3599687 prefixEnd_3599687 1848369636741162941757847 := by
  unfold tailWord_3599687
  simp only [CollatzResearch.WordTrace]
  refine ⟨131291370909956251439765315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87527580606637500959843543 131291370909956251439765315)
  ·
    refine ⟨196937056364934377159647973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131291370909956251439765315 196937056364934377159647973)
    ·
      refine ⟨36925698068425195717433995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 196937056364934377159647973 36925698068425195717433995)
      ·
        refine ⟨55388547102637793576150993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36925698068425195717433995 55388547102637793576150993)
        ·
          refine ⟨41541410326978345182113245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55388547102637793576150993 41541410326978345182113245)
          ·
            refine ⟨15578028872616879443292467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41541410326978345182113245 15578028872616879443292467)
            ·
              refine ⟨23367043308925319164938701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15578028872616879443292467 23367043308925319164938701)
              ·
                refine ⟨8762641240846994686852013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23367043308925319164938701 8762641240846994686852013)
                ·
                  refine ⟨3285990465317623007569505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8762641240846994686852013 3285990465317623007569505)
                  ·
                    refine ⟨2464492848988217255677129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3285990465317623007569505 2464492848988217255677129)
                    ·
                      refine ⟨1848369636741162941757847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2464492848988217255677129 1848369636741162941757847)
                      ·
                        rfl

theorem cell23_3599687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 3, 3, 2, 2].length) (baseStart_3599687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3599687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3599687 prefixEnd_3599687 := by exact prefixLift 3599687
  have htrace : WordTrace (prefixWord ++ tailWord_3599687) baseStart_3599687 baseEnd_3599687 := by
    simpa [prefixWord, tailWord_3599687, baseEnd_3599687] using wordTrace_append hprefix tailTrace_3599687
  have hstable : (prefixWord ++ tailWord_3599687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3599687).length < 2 ^ (prefixWord ++ tailWord_3599687).sum := by decide
  have hdescent : baseEnd_3599687 < baseStart_3599687 := by decide
  rcases family_descends (prefixWord ++ tailWord_3599687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3599697 : List Nat := [1, 2, 2, 1, 4, 1, 5, 1, 2, 4]
def baseStart_3599697 : Nat := 118140960795 + 3599697 * 2 ^ 59
def prefixEnd_3599697 : Nat := 4983230072969 + 3 ^ 40 * 3599697 * 2
def baseEnd_3599697 : Nat := 616124923849235967544267

theorem tailTrace_3599697 : CollatzResearch.WordTrace tailWord_3599697 prefixEnd_3599697 616124923849235967544267 := by
  unfold tailWord_3599697
  simp only [CollatzResearch.WordTrace]
  refine ⟨131291735639920023147629345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87527823759946682098419563 131291735639920023147629345)
  ·
    refine ⟨98468801729940017360722009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131291735639920023147629345 98468801729940017360722009)
    ·
      refine ⟨73851601297455013020541507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98468801729940017360722009 73851601297455013020541507)
      ·
        refine ⟨110777401946182519530812261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73851601297455013020541507 110777401946182519530812261)
        ·
          refine ⟨20770762864909222412027299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110777401946182519530812261 20770762864909222412027299)
          ·
            refine ⟨31156144297363833618040949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20770762864909222412027299 31156144297363833618040949)
            ·
              refine ⟨2920888527877859401691339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31156144297363833618040949 2920888527877859401691339)
              ·
                refine ⟨4381332791816789102537009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2920888527877859401691339 4381332791816789102537009)
                ·
                  refine ⟨3285999593862591826902757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4381332791816789102537009 3285999593862591826902757)
                  ·
                    refine ⟨616124923849235967544267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3285999593862591826902757 616124923849235967544267)
                    ·
                      rfl

theorem cell23_3599697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 5, 1, 2, 4].length) (baseStart_3599697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3599697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3599697 prefixEnd_3599697 := by exact prefixLift 3599697
  have htrace : WordTrace (prefixWord ++ tailWord_3599697) baseStart_3599697 baseEnd_3599697 := by
    simpa [prefixWord, tailWord_3599697, baseEnd_3599697] using wordTrace_append hprefix tailTrace_3599697
  have hstable : (prefixWord ++ tailWord_3599697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3599697).length < 2 ^ (prefixWord ++ tailWord_3599697).sum := by decide
  have hdescent : baseEnd_3599697 < baseStart_3599697 := by decide
  rcases family_descends (prefixWord ++ tailWord_3599697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3599764 : List Nat := [2, 4, 2, 1, 2, 2, 1, 1, 3, 3, 2]
def baseStart_3599764 : Nat := 118140960795 + 3599764 * 2 ^ 59
def prefixEnd_3599764 : Nat := 4983230072969 + 3 ^ 40 * 3599764 * 2
def baseEnd_3599764 : Nat := 1848409174751559140494993

theorem tailTrace_3599764 : CollatzResearch.WordTrace tailWord_3599764 prefixEnd_3599764 1848409174751559140494993 := by
  unfold tailWord_3599764
  simp only [CollatzResearch.WordTrace]
  refine ⟨65647089665338646795159173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87529452887118195726878897 65647089665338646795159173)
  ·
    refine ⟨12308829312250996274092345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65647089665338646795159173 12308829312250996274092345)
    ·
      refine ⟨9231621984188247205569259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12308829312250996274092345 9231621984188247205569259)
      ·
        refine ⟨13847432976282370808353889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9231621984188247205569259 13847432976282370808353889)
        ·
          refine ⟨10385574732211778106265417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13847432976282370808353889 10385574732211778106265417)
          ·
            refine ⟨7789181049158833579699063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10385574732211778106265417 7789181049158833579699063)
            ·
              refine ⟨11683771573738250369548595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7789181049158833579699063 11683771573738250369548595)
              ·
                refine ⟨17525657360607375554322893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11683771573738250369548595 17525657360607375554322893)
                ·
                  refine ⟨6572121510227765832871085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17525657360607375554322893 6572121510227765832871085)
                  ·
                    refine ⟨2464545566335412187326657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6572121510227765832871085 2464545566335412187326657)
                    ·
                      refine ⟨1848409174751559140494993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2464545566335412187326657 1848409174751559140494993)
                      ·
                        rfl

theorem cell23_3599764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 1, 3, 3, 2].length) (baseStart_3599764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3599764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3599764 prefixEnd_3599764 := by exact prefixLift 3599764
  have htrace : WordTrace (prefixWord ++ tailWord_3599764) baseStart_3599764 baseEnd_3599764 := by
    simpa [prefixWord, tailWord_3599764, baseEnd_3599764] using wordTrace_append hprefix tailTrace_3599764
  have hstable : (prefixWord ++ tailWord_3599764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3599764).length < 2 ^ (prefixWord ++ tailWord_3599764).sum := by decide
  have hdescent : baseEnd_3599764 < baseStart_3599764 := by decide
  rcases family_descends (prefixWord ++ tailWord_3599764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3599823 : List Nat := [1, 1, 2, 1, 1, 4, 2, 2, 1, 1, 7]
def baseStart_3599823 : Nat := 118140960795 + 3599823 * 2 ^ 59
def prefixEnd_3599823 : Nat := 4983230072969 + 3 ^ 40 * 3599823 * 2
def baseEnd_3599823 : Nat := 1848439470110174409657221

theorem tailTrace_3599823 : CollatzResearch.WordTrace tailWord_3599823 prefixEnd_3599823 1848439470110174409657221 := by
  unfold tailWord_3599823
  simp only [CollatzResearch.WordTrace]
  refine ⟨131296331237463546666716123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87530887491642364444477415 131296331237463546666716123)
  ·
    refine ⟨196944496856195320000074185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131296331237463546666716123 196944496856195320000074185)
    ·
      refine ⟨147708372642146490000055639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196944496856195320000074185 147708372642146490000055639)
      ·
        refine ⟨221562558963219735000083459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147708372642146490000055639 221562558963219735000083459)
        ·
          refine ⟨332343838444829602500125189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221562558963219735000083459 332343838444829602500125189)
          ·
            refine ⟨62314469708405550468773473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 332343838444829602500125189 62314469708405550468773473)
            ·
              refine ⟨46735852281304162851580105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62314469708405550468773473 46735852281304162851580105)
              ·
                refine ⟨35051889210978122138685079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46735852281304162851580105 35051889210978122138685079)
                ·
                  refine ⟨52577833816467183208027619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35051889210978122138685079 52577833816467183208027619)
                  ·
                    refine ⟨78866750724700774812041429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52577833816467183208027619 78866750724700774812041429)
                    ·
                      refine ⟨1848439470110174409657221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 78866750724700774812041429 1848439470110174409657221)
                      ·
                        rfl

theorem cell23_3599823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 2, 1, 1, 7].length) (baseStart_3599823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3599823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3599823 prefixEnd_3599823 := by exact prefixLift 3599823
  have htrace : WordTrace (prefixWord ++ tailWord_3599823) baseStart_3599823 baseEnd_3599823 := by
    simpa [prefixWord, tailWord_3599823, baseEnd_3599823] using wordTrace_append hprefix tailTrace_3599823
  have hstable : (prefixWord ++ tailWord_3599823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3599823).length < 2 ^ (prefixWord ++ tailWord_3599823).sum := by decide
  have hdescent : baseEnd_3599823 < baseStart_3599823 := by decide
  rcases family_descends (prefixWord ++ tailWord_3599823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3599885 : List Nat := [1, 7, 1, 1, 3, 1, 1, 3, 5]
def baseStart_3599885 : Nat := 118140960795 + 3599885 * 2 ^ 59
def prefixEnd_3599885 : Nat := 4983230072969 + 3 ^ 40 * 3599885 * 2
def baseEnd_3599885 : Nat := 205385700656750351897993

theorem tailTrace_3599885 : CollatzResearch.WordTrace tailWord_3599885 prefixEnd_3599885 205385700656750351897993 := by
  unfold tailWord_3599885
  simp only [CollatzResearch.WordTrace]
  refine ⟨131298592563238931255473109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87532395042159287503648739 131298592563238931255473109)
  ·
    refine ⟨3077310763200912451300151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 131298592563238931255473109 3077310763200912451300151)
    ·
      refine ⟨4615966144801368676950227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3077310763200912451300151 4615966144801368676950227)
      ·
        refine ⟨6923949217202053015425341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4615966144801368676950227 6923949217202053015425341)
        ·
          refine ⟨2596480956450769880784503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6923949217202053015425341 2596480956450769880784503)
          ·
            refine ⟨3894721434676154821176755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2596480956450769880784503 3894721434676154821176755)
            ·
              refine ⟨5842082152014232231765133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3894721434676154821176755 5842082152014232231765133)
              ·
                refine ⟨2190780807005337086911925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5842082152014232231765133 2190780807005337086911925)
                ·
                  refine ⟨205385700656750351897993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2190780807005337086911925 205385700656750351897993)
                  ·
                    rfl

theorem cell23_3599885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 1, 3, 5].length) (baseStart_3599885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3599885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3599885 prefixEnd_3599885 := by exact prefixLift 3599885
  have htrace : WordTrace (prefixWord ++ tailWord_3599885) baseStart_3599885 baseEnd_3599885 := by
    simpa [prefixWord, tailWord_3599885, baseEnd_3599885] using wordTrace_append hprefix tailTrace_3599885
  have hstable : (prefixWord ++ tailWord_3599885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3599885).length < 2 ^ (prefixWord ++ tailWord_3599885).sum := by decide
  have hdescent : baseEnd_3599885 < baseStart_3599885 := by decide
  rcases family_descends (prefixWord ++ tailWord_3599885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3599904 : List Nat := [2, 1, 1, 6, 1, 2, 1, 2, 2, 2, 3]
def baseStart_3599904 : Nat := 118140960795 + 3599904 * 2 ^ 59
def prefixEnd_3599904 : Nat := 4983230072969 + 3 ^ 40 * 3599904 * 2
def baseEnd_3599904 : Nat := 1848481062043188592744349

theorem tailTrace_3599904 : CollatzResearch.WordTrace tailWord_3599904 prefixEnd_3599904 1848481062043188592744349 := by
  unfold tailWord_3599904
  simp only [CollatzResearch.WordTrace]
  refine ⟨65649642775085048750207383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87532857033446731666943177 65649642775085048750207383)
  ·
    refine ⟨98474464162627573125311075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65649642775085048750207383 98474464162627573125311075)
    ·
      refine ⟨147711696243941359687966613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98474464162627573125311075 147711696243941359687966613)
      ·
        refine ⟨6923985761434751235373435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 147711696243941359687966613 6923985761434751235373435)
        ·
          refine ⟨10385978642152126853060153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6923985761434751235373435 10385978642152126853060153)
          ·
            refine ⟨7789483981614095139795115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10385978642152126853060153 7789483981614095139795115)
            ·
              refine ⟨11684225972421142709692673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7789483981614095139795115 11684225972421142709692673)
              ·
                refine ⟨8763169479315857032269505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11684225972421142709692673 8763169479315857032269505)
                ·
                  refine ⟨6572377109486892774202129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8763169479315857032269505 6572377109486892774202129)
                  ·
                    refine ⟨4929282832115169580651597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6572377109486892774202129 4929282832115169580651597)
                    ·
                      refine ⟨1848481062043188592744349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4929282832115169580651597 1848481062043188592744349)
                      ·
                        rfl

theorem cell23_3599904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_3599904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3599904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3599904 prefixEnd_3599904 := by exact prefixLift 3599904
  have htrace : WordTrace (prefixWord ++ tailWord_3599904) baseStart_3599904 baseEnd_3599904 := by
    simpa [prefixWord, tailWord_3599904, baseEnd_3599904] using wordTrace_append hprefix tailTrace_3599904
  have hstable : (prefixWord ++ tailWord_3599904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3599904).length < 2 ^ (prefixWord ++ tailWord_3599904).sum := by decide
  have hdescent : baseEnd_3599904 < baseStart_3599904 := by decide
  rcases family_descends (prefixWord ++ tailWord_3599904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3599920 : List Nat := [2, 1, 1, 1, 2, 3, 1, 4, 3, 5]
def baseStart_3599920 : Nat := 118140960795 + 3599920 * 2 ^ 59
def prefixEnd_3599920 : Nat := 4983230072969 + 3 ^ 40 * 3599920 * 2
def baseEnd_3599920 : Nat := 616163092577886843381425

theorem tailTrace_3599920 : CollatzResearch.WordTrace tailWord_3599920 prefixEnd_3599920 616163092577886843381425 := by
  unfold tailWord_3599920
  simp only [CollatzResearch.WordTrace]
  refine ⟨65649934559056066116498607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87533246078741421488664809 65649934559056066116498607)
  ·
    refine ⟨98474901838584099174747911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65649934559056066116498607 98474901838584099174747911)
    ·
      refine ⟨147712352757876148762121867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98474901838584099174747911 147712352757876148762121867)
      ·
        refine ⟨221568529136814223143182801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147712352757876148762121867 221568529136814223143182801)
        ·
          refine ⟨166176396852610667357387101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 221568529136814223143182801 166176396852610667357387101)
          ·
            refine ⟨62316148819729000259020163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 166176396852610667357387101 62316148819729000259020163)
            ·
              refine ⟨93474223229593500388530245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62316148819729000259020163 93474223229593500388530245)
              ·
                refine ⟨17526416855548781322849421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 93474223229593500388530245 17526416855548781322849421)
                ·
                  refine ⟨6572406320830792996068533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17526416855548781322849421 6572406320830792996068533)
                  ·
                    refine ⟨616163092577886843381425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6572406320830792996068533 616163092577886843381425)
                    ·
                      rfl

theorem cell23_3599920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 4, 3, 5].length) (baseStart_3599920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3599920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3599920 prefixEnd_3599920 := by exact prefixLift 3599920
  have htrace : WordTrace (prefixWord ++ tailWord_3599920) baseStart_3599920 baseEnd_3599920 := by
    simpa [prefixWord, tailWord_3599920, baseEnd_3599920] using wordTrace_append hprefix tailTrace_3599920
  have hstable : (prefixWord ++ tailWord_3599920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3599920).length < 2 ^ (prefixWord ++ tailWord_3599920).sum := by decide
  have hdescent : baseEnd_3599920 < baseStart_3599920 := by decide
  rcases family_descends (prefixWord ++ tailWord_3599920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3599937 : List Nat := [1, 2, 5, 1, 1, 1, 3, 1, 3, 5]
def baseStart_3599937 : Nat := 118140960795 + 3599937 * 2 ^ 59
def prefixEnd_3599937 : Nat := 4983230072969 + 3 ^ 40 * 3599937 * 2
def baseEnd_3599937 : Nat := 616166002301595654543899

theorem tailTrace_3599937 : CollatzResearch.WordTrace tailWord_3599937 prefixEnd_3599937 616166002301595654543899 := by
  unfold tailWord_3599937
  simp only [CollatzResearch.WordTrace]
  refine ⟨131300489159050544136366065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87533659439367029424244043 131300489159050544136366065)
  ·
    refine ⟨98475366869287908102274549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131300489159050544136366065 98475366869287908102274549)
    ·
      refine ⟨9232065643995741384588239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 98475366869287908102274549 9232065643995741384588239)
      ·
        refine ⟨13848098465993612076882359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9232065643995741384588239 13848098465993612076882359)
        ·
          refine ⟨20772147698990418115323539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13848098465993612076882359 20772147698990418115323539)
          ·
            refine ⟨31158221548485627172985309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20772147698990418115323539 31158221548485627172985309)
            ·
              refine ⟨11684333080682110189869491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31158221548485627172985309 11684333080682110189869491)
              ·
                refine ⟨17526499621023165284804237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11684333080682110189869491 17526499621023165284804237)
                ·
                  refine ⟨6572437357883686981801589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17526499621023165284804237 6572437357883686981801589)
                  ·
                    refine ⟨616166002301595654543899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6572437357883686981801589 616166002301595654543899)
                    ·
                      rfl

theorem cell23_3599937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 1, 3, 5].length) (baseStart_3599937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3599937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3599937 prefixEnd_3599937 := by exact prefixLift 3599937
  have htrace : WordTrace (prefixWord ++ tailWord_3599937) baseStart_3599937 baseEnd_3599937 := by
    simpa [prefixWord, tailWord_3599937, baseEnd_3599937] using wordTrace_append hprefix tailTrace_3599937
  have hstable : (prefixWord ++ tailWord_3599937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3599937).length < 2 ^ (prefixWord ++ tailWord_3599937).sum := by decide
  have hdescent : baseEnd_3599937 < baseStart_3599937 := by decide
  rcases family_descends (prefixWord ++ tailWord_3599937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3599958 : List Nat := [5, 2, 2, 2, 1, 1, 2, 2, 6]
def baseStart_3599958 : Nat := 118140960795 + 3599958 * 2 ^ 59
def prefixEnd_3599958 : Nat := 4983230072969 + 3 ^ 40 * 3599958 * 2
def baseEnd_3599958 : Nat := 205389865555392375718789

theorem tailTrace_3599958 : CollatzResearch.WordTrace tailWord_3599958 prefixEnd_3599958 205389865555392375718789 := by
  unfold tailWord_3599958
  simp only [CollatzResearch.WordTrace]
  refine ⟨8206328443248404045180033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 87534170061316309815253685 8206328443248404045180033)
  ·
    refine ⟨6154746332436303033885025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8206328443248404045180033 6154746332436303033885025)
    ·
      refine ⟨4616059749327227275413769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6154746332436303033885025 4616059749327227275413769)
      ·
        refine ⟨3462044811995420456560327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4616059749327227275413769 3462044811995420456560327)
        ·
          refine ⟨5193067217993130684840491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3462044811995420456560327 5193067217993130684840491)
          ·
            refine ⟨7789600826989696027260737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5193067217993130684840491 7789600826989696027260737)
            ·
              refine ⟨5842200620242272020445553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7789600826989696027260737 5842200620242272020445553)
              ·
                refine ⟨4381650465181704015334165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5842200620242272020445553 4381650465181704015334165)
                ·
                  refine ⟨205389865555392375718789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4381650465181704015334165 205389865555392375718789)
                  ·
                    rfl

theorem cell23_3599958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 2, 2, 6].length) (baseStart_3599958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3599958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3599958 prefixEnd_3599958 := by exact prefixLift 3599958
  have htrace : WordTrace (prefixWord ++ tailWord_3599958) baseStart_3599958 baseEnd_3599958 := by
    simpa [prefixWord, tailWord_3599958, baseEnd_3599958] using wordTrace_append hprefix tailTrace_3599958
  have hstable : (prefixWord ++ tailWord_3599958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3599958).length < 2 ^ (prefixWord ++ tailWord_3599958).sum := by decide
  have hdescent : baseEnd_3599958 < baseStart_3599958 := by decide
  rcases family_descends (prefixWord ++ tailWord_3599958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3599977 : List Nat := [1, 2, 1, 1, 1, 4, 3, 2, 3, 2, 3]
def baseStart_3599977 : Nat := 118140960795 + 3599977 * 2 ^ 59
def prefixEnd_3599977 : Nat := 4983230072969 + 3 ^ 40 * 3599977 * 2
def baseEnd_3599977 : Nat := 1848518546130966807131513

theorem tailTrace_3599977 : CollatzResearch.WordTrace tailWord_3599977 prefixEnd_3599977 1848518546130966807131513 := by
  unfold tailWord_3599977
  simp only [CollatzResearch.WordTrace]
  refine ⟨131301948078905630967822185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87534632052603753978548123 131301948078905630967822185)
  ·
    refine ⟨98476461059179223225866639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131301948078905630967822185 98476461059179223225866639)
    ·
      refine ⟨147714691588768834838799959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98476461059179223225866639 147714691588768834838799959)
      ·
        refine ⟨221572037383153252258199939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147714691588768834838799959 221572037383153252258199939)
        ·
          refine ⟨332358056074729878387299909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221572037383153252258199939 332358056074729878387299909)
          ·
            refine ⟨62317135514011852197618733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 332358056074729878387299909 62317135514011852197618733)
            ·
              refine ⟨23368925817754444574107025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62317135514011852197618733 23368925817754444574107025)
              ·
                refine ⟨17526694363315833430580269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23368925817754444574107025 17526694363315833430580269)
                ·
                  refine ⟨6572510386243437536467601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17526694363315833430580269 6572510386243437536467601)
                  ·
                    refine ⟨4929382789682578152350701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6572510386243437536467601 4929382789682578152350701)
                    ·
                      refine ⟨1848518546130966807131513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4929382789682578152350701 1848518546130966807131513)
                      ·
                        rfl

theorem cell23_3599977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 2, 3, 2, 3].length) (baseStart_3599977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3599977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3599977 prefixEnd_3599977 := by exact prefixLift 3599977
  have htrace : WordTrace (prefixWord ++ tailWord_3599977) baseStart_3599977 baseEnd_3599977 := by
    simpa [prefixWord, tailWord_3599977, baseEnd_3599977] using wordTrace_append hprefix tailTrace_3599977
  have hstable : (prefixWord ++ tailWord_3599977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3599977).length < 2 ^ (prefixWord ++ tailWord_3599977).sum := by decide
  have hdescent : baseEnd_3599977 < baseStart_3599977 := by decide
  rcases family_descends (prefixWord ++ tailWord_3599977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3599984 : List Nat := [2, 1, 1, 1, 6, 1, 2, 3, 2, 4]
def baseStart_3599984 : Nat := 118140960795 + 3599984 * 2 ^ 59
def prefixEnd_3599984 : Nat := 4983230072969 + 3 ^ 40 * 3599984 * 2
def baseEnd_3599984 : Nat := 616174046831849426581327

theorem tailTrace_3599984 : CollatzResearch.WordTrace tailWord_3599984 prefixEnd_3599984 616174046831849426581327 := by
  unfold tailWord_3599984
  simp only [CollatzResearch.WordTrace]
  refine ⟨65651101694940135581663503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87534802259920180775551337 65651101694940135581663503)
  ·
    refine ⟨98476652542410203372495255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65651101694940135581663503 98476652542410203372495255)
    ·
      refine ⟨147714978813615305058742883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98476652542410203372495255 147714978813615305058742883)
      ·
        refine ⟨221572468220422957588114325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147714978813615305058742883 221572468220422957588114325)
        ·
          refine ⟨10386209447832326136942859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 221572468220422957588114325 10386209447832326136942859)
          ·
            refine ⟨15579314171748489205414289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10386209447832326136942859 15579314171748489205414289)
            ·
              refine ⟨11684485628811366904060717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15579314171748489205414289 11684485628811366904060717)
              ·
                refine ⟨4381682110804262589022769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11684485628811366904060717 4381682110804262589022769)
                ·
                  refine ⟨3286261583103196941767077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4381682110804262589022769 3286261583103196941767077)
                  ·
                    refine ⟨616174046831849426581327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3286261583103196941767077 616174046831849426581327)
                    ·
                      rfl

theorem cell23_3599984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 3, 2, 4].length) (baseStart_3599984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3599984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3599984 prefixEnd_3599984 := by exact prefixLift 3599984
  have htrace : WordTrace (prefixWord ++ tailWord_3599984) baseStart_3599984 baseEnd_3599984 := by
    simpa [prefixWord, tailWord_3599984, baseEnd_3599984] using wordTrace_append hprefix tailTrace_3599984
  have hstable : (prefixWord ++ tailWord_3599984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3599984).length < 2 ^ (prefixWord ++ tailWord_3599984).sum := by decide
  have hdescent : baseEnd_3599984 < baseStart_3599984 := by decide
  rcases family_descends (prefixWord ++ tailWord_3599984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3600018 : List Nat := [3, 2, 3, 1, 3, 2, 1, 2, 2, 4]
def baseStart_3600018 : Nat := 118140960795 + 3600018 * 2 ^ 59
def prefixEnd_3600018 : Nat := 4983230072969 + 3 ^ 40 * 3600018 * 2
def baseEnd_3600018 : Nat := 616179866279267048906275

theorem tailTrace_3600018 : CollatzResearch.WordTrace tailWord_3600018 prefixEnd_3600018 616179866279267048906275 := by
  unfold tailWord_3600018
  simp only [CollatzResearch.WordTrace]
  refine ⟨32825860867939273742516177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87535628981171396646709805 32825860867939273742516177)
  ·
    refine ⟨24619395650954455306887133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32825860867939273742516177 24619395650954455306887133)
    ·
      refine ⟨9232273369107920740082675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24619395650954455306887133 9232273369107920740082675)
      ·
        refine ⟨13848410053661881110124013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9232273369107920740082675 13848410053661881110124013)
        ·
          refine ⟨5193153770123205416296505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13848410053661881110124013 5193153770123205416296505)
          ·
            refine ⟨3894865327592404062222379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5193153770123205416296505 3894865327592404062222379)
            ·
              refine ⟨5842297991388606093333569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3894865327592404062222379 5842297991388606093333569)
              ·
                refine ⟨4381723493541454570000177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5842297991388606093333569 4381723493541454570000177)
                ·
                  refine ⟨3286292620156090927500133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4381723493541454570000177 3286292620156090927500133)
                  ·
                    refine ⟨616179866279267048906275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3286292620156090927500133 616179866279267048906275)
                    ·
                      rfl

theorem cell23_3600018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 1, 2, 2, 4].length) (baseStart_3600018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3600018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3600018 prefixEnd_3600018 := by exact prefixLift 3600018
  have htrace : WordTrace (prefixWord ++ tailWord_3600018) baseStart_3600018 baseEnd_3600018 := by
    simpa [prefixWord, tailWord_3600018, baseEnd_3600018] using wordTrace_append hprefix tailTrace_3600018
  have hstable : (prefixWord ++ tailWord_3600018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3600018).length < 2 ^ (prefixWord ++ tailWord_3600018).sum := by decide
  have hdescent : baseEnd_3600018 < baseStart_3600018 := by decide
  rcases family_descends (prefixWord ++ tailWord_3600018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3600051 : List Nat := [1, 1, 1, 2, 3, 3, 4, 2, 1, 3, 2]
def baseStart_3600051 : Nat := 118140960795 + 3600051 * 2 ^ 59
def prefixEnd_3600051 : Nat := 4983230072969 + 3 ^ 40 * 3600051 * 2
def baseEnd_3600051 : Nat := 1848556543699399517606173

theorem tailTrace_3600051 : CollatzResearch.WordTrace tailWord_3600051 prefixEnd_3600051 1848556543699399517606173 := by
  unfold tailWord_3600051
  simp only [CollatzResearch.WordTrace]
  refine ⟨131304647080637541606016007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87536431387091694404010671 131304647080637541606016007)
  ·
    refine ⟨196956970620956312409024011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131304647080637541606016007 196956970620956312409024011)
    ·
      refine ⟨295435455931434468613536017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196956970620956312409024011 295435455931434468613536017)
      ·
        refine ⟨221576591948575851460152013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 295435455931434468613536017 221576591948575851460152013)
        ·
          refine ⟨83091221980715944297557005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 221576591948575851460152013 83091221980715944297557005)
          ·
            refine ⟨31159208242768479111583877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83091221980715944297557005 31159208242768479111583877)
            ·
              refine ⟨5842351545519089833421977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31159208242768479111583877 5842351545519089833421977)
              ·
                refine ⟨4381763659139317375066483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5842351545519089833421977 4381763659139317375066483)
                ·
                  refine ⟨6572645488708976062599725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4381763659139317375066483 6572645488708976062599725)
                  ·
                    refine ⟨2464742058265866023474897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6572645488708976062599725 2464742058265866023474897)
                    ·
                      refine ⟨1848556543699399517606173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2464742058265866023474897 1848556543699399517606173)
                      ·
                        rfl

theorem cell23_3600051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 4, 2, 1, 3, 2].length) (baseStart_3600051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3600051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3600051 prefixEnd_3600051 := by exact prefixLift 3600051
  have htrace : WordTrace (prefixWord ++ tailWord_3600051) baseStart_3600051 baseEnd_3600051 := by
    simpa [prefixWord, tailWord_3600051, baseEnd_3600051] using wordTrace_append hprefix tailTrace_3600051
  have hstable : (prefixWord ++ tailWord_3600051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3600051).length < 2 ^ (prefixWord ++ tailWord_3600051).sum := by decide
  have hdescent : baseEnd_3600051 < baseStart_3600051 := by decide
  rcases family_descends (prefixWord ++ tailWord_3600051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3600064 : List Nat := [2, 1, 1, 2, 4, 1, 2, 1, 3, 4, 2]
def baseStart_3600064 : Nat := 118140960795 + 3600064 * 2 ^ 59
def prefixEnd_3600064 : Nat := 4983230072969 + 3 ^ 40 * 3600064 * 2
def baseEnd_3600064 : Nat := 1848563218947907966743613

theorem tailTrace_3600064 : CollatzResearch.WordTrace tailWord_3600064 prefixEnd_3600064 1848563218947907966743613 := by
  unfold tailWord_3600064
  simp only [CollatzResearch.WordTrace]
  refine ⟨65652560614795222413119623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87536747486393629884159497 65652560614795222413119623)
  ·
    refine ⟨98478840922192833619679435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65652560614795222413119623 98478840922192833619679435)
    ·
      refine ⟨147718261383289250429519153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98478840922192833619679435 147718261383289250429519153)
      ·
        refine ⟨110788696037466937822139365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147718261383289250429519153 110788696037466937822139365)
        ·
          refine ⟨20772880507025050841651131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110788696037466937822139365 20772880507025050841651131)
          ·
            refine ⟨31159320760537576262476697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20772880507025050841651131 31159320760537576262476697)
            ·
              refine ⟨23369490570403182196857523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31159320760537576262476697 23369490570403182196857523)
              ·
                refine ⟨35054235855604773295286285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23369490570403182196857523 35054235855604773295286285)
                ·
                  refine ⟨13145338445851789985732357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35054235855604773295286285 13145338445851789985732357)
                  ·
                    refine ⟨2464750958597210622324817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13145338445851789985732357 2464750958597210622324817)
                    ·
                      refine ⟨1848563218947907966743613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2464750958597210622324817 1848563218947907966743613)
                      ·
                        rfl

theorem cell23_3600064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 3, 4, 2].length) (baseStart_3600064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3600064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3600064 prefixEnd_3600064 := by exact prefixLift 3600064
  have htrace : WordTrace (prefixWord ++ tailWord_3600064) baseStart_3600064 baseEnd_3600064 := by
    simpa [prefixWord, tailWord_3600064, baseEnd_3600064] using wordTrace_append hprefix tailTrace_3600064
  have hstable : (prefixWord ++ tailWord_3600064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3600064).length < 2 ^ (prefixWord ++ tailWord_3600064).sum := by decide
  have hdescent : baseEnd_3600064 < baseStart_3600064 := by decide
  rcases family_descends (prefixWord ++ tailWord_3600064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3600081 : List Nat := [1, 2, 2, 1, 2, 4, 2, 1, 4, 2, 2]
def baseStart_3600081 : Nat := 118140960795 + 3600081 * 2 ^ 59
def prefixEnd_3600081 : Nat := 4983230072969 + 3 ^ 40 * 3600081 * 2
def baseEnd_3600081 : Nat := 1848571948119034400231035

theorem tailTrace_3600081 : CollatzResearch.WordTrace tailWord_3600081 prefixEnd_3600081 1848571948119034400231035 := by
  unfold tailWord_3600081
  simp only [CollatzResearch.WordTrace]
  refine ⟨131305741270528856729608097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87537160847019237819738731 131305741270528856729608097)
  ·
    refine ⟨98479305952896642547206073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131305741270528856729608097 98479305952896642547206073)
    ·
      refine ⟨73859479464672481910404555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98479305952896642547206073 73859479464672481910404555)
      ·
        refine ⟨110789219197008722865606833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73859479464672481910404555 110789219197008722865606833)
        ·
          refine ⟨83091914397756542149205125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110789219197008722865606833 83091914397756542149205125)
          ·
            refine ⟨15579733949579351652975961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83091914397756542149205125 15579733949579351652975961)
            ·
              refine ⟨11684800462184513739731971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15579733949579351652975961 11684800462184513739731971)
              ·
                refine ⟨17527200693276770609597957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11684800462184513739731971 17527200693276770609597957)
                ·
                  refine ⟨3286350129989394489299617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17527200693276770609597957 3286350129989394489299617)
                  ·
                    refine ⟨2464762597492045866974713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3286350129989394489299617 2464762597492045866974713)
                    ·
                      refine ⟨1848571948119034400231035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2464762597492045866974713 1848571948119034400231035)
                      ·
                        rfl

theorem cell23_3600081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 1, 4, 2, 2].length) (baseStart_3600081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3600081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3600081 prefixEnd_3600081 := by exact prefixLift 3600081
  have htrace : WordTrace (prefixWord ++ tailWord_3600081) baseStart_3600081 baseEnd_3600081 := by
    simpa [prefixWord, tailWord_3600081, baseEnd_3600081] using wordTrace_append hprefix tailTrace_3600081
  have hstable : (prefixWord ++ tailWord_3600081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3600081).length < 2 ^ (prefixWord ++ tailWord_3600081).sum := by decide
  have hdescent : baseEnd_3600081 < baseStart_3600081 := by decide
  rcases family_descends (prefixWord ++ tailWord_3600081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3600092 : List Nat := [2, 2, 5, 1, 2, 2, 2, 1, 2, 1, 3]
def baseStart_3600092 : Nat := 118140960795 + 3600092 * 2 ^ 59
def prefixEnd_3600092 : Nat := 4983230072969 + 3 ^ 40 * 3600092 * 2
def baseEnd_3600092 : Nat := 1848577596406233857193485

theorem tailTrace_3600092 : CollatzResearch.WordTrace tailWord_3600092 prefixEnd_3600092 1848577596406233857193485 := by
  unfold tailWord_3600092
  simp only [CollatzResearch.WordTrace]
  refine ⟨65653071236744502804129265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87537428315659337072172353 65653071236744502804129265)
  ·
    refine ⟨49239803427558377103096949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65653071236744502804129265 49239803427558377103096949)
    ·
      refine ⟨4616231571333597853415339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 49239803427558377103096949 4616231571333597853415339)
      ·
        refine ⟨6924347357000396780123009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4616231571333597853415339 6924347357000396780123009)
        ·
          refine ⟨5193260517750297585092257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6924347357000396780123009 5193260517750297585092257)
          ·
            refine ⟨3894945388312723188819193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5193260517750297585092257 3894945388312723188819193)
            ·
              refine ⟨2921209041234542391614395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3894945388312723188819193 2921209041234542391614395)
              ·
                refine ⟨4381813561851813587421593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2921209041234542391614395 4381813561851813587421593)
                ·
                  refine ⟨3286360171388860190566195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4381813561851813587421593 3286360171388860190566195)
                  ·
                    refine ⟨4929540257083290285849293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3286360171388860190566195 4929540257083290285849293)
                    ·
                      refine ⟨1848577596406233857193485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4929540257083290285849293 1848577596406233857193485)
                      ·
                        rfl

theorem cell23_3600092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 2, 1, 2, 1, 3].length) (baseStart_3600092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3600092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3600092 prefixEnd_3600092 := by exact prefixLift 3600092
  have htrace : WordTrace (prefixWord ++ tailWord_3600092) baseStart_3600092 baseEnd_3600092 := by
    simpa [prefixWord, tailWord_3600092, baseEnd_3600092] using wordTrace_append hprefix tailTrace_3600092
  have hstable : (prefixWord ++ tailWord_3600092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3600092).length < 2 ^ (prefixWord ++ tailWord_3600092).sum := by decide
  have hdescent : baseEnd_3600092 < baseStart_3600092 := by decide
  rcases family_descends (prefixWord ++ tailWord_3600092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3600127 : List Nat := [1, 1, 2, 2, 1, 3, 3, 2, 1, 2, 5]
def baseStart_3600127 : Nat := 118140960795 + 3600127 * 2 ^ 59
def prefixEnd_3600127 : Nat := 4983230072969 + 3 ^ 40 * 3600127 * 2
def baseEnd_3600127 : Nat := 1848595568229141220255823

theorem tailTrace_3600127 : CollatzResearch.WordTrace tailWord_3600127 prefixEnd_3600127 1848595568229141220255823 := by
  unfold tailWord_3600127
  simp only [CollatzResearch.WordTrace]
  refine ⟨131307419028362206585782635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87538279352241471057188423 131307419028362206585782635)
  ·
    refine ⟨196961128542543309878673953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131307419028362206585782635 196961128542543309878673953)
    ·
      refine ⟨147720846406907482409005465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196961128542543309878673953 147720846406907482409005465)
      ·
        refine ⟨110790634805180611806754099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147720846406907482409005465 110790634805180611806754099)
        ·
          refine ⟨166185952207770917710131149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110790634805180611806754099 166185952207770917710131149)
          ·
            refine ⟨62319732077914094141299181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 166185952207770917710131149 62319732077914094141299181)
            ·
              refine ⟨23369899529217785302987193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62319732077914094141299181 23369899529217785302987193)
              ·
                refine ⟨17527424646913338977240395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23369899529217785302987193 17527424646913338977240395)
                ·
                  refine ⟨26291136970370008465860593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17527424646913338977240395 26291136970370008465860593)
                  ·
                    refine ⟨19718352727777506349395445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26291136970370008465860593 19718352727777506349395445)
                    ·
                      refine ⟨1848595568229141220255823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19718352727777506349395445 1848595568229141220255823)
                      ·
                        rfl

theorem cell23_3600127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 2, 1, 2, 5].length) (baseStart_3600127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3600127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3600127 prefixEnd_3600127 := by exact prefixLift 3600127
  have htrace : WordTrace (prefixWord ++ tailWord_3600127) baseStart_3600127 baseEnd_3600127 := by
    simpa [prefixWord, tailWord_3600127, baseEnd_3600127] using wordTrace_append hprefix tailTrace_3600127
  have hstable : (prefixWord ++ tailWord_3600127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3600127).length < 2 ^ (prefixWord ++ tailWord_3600127).sum := by decide
  have hdescent : baseEnd_3600127 < baseStart_3600127 := by decide
  rcases family_descends (prefixWord ++ tailWord_3600127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3600137 : List Nat := [1, 2, 1, 1, 3, 2, 1, 2, 3, 3, 4]
def baseStart_3600137 : Nat := 118140960795 + 3600137 * 2 ^ 59
def prefixEnd_3600137 : Nat := 4983230072969 + 3 ^ 40 * 3600137 * 2
def baseEnd_3600137 : Nat := 1848600703035686181130777

theorem tailTrace_3600137 : CollatzResearch.WordTrace tailWord_3600137 prefixEnd_3600137 1848600703035686181130777 := by
  unfold tailWord_3600137
  simp only [CollatzResearch.WordTrace]
  refine ⟨131307783758325978293646665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87538522505550652195764443 131307783758325978293646665)
  ·
    refine ⟨98480837818744483720234999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131307783758325978293646665 98480837818744483720234999)
    ·
      refine ⟨147721256728116725580352499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98480837818744483720234999 147721256728116725580352499)
      ·
        refine ⟨221581885092175088370528749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147721256728116725580352499 221581885092175088370528749)
        ·
          refine ⟨83093206909565658138948281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 221581885092175088370528749 83093206909565658138948281)
          ·
            refine ⟨62319905182174243604211211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83093206909565658138948281 62319905182174243604211211)
            ·
              refine ⟨93479857773261365406316817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62319905182174243604211211 93479857773261365406316817)
              ·
                refine ⟨70109893329946024054737613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93479857773261365406316817 70109893329946024054737613)
                ·
                  refine ⟨26291209998729759020526605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70109893329946024054737613 26291209998729759020526605)
                  ·
                    refine ⟨9859203749523659632697477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26291209998729759020526605 9859203749523659632697477)
                    ·
                      refine ⟨1848600703035686181130777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9859203749523659632697477 1848600703035686181130777)
                      ·
                        rfl

theorem cell23_3600137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 3, 3, 4].length) (baseStart_3600137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3600137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3600137 prefixEnd_3600137 := by exact prefixLift 3600137
  have htrace : WordTrace (prefixWord ++ tailWord_3600137) baseStart_3600137 baseEnd_3600137 := by
    simpa [prefixWord, tailWord_3600137, baseEnd_3600137] using wordTrace_append hprefix tailTrace_3600137
  have hstable : (prefixWord ++ tailWord_3600137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3600137).length < 2 ^ (prefixWord ++ tailWord_3600137).sum := by decide
  have hdescent : baseEnd_3600137 < baseStart_3600137 := by decide
  rcases family_descends (prefixWord ++ tailWord_3600137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3600138 : List Nat := [3, 1, 2, 2, 1, 5, 2, 2, 5]
def baseStart_3600138 : Nat := 118140960795 + 3600138 * 2 ^ 59
def prefixEnd_3600138 : Nat := 4983230072969 + 3 ^ 40 * 3600138 * 2
def baseEnd_3600138 : Nat := 205400135168482297468697

theorem tailTrace_3600138 : CollatzResearch.WordTrace tailWord_3600138 prefixEnd_3600138 205400135168482297468697 := by
  unfold tailWord_3600138
  simp only [CollatzResearch.WordTrace]
  refine ⟨32826955057830588866108267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87538546820881570309622045 32826955057830588866108267)
  ·
    refine ⟨49240432586745883299162401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32826955057830588866108267 49240432586745883299162401)
    ·
      refine ⟨36930324440059412474371801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49240432586745883299162401 36930324440059412474371801)
      ·
        refine ⟨27697743330044559355778851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36930324440059412474371801 27697743330044559355778851)
        ·
          refine ⟨41546614995066839033668277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27697743330044559355778851 41546614995066839033668277)
          ·
            refine ⟨3894995155787516159406401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41546614995066839033668277 3894995155787516159406401)
            ·
              refine ⟨2921246366840637119554801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3894995155787516159406401 2921246366840637119554801)
              ·
                refine ⟨2190934775130477839666101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2921246366840637119554801 2190934775130477839666101)
                ·
                  refine ⟨205400135168482297468697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2190934775130477839666101 205400135168482297468697)
                  ·
                    rfl

theorem cell23_3600138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 2, 2, 5].length) (baseStart_3600138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3600138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3600138 prefixEnd_3600138 := by exact prefixLift 3600138
  have htrace : WordTrace (prefixWord ++ tailWord_3600138) baseStart_3600138 baseEnd_3600138 := by
    simpa [prefixWord, tailWord_3600138, baseEnd_3600138] using wordTrace_append hprefix tailTrace_3600138
  have hstable : (prefixWord ++ tailWord_3600138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3600138).length < 2 ^ (prefixWord ++ tailWord_3600138).sum := by decide
  have hdescent : baseEnd_3600138 < baseStart_3600138 := by decide
  rcases family_descends (prefixWord ++ tailWord_3600138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3600197 : List Nat := [1, 3, 1, 1, 1, 2, 3, 1, 1, 1, 8]
def baseStart_3600197 : Nat := 118140960795 + 3600197 * 2 ^ 59
def prefixEnd_3600197 : Nat := 4983230072969 + 3 ^ 40 * 3600197 * 2
def baseEnd_3600197 : Nat := 1848631511874955946380501

theorem tailTrace_3600197 : CollatzResearch.WordTrace tailWord_3600197 prefixEnd_3600197 1848631511874955946380501 := by
  unfold tailWord_3600197
  simp only [CollatzResearch.WordTrace]
  refine ⟨131309972138108608540830845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87539981425405739027220563 131309972138108608540830845)
  ·
    refine ⟨49241239551790728202811567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131309972138108608540830845 49241239551790728202811567)
    ·
      refine ⟨73861859327686092304217351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49241239551790728202811567 73861859327686092304217351)
      ·
        refine ⟨110792788991529138456326027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73861859327686092304217351 110792788991529138456326027)
        ·
          refine ⟨166189183487293707684489041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110792788991529138456326027 166189183487293707684489041)
          ·
            refine ⟨124641887615470280763366781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166189183487293707684489041 124641887615470280763366781)
            ·
              refine ⟨46740707855801355286262543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124641887615470280763366781 46740707855801355286262543)
              ·
                refine ⟨70111061783702032929393815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46740707855801355286262543 70111061783702032929393815)
                ·
                  refine ⟨105166592675553049394090723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70111061783702032929393815 105166592675553049394090723)
                  ·
                    refine ⟨157749889013329574091136085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 105166592675553049394090723 157749889013329574091136085)
                    ·
                      refine ⟨1848631511874955946380501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 157749889013329574091136085 1848631511874955946380501)
                      ·
                        rfl

theorem cell23_3600197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 1, 8].length) (baseStart_3600197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3600197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3600197 prefixEnd_3600197 := by exact prefixLift 3600197
  have htrace : WordTrace (prefixWord ++ tailWord_3600197) baseStart_3600197 baseEnd_3600197 := by
    simpa [prefixWord, tailWord_3600197, baseEnd_3600197] using wordTrace_append hprefix tailTrace_3600197
  have hstable : (prefixWord ++ tailWord_3600197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3600197).length < 2 ^ (prefixWord ++ tailWord_3600197).sum := by decide
  have hdescent : baseEnd_3600197 < baseStart_3600197 := by decide
  rcases family_descends (prefixWord ++ tailWord_3600197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3600231 : List Nat := [1, 1, 5, 1, 2, 1, 1, 3, 1, 5, 2]
def baseStart_3600231 : Nat := 118140960795 + 3600231 * 2 ^ 59
def prefixEnd_3600231 : Nat := 4983230072969 + 3 ^ 40 * 3600231 * 2
def baseEnd_3600231 : Nat := 1848648970217208813355345

theorem tailTrace_3600231 : CollatzResearch.WordTrace tailWord_3600231 prefixEnd_3600231 1848648970217208813355345 := by
  unfold tailWord_3600231
  simp only [CollatzResearch.WordTrace]
  refine ⟨131311212219985432347568547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87540808146656954898379031 131311212219985432347568547)
  ·
    refine ⟨196966818329978148521352821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131311212219985432347568547 196966818329978148521352821)
    ·
      refine ⟨18465639218435451423876827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 196966818329978148521352821 18465639218435451423876827)
      ·
        refine ⟨27698458827653177135815241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18465639218435451423876827 27698458827653177135815241)
        ·
          refine ⟨20773844120739882851861431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27698458827653177135815241 20773844120739882851861431)
          ·
            refine ⟨31160766181109824277792147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20773844120739882851861431 31160766181109824277792147)
            ·
              refine ⟨46741149271664736416688221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31160766181109824277792147 46741149271664736416688221)
              ·
                refine ⟨17527930976874276156258083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46741149271664736416688221 17527930976874276156258083)
                ·
                  refine ⟨26291896465311414234387125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17527930976874276156258083 26291896465311414234387125)
                  ·
                    refine ⟨2464865293622945084473793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26291896465311414234387125 2464865293622945084473793)
                    ·
                      refine ⟨1848648970217208813355345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2464865293622945084473793 1848648970217208813355345)
                      ·
                        rfl

theorem cell23_3600231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 3, 1, 5, 2].length) (baseStart_3600231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3600231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3600231 prefixEnd_3600231 := by exact prefixLift 3600231
  have htrace : WordTrace (prefixWord ++ tailWord_3600231) baseStart_3600231 baseEnd_3600231 := by
    simpa [prefixWord, tailWord_3600231, baseEnd_3600231] using wordTrace_append hprefix tailTrace_3600231
  have hstable : (prefixWord ++ tailWord_3600231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3600231).length < 2 ^ (prefixWord ++ tailWord_3600231).sum := by decide
  have hdescent : baseEnd_3600231 < baseStart_3600231 := by decide
  rcases family_descends (prefixWord ++ tailWord_3600231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3600295 : List Nat := [1, 1, 6, 1, 2, 2, 3, 1, 1, 1, 4]
def baseStart_3600295 : Nat := 118140960795 + 3600295 * 2 ^ 59
def prefixEnd_3600295 : Nat := 4983230072969 + 3 ^ 40 * 3600295 * 2
def baseEnd_3600295 : Nat := 1848681832979096562955051

theorem tailTrace_3600295 : CollatzResearch.WordTrace tailWord_3600295 prefixEnd_3600295 1848681832979096562955051 := by
  unfold tailWord_3600295
  simp only [CollatzResearch.WordTrace]
  refine ⟨131313546491753571277898339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87542364327835714185265559 131313546491753571277898339)
  ·
    refine ⟨196970319737630356916847509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131313546491753571277898339 196970319737630356916847509)
    ·
      refine ⟨9232983737701422980477227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 196970319737630356916847509 9232983737701422980477227)
      ·
        refine ⟨13849475606552134470715841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9232983737701422980477227 13849475606552134470715841)
        ·
          refine ⟨10387106704914100853036881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13849475606552134470715841 10387106704914100853036881)
          ·
            refine ⟨7790330028685575639777661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10387106704914100853036881 7790330028685575639777661)
            ·
              refine ⟨2921373760757090864916623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7790330028685575639777661 2921373760757090864916623)
              ·
                refine ⟨4382060641135636297374935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2921373760757090864916623 4382060641135636297374935)
                ·
                  refine ⟨6573090961703454446062403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4382060641135636297374935 6573090961703454446062403)
                  ·
                    refine ⟨9859636442555181669093605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6573090961703454446062403 9859636442555181669093605)
                    ·
                      refine ⟨1848681832979096562955051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9859636442555181669093605 1848681832979096562955051)
                      ·
                        rfl

theorem cell23_3600295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 3, 1, 1, 1, 4].length) (baseStart_3600295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3600295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3600295 prefixEnd_3600295 := by exact prefixLift 3600295
  have htrace : WordTrace (prefixWord ++ tailWord_3600295) baseStart_3600295 baseEnd_3600295 := by
    simpa [prefixWord, tailWord_3600295, baseEnd_3600295] using wordTrace_append hprefix tailTrace_3600295
  have hstable : (prefixWord ++ tailWord_3600295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3600295).length < 2 ^ (prefixWord ++ tailWord_3600295).sum := by decide
  have hdescent : baseEnd_3600295 < baseStart_3600295 := by decide
  rcases family_descends (prefixWord ++ tailWord_3600295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3600328 : List Nat := [2, 1, 3, 1, 4, 2, 2, 1, 1, 3, 3]
def baseStart_3600328 : Nat := 118140960795 + 3600328 * 2 ^ 59
def prefixEnd_3600328 : Nat := 4983230072969 + 3 ^ 40 * 3600328 * 2
def baseEnd_3600328 : Nat := 1848698777840694933842399

theorem tailTrace_3600328 : CollatzResearch.WordTrace tailWord_3600328 prefixEnd_3600328 1848698777840694933842399 := by
  unfold tailWord_3600328
  simp only [CollatzResearch.WordTrace]
  refine ⟨65657375050317008956924819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87543166733756011942566425 65657375050317008956924819)
  ·
    refine ⟨98486062575475513435387229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65657375050317008956924819 98486062575475513435387229)
    ·
      refine ⟨36932273465803317538270211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98486062575475513435387229 36932273465803317538270211)
      ·
        refine ⟨55398410198704976307405317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36932273465803317538270211 55398410198704976307405317)
        ·
          refine ⟨10387201912257183057638497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55398410198704976307405317 10387201912257183057638497)
          ·
            refine ⟨7790401434192887293228873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10387201912257183057638497 7790401434192887293228873)
            ·
              refine ⟨5842801075644665469921655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7790401434192887293228873 5842801075644665469921655)
              ·
                refine ⟨8764201613466998204882483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5842801075644665469921655 8764201613466998204882483)
                ·
                  refine ⟨13146302420200497307323725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8764201613466998204882483 13146302420200497307323725)
                  ·
                    refine ⟨4929863407575186490246397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13146302420200497307323725 4929863407575186490246397)
                    ·
                      refine ⟨1848698777840694933842399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4929863407575186490246397 1848698777840694933842399)
                      ·
                        rfl

theorem cell23_3600328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 2, 1, 1, 3, 3].length) (baseStart_3600328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3600328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3600328 prefixEnd_3600328 := by exact prefixLift 3600328
  have htrace : WordTrace (prefixWord ++ tailWord_3600328) baseStart_3600328 baseEnd_3600328 := by
    simpa [prefixWord, tailWord_3600328, baseEnd_3600328] using wordTrace_append hprefix tailTrace_3600328
  have hstable : (prefixWord ++ tailWord_3600328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3600328).length < 2 ^ (prefixWord ++ tailWord_3600328).sum := by decide
  have hdescent : baseEnd_3600328 < baseStart_3600328 := by decide
  rcases family_descends (prefixWord ++ tailWord_3600328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3600344 : List Nat := [2, 1, 2, 2, 2, 2, 1, 2, 1, 8]
def baseStart_3600344 : Nat := 118140960795 + 3600344 * 2 ^ 59
def prefixEnd_3600344 : Nat := 4983230072969 + 3 ^ 40 * 3600344 * 2
def baseEnd_3600344 : Nat := 616235664510388957080775

theorem tailTrace_3600344 : CollatzResearch.WordTrace tailWord_3600344 prefixEnd_3600344 616235664510388957080775 := by
  unfold tailWord_3600344
  simp only [CollatzResearch.WordTrace]
  refine ⟨65657666834288026323216043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87543555779050701764288057 65657666834288026323216043)
  ·
    refine ⟨98486500251432039484824065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65657666834288026323216043 98486500251432039484824065)
    ·
      refine ⟨73864875188574029613618049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98486500251432039484824065 73864875188574029613618049)
      ·
        refine ⟨55398656391430522210213537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73864875188574029613618049 55398656391430522210213537)
        ·
          refine ⟨41548992293572891657660153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55398656391430522210213537 41548992293572891657660153)
          ·
            refine ⟨31161744220179668743245115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41548992293572891657660153 31161744220179668743245115)
            ·
              refine ⟨46742616330269503114867673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31161744220179668743245115 46742616330269503114867673)
              ·
                refine ⟨35056962247702127336150755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46742616330269503114867673 35056962247702127336150755)
                ·
                  refine ⟨52585443371553191004226133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35056962247702127336150755 52585443371553191004226133)
                  ·
                    refine ⟨616235664510388957080775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 52585443371553191004226133 616235664510388957080775)
                    ·
                      rfl

theorem cell23_3600344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 2, 1, 8].length) (baseStart_3600344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3600344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3600344 prefixEnd_3600344 := by exact prefixLift 3600344
  have htrace : WordTrace (prefixWord ++ tailWord_3600344) baseStart_3600344 baseEnd_3600344 := by
    simpa [prefixWord, tailWord_3600344, baseEnd_3600344] using wordTrace_append hprefix tailTrace_3600344
  have hstable : (prefixWord ++ tailWord_3600344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3600344).length < 2 ^ (prefixWord ++ tailWord_3600344).sum := by decide
  have hdescent : baseEnd_3600344 < baseStart_3600344 := by decide
  rcases family_descends (prefixWord ++ tailWord_3600344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3600349 : List Nat := [1, 4, 3, 1, 4, 1, 2, 1, 1, 2, 3]
def baseStart_3600349 : Nat := 118140960795 + 3600349 * 2 ^ 59
def prefixEnd_3600349 : Nat := 4983230072969 + 3 ^ 40 * 3600349 * 2
def baseEnd_3600349 : Nat := 1848709560934439351679803

theorem tailTrace_3600349 : CollatzResearch.WordTrace tailWord_3600349 prefixEnd_3600349 1848709560934439351679803 := by
  unfold tailWord_3600349
  simp only [CollatzResearch.WordTrace]
  refine ⟨131315516033557938500364101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87543677355705292333576067 131315516033557938500364101)
  ·
    refine ⟨24621659256292113468818269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 131315516033557938500364101 24621659256292113468818269)
    ·
      refine ⟨9233122221109542550806851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24621659256292113468818269 9233122221109542550806851)
      ·
        refine ⟨13849683331664313826210277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9233122221109542550806851 13849683331664313826210277)
        ·
          refine ⟨2596815624687058842414427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13849683331664313826210277 2596815624687058842414427)
          ·
            refine ⟨3895223437030588263621641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2596815624687058842414427 3895223437030588263621641)
            ·
              refine ⟨2921417577772941197716231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3895223437030588263621641 2921417577772941197716231)
              ·
                refine ⟨4382126366659411796574347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2921417577772941197716231 4382126366659411796574347)
                ·
                  refine ⟨6573189549989117694861521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4382126366659411796574347 6573189549989117694861521)
                  ·
                    refine ⟨4929892162491838271146141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6573189549989117694861521 4929892162491838271146141)
                    ·
                      refine ⟨1848709560934439351679803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4929892162491838271146141 1848709560934439351679803)
                      ·
                        rfl

theorem cell23_3600349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 2, 1, 1, 2, 3].length) (baseStart_3600349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3600349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3600349 prefixEnd_3600349 := by exact prefixLift 3600349
  have htrace : WordTrace (prefixWord ++ tailWord_3600349) baseStart_3600349 baseEnd_3600349 := by
    simpa [prefixWord, tailWord_3600349, baseEnd_3600349] using wordTrace_append hprefix tailTrace_3600349
  have hstable : (prefixWord ++ tailWord_3600349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3600349).length < 2 ^ (prefixWord ++ tailWord_3600349).sum := by decide
  have hdescent : baseEnd_3600349 < baseStart_3600349 := by decide
  rcases family_descends (prefixWord ++ tailWord_3600349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3600355 : List Nat := [1, 1, 1, 6, 1, 3, 1, 3, 1, 3, 2]
def baseStart_3600355 : Nat := 118140960795 + 3600355 * 2 ^ 59
def prefixEnd_3600355 : Nat := 4983230072969 + 3 ^ 40 * 3600355 * 2
def baseEnd_3600355 : Nat := 1848712641818366328204775

theorem tailTrace_3600355 : CollatzResearch.WordTrace tailWord_3600355 prefixEnd_3600355 1848712641818366328204775 := by
  unfold tailWord_3600355
  simp only [CollatzResearch.WordTrace]
  refine ⟨131315734871536201525082519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87543823247690801016721679 131315734871536201525082519)
  ·
    refine ⟨196973602307304302287623779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131315734871536201525082519 196973602307304302287623779)
    ·
      refine ⟨295460403460956453431435669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196973602307304302287623779 295460403460956453431435669)
      ·
        refine ⟨13849706412232333754598547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 295460403460956453431435669 13849706412232333754598547)
        ·
          refine ⟨20774559618348500631897821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13849706412232333754598547 20774559618348500631897821)
          ·
            refine ⟨7790459856880687736961683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20774559618348500631897821 7790459856880687736961683)
            ·
              refine ⟨11685689785321031605442525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7790459856880687736961683 11685689785321031605442525)
              ·
                refine ⟨4382133669495386852040947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11685689785321031605442525 4382133669495386852040947)
                ·
                  refine ⟨6573200504243080278061421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4382133669495386852040947 6573200504243080278061421)
                  ·
                    refine ⟨2464950189091155104273033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6573200504243080278061421 2464950189091155104273033)
                    ·
                      refine ⟨1848712641818366328204775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2464950189091155104273033 1848712641818366328204775)
                      ·
                        rfl

theorem cell23_3600355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 3, 1, 3, 2].length) (baseStart_3600355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3600355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3600355 prefixEnd_3600355 := by exact prefixLift 3600355
  have htrace : WordTrace (prefixWord ++ tailWord_3600355) baseStart_3600355 baseEnd_3600355 := by
    simpa [prefixWord, tailWord_3600355, baseEnd_3600355] using wordTrace_append hprefix tailTrace_3600355
  have hstable : (prefixWord ++ tailWord_3600355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3600355).length < 2 ^ (prefixWord ++ tailWord_3600355).sum := by decide
  have hdescent : baseEnd_3600355 < baseStart_3600355 := by decide
  rcases family_descends (prefixWord ++ tailWord_3600355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3600381 : List Nat := [1, 4, 1, 1, 1, 2, 4, 1, 2, 2, 4]
def baseStart_3600381 : Nat := 118140960795 + 3600381 * 2 ^ 59
def prefixEnd_3600381 : Nat := 4983230072969 + 3 ^ 40 * 3600381 * 2
def baseEnd_3600381 : Nat := 1848725992315383226479655

theorem tailTrace_3600381 : CollatzResearch.WordTrace tailWord_3600381 prefixEnd_3600381 1848725992315383226479655 := by
  unfold tailWord_3600381
  simp only [CollatzResearch.WordTrace]
  refine ⟨131316683169442007965528997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87544455446294671977019331 131316683169442007965528997)
  ·
    refine ⟨24621878094270376493536687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 131316683169442007965528997 24621878094270376493536687)
    ·
      refine ⟨36932817141405564740305031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24621878094270376493536687 36932817141405564740305031)
      ·
        refine ⟨55399225712108347110457547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36932817141405564740305031 55399225712108347110457547)
        ·
          refine ⟨83098838568162520665686321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55399225712108347110457547 83098838568162520665686321)
          ·
            refine ⟨62324128926121890499264741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83098838568162520665686321 62324128926121890499264741)
            ·
              refine ⟨11685774173647854468612139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62324128926121890499264741 11685774173647854468612139)
              ·
                refine ⟨17528661260471781702918209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11685774173647854468612139 17528661260471781702918209)
                ·
                  refine ⟨13146495945353836277188657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17528661260471781702918209 13146495945353836277188657)
                  ·
                    refine ⟨9859871959015377207891493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13146495945353836277188657 9859871959015377207891493)
                    ·
                      refine ⟨1848725992315383226479655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9859871959015377207891493 1848725992315383226479655)
                      ·
                        rfl

theorem cell23_3600381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 1, 2, 2, 4].length) (baseStart_3600381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3600381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3600381 prefixEnd_3600381 := by exact prefixLift 3600381
  have htrace : WordTrace (prefixWord ++ tailWord_3600381) baseStart_3600381 baseEnd_3600381 := by
    simpa [prefixWord, tailWord_3600381, baseEnd_3600381] using wordTrace_append hprefix tailTrace_3600381
  have hstable : (prefixWord ++ tailWord_3600381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3600381).length < 2 ^ (prefixWord ++ tailWord_3600381).sum := by decide
  have hdescent : baseEnd_3600381 < baseStart_3600381 := by decide
  rcases family_descends (prefixWord ++ tailWord_3600381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3600391 : List Nat := [1, 1, 4, 3, 1, 2, 2, 2, 7]
def baseStart_3600391 : Nat := 118140960795 + 3600391 * 2 ^ 59
def prefixEnd_3600391 : Nat := 4983230072969 + 3 ^ 40 * 3600391 * 2
def baseEnd_3600391 : Nat := 205414569680214243039401

theorem tailTrace_3600391 : CollatzResearch.WordTrace tailWord_3600391 prefixEnd_3600391 205414569680214243039401 := by
  unfold tailWord_3600391
  simp only [CollatzResearch.WordTrace]
  refine ⟨131317047899405779673393027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87544698599603853115595351 131317047899405779673393027)
  ·
    refine ⟨196975571849108669510089541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131317047899405779673393027 196975571849108669510089541)
    ·
      refine ⟨36932919721707875533141789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 196975571849108669510089541 36932919721707875533141789)
      ·
        refine ⟨13849844895640453324928171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36932919721707875533141789 13849844895640453324928171)
        ·
          refine ⟨20774767343460679987392257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13849844895640453324928171 20774767343460679987392257)
          ·
            refine ⟨15581075507595509990544193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20774767343460679987392257 15581075507595509990544193)
            ·
              refine ⟨11685806630696632492908145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15581075507595509990544193 11685806630696632492908145)
              ·
                refine ⟨8764354973022474369681109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11685806630696632492908145 8764354973022474369681109)
                ·
                  refine ⟨205414569680214243039401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8764354973022474369681109 205414569680214243039401)
                  ·
                    rfl

theorem cell23_3600391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 2, 7].length) (baseStart_3600391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3600391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3600391 prefixEnd_3600391 := by exact prefixLift 3600391
  have htrace : WordTrace (prefixWord ++ tailWord_3600391) baseStart_3600391 baseEnd_3600391 := by
    simpa [prefixWord, tailWord_3600391, baseEnd_3600391] using wordTrace_append hprefix tailTrace_3600391
  have hstable : (prefixWord ++ tailWord_3600391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3600391).length < 2 ^ (prefixWord ++ tailWord_3600391).sum := by decide
  have hdescent : baseEnd_3600391 < baseStart_3600391 := by decide
  rcases family_descends (prefixWord ++ tailWord_3600391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3600421 : List Nat := [1, 3, 1, 2, 2, 3, 1, 1, 4, 5]
def baseStart_3600421 : Nat := 118140960795 + 3600421 * 2 ^ 59
def prefixEnd_3600421 : Nat := 4983230072969 + 3 ^ 40 * 3600421 * 2
def baseEnd_3600421 : Nat := 616248843847187689993157

theorem tailTrace_3600421 : CollatzResearch.WordTrace tailWord_3600421 prefixEnd_3600421 616248843847187689993157 := by
  unfold tailWord_3600421
  simp only [CollatzResearch.WordTrace]
  refine ⟨131318142089297094796985117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87545428059531396531323411 131318142089297094796985117)
  ·
    refine ⟨49244303283486410548869419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131318142089297094796985117 49244303283486410548869419)
    ·
      refine ⟨73866454925229615823304129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49244303283486410548869419 73866454925229615823304129)
      ·
        refine ⟨55399841193922211867478097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73866454925229615823304129 55399841193922211867478097)
        ·
          refine ⟨41549880895441658900608573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55399841193922211867478097 41549880895441658900608573)
          ·
            refine ⟨15581205335790622087728215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41549880895441658900608573 15581205335790622087728215)
            ·
              refine ⟨23371808003685933131592323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15581205335790622087728215 23371808003685933131592323)
              ·
                refine ⟨35057712005528899697388485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23371808003685933131592323 35057712005528899697388485)
                ·
                  refine ⟨6573321001036668693260341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35057712005528899697388485 6573321001036668693260341)
                  ·
                    refine ⟨616248843847187689993157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6573321001036668693260341 616248843847187689993157)
                    ·
                      rfl

theorem cell23_3600421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 1, 4, 5].length) (baseStart_3600421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3600421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3600421 prefixEnd_3600421 := by exact prefixLift 3600421
  have htrace : WordTrace (prefixWord ++ tailWord_3600421) baseStart_3600421 baseEnd_3600421 := by
    simpa [prefixWord, tailWord_3600421, baseEnd_3600421] using wordTrace_append hprefix tailTrace_3600421
  have hstable : (prefixWord ++ tailWord_3600421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3600421).length < 2 ^ (prefixWord ++ tailWord_3600421).sum := by decide
  have hdescent : baseEnd_3600421 < baseStart_3600421 := by decide
  rcases family_descends (prefixWord ++ tailWord_3600421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3600438 : List Nat := [5, 1, 2, 1, 1, 1, 1, 2, 4, 5]
def baseStart_3600438 : Nat := 118140960795 + 3600438 * 2 ^ 59
def prefixEnd_3600438 : Nat := 4983230072969 + 3 ^ 40 * 3600438 * 2
def baseEnd_3600438 : Nat := 616251753570896501155631

theorem tailTrace_3600438 : CollatzResearch.WordTrace tailWord_3600438 prefixEnd_3600438 616251753570896501155631 := by
  unfold tailWord_3600438
  simp only [CollatzResearch.WordTrace]
  refine ⟨8207422633139719168772123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 87545841420157004466902645 8207422633139719168772123)
  ·
    refine ⟨12311133949709578753158185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8207422633139719168772123 12311133949709578753158185)
    ·
      refine ⟨9233350462282184064868639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12311133949709578753158185 9233350462282184064868639)
      ·
        refine ⟨13850025693423276097302959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9233350462282184064868639 13850025693423276097302959)
        ·
          refine ⟨20775038540134914145954439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13850025693423276097302959 20775038540134914145954439)
          ·
            refine ⟨31162557810202371218931659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20775038540134914145954439 31162557810202371218931659)
            ·
              refine ⟨46743836715303556828397489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31162557810202371218931659 46743836715303556828397489)
              ·
                refine ⟨35057877536477667621298117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46743836715303556828397489 35057877536477667621298117)
                ·
                  refine ⟨6573352038089562678993397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35057877536477667621298117 6573352038089562678993397)
                  ·
                    refine ⟨616251753570896501155631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6573352038089562678993397 616251753570896501155631)
                    ·
                      rfl

theorem cell23_3600438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 2, 4, 5].length) (baseStart_3600438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3600438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3600438 prefixEnd_3600438 := by exact prefixLift 3600438
  have htrace : WordTrace (prefixWord ++ tailWord_3600438) baseStart_3600438 baseEnd_3600438 := by
    simpa [prefixWord, tailWord_3600438, baseEnd_3600438] using wordTrace_append hprefix tailTrace_3600438
  have hstable : (prefixWord ++ tailWord_3600438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3600438).length < 2 ^ (prefixWord ++ tailWord_3600438).sum := by decide
  have hdescent : baseEnd_3600438 < baseStart_3600438 := by decide
  rcases family_descends (prefixWord ++ tailWord_3600438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3600458 : List Nat := [3, 1, 2, 1, 1, 2, 1, 2, 4, 4, 2]
def baseStart_3600458 : Nat := 118140960795 + 3600458 * 2 ^ 59
def prefixEnd_3600458 : Nat := 4983230072969 + 3 ^ 40 * 3600458 * 2
def baseEnd_3600458 : Nat := 1848765530325779425216801

theorem tailTrace_3600458 : CollatzResearch.WordTrace tailWord_3600458 prefixEnd_3600458 1848765530325779425216801 := by
  unfold tailWord_3600458
  simp only [CollatzResearch.WordTrace]
  refine ⟨32829872897540762529020507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87546327726775366744054685 32829872897540762529020507)
  ·
    refine ⟨49244809346311143793530761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32829872897540762529020507 49244809346311143793530761)
    ·
      refine ⟨36933607009733357845148071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49244809346311143793530761 36933607009733357845148071)
      ·
        refine ⟨55400410514600036767722107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36933607009733357845148071 55400410514600036767722107)
        ·
          refine ⟨83100615771900055151583161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55400410514600036767722107 83100615771900055151583161)
          ·
            refine ⟨62325461828925041363687371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83100615771900055151583161 62325461828925041363687371)
            ·
              refine ⟨93488192743387562045531057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62325461828925041363687371 93488192743387562045531057)
              ·
                refine ⟨70116144557540671534148293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93488192743387562045531057 70116144557540671534148293)
                ·
                  refine ⟨13146777104538875912652805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70116144557540671534148293 13146777104538875912652805)
                  ·
                    refine ⟨2465020707101039233622401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13146777104538875912652805 2465020707101039233622401)
                    ·
                      refine ⟨1848765530325779425216801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2465020707101039233622401 1848765530325779425216801)
                      ·
                        rfl

theorem cell23_3600458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 4, 4, 2].length) (baseStart_3600458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3600458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3600458 prefixEnd_3600458 := by exact prefixLift 3600458
  have htrace : WordTrace (prefixWord ++ tailWord_3600458) baseStart_3600458 baseEnd_3600458 := by
    simpa [prefixWord, tailWord_3600458, baseEnd_3600458] using wordTrace_append hprefix tailTrace_3600458
  have hstable : (prefixWord ++ tailWord_3600458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3600458).length < 2 ^ (prefixWord ++ tailWord_3600458).sum := by decide
  have hdescent : baseEnd_3600458 < baseStart_3600458 := by decide
  rcases family_descends (prefixWord ++ tailWord_3600458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3600498 : List Nat := [3, 2, 1, 2, 2, 2, 2, 3, 6]
def baseStart_3600498 : Nat := 118140960795 + 3600498 * 2 ^ 59
def prefixEnd_3600498 : Nat := 4983230072969 + 3 ^ 40 * 3600498 * 2
def baseEnd_3600498 : Nat := 205420674394662140968513

theorem tailTrace_3600498 : CollatzResearch.WordTrace tailWord_3600498 prefixEnd_3600498 205420674394662140968513 := by
  unfold tailWord_3600498
  simp only [CollatzResearch.WordTrace]
  refine ⟨32830237627504534236884537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87547300340012091298358765 32830237627504534236884537)
  ·
    refine ⟨24622678220628400677663403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32830237627504534236884537 24622678220628400677663403)
    ·
      refine ⟨36934017330942601016495105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24622678220628400677663403 36934017330942601016495105)
      ·
        refine ⟨27700512998206950762371329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36934017330942601016495105 27700512998206950762371329)
        ·
          refine ⟨20775384748655213071778497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27700512998206950762371329 20775384748655213071778497)
          ·
            refine ⟨15581538561491409803833873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20775384748655213071778497 15581538561491409803833873)
            ·
              refine ⟨11686153921118557352875405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15581538561491409803833873 11686153921118557352875405)
              ·
                refine ⟨4382307720419459007328277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11686153921118557352875405 4382307720419459007328277)
                ·
                  refine ⟨205420674394662140968513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4382307720419459007328277 205420674394662140968513)
                  ·
                    rfl

theorem cell23_3600498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 3, 6].length) (baseStart_3600498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3600498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3600498 prefixEnd_3600498 := by exact prefixLift 3600498
  have htrace : WordTrace (prefixWord ++ tailWord_3600498) baseStart_3600498 baseEnd_3600498 := by
    simpa [prefixWord, tailWord_3600498, baseEnd_3600498] using wordTrace_append hprefix tailTrace_3600498
  have hstable : (prefixWord ++ tailWord_3600498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3600498).length < 2 ^ (prefixWord ++ tailWord_3600498).sum := by decide
  have hdescent : baseEnd_3600498 < baseStart_3600498 := by decide
  rcases family_descends (prefixWord ++ tailWord_3600498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3600528 : List Nat := [2, 1, 1, 1, 1, 1, 7, 3, 1, 5]
def baseStart_3600528 : Nat := 118140960795 + 3600528 * 2 ^ 59
def prefixEnd_3600528 : Nat := 4983230072969 + 3 ^ 40 * 3600528 * 2
def baseEnd_3600528 : Nat := 616267157990531383780493

theorem tailTrace_3600528 : CollatzResearch.WordTrace tailWord_3600528 prefixEnd_3600528 616267157990531383780493 := by
  unfold tailWord_3600528
  simp only [CollatzResearch.WordTrace]
  refine ⟨65661022349954726035565119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87548029799939634714086825 65661022349954726035565119)
  ·
    refine ⟨98491533524932089053347679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65661022349954726035565119 98491533524932089053347679)
    ·
      refine ⟨147737300287398133580021519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98491533524932089053347679 147737300287398133580021519)
      ·
        refine ⟨221605950431097200370032279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147737300287398133580021519 221605950431097200370032279)
        ·
          refine ⟨332408925646645800555048419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221605950431097200370032279 332408925646645800555048419)
          ·
            refine ⟨498613388469968700832572629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 332408925646645800555048419 498613388469968700832572629)
            ·
              refine ⟨11686251292264891425763421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 498613388469968700832572629 11686251292264891425763421)
              ·
                refine ⟨4382344234599334284661283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11686251292264891425763421 4382344234599334284661283)
                ·
                  refine ⟨6573516351899001426991925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4382344234599334284661283 6573516351899001426991925)
                  ·
                    refine ⟨616267157990531383780493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6573516351899001426991925 616267157990531383780493)
                    ·
                      rfl

theorem cell23_3600528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 3, 1, 5].length) (baseStart_3600528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3600528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3600528 prefixEnd_3600528 := by exact prefixLift 3600528
  have htrace : WordTrace (prefixWord ++ tailWord_3600528) baseStart_3600528 baseEnd_3600528 := by
    simpa [prefixWord, tailWord_3600528, baseEnd_3600528] using wordTrace_append hprefix tailTrace_3600528
  have hstable : (prefixWord ++ tailWord_3600528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3600528).length < 2 ^ (prefixWord ++ tailWord_3600528).sum := by decide
  have hdescent : baseEnd_3600528 < baseStart_3600528 := by decide
  rcases family_descends (prefixWord ++ tailWord_3600528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3600571 : List Nat := [1, 1, 1, 1, 1, 2, 7, 9]
def baseStart_3600571 : Nat := 118140960795 + 3600571 * 2 ^ 59
def prefixEnd_3600571 : Nat := 4983230072969 + 3 ^ 40 * 3600571 * 2
def baseEnd_3600571 : Nat := 68474946431101388263103

theorem tailTrace_3600571 : CollatzResearch.WordTrace tailWord_3600571 prefixEnd_3600571 68474946431101388263103 := by
  unfold tailWord_3600571
  simp only [CollatzResearch.WordTrace]
  refine ⟨131323613038753670414945567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87549075359169113609963711 131323613038753670414945567)
  ·
    refine ⟨196985419558130505622418351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131323613038753670414945567 196985419558130505622418351)
    ·
      refine ⟨295478129337195758433627527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196985419558130505622418351 295478129337195758433627527)
      ·
        refine ⟨443217194005793637650441291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295478129337195758433627527 443217194005793637650441291)
        ·
          refine ⟨664825791008690456475661937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 443217194005793637650441291 664825791008690456475661937)
          ·
            refine ⟨498619343256517842356746453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 664825791008690456475661937 498619343256517842356746453)
            ·
              refine ⟨11686390857574636930236245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 498619343256517842356746453 11686390857574636930236245)
              ·
                refine ⟨68474946431101388263103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11686390857574636930236245 68474946431101388263103)
                ·
                  rfl

theorem cell23_3600571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 9].length) (baseStart_3600571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3600571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3600571 prefixEnd_3600571 := by exact prefixLift 3600571
  have htrace : WordTrace (prefixWord ++ tailWord_3600571) baseStart_3600571 baseEnd_3600571 := by
    simpa [prefixWord, tailWord_3600571, baseEnd_3600571] using wordTrace_append hprefix tailTrace_3600571
  have hstable : (prefixWord ++ tailWord_3600571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3600571).length < 2 ^ (prefixWord ++ tailWord_3600571).sum := by decide
  have hdescent : baseEnd_3600571 < baseStart_3600571 := by decide
  rcases family_descends (prefixWord ++ tailWord_3600571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3600605 : List Nat := [1, 4, 3, 2, 1, 2, 2, 8]
def baseStart_3600605 : Nat := 118140960795 + 3600605 * 2 ^ 59
def prefixEnd_3600605 : Nat := 4983230072969 + 3 ^ 40 * 3600605 * 2
def baseEnd_3600605 : Nat := 68475593036370012965875

theorem tailTrace_3600605 : CollatzResearch.WordTrace tailWord_3600605 prefixEnd_3600605 68475593036370012965875 := by
  unfold tailWord_3600605
  simp only [CollatzResearch.WordTrace]
  refine ⟨131324853120630494221683269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87549902080420329481122179 131324853120630494221683269)
  ·
    refine ⟨24623409960118217666565613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 131324853120630494221683269 24623409960118217666565613)
    ·
      refine ⟨9233778735044331624962105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24623409960118217666565613 9233778735044331624962105)
      ·
        refine ⟨6925334051283248718721579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9233778735044331624962105 6925334051283248718721579)
        ·
          refine ⟨10388001076924873078082369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6925334051283248718721579 10388001076924873078082369)
          ·
            refine ⟨7791000807693654808561777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10388001076924873078082369 7791000807693654808561777)
            ·
              refine ⟨5843250605770241106421333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7791000807693654808561777 5843250605770241106421333)
              ·
                refine ⟨68475593036370012965875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5843250605770241106421333 68475593036370012965875)
                ·
                  rfl

theorem cell23_3600605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 2, 8].length) (baseStart_3600605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3600605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3600605 prefixEnd_3600605 := by exact prefixLift 3600605
  have htrace : WordTrace (prefixWord ++ tailWord_3600605) baseStart_3600605 baseEnd_3600605 := by
    simpa [prefixWord, tailWord_3600605, baseEnd_3600605] using wordTrace_append hprefix tailTrace_3600605
  have hstable : (prefixWord ++ tailWord_3600605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3600605).length < 2 ^ (prefixWord ++ tailWord_3600605).sum := by decide
  have hdescent : baseEnd_3600605 < baseStart_3600605 := by decide
  rcases family_descends (prefixWord ++ tailWord_3600605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3600672 : List Nat := [2, 1, 1, 5, 2, 1, 1, 3, 1, 4, 2]
def baseStart_3600672 : Nat := 118140960795 + 3600672 * 2 ^ 59
def prefixEnd_3600672 : Nat := 4983230072969 + 3 ^ 40 * 3600672 * 2
def baseEnd_3600672 : Nat := 1848875415185841587940817

theorem tailTrace_3600672 : CollatzResearch.WordTrace tailWord_3600672 prefixEnd_3600672 1848875415185841587940817 := by
  unfold tailWord_3600672
  simp only [CollatzResearch.WordTrace]
  refine ⟨65663648405693882332186135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87551531207591843109581513 65663648405693882332186135)
  ·
    refine ⟨98495472608540823498279203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65663648405693882332186135 98495472608540823498279203)
    ·
      refine ⟨147743208912811235247418805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98495472608540823498279203 147743208912811235247418805)
      ·
        refine ⟨13850925835576053304445513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 147743208912811235247418805 13850925835576053304445513)
        ·
          refine ⟨10388194376682039978334135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13850925835576053304445513 10388194376682039978334135)
          ·
            refine ⟨15582291565023059967501203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10388194376682039978334135 15582291565023059967501203)
            ·
              refine ⟨23373437347534589951251805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15582291565023059967501203 23373437347534589951251805)
              ·
                refine ⟨8765039005325471231719427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23373437347534589951251805 8765039005325471231719427)
                ·
                  refine ⟨13147558507988206847579141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8765039005325471231719427 13147558507988206847579141)
                  ·
                    refine ⟨2465167220247788783921089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13147558507988206847579141 2465167220247788783921089)
                    ·
                      refine ⟨1848875415185841587940817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2465167220247788783921089 1848875415185841587940817)
                      ·
                        rfl

theorem cell23_3600672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 3, 1, 4, 2].length) (baseStart_3600672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3600672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3600672 prefixEnd_3600672 := by exact prefixLift 3600672
  have htrace : WordTrace (prefixWord ++ tailWord_3600672) baseStart_3600672 baseEnd_3600672 := by
    simpa [prefixWord, tailWord_3600672, baseEnd_3600672] using wordTrace_append hprefix tailTrace_3600672
  have hstable : (prefixWord ++ tailWord_3600672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3600672).length < 2 ^ (prefixWord ++ tailWord_3600672).sum := by decide
  have hdescent : baseEnd_3600672 < baseStart_3600672 := by decide
  rcases family_descends (prefixWord ++ tailWord_3600672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3600715 : List Nat := [1, 1, 1, 1, 3, 1, 1, 5, 2, 5, 2]
def baseStart_3600715 : Nat := 118140960795 + 3600715 * 2 ^ 59
def prefixEnd_3600715 : Nat := 4983230072969 + 3 ^ 40 * 3600715 * 2
def baseEnd_3600715 : Nat := 1848897494853984919703119

theorem tailTrace_3600715 : CollatzResearch.WordTrace tailWord_3600715 prefixEnd_3600715 1848897494853984919703119 := by
  unfold tailWord_3600715
  simp only [CollatzResearch.WordTrace]
  refine ⟨131328865150231983008187599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87552576766821322005458399 131328865150231983008187599)
  ·
    refine ⟨196993297725347974512281399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131328865150231983008187599 196993297725347974512281399)
    ·
      refine ⟨295489946588021961768422099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196993297725347974512281399 295489946588021961768422099)
      ·
        refine ⟨443234919882032942652633149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295489946588021961768422099 443234919882032942652633149)
        ·
          refine ⟨166213094955762353494737431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 443234919882032942652633149 166213094955762353494737431)
          ·
            refine ⟨249319642433643530242106147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166213094955762353494737431 249319642433643530242106147)
            ·
              refine ⟨373979463650465295363159221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 249319642433643530242106147 373979463650465295363159221)
              ·
                refine ⟨35060574717231121440296177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 373979463650465295363159221 35060574717231121440296177)
                ·
                  refine ⟨26295431037923341080222133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35060574717231121440296177 26295431037923341080222133)
                  ·
                    refine ⟨2465196659805313226270825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26295431037923341080222133 2465196659805313226270825)
                    ·
                      refine ⟨1848897494853984919703119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2465196659805313226270825 1848897494853984919703119)
                      ·
                        rfl

theorem cell23_3600715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 5, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 5, 2, 5, 2].length) (baseStart_3600715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3600715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3600715 prefixEnd_3600715 := by exact prefixLift 3600715
  have htrace : WordTrace (prefixWord ++ tailWord_3600715) baseStart_3600715 baseEnd_3600715 := by
    simpa [prefixWord, tailWord_3600715, baseEnd_3600715] using wordTrace_append hprefix tailTrace_3600715
  have hstable : (prefixWord ++ tailWord_3600715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3600715).length < 2 ^ (prefixWord ++ tailWord_3600715).sum := by decide
  have hdescent : baseEnd_3600715 < baseStart_3600715 := by decide
  rcases family_descends (prefixWord ++ tailWord_3600715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3600745 : List Nat := [1, 2, 1, 1, 1, 3, 4, 3, 2, 1, 4]
def baseStart_3600745 : Nat := 118140960795 + 3600745 * 2 ^ 59
def prefixEnd_3600745 : Nat := 4983230072969 + 3 ^ 40 * 3600745 * 2
def baseEnd_3600745 : Nat := 1848912899273619802327981

theorem tailTrace_3600745 : CollatzResearch.WordTrace tailWord_3600745 prefixEnd_3600745 1848912899273619802327981 := by
  unfold tailWord_3600745
  simp only [CollatzResearch.WordTrace]
  refine ⟨131329959340123298131779689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87553306226748865421186459 131329959340123298131779689)
  ·
    refine ⟨98497469505092473598834767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131329959340123298131779689 98497469505092473598834767)
    ·
      refine ⟨147746204257638710398252151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98497469505092473598834767 147746204257638710398252151)
      ·
        refine ⟨221619306386458065597378227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147746204257638710398252151 221619306386458065597378227)
        ·
          refine ⟨332428959579687098396067341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221619306386458065597378227 332428959579687098396067341)
          ·
            refine ⟨124660859842382661898525253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 332428959579687098396067341 124660859842382661898525253)
            ·
              refine ⟨23373911220446749105973485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 124660859842382661898525253 23373911220446749105973485)
              ·
                refine ⟨8765216707667530914740057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23373911220446749105973485 8765216707667530914740057)
                ·
                  refine ⟨6573912530750648186055043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8765216707667530914740057 6573912530750648186055043)
                  ·
                    refine ⟨9860868796125972279082565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6573912530750648186055043 9860868796125972279082565)
                    ·
                      refine ⟨1848912899273619802327981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9860868796125972279082565 1848912899273619802327981)
                      ·
                        rfl

theorem cell23_3600745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 3, 2, 1, 4].length) (baseStart_3600745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3600745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3600745 prefixEnd_3600745 := by exact prefixLift 3600745
  have htrace : WordTrace (prefixWord ++ tailWord_3600745) baseStart_3600745 baseEnd_3600745 := by
    simpa [prefixWord, tailWord_3600745, baseEnd_3600745] using wordTrace_append hprefix tailTrace_3600745
  have hstable : (prefixWord ++ tailWord_3600745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3600745).length < 2 ^ (prefixWord ++ tailWord_3600745).sum := by decide
  have hdescent : baseEnd_3600745 < baseStart_3600745 := by decide
  rcases family_descends (prefixWord ++ tailWord_3600745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3600915 : List Nat := [1, 1, 1, 2, 1, 5, 1, 1, 1, 4, 5]
def baseStart_3600915 : Nat := 118140960795 + 3600915 * 2 ^ 59
def prefixEnd_3600915 : Nat := 4983230072969 + 3 ^ 40 * 3600915 * 2
def baseEnd_3600915 : Nat := 1849000190984884137202199

theorem tailTrace_3600915 : CollatzResearch.WordTrace tailWord_3600915 prefixEnd_3600915 1849000190984884137202199 := by
  unfold tailWord_3600915
  simp only [CollatzResearch.WordTrace]
  refine ⟨131336159749507417165468199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87557439833004944776978799 131336159749507417165468199)
  ·
    refine ⟨197004239624261125748202299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131336159749507417165468199 197004239624261125748202299)
    ·
      refine ⟨295506359436391688622303449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197004239624261125748202299 295506359436391688622303449)
      ·
        refine ⟨221629769577293766466727587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 295506359436391688622303449 221629769577293766466727587)
        ·
          refine ⟨332444654365940649700091381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221629769577293766466727587 332444654365940649700091381)
          ·
            refine ⟨31166686346806935909383567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 332444654365940649700091381 31166686346806935909383567)
            ·
              refine ⟨46750029520210403864075351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31166686346806935909383567 46750029520210403864075351)
              ·
                refine ⟨70125044280315605796113027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46750029520210403864075351 70125044280315605796113027)
                ·
                  refine ⟨105187566420473408694169541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70125044280315605796113027 105187566420473408694169541)
                  ·
                    refine ⟨19722668703838764130156789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 105187566420473408694169541 19722668703838764130156789)
                    ·
                      refine ⟨1849000190984884137202199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19722668703838764130156789 1849000190984884137202199)
                      ·
                        rfl

theorem cell23_3600915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 4, 5].length) (baseStart_3600915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3600915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3600915 prefixEnd_3600915 := by exact prefixLift 3600915
  have htrace : WordTrace (prefixWord ++ tailWord_3600915) baseStart_3600915 baseEnd_3600915 := by
    simpa [prefixWord, tailWord_3600915, baseEnd_3600915] using wordTrace_append hprefix tailTrace_3600915
  have hstable : (prefixWord ++ tailWord_3600915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3600915).length < 2 ^ (prefixWord ++ tailWord_3600915).sum := by decide
  have hdescent : baseEnd_3600915 < baseStart_3600915 := by decide
  rcases family_descends (prefixWord ++ tailWord_3600915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3600920 : List Nat := [2, 1, 2, 3, 3, 3, 1, 3, 1, 2, 2]
def baseStart_3600920 : Nat := 118140960795 + 3600920 * 2 ^ 59
def prefixEnd_3600920 : Nat := 4983230072969 + 3 ^ 40 * 3600920 * 2
def baseEnd_3600920 : Nat := 1849002758388156617639677

theorem tailTrace_3600920 : CollatzResearch.WordTrace tailWord_3600920 prefixEnd_3600920 1849002758388156617639677 := by
  unfold tailWord_3600920
  simp only [CollatzResearch.WordTrace]
  refine ⟨65668171057244651509700107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87557561409659535346266809 65668171057244651509700107)
  ·
    refine ⟨98502256585866977264550161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65668171057244651509700107 98502256585866977264550161)
    ·
      refine ⟨73876692439400232948412621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98502256585866977264550161 73876692439400232948412621)
      ·
        refine ⟨27703759664775087355654733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73876692439400232948412621 27703759664775087355654733)
        ·
          refine ⟨10388909874290657758370525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27703759664775087355654733 10388909874290657758370525)
          ·
            refine ⟨3895841202858996659388947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10388909874290657758370525 3895841202858996659388947)
            ·
              refine ⟨5843761804288494989083421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3895841202858996659388947 5843761804288494989083421)
              ·
                refine ⟨2191410676608185620906283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5843761804288494989083421 2191410676608185620906283)
                ·
                  refine ⟨3287116014912278431359425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2191410676608185620906283 3287116014912278431359425)
                  ·
                    refine ⟨2465337011184208823519569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3287116014912278431359425 2465337011184208823519569)
                    ·
                      refine ⟨1849002758388156617639677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2465337011184208823519569 1849002758388156617639677)
                      ·
                        rfl

theorem cell23_3600920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 1, 3, 1, 2, 2].length) (baseStart_3600920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3600920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3600920 prefixEnd_3600920 := by exact prefixLift 3600920
  have htrace : WordTrace (prefixWord ++ tailWord_3600920) baseStart_3600920 baseEnd_3600920 := by
    simpa [prefixWord, tailWord_3600920, baseEnd_3600920] using wordTrace_append hprefix tailTrace_3600920
  have hstable : (prefixWord ++ tailWord_3600920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3600920).length < 2 ^ (prefixWord ++ tailWord_3600920).sum := by decide
  have hdescent : baseEnd_3600920 < baseStart_3600920 := by decide
  rcases family_descends (prefixWord ++ tailWord_3600920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3600936 : List Nat := [2, 1, 5, 2, 1, 1, 2, 1, 4, 1, 3]
def baseStart_3600936 : Nat := 118140960795 + 3600936 * 2 ^ 59
def prefixEnd_3600936 : Nat := 4983230072969 + 3 ^ 40 * 3600936 * 2
def baseEnd_3600936 : Nat := 1849010974078628555039603

theorem tailTrace_3600936 : CollatzResearch.WordTrace tailWord_3600936 prefixEnd_3600936 1849010974078628555039603 := by
  unfold tailWord_3600936
  simp only [CollatzResearch.WordTrace]
  refine ⟨65668462841215668875991331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87557950454954225167988441 65668462841215668875991331)
  ·
    refine ⟨98502694261823503313986997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65668462841215668875991331 98502694261823503313986997)
    ·
      refine ⟨9234627587045953435686281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 98502694261823503313986997 9234627587045953435686281)
      ·
        refine ⟨6925970690284465076764711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9234627587045953435686281 6925970690284465076764711)
        ·
          refine ⟨10388956035426697615147067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6925970690284465076764711 10388956035426697615147067)
          ·
            refine ⟨15583434053140046422720601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10388956035426697615147067 15583434053140046422720601)
            ·
              refine ⟨11687575539855034817040451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15583434053140046422720601 11687575539855034817040451)
              ·
                refine ⟨17531363309782552225560677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11687575539855034817040451 17531363309782552225560677)
                ·
                  refine ⟨3287130620584228542292627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17531363309782552225560677 3287130620584228542292627)
                  ·
                    refine ⟨4930695930876342813438941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3287130620584228542292627 4930695930876342813438941)
                    ·
                      refine ⟨1849010974078628555039603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4930695930876342813438941 1849010974078628555039603)
                      ·
                        rfl

theorem cell23_3600936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_3600936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3600936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3600936 prefixEnd_3600936 := by exact prefixLift 3600936
  have htrace : WordTrace (prefixWord ++ tailWord_3600936) baseStart_3600936 baseEnd_3600936 := by
    simpa [prefixWord, tailWord_3600936, baseEnd_3600936] using wordTrace_append hprefix tailTrace_3600936
  have hstable : (prefixWord ++ tailWord_3600936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3600936).length < 2 ^ (prefixWord ++ tailWord_3600936).sum := by decide
  have hdescent : baseEnd_3600936 < baseStart_3600936 := by decide
  rcases family_descends (prefixWord ++ tailWord_3600936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3600959 : List Nat := [1, 1, 2, 2, 3, 2, 2, 3, 1, 4, 2]
def baseStart_3600959 : Nat := 118140960795 + 3600959 * 2 ^ 59
def prefixEnd_3600959 : Nat := 4983230072969 + 3 ^ 40 * 3600959 * 2
def baseEnd_3600959 : Nat := 1849022784133681965051997

theorem tailTrace_3600959 : CollatzResearch.WordTrace tailWord_3600959 prefixEnd_3600959 1849022784133681965051997 := by
  unfold tailWord_3600959
  simp only [CollatzResearch.WordTrace]
  refine ⟨131337764561348012680069931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87558509707565341786713287 131337764561348012680069931)
  ·
    refine ⟨197006646842022019020104897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131337764561348012680069931 197006646842022019020104897)
    ·
      refine ⟨147754985131516514265078673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197006646842022019020104897 147754985131516514265078673)
      ·
        refine ⟨110816238848637385698809005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147754985131516514265078673 110816238848637385698809005)
        ·
          refine ⟨41556089568239019637053377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110816238848637385698809005 41556089568239019637053377)
          ·
            refine ⟨31167067176179264727790033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41556089568239019637053377 31167067176179264727790033)
            ·
              refine ⟨23375300382134448545842525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31167067176179264727790033 23375300382134448545842525)
              ·
                refine ⟨8765737643300418204690947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23375300382134448545842525 8765737643300418204690947)
                ·
                  refine ⟨13148606464950627307036421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8765737643300418204690947 13148606464950627307036421)
                  ·
                    refine ⟨2465363712178242620069329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13148606464950627307036421 2465363712178242620069329)
                    ·
                      refine ⟨1849022784133681965051997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2465363712178242620069329 1849022784133681965051997)
                      ·
                        rfl

theorem cell23_3600959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 3, 1, 4, 2].length) (baseStart_3600959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3600959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3600959 prefixEnd_3600959 := by exact prefixLift 3600959
  have htrace : WordTrace (prefixWord ++ tailWord_3600959) baseStart_3600959 baseEnd_3600959 := by
    simpa [prefixWord, tailWord_3600959, baseEnd_3600959] using wordTrace_append hprefix tailTrace_3600959
  have hstable : (prefixWord ++ tailWord_3600959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3600959).length < 2 ^ (prefixWord ++ tailWord_3600959).sum := by decide
  have hdescent : baseEnd_3600959 < baseStart_3600959 := by decide
  rcases family_descends (prefixWord ++ tailWord_3600959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3600993 : List Nat := [1, 2, 3, 1, 1, 5, 2, 2, 2, 2, 2]
def baseStart_3600993 : Nat := 118140960795 + 3600993 * 2 ^ 59
def prefixEnd_3600993 : Nat := 4983230072969 + 3 ^ 40 * 3600993 * 2
def baseEnd_3600993 : Nat := 1849040242475934832026841

theorem tailTrace_3600993 : CollatzResearch.WordTrace tailWord_3600993 prefixEnd_3600993 1849040242475934832026841 := by
  unfold tailWord_3600993
  simp only [CollatzResearch.WordTrace]
  refine ⟨131339004643224836486807633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87559336428816557657871755 131339004643224836486807633)
  ·
    refine ⟨98504253482418627365105725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131339004643224836486807633 98504253482418627365105725)
    ·
      refine ⟨36939095055906985261914647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98504253482418627365105725 36939095055906985261914647)
      ·
        refine ⟨55408642583860477892871971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36939095055906985261914647 55408642583860477892871971)
        ·
          refine ⟨83112963875790716839307957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55408642583860477892871971 83112963875790716839307957)
          ·
            refine ⟨7791840363355379703685121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 83112963875790716839307957 7791840363355379703685121)
            ·
              refine ⟨5843880272516534777763841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7791840363355379703685121 5843880272516534777763841)
              ·
                refine ⟨4382910204387401083322881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5843880272516534777763841 4382910204387401083322881)
                ·
                  refine ⟨3287182653290550812492161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4382910204387401083322881 3287182653290550812492161)
                  ·
                    refine ⟨2465386989967913109369121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3287182653290550812492161 2465386989967913109369121)
                    ·
                      refine ⟨1849040242475934832026841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2465386989967913109369121 1849040242475934832026841)
                      ·
                        rfl

theorem cell23_3600993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 2, 2, 2, 2, 2].length) (baseStart_3600993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3600993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3600993 prefixEnd_3600993 := by exact prefixLift 3600993
  have htrace : WordTrace (prefixWord ++ tailWord_3600993) baseStart_3600993 baseEnd_3600993 := by
    simpa [prefixWord, tailWord_3600993, baseEnd_3600993] using wordTrace_append hprefix tailTrace_3600993
  have hstable : (prefixWord ++ tailWord_3600993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3600993).length < 2 ^ (prefixWord ++ tailWord_3600993).sum := by decide
  have hdescent : baseEnd_3600993 < baseStart_3600993 := by decide
  rcases family_descends (prefixWord ++ tailWord_3600993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3601029 : List Nat := [1, 3, 1, 1, 4, 2, 3, 1, 2, 5]
def baseStart_3601029 : Nat := 118140960795 + 3601029 * 2 ^ 59
def prefixEnd_3601029 : Nat := 4983230072969 + 3 ^ 40 * 3601029 * 2
def baseEnd_3601029 : Nat := 616352909259832230392225

theorem tailTrace_3601029 : CollatzResearch.WordTrace tailWord_3601029 prefixEnd_3601029 616352909259832230392225 := by
  unfold tailWord_3601029
  simp only [CollatzResearch.WordTrace]
  refine ⟨131340317671094414635118141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87560211780729609756745427 131340317671094414635118141)
  ·
    refine ⟨49252619126660405488169303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131340317671094414635118141 49252619126660405488169303)
    ·
      refine ⟨73878928689990608232253955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49252619126660405488169303 73878928689990608232253955)
      ·
        refine ⟨110818393034985912348380933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73878928689990608232253955 110818393034985912348380933)
        ·
          refine ⟨20778448694059858565321425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110818393034985912348380933 20778448694059858565321425)
          ·
            refine ⟨15583836520544893923991069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20778448694059858565321425 15583836520544893923991069)
            ·
              refine ⟨5843938695204335221496651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15583836520544893923991069 5843938695204335221496651)
              ·
                refine ⟨8765908042806502832244977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5843938695204335221496651 8765908042806502832244977)
                ·
                  refine ⟨6574431032104877124183733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8765908042806502832244977 6574431032104877124183733)
                  ·
                    refine ⟨616352909259832230392225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6574431032104877124183733 616352909259832230392225)
                    ·
                      rfl

theorem cell23_3601029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 3, 1, 2, 5].length) (baseStart_3601029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3601029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3601029 prefixEnd_3601029 := by exact prefixLift 3601029
  have htrace : WordTrace (prefixWord ++ tailWord_3601029) baseStart_3601029 baseEnd_3601029 := by
    simpa [prefixWord, tailWord_3601029, baseEnd_3601029] using wordTrace_append hprefix tailTrace_3601029
  have hstable : (prefixWord ++ tailWord_3601029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3601029).length < 2 ^ (prefixWord ++ tailWord_3601029).sum := by decide
  have hdescent : baseEnd_3601029 < baseStart_3601029 := by decide
  rcases family_descends (prefixWord ++ tailWord_3601029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3601049 : List Nat := [1, 2, 1, 2, 1, 2, 3, 1, 4, 4, 2]
def baseStart_3601049 : Nat := 118140960795 + 3601049 * 2 ^ 59
def prefixEnd_3601049 : Nat := 4983230072969 + 3 ^ 40 * 3601049 * 2
def baseEnd_3601049 : Nat := 1849068997392586612926583

theorem tailTrace_3601049 : CollatzResearch.WordTrace tailWord_3601049 prefixEnd_3601049 1849068997392586612926583 := by
  unfold tailWord_3601049
  simp only [CollatzResearch.WordTrace]
  refine ⟨131341047131021958050846201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87560698087347972033897467 131341047131021958050846201)
  ·
    refine ⟨98505785348266468538134651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131341047131021958050846201 98505785348266468538134651)
    ·
      refine ⟨147758678022399702807201977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98505785348266468538134651 147758678022399702807201977)
      ·
        refine ⟨110819008516799777105401483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147758678022399702807201977 110819008516799777105401483)
        ·
          refine ⟨166228512775199665658102225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110819008516799777105401483 166228512775199665658102225)
          ·
            refine ⟨124671384581399749243576669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166228512775199665658102225 124671384581399749243576669)
            ·
              refine ⟨46751769218024905966341251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124671384581399749243576669 46751769218024905966341251)
              ·
                refine ⟨70127653827037358949511877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46751769218024905966341251 70127653827037358949511877)
                ·
                  refine ⟨13148935092569504803033477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70127653827037358949511877 13148935092569504803033477)
                  ·
                    refine ⟨2465425329856782150568777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13148935092569504803033477 2465425329856782150568777)
                    ·
                      refine ⟨1849068997392586612926583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2465425329856782150568777 1849068997392586612926583)
                      ·
                        rfl

theorem cell23_3601049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 4, 4, 2].length) (baseStart_3601049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3601049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3601049 prefixEnd_3601049 := by exact prefixLift 3601049
  have htrace : WordTrace (prefixWord ++ tailWord_3601049) baseStart_3601049 baseEnd_3601049 := by
    simpa [prefixWord, tailWord_3601049, baseEnd_3601049] using wordTrace_append hprefix tailTrace_3601049
  have hstable : (prefixWord ++ tailWord_3601049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3601049).length < 2 ^ (prefixWord ++ tailWord_3601049).sum := by decide
  have hdescent : baseEnd_3601049 < baseStart_3601049 := by decide
  rcases family_descends (prefixWord ++ tailWord_3601049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3601086 : List Nat := [4, 2, 1, 1, 2, 1, 2, 3, 2, 2, 3]
def baseStart_3601086 : Nat := 118140960795 + 3601086 * 2 ^ 59
def prefixEnd_3601086 : Nat := 4983230072969 + 3 ^ 40 * 3601086 * 2
def baseEnd_3601086 : Nat := 1849087996176802968163913

theorem tailTrace_3601086 : CollatzResearch.WordTrace tailWord_3601086 prefixEnd_3601086 1849087996176802968163913 := by
  unfold tailWord_3601086
  simp only [CollatzResearch.WordTrace]
  refine ⟨16417799578985989171242889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87561597754591942246628741 16417799578985989171242889)
  ·
    refine ⟨12313349684239491878432167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16417799578985989171242889 12313349684239491878432167)
    ·
      refine ⟨18470024526359237817648251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12313349684239491878432167 18470024526359237817648251)
      ·
        refine ⟨27705036789538856726472377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18470024526359237817648251 27705036789538856726472377)
        ·
          refine ⟨20778777592154142544854283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27705036789538856726472377 20778777592154142544854283)
          ·
            refine ⟨31168166388231213817281425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20778777592154142544854283 31168166388231213817281425)
            ·
              refine ⟨23376124791173410362961069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31168166388231213817281425 23376124791173410362961069)
              ·
                refine ⟨8766046796690028886110401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23376124791173410362961069 8766046796690028886110401)
                ·
                  refine ⟨6574535097517521664582801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8766046796690028886110401 6574535097517521664582801)
                  ·
                    refine ⟨4930901323138141248437101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6574535097517521664582801 4930901323138141248437101)
                    ·
                      refine ⟨1849087996176802968163913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4930901323138141248437101 1849087996176802968163913)
                      ·
                        rfl

theorem cell23_3601086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 3, 2, 2, 3].length) (baseStart_3601086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3601086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3601086 prefixEnd_3601086 := by exact prefixLift 3601086
  have htrace : WordTrace (prefixWord ++ tailWord_3601086) baseStart_3601086 baseEnd_3601086 := by
    simpa [prefixWord, tailWord_3601086, baseEnd_3601086] using wordTrace_append hprefix tailTrace_3601086
  have hstable : (prefixWord ++ tailWord_3601086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3601086).length < 2 ^ (prefixWord ++ tailWord_3601086).sum := by decide
  have hdescent : baseEnd_3601086 < baseStart_3601086 := by decide
  rcases family_descends (prefixWord ++ tailWord_3601086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3601123 : List Nat := [1, 1, 1, 7, 1, 3, 2, 1, 6]
def baseStart_3601123 : Nat := 118140960795 + 3601123 * 2 ^ 59
def prefixEnd_3601123 : Nat := 4983230072969 + 3 ^ 40 * 3601123 * 2
def baseEnd_3601123 : Nat := 205456332773446591489027

theorem tailTrace_3601123 : CollatzResearch.WordTrace tailWord_3601123 prefixEnd_3601123 205456332773446591489027 := by
  unfold tailWord_3601123
  simp only [CollatzResearch.WordTrace]
  refine ⟨131343746132753868689040023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87562497421835912459360015 131343746132753868689040023)
  ·
    refine ⟨197015619199130803033560035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131343746132753868689040023 197015619199130803033560035)
    ·
      refine ⟨295523428798696204550340053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197015619199130803033560035 295523428798696204550340053)
      ·
        refine ⟨6926330362469442294148595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 295523428798696204550340053 6926330362469442294148595)
        ·
          refine ⟨10389495543704163441222893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6926330362469442294148595 10389495543704163441222893)
          ·
            refine ⟨3896060828889061290458585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10389495543704163441222893 3896060828889061290458585)
            ·
              refine ⟨2922045621666795967843939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3896060828889061290458585 2922045621666795967843939)
              ·
                refine ⟨4383068432500193951765909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2922045621666795967843939 4383068432500193951765909)
                ·
                  refine ⟨205456332773446591489027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4383068432500193951765909 205456332773446591489027)
                  ·
                    rfl

theorem cell23_3601123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 2, 1, 6].length) (baseStart_3601123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3601123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3601123 prefixEnd_3601123 := by exact prefixLift 3601123
  have htrace : WordTrace (prefixWord ++ tailWord_3601123) baseStart_3601123 baseEnd_3601123 := by
    simpa [prefixWord, tailWord_3601123, baseEnd_3601123] using wordTrace_append hprefix tailTrace_3601123
  have hstable : (prefixWord ++ tailWord_3601123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3601123).length < 2 ^ (prefixWord ++ tailWord_3601123).sum := by decide
  have hdescent : baseEnd_3601123 < baseStart_3601123 := by decide
  rcases family_descends (prefixWord ++ tailWord_3601123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3601149 : List Nat := [1, 4, 1, 1, 1, 1, 5, 2, 1, 6]
def baseStart_3601149 : Nat := 118140960795 + 3601149 * 2 ^ 59
def prefixEnd_3601149 : Nat := 4983230072969 + 3 ^ 40 * 3601149 * 2
def baseEnd_3601149 : Nat := 616373448486012073892041

theorem tailTrace_3601149 : CollatzResearch.WordTrace tailWord_3601149 prefixEnd_3601149 616373448486012073892041 := by
  unfold tailWord_3601149
  simp only [CollatzResearch.WordTrace]
  refine ⟨131344694430659675129486501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87563129620439783419657667 131344694430659675129486501)
  ·
    refine ⟨24627130205748689086778719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 131344694430659675129486501 24627130205748689086778719)
    ·
      refine ⟨36940695308623033630168079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24627130205748689086778719 36940695308623033630168079)
      ·
        refine ⟨55411042962934550445252119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36940695308623033630168079 55411042962934550445252119)
        ·
          refine ⟨83116564444401825667878179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55411042962934550445252119 83116564444401825667878179)
          ·
            refine ⟨124674846666602738501817269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83116564444401825667878179 124674846666602738501817269)
            ·
              refine ⟨11688266874994006734545369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 124674846666602738501817269 11688266874994006734545369)
              ·
                refine ⟨8766200156245505050909027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11688266874994006734545369 8766200156245505050909027)
                ·
                  refine ⟨13149300234368257576363541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8766200156245505050909027 13149300234368257576363541)
                  ·
                    refine ⟨616373448486012073892041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13149300234368257576363541 616373448486012073892041)
                    ·
                      rfl

theorem cell23_3601149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 2, 1, 6].length) (baseStart_3601149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3601149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3601149 prefixEnd_3601149 := by exact prefixLift 3601149
  have htrace : WordTrace (prefixWord ++ tailWord_3601149) baseStart_3601149 baseEnd_3601149 := by
    simpa [prefixWord, tailWord_3601149, baseEnd_3601149] using wordTrace_append hprefix tailTrace_3601149
  have hstable : (prefixWord ++ tailWord_3601149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3601149).length < 2 ^ (prefixWord ++ tailWord_3601149).sum := by decide
  have hdescent : baseEnd_3601149 < baseStart_3601149 := by decide
  rcases family_descends (prefixWord ++ tailWord_3601149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3601173 : List Nat := [1, 3, 2, 1, 2, 2, 2, 3, 3, 2, 2]
def baseStart_3601173 : Nat := 118140960795 + 3601173 * 2 ^ 59
def prefixEnd_3601173 : Nat := 4983230072969 + 3 ^ 40 * 3601173 * 2
def baseEnd_3601173 : Nat := 1849132668993744127776013

theorem tailTrace_3601173 : CollatzResearch.WordTrace tailWord_3601173 prefixEnd_3601173 1849132668993744127776013 := by
  unfold tailWord_3601173
  simp only [CollatzResearch.WordTrace]
  refine ⟨131345569782572727228360173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87563713188381818152240115 131345569782572727228360173)
  ·
    refine ⟨49254588668464772710635065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131345569782572727228360173 49254588668464772710635065)
    ·
      refine ⟨36940941501348579532976299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49254588668464772710635065 36940941501348579532976299)
      ·
        refine ⟨55411412252022869299464449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36940941501348579532976299 55411412252022869299464449)
        ·
          refine ⟨41558559189017151974598337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55411412252022869299464449 41558559189017151974598337)
          ·
            refine ⟨31168919391762863980948753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41558559189017151974598337 31168919391762863980948753)
            ·
              refine ⟨23376689543822147985711565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31168919391762863980948753 23376689543822147985711565)
              ·
                refine ⟨8766258578933305494641837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23376689543822147985711565 8766258578933305494641837)
                ·
                  refine ⟨3287346967099989560490689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8766258578933305494641837 3287346967099989560490689)
                  ·
                    refine ⟨2465510225324992170368017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3287346967099989560490689 2465510225324992170368017)
                    ·
                      refine ⟨1849132668993744127776013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2465510225324992170368017 1849132668993744127776013)
                      ·
                        rfl

theorem cell23_3601173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 3, 3, 2, 2].length) (baseStart_3601173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3601173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3601173 prefixEnd_3601173 := by exact prefixLift 3601173
  have htrace : WordTrace (prefixWord ++ tailWord_3601173) baseStart_3601173 baseEnd_3601173 := by
    simpa [prefixWord, tailWord_3601173, baseEnd_3601173] using wordTrace_append hprefix tailTrace_3601173
  have hstable : (prefixWord ++ tailWord_3601173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3601173).length < 2 ^ (prefixWord ++ tailWord_3601173).sum := by decide
  have hdescent : baseEnd_3601173 < baseStart_3601173 := by decide
  rcases family_descends (prefixWord ++ tailWord_3601173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3601186 : List Nat := [3, 3, 1, 1, 2, 2, 1, 3, 1, 2, 4]
def baseStart_3601186 : Nat := 118140960795 + 3601186 * 2 ^ 59
def prefixEnd_3601186 : Nat := 4983230072969 + 3 ^ 40 * 3601186 * 2
def baseEnd_3601186 : Nat := 1849139344242252576913453

theorem tailTrace_3601186 : CollatzResearch.WordTrace tailWord_3601186 prefixEnd_3601186 1849139344242252576913453 := by
  unfold tailWord_3601186
  simp only [CollatzResearch.WordTrace]
  refine ⟨32836510982881407612145853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87564029287683753632388941 32836510982881407612145853)
  ·
    refine ⟨12313691618580527854554695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32836510982881407612145853 12313691618580527854554695)
    ·
      refine ⟨18470537427870791781832043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12313691618580527854554695 18470537427870791781832043)
      ·
        refine ⟨27705806141806187672748065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18470537427870791781832043 27705806141806187672748065)
        ·
          refine ⟨20779354606354640754561049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27705806141806187672748065 20779354606354640754561049)
          ·
            refine ⟨15584515954765980565920787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20779354606354640754561049 15584515954765980565920787)
            ·
              refine ⟨23376773932148970848881181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15584515954765980565920787 23376773932148970848881181)
              ·
                refine ⟨8766290224555864068330443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23376773932148970848881181 8766290224555864068330443)
                ·
                  refine ⟨13149435336833796102495665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8766290224555864068330443 13149435336833796102495665)
                  ·
                    refine ⟨9862076502625347076871749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13149435336833796102495665 9862076502625347076871749)
                    ·
                      refine ⟨1849139344242252576913453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9862076502625347076871749 1849139344242252576913453)
                      ·
                        rfl

theorem cell23_3601186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 3, 1, 2, 4].length) (baseStart_3601186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3601186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3601186 prefixEnd_3601186 := by exact prefixLift 3601186
  have htrace : WordTrace (prefixWord ++ tailWord_3601186) baseStart_3601186 baseEnd_3601186 := by
    simpa [prefixWord, tailWord_3601186, baseEnd_3601186] using wordTrace_append hprefix tailTrace_3601186
  have hstable : (prefixWord ++ tailWord_3601186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3601186).length < 2 ^ (prefixWord ++ tailWord_3601186).sum := by decide
  have hdescent : baseEnd_3601186 < baseStart_3601186 := by decide
  rcases family_descends (prefixWord ++ tailWord_3601186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3601194 : List Nat := [3, 1, 4, 3, 2, 1, 1, 1, 2, 3, 2]
def baseStart_3601194 : Nat := 118140960795 + 3601194 * 2 ^ 59
def prefixEnd_3601194 : Nat := 4983230072969 + 3 ^ 40 * 3601194 * 2
def baseEnd_3601194 : Nat := 1849143452087488545613417

theorem tailTrace_3601194 : CollatzResearch.WordTrace tailWord_3601194 prefixEnd_3601194 1849143452087488545613417 := by
  unfold tailWord_3601194
  simp only [CollatzResearch.WordTrace]
  refine ⟨32836583928874161953718659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87564223810331098543249757 32836583928874161953718659)
  ·
    refine ⟨49254875893311242930577989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32836583928874161953718659 49254875893311242930577989)
    ·
      refine ⟨9235289229995858049483373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49254875893311242930577989 9235289229995858049483373)
      ·
        refine ⟨3463233461248446768556265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9235289229995858049483373 3463233461248446768556265)
        ·
          refine ⟨2597425095936335076417199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3463233461248446768556265 2597425095936335076417199)
          ·
            refine ⟨3896137643904502614625799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2597425095936335076417199 3896137643904502614625799)
            ·
              refine ⟨5844206465856753921938699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3896137643904502614625799 5844206465856753921938699)
              ·
                refine ⟨8766309698785130882908049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5844206465856753921938699 8766309698785130882908049)
                ·
                  refine ⟨6574732274088848162181037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8766309698785130882908049 6574732274088848162181037)
                  ·
                    refine ⟨2465524602783318060817889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6574732274088848162181037 2465524602783318060817889)
                    ·
                      refine ⟨1849143452087488545613417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2465524602783318060817889 1849143452087488545613417)
                      ·
                        rfl

theorem cell23_3601194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_3601194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3601194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3601194 prefixEnd_3601194 := by exact prefixLift 3601194
  have htrace : WordTrace (prefixWord ++ tailWord_3601194) baseStart_3601194 baseEnd_3601194 := by
    simpa [prefixWord, tailWord_3601194, baseEnd_3601194] using wordTrace_append hprefix tailTrace_3601194
  have hstable : (prefixWord ++ tailWord_3601194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3601194).length < 2 ^ (prefixWord ++ tailWord_3601194).sum := by decide
  have hdescent : baseEnd_3601194 < baseStart_3601194 := by decide
  rcases family_descends (prefixWord ++ tailWord_3601194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3601217 : List Nat := [1, 2, 5, 3, 1, 2, 1, 2, 2, 4]
def baseStart_3601217 : Nat := 118140960795 + 3601217 * 2 ^ 59
def prefixEnd_3601217 : Nat := 4983230072969 + 3 ^ 40 * 3601217 * 2
def baseEnd_3601217 : Nat := 616385087380847318541937

theorem tailTrace_3601217 : CollatzResearch.WordTrace tailWord_3601217 prefixEnd_3601217 616385087380847318541937 := by
  unfold tailWord_3601217
  simp only [CollatzResearch.WordTrace]
  refine ⟨131347174594413322742961905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87564783062942215161974603 131347174594413322742961905)
  ·
    refine ⟨98510380945809992057221429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131347174594413322742961905 98510380945809992057221429)
    ·
      refine ⟨9235348213669686755364509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 98510380945809992057221429 9235348213669686755364509)
      ·
        refine ⟨3463255580126132533261691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9235348213669686755364509 3463255580126132533261691)
        ·
          refine ⟨5194883370189198799892537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3463255580126132533261691 5194883370189198799892537)
          ·
            refine ⟨3896162527641899099919403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5194883370189198799892537 3896162527641899099919403)
            ·
              refine ⟨5844243791462848649879105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3896162527641899099919403 5844243791462848649879105)
              ·
                refine ⟨4383182843597136487409329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5844243791462848649879105 4383182843597136487409329)
                ·
                  refine ⟨3287387132697852365556997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4383182843597136487409329 3287387132697852365556997)
                  ·
                    refine ⟨616385087380847318541937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3287387132697852365556997 616385087380847318541937)
                    ·
                      rfl

theorem cell23_3601217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 1, 2, 2, 4].length) (baseStart_3601217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3601217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3601217 prefixEnd_3601217 := by exact prefixLift 3601217
  have htrace : WordTrace (prefixWord ++ tailWord_3601217) baseStart_3601217 baseEnd_3601217 := by
    simpa [prefixWord, tailWord_3601217, baseEnd_3601217] using wordTrace_append hprefix tailTrace_3601217
  have hstable : (prefixWord ++ tailWord_3601217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3601217).length < 2 ^ (prefixWord ++ tailWord_3601217).sum := by decide
  have hdescent : baseEnd_3601217 < baseStart_3601217 := by decide
  rcases family_descends (prefixWord ++ tailWord_3601217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3601259 : List Nat := [1, 1, 1, 1, 2, 2, 4, 2, 1, 4, 4]
def baseStart_3601259 : Nat := 118140960795 + 3601259 * 2 ^ 59
def prefixEnd_3601259 : Nat := 4983230072969 + 3 ^ 40 * 3601259 * 2
def baseEnd_3601259 : Nat := 1849176828330030791300617

theorem tailTrace_3601259 : CollatzResearch.WordTrace tailWord_3601259 prefixEnd_3601259 1849176828330030791300617 := by
  unfold tailWord_3601259
  simp only [CollatzResearch.WordTrace]
  refine ⟨131348706460261163915990831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87565804306840775943993887 131348706460261163915990831)
  ·
    refine ⟨197023059690391745873986247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131348706460261163915990831 197023059690391745873986247)
    ·
      refine ⟨295534589535587618810979371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197023059690391745873986247 295534589535587618810979371)
      ·
        refine ⟨443301884303381428216469057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295534589535587618810979371 443301884303381428216469057)
        ·
          refine ⟨332476413227536071162351793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 443301884303381428216469057 332476413227536071162351793)
          ·
            refine ⟨249357309920652053371763845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 332476413227536071162351793 249357309920652053371763845)
            ·
              refine ⟨46754495610122260007205721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 249357309920652053371763845 46754495610122260007205721)
              ·
                refine ⟨35065871707591695005404291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46754495610122260007205721 35065871707591695005404291)
                ·
                  refine ⟨52598807561387542508106437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35065871707591695005404291 52598807561387542508106437)
                  ·
                    refine ⟨9862276417760164220269957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52598807561387542508106437 9862276417760164220269957)
                    ·
                      refine ⟨1849176828330030791300617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9862276417760164220269957 1849176828330030791300617)
                      ·
                        rfl

theorem cell23_3601259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 2, 1, 4, 4].length) (baseStart_3601259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3601259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3601259 prefixEnd_3601259 := by exact prefixLift 3601259
  have htrace : WordTrace (prefixWord ++ tailWord_3601259) baseStart_3601259 baseEnd_3601259 := by
    simpa [prefixWord, tailWord_3601259, baseEnd_3601259] using wordTrace_append hprefix tailTrace_3601259
  have hstable : (prefixWord ++ tailWord_3601259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3601259).length < 2 ^ (prefixWord ++ tailWord_3601259).sum := by decide
  have hdescent : baseEnd_3601259 < baseStart_3601259 := by decide
  rcases family_descends (prefixWord ++ tailWord_3601259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3601299 : List Nat := [1, 1, 1, 2, 1, 2, 1, 6, 1, 7]
def baseStart_3601299 : Nat := 118140960795 + 3601299 * 2 ^ 59
def prefixEnd_3601299 : Nat := 4983230072969 + 3 ^ 40 * 3601299 * 2
def baseEnd_3601299 : Nat := 616399122518736878266811

theorem tailTrace_3601299 : CollatzResearch.WordTrace tailWord_3601299 prefixEnd_3601299 616399122518736878266811 := by
  unfold tailWord_3601299
  simp only [CollatzResearch.WordTrace]
  refine ⟨131350165380116250747446951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87566776920077500498297967 131350165380116250747446951)
  ·
    refine ⟨197025248070174376121170427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131350165380116250747446951 197025248070174376121170427)
    ·
      refine ⟨295537872105261564181755641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197025248070174376121170427 295537872105261564181755641)
      ·
        refine ⟨221653404078946173136316731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 295537872105261564181755641 221653404078946173136316731)
        ·
          refine ⟨332480106118419259704475097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221653404078946173136316731 332480106118419259704475097)
          ·
            refine ⟨249360079588814444778356323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 332480106118419259704475097 249360079588814444778356323)
            ·
              refine ⟨374040119383221667167534485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 249360079588814444778356323 374040119383221667167534485)
              ·
                refine ⟨17533130596088515648478179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 374040119383221667167534485 17533130596088515648478179)
                ·
                  refine ⟨26299695894132773472717269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17533130596088515648478179 26299695894132773472717269)
                  ·
                    refine ⟨616399122518736878266811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26299695894132773472717269 616399122518736878266811)
                    ·
                      rfl

theorem cell23_3601299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 6, 1, 7].length) (baseStart_3601299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3601299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3601299 prefixEnd_3601299 := by exact prefixLift 3601299
  have htrace : WordTrace (prefixWord ++ tailWord_3601299) baseStart_3601299 baseEnd_3601299 := by
    simpa [prefixWord, tailWord_3601299, baseEnd_3601299] using wordTrace_append hprefix tailTrace_3601299
  have hstable : (prefixWord ++ tailWord_3601299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3601299).length < 2 ^ (prefixWord ++ tailWord_3601299).sum := by decide
  have hdescent : baseEnd_3601299 < baseStart_3601299 := by decide
  rcases family_descends (prefixWord ++ tailWord_3601299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3601370 : List Nat := [3, 1, 1, 2, 4, 3, 1, 1, 2, 1, 4]
def baseStart_3601370 : Nat := 118140960795 + 3601370 * 2 ^ 59
def prefixEnd_3601370 : Nat := 4983230072969 + 3 ^ 40 * 3601370 * 2
def baseEnd_3601370 : Nat := 1849233824682679857012607

theorem tailTrace_3601370 : CollatzResearch.WordTrace tailWord_3601370 prefixEnd_3601370 1849233824682679857012607 := by
  unfold tailWord_3601370
  simp only [CollatzResearch.WordTrace]
  refine ⟨32838188740714757468320391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87568503308572686582187709 32838188740714757468320391)
  ·
    refine ⟨49257283111072136202480587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32838188740714757468320391 49257283111072136202480587)
    ·
      refine ⟨73885924666608204303720881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49257283111072136202480587 73885924666608204303720881)
      ·
        refine ⟨55414443499956153227790661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73885924666608204303720881 55414443499956153227790661)
        ·
          refine ⟨10390208156241778730210749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55414443499956153227790661 10390208156241778730210749)
          ·
            refine ⟨3896328058590667023829031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10390208156241778730210749 3896328058590667023829031)
            ·
              refine ⟨5844492087886000535743547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3896328058590667023829031 5844492087886000535743547)
              ·
                refine ⟨8766738131829000803615321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5844492087886000535743547 8766738131829000803615321)
                ·
                  refine ⟨6575053598871750602711491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8766738131829000803615321 6575053598871750602711491)
                  ·
                    refine ⟨9862580398307625904067237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6575053598871750602711491 9862580398307625904067237)
                    ·
                      refine ⟨1849233824682679857012607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9862580398307625904067237 1849233824682679857012607)
                      ·
                        rfl

theorem cell23_3601370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 1, 4].length) (baseStart_3601370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3601370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3601370 prefixEnd_3601370 := by exact prefixLift 3601370
  have htrace : WordTrace (prefixWord ++ tailWord_3601370) baseStart_3601370 baseEnd_3601370 := by
    simpa [prefixWord, tailWord_3601370, baseEnd_3601370] using wordTrace_append hprefix tailTrace_3601370
  have hstable : (prefixWord ++ tailWord_3601370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3601370).length < 2 ^ (prefixWord ++ tailWord_3601370).sum := by decide
  have hdescent : baseEnd_3601370 < baseStart_3601370 := by decide
  rcases family_descends (prefixWord ++ tailWord_3601370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
