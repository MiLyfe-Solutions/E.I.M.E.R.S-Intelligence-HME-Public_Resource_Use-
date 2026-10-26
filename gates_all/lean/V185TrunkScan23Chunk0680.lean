import V185TrunkScan23Chunk0679

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4021446 : List Nat := [6, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5]
def baseStart_4021446 : Nat := 118140960795 + 4021446 * 2 ^ 59
def prefixEnd_4021446 : Nat := 4983230072969 + 3 ^ 40 * 4021446 * 2
def baseEnd_4021446 : Nat := 2064934724100778307730713

theorem tailTrace_4021446 : CollatzResearch.WordTrace tailWord_4021446 prefixEnd_4021446 2064934724100778307730713 := by
  unfold tailWord_4021446
  simp only [CollatzResearch.WordTrace]
  refine ⟨4583568293406107035697131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 97782790259330283428205461 4583568293406107035697131)
  ·
    refine ⟨6875352440109160553545697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4583568293406107035697131 6875352440109160553545697)
    ·
      refine ⟨5156514330081870415159273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6875352440109160553545697 5156514330081870415159273)
      ·
        refine ⟨3867385747561402811369455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5156514330081870415159273 3867385747561402811369455)
        ·
          refine ⟨5801078621342104217054183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3867385747561402811369455 5801078621342104217054183)
          ·
            refine ⟨8701617932013156325581275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5801078621342104217054183 8701617932013156325581275)
            ·
              refine ⟨13052426898019734488371913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8701617932013156325581275 13052426898019734488371913)
              ·
                refine ⟨9789320173514800866278935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13052426898019734488371913 9789320173514800866278935)
                ·
                  refine ⟨14683980260272201299418403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9789320173514800866278935 14683980260272201299418403)
                  ·
                    refine ⟨22025970390408301949127605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14683980260272201299418403 22025970390408301949127605)
                    ·
                      refine ⟨2064934724100778307730713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22025970390408301949127605 2064934724100778307730713)
                      ·
                        rfl

theorem cell23_4021446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_4021446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4021446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4021446 prefixEnd_4021446 := by exact prefixLift 4021446
  have htrace : WordTrace (prefixWord ++ tailWord_4021446) baseStart_4021446 baseEnd_4021446 := by
    simpa [prefixWord, tailWord_4021446, baseEnd_4021446] using wordTrace_append hprefix tailTrace_4021446
  have hstable : (prefixWord ++ tailWord_4021446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4021446).length < 2 ^ (prefixWord ++ tailWord_4021446).sum := by decide
  have hdescent : baseEnd_4021446 < baseStart_4021446 := by decide
  rcases family_descends (prefixWord ++ tailWord_4021446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4021448 : List Nat := [2, 1, 3, 1, 2, 1, 2, 1, 1, 5, 4]
def baseStart_4021448 : Nat := 118140960795 + 4021448 * 2 ^ 59
def prefixEnd_4021448 : Nat := 4983230072969 + 3 ^ 40 * 4021448 * 2
def baseEnd_4021448 : Nat := 2064935751062087299905703

theorem tailTrace_4021448 : CollatzResearch.WordTrace tailWord_4021448 prefixEnd_4021448 2064935751062087299905703 := by
  unfold tailWord_4021448
  simp only [CollatzResearch.WordTrace]
  refine ⟨73337129167494089741940499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97782838889992119655920665 73337129167494089741940499)
  ·
    refine ⟨110005693751241134612910749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73337129167494089741940499 110005693751241134612910749)
    ·
      refine ⟨41252135156715425479841531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110005693751241134612910749 41252135156715425479841531)
      ·
        refine ⟨61878202735073138219762297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41252135156715425479841531 61878202735073138219762297)
        ·
          refine ⟨46408652051304853664821723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61878202735073138219762297 46408652051304853664821723)
          ·
            refine ⟨69612978076957280497232585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46408652051304853664821723 69612978076957280497232585)
            ·
              refine ⟨52209733557717960372924439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69612978076957280497232585 52209733557717960372924439)
              ·
                refine ⟨78314600336576940559386659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52209733557717960372924439 78314600336576940559386659)
                ·
                  refine ⟨117471900504865410839079989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78314600336576940559386659 117471900504865410839079989)
                  ·
                    refine ⟨11012990672331132266163749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 117471900504865410839079989 11012990672331132266163749)
                    ·
                      refine ⟨2064935751062087299905703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11012990672331132266163749 2064935751062087299905703)
                      ·
                        rfl

theorem cell23_4021448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 1, 5, 4].length) (baseStart_4021448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4021448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4021448 prefixEnd_4021448 := by exact prefixLift 4021448
  have htrace : WordTrace (prefixWord ++ tailWord_4021448) baseStart_4021448 baseEnd_4021448 := by
    simpa [prefixWord, tailWord_4021448, baseEnd_4021448] using wordTrace_append hprefix tailTrace_4021448
  have hstable : (prefixWord ++ tailWord_4021448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4021448).length < 2 ^ (prefixWord ++ tailWord_4021448).sum := by decide
  have hdescent : baseEnd_4021448 < baseStart_4021448 := by decide
  rcases family_descends (prefixWord ++ tailWord_4021448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4021453 : List Nat := [1, 6, 2, 2, 1, 1, 3, 1, 2, 4]
def baseStart_4021453 : Nat := 118140960795 + 4021453 * 2 ^ 59
def prefixEnd_4021453 : Nat := 4983230072969 + 3 ^ 40 * 4021453 * 2
def baseEnd_4021453 : Nat := 688312772821786593447727

theorem tailTrace_4021453 : CollatzResearch.WordTrace tailWord_4021453 prefixEnd_4021453 688312772821786593447727 := by
  unfold tailWord_4021453
  simp only [CollatzResearch.WordTrace]
  refine ⟨146674440699970065337813013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97782960466646710225208675 146674440699970065337813013)
  ·
    refine ⟨6875364407811096812709985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 146674440699970065337813013 6875364407811096812709985)
    ·
      refine ⟨5156523305858322609532489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6875364407811096812709985 5156523305858322609532489)
      ·
        refine ⟨3867392479393741957149367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5156523305858322609532489 3867392479393741957149367)
        ·
          refine ⟨5801088719090612935724051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3867392479393741957149367 5801088719090612935724051)
          ·
            refine ⟨8701633078635919403586077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5801088719090612935724051 8701633078635919403586077)
            ·
              refine ⟨3263112404488469776344779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8701633078635919403586077 3263112404488469776344779)
              ·
                refine ⟨4894668606732704664517169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3263112404488469776344779 4894668606732704664517169)
                ·
                  refine ⟨3671001455049528498387877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4894668606732704664517169 3671001455049528498387877)
                  ·
                    refine ⟨688312772821786593447727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3671001455049528498387877 688312772821786593447727)
                    ·
                      rfl

theorem cell23_4021453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_4021453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4021453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4021453 prefixEnd_4021453 := by exact prefixLift 4021453
  have htrace : WordTrace (prefixWord ++ tailWord_4021453) baseStart_4021453 baseEnd_4021453 := by
    simpa [prefixWord, tailWord_4021453, baseEnd_4021453] using wordTrace_append hprefix tailTrace_4021453
  have hstable : (prefixWord ++ tailWord_4021453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4021453).length < 2 ^ (prefixWord ++ tailWord_4021453).sum := by decide
  have hdescent : baseEnd_4021453 < baseStart_4021453 := by decide
  rcases family_descends (prefixWord ++ tailWord_4021453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4021485 : List Nat := [1, 5, 1, 2, 2, 1, 1, 1, 1, 3, 5]
def baseStart_4021485 : Nat := 118140960795 + 4021485 * 2 ^ 59
def prefixEnd_4021485 : Nat := 4983230072969 + 3 ^ 40 * 4021485 * 2
def baseEnd_4021485 : Nat := 2064954749846303655143033

theorem tailTrace_4021485 : CollatzResearch.WordTrace tailWord_4021485 prefixEnd_4021485 2064954749846303655143033 := by
  unfold tailWord_4021485
  simp only [CollatzResearch.WordTrace]
  refine ⟨146675607835854134802977909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97783738557236089868651939 146675607835854134802977909)
  ·
    refine ⟨13750838234611325137779179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 146675607835854134802977909 13750838234611325137779179)
    ·
      refine ⟨20626257351916987706668769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13750838234611325137779179 20626257351916987706668769)
      ·
        refine ⟨15469693013937740780001577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20626257351916987706668769 15469693013937740780001577)
        ·
          refine ⟨11602269760453305585001183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15469693013937740780001577 11602269760453305585001183)
          ·
            refine ⟨17403404640679958377501775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11602269760453305585001183 17403404640679958377501775)
            ·
              refine ⟨26105106961019937566252663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17403404640679958377501775 26105106961019937566252663)
              ·
                refine ⟨39157660441529906349378995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26105106961019937566252663 39157660441529906349378995)
                ·
                  refine ⟨58736490662294859524068493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39157660441529906349378995 58736490662294859524068493)
                  ·
                    refine ⟨22026183998360572321525685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58736490662294859524068493 22026183998360572321525685)
                    ·
                      refine ⟨2064954749846303655143033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22026183998360572321525685 2064954749846303655143033)
                      ·
                        rfl

theorem cell23_4021485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_4021485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4021485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4021485 prefixEnd_4021485 := by exact prefixLift 4021485
  have htrace : WordTrace (prefixWord ++ tailWord_4021485) baseStart_4021485 baseEnd_4021485 := by
    simpa [prefixWord, tailWord_4021485, baseEnd_4021485] using wordTrace_append hprefix tailTrace_4021485
  have hstable : (prefixWord ++ tailWord_4021485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4021485).length < 2 ^ (prefixWord ++ tailWord_4021485).sum := by decide
  have hdescent : baseEnd_4021485 < baseStart_4021485 := by decide
  rcases family_descends (prefixWord ++ tailWord_4021485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4021498 : List Nat := [3, 1, 1, 1, 1, 4, 1, 1, 1, 2, 7]
def baseStart_4021498 : Nat := 118140960795 + 4021498 * 2 ^ 59
def prefixEnd_4021498 : Nat := 4983230072969 + 3 ^ 40 * 4021498 * 2
def baseEnd_4021498 : Nat := 2064961425094812104280473

theorem tailTrace_4021498 : CollatzResearch.WordTrace tailWord_4021498 prefixEnd_4021498 2064961425094812104280473 := by
  unfold tailWord_4021498
  simp only [CollatzResearch.WordTrace]
  refine ⟨36669020496201759505800287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97784054656538025348800765 36669020496201759505800287)
  ·
    refine ⟨55003530744302639258700431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36669020496201759505800287 55003530744302639258700431)
    ·
      refine ⟨82505296116453958888050647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55003530744302639258700431 82505296116453958888050647)
      ·
        refine ⟨123757944174680938332075971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82505296116453958888050647 123757944174680938332075971)
        ·
          refine ⟨185636916262021407498113957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123757944174680938332075971 185636916262021407498113957)
          ·
            refine ⟨34806921799129013905896367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 185636916262021407498113957 34806921799129013905896367)
            ·
              refine ⟨52210382698693520858844551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34806921799129013905896367 52210382698693520858844551)
              ·
                refine ⟨78315574048040281288266827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52210382698693520858844551 78315574048040281288266827)
                ·
                  refine ⟨117473361072060421932400241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78315574048040281288266827 117473361072060421932400241)
                  ·
                    refine ⟨88105020804045316449300181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 117473361072060421932400241 88105020804045316449300181)
                    ·
                      refine ⟨2064961425094812104280473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 88105020804045316449300181 2064961425094812104280473)
                      ·
                        rfl

theorem cell23_4021498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 1, 2, 7].length) (baseStart_4021498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4021498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4021498 prefixEnd_4021498 := by exact prefixLift 4021498
  have htrace : WordTrace (prefixWord ++ tailWord_4021498) baseStart_4021498 baseEnd_4021498 := by
    simpa [prefixWord, tailWord_4021498, baseEnd_4021498] using wordTrace_append hprefix tailTrace_4021498
  have hstable : (prefixWord ++ tailWord_4021498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4021498).length < 2 ^ (prefixWord ++ tailWord_4021498).sum := by decide
  have hdescent : baseEnd_4021498 < baseStart_4021498 := by decide
  rcases family_descends (prefixWord ++ tailWord_4021498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4021505 : List Nat := [1, 2, 4, 1, 1, 3, 3, 1, 7]
def baseStart_4021505 : Nat := 118140960795 + 4021505 * 2 ^ 59
def prefixEnd_4021505 : Nat := 4983230072969 + 3 ^ 40 * 4021505 * 2
def baseEnd_4021505 : Nat := 229440557717710397432549

theorem tailTrace_4021505 : CollatzResearch.WordTrace tailWord_4021505 prefixEnd_4021505 229440557717710397432549 := by
  unfold tailWord_4021505
  simp only [CollatzResearch.WordTrace]
  refine ⟨146676337295781678218705969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97784224863854452145803979 146676337295781678218705969)
  ·
    refine ⟨110007252971836258664029477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146676337295781678218705969 110007252971836258664029477)
    ·
      refine ⟨20626359932219298499505527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110007252971836258664029477 20626359932219298499505527)
      ·
        refine ⟨30939539898328947749258291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20626359932219298499505527 30939539898328947749258291)
        ·
          refine ⟨46409309847493421623887437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30939539898328947749258291 46409309847493421623887437)
          ·
            refine ⟨17403491192810033108957789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46409309847493421623887437 17403491192810033108957789)
            ·
              refine ⟨6526309197303762415859171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17403491192810033108957789 6526309197303762415859171)
              ·
                refine ⟨9789463795955643623788757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6526309197303762415859171 9789463795955643623788757)
                ·
                  refine ⟨229440557717710397432549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9789463795955643623788757 229440557717710397432549)
                  ·
                    rfl

theorem cell23_4021505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 3, 1, 7].length) (baseStart_4021505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4021505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4021505 prefixEnd_4021505 := by exact prefixLift 4021505
  have htrace : WordTrace (prefixWord ++ tailWord_4021505) baseStart_4021505 baseEnd_4021505 := by
    simpa [prefixWord, tailWord_4021505, baseEnd_4021505] using wordTrace_append hprefix tailTrace_4021505
  have hstable : (prefixWord ++ tailWord_4021505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4021505).length < 2 ^ (prefixWord ++ tailWord_4021505).sum := by decide
  have hdescent : baseEnd_4021505 < baseStart_4021505 := by decide
  rcases family_descends (prefixWord ++ tailWord_4021505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4021516 : List Nat := [2, 2, 1, 2, 2, 3, 4, 1, 2, 2, 2]
def baseStart_4021516 : Nat := 118140960795 + 4021516 * 2 ^ 59
def prefixEnd_4021516 : Nat := 4983230072969 + 3 ^ 40 * 4021516 * 2
def baseEnd_4021516 : Nat := 2064970667746593033855391

theorem tailTrace_4021516 : CollatzResearch.WordTrace tailWord_4021516 prefixEnd_4021516 2064970667746593033855391 := by
  unfold tailWord_4021516
  simp only [CollatzResearch.WordTrace]
  refine ⟨73338369249370913548678201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97784492332494551398237601 73338369249370913548678201)
  ·
    refine ⟨55003776937028185161508651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73338369249370913548678201 55003776937028185161508651)
    ·
      refine ⟨82505665405542277742262977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55003776937028185161508651 82505665405542277742262977)
      ·
        refine ⟨61879249054156708306697233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82505665405542277742262977 61879249054156708306697233)
        ·
          refine ⟨46409436790617531230022925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61879249054156708306697233 46409436790617531230022925)
          ·
            refine ⟨17403538796481574211258597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46409436790617531230022925 17403538796481574211258597)
            ·
              refine ⟨3263163524340295164610987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17403538796481574211258597 3263163524340295164610987)
              ·
                refine ⟨4894745286510442746916481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3263163524340295164610987 4894745286510442746916481)
                ·
                  refine ⟨3671058964882832060187361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4894745286510442746916481 3671058964882832060187361)
                  ·
                    refine ⟨2753294223662124045140521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3671058964882832060187361 2753294223662124045140521)
                    ·
                      refine ⟨2064970667746593033855391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2753294223662124045140521 2064970667746593033855391)
                      ·
                        rfl

theorem cell23_4021516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 4, 1, 2, 2, 2].length) (baseStart_4021516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4021516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4021516 prefixEnd_4021516 := by exact prefixLift 4021516
  have htrace : WordTrace (prefixWord ++ tailWord_4021516) baseStart_4021516 baseEnd_4021516 := by
    simpa [prefixWord, tailWord_4021516, baseEnd_4021516] using wordTrace_append hprefix tailTrace_4021516
  have hstable : (prefixWord ++ tailWord_4021516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4021516).length < 2 ^ (prefixWord ++ tailWord_4021516).sum := by decide
  have hdescent : baseEnd_4021516 < baseStart_4021516 := by decide
  rcases family_descends (prefixWord ++ tailWord_4021516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4021582 : List Nat := [4, 1, 1, 1, 1, 1, 5, 2, 3, 4]
def baseStart_4021582 : Nat := 118140960795 + 4021582 * 2 ^ 59
def prefixEnd_4021582 : Nat := 4983230072969 + 3 ^ 40 * 4021582 * 2
def baseEnd_4021582 : Nat := 688334852489929925210029

theorem tailTrace_4021582 : CollatzResearch.WordTrace tailWord_4021582 prefixEnd_4021582 688334852489929925210029 := by
  unfold tailWord_4021582
  simp only [CollatzResearch.WordTrace]
  refine ⟨18334893214562840046157375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97786097144335146912839333 18334893214562840046157375)
  ·
    refine ⟨27502339821844260069236063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18334893214562840046157375 27502339821844260069236063)
    ·
      refine ⟨41253509732766390103854095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27502339821844260069236063 41253509732766390103854095)
      ·
        refine ⟨61880264599149585155781143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41253509732766390103854095 61880264599149585155781143)
        ·
          refine ⟨92820396898724377733671715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61880264599149585155781143 92820396898724377733671715)
          ·
            refine ⟨139230595348086566600507573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92820396898724377733671715 139230595348086566600507573)
            ·
              refine ⟨13052868313883115618797585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 139230595348086566600507573 13052868313883115618797585)
              ·
                refine ⟨9789651235412336714098189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13052868313883115618797585 9789651235412336714098189)
                ·
                  refine ⟨3671119213279626267786821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9789651235412336714098189 3671119213279626267786821)
                  ·
                    refine ⟨688334852489929925210029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3671119213279626267786821 688334852489929925210029)
                    ·
                      rfl

theorem cell23_4021582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 2, 3, 4].length) (baseStart_4021582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4021582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4021582 prefixEnd_4021582 := by exact prefixLift 4021582
  have htrace : WordTrace (prefixWord ++ tailWord_4021582) baseStart_4021582 baseEnd_4021582 := by
    simpa [prefixWord, tailWord_4021582, baseEnd_4021582] using wordTrace_append hprefix tailTrace_4021582
  have hstable : (prefixWord ++ tailWord_4021582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4021582).length < 2 ^ (prefixWord ++ tailWord_4021582).sum := by decide
  have hdescent : baseEnd_4021582 < baseStart_4021582 := by decide
  rcases family_descends (prefixWord ++ tailWord_4021582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4021589 : List Nat := [1, 3, 2, 2, 3, 3, 1, 1, 2, 1, 4]
def baseStart_4021589 : Nat := 118140960795 + 4021589 * 2 ^ 59
def prefixEnd_4021589 : Nat := 4983230072969 + 3 ^ 40 * 4021589 * 2
def baseEnd_4021589 : Nat := 2065008151834371248242555

theorem tailTrace_4021589 : CollatzResearch.WordTrace tailWord_4021589 prefixEnd_4021589 2065008151834371248242555 := by
  unfold tailWord_4021589
  simp only [CollatzResearch.WordTrace]
  refine ⟨146679401027477360564763821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97786267351651573709842547 146679401027477360564763821)
  ·
    refine ⟨55004775385304010211786433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146679401027477360564763821 55004775385304010211786433)
    ·
      refine ⟨41253581538978007658839825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55004775385304010211786433 41253581538978007658839825)
      ·
        refine ⟨30940186154233505744129869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41253581538978007658839825 30940186154233505744129869)
        ·
          refine ⟨11602569807837564654048701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30940186154233505744129869 11602569807837564654048701)
          ·
            refine ⟨4350963677939086745268263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11602569807837564654048701 4350963677939086745268263)
            ·
              refine ⟨6526445516908630117902395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4350963677939086745268263 6526445516908630117902395)
              ·
                refine ⟨9789668275362945176853593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6526445516908630117902395 9789668275362945176853593)
                ·
                  refine ⟨7342251206522208882640195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9789668275362945176853593 7342251206522208882640195)
                  ·
                    refine ⟨11013376809783313323960293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7342251206522208882640195 11013376809783313323960293)
                    ·
                      refine ⟨2065008151834371248242555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11013376809783313323960293 2065008151834371248242555)
                      ·
                        rfl

theorem cell23_4021589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 1, 1, 2, 1, 4].length) (baseStart_4021589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4021589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4021589 prefixEnd_4021589 := by exact prefixLift 4021589
  have htrace : WordTrace (prefixWord ++ tailWord_4021589) baseStart_4021589 baseEnd_4021589 := by
    simpa [prefixWord, tailWord_4021589, baseEnd_4021589] using wordTrace_append hprefix tailTrace_4021589
  have hstable : (prefixWord ++ tailWord_4021589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4021589).length < 2 ^ (prefixWord ++ tailWord_4021589).sum := by decide
  have hdescent : baseEnd_4021589 < baseStart_4021589 := by decide
  rcases family_descends (prefixWord ++ tailWord_4021589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4021590 : List Nat := [5, 2, 3, 1, 1, 1, 2, 3, 5]
def baseStart_4021590 : Nat := 118140960795 + 4021590 * 2 ^ 59
def prefixEnd_4021590 : Nat := 4983230072969 + 3 ^ 40 * 4021590 * 2
def baseEnd_4021590 : Nat := 229445407257225082703339

theorem tailTrace_4021590 : CollatzResearch.WordTrace tailWord_4021590 prefixEnd_4021590 229445407257225082703339 := by
  unfold tailWord_4021590
  simp only [CollatzResearch.WordTrace]
  refine ⟨9167464843779608608471889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 97786291666982491823700149 9167464843779608608471889)
  ·
    refine ⟨6875598632834706456353917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9167464843779608608471889 6875598632834706456353917)
    ·
      refine ⟨2578349487313014921132719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6875598632834706456353917 2578349487313014921132719)
      ·
        refine ⟨3867524230969522381699079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2578349487313014921132719 3867524230969522381699079)
        ·
          refine ⟨5801286346454283572548619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3867524230969522381699079 5801286346454283572548619)
          ·
            refine ⟨8701929519681425358822929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5801286346454283572548619 8701929519681425358822929)
            ·
              refine ⟨6526447139761069019117197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8701929519681425358822929 6526447139761069019117197)
              ·
                refine ⟨2447417677410400882168949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6526447139761069019117197 2447417677410400882168949)
                ·
                  refine ⟨229445407257225082703339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2447417677410400882168949 229445407257225082703339)
                  ·
                    rfl

theorem cell23_4021590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 2, 3, 5].length) (baseStart_4021590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4021590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4021590 prefixEnd_4021590 := by exact prefixLift 4021590
  have htrace : WordTrace (prefixWord ++ tailWord_4021590) baseStart_4021590 baseEnd_4021590 := by
    simpa [prefixWord, tailWord_4021590, baseEnd_4021590] using wordTrace_append hprefix tailTrace_4021590
  have hstable : (prefixWord ++ tailWord_4021590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4021590).length < 2 ^ (prefixWord ++ tailWord_4021590).sum := by decide
  have hdescent : baseEnd_4021590 < baseStart_4021590 := by decide
  rcases family_descends (prefixWord ++ tailWord_4021590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4021612 : List Nat := [2, 2, 1, 1, 5, 1, 3, 2, 6]
def baseStart_4021612 : Nat := 118140960795 + 4021612 * 2 ^ 59
def prefixEnd_4021612 : Nat := 4983230072969 + 3 ^ 40 * 4021612 * 2
def baseEnd_4021612 : Nat := 229446662432158295361661

theorem tailTrace_4021612 : CollatzResearch.WordTrace tailWord_4021612 prefixEnd_4021612 229446662432158295361661 := by
  unfold tailWord_4021612
  simp only [CollatzResearch.WordTrace]
  refine ⟨73340119953197017746425545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97786826604262690328567393 73340119953197017746425545)
  ·
    refine ⟨55005089964897763309819159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73340119953197017746425545 55005089964897763309819159)
    ·
      refine ⟨82507634947346644964728739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55005089964897763309819159 82507634947346644964728739)
      ·
        refine ⟨123761452421019967447093109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82507634947346644964728739 123761452421019967447093109)
        ·
          refine ⟨11602636164470621948164979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 123761452421019967447093109 11602636164470621948164979)
          ·
            refine ⟨17403954246705932922247469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11602636164470621948164979 17403954246705932922247469)
            ·
              refine ⟨6526482842514724845842801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17403954246705932922247469 6526482842514724845842801)
              ·
                refine ⟨4894862131886043634382101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6526482842514724845842801 4894862131886043634382101)
                ·
                  refine ⟨229446662432158295361661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4894862131886043634382101 229446662432158295361661)
                  ·
                    rfl

theorem cell23_4021612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 6].length) (baseStart_4021612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4021612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4021612 prefixEnd_4021612 := by exact prefixLift 4021612
  have htrace : WordTrace (prefixWord ++ tailWord_4021612) baseStart_4021612 baseEnd_4021612 := by
    simpa [prefixWord, tailWord_4021612, baseEnd_4021612] using wordTrace_append hprefix tailTrace_4021612
  have hstable : (prefixWord ++ tailWord_4021612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4021612).length < 2 ^ (prefixWord ++ tailWord_4021612).sum := by decide
  have hdescent : baseEnd_4021612 < baseStart_4021612 := by decide
  rcases family_descends (prefixWord ++ tailWord_4021612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4021625 : List Nat := [1, 2, 1, 3, 2, 1, 2, 1, 5, 5]
def baseStart_4021625 : Nat := 118140960795 + 4021625 * 2 ^ 59
def prefixEnd_4021625 : Nat := 4983230072969 + 3 ^ 40 * 4021625 * 2
def baseEnd_4021625 : Nat := 688342212379311035797463

theorem tailTrace_4021625 : CollatzResearch.WordTrace tailWord_4021625 prefixEnd_4021625 688342212379311035797463 := by
  unfold tailWord_4021625
  simp only [CollatzResearch.WordTrace]
  refine ⟨146680714055346938713074329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97787142703564625808716219 146680714055346938713074329)
  ·
    refine ⟨110010535541510204034805747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146680714055346938713074329 110010535541510204034805747)
    ·
      refine ⟨165015803312265306052208621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110010535541510204034805747 165015803312265306052208621)
      ·
        refine ⟨61880926242099489769578233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165015803312265306052208621 61880926242099489769578233)
        ·
          refine ⟨46410694681574617327183675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61880926242099489769578233 46410694681574617327183675)
          ·
            refine ⟨69616042022361925990775513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46410694681574617327183675 69616042022361925990775513)
            ·
              refine ⟨52212031516771444493081635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69616042022361925990775513 52212031516771444493081635)
              ·
                refine ⟨78318047275157166739622453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52212031516771444493081635 78318047275157166739622453)
                ·
                  refine ⟨7342316932045984381839605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78318047275157166739622453 7342316932045984381839605)
                  ·
                    refine ⟨688342212379311035797463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7342316932045984381839605 688342212379311035797463)
                    ·
                      rfl

theorem cell23_4021625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 5, 5].length) (baseStart_4021625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4021625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4021625 prefixEnd_4021625 := by exact prefixLift 4021625
  have htrace : WordTrace (prefixWord ++ tailWord_4021625) baseStart_4021625 baseEnd_4021625 := by
    simpa [prefixWord, tailWord_4021625, baseEnd_4021625] using wordTrace_append hprefix tailTrace_4021625
  have hstable : (prefixWord ++ tailWord_4021625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4021625).length < 2 ^ (prefixWord ++ tailWord_4021625).sum := by decide
  have hdescent : baseEnd_4021625 < baseStart_4021625 := by decide
  rcases family_descends (prefixWord ++ tailWord_4021625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4021639 : List Nat := [1, 1, 4, 2, 2, 2, 2, 2, 3, 1, 3]
def baseStart_4021639 : Nat := 118140960795 + 4021639 * 2 ^ 59
def prefixEnd_4021639 : Nat := 4983230072969 + 3 ^ 40 * 4021639 * 2
def baseEnd_4021639 : Nat := 2065033825867096052617325

theorem tailTrace_4021639 : CollatzResearch.WordTrace tailWord_4021639 prefixEnd_4021639 2065033825867096052617325 := by
  unfold tailWord_4021639
  simp only [CollatzResearch.WordTrace]
  refine ⟨146681224677296219104083971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97787483118197479402722647 146681224677296219104083971)
  ·
    refine ⟨220021837015944328656125957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146681224677296219104083971 220021837015944328656125957)
    ·
      refine ⟨41254094440489561623023617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 220021837015944328656125957 41254094440489561623023617)
      ·
        refine ⟨30940570830367171217267713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41254094440489561623023617 30940570830367171217267713)
        ·
          refine ⟨23205428122775378412950785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30940570830367171217267713 23205428122775378412950785)
          ·
            refine ⟨17404071092081533809713089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23205428122775378412950785 17404071092081533809713089)
            ·
              refine ⟨13053053319061150357284817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17404071092081533809713089 13053053319061150357284817)
              ·
                refine ⟨9789789989295862767963613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13053053319061150357284817 9789789989295862767963613)
                ·
                  refine ⟨3671171245985948537986355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9789789989295862767963613 3671171245985948537986355)
                  ·
                    refine ⟨5506756868978922806979533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3671171245985948537986355 5506756868978922806979533)
                    ·
                      refine ⟨2065033825867096052617325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5506756868978922806979533 2065033825867096052617325)
                      ·
                        rfl

theorem cell23_4021639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 2, 3, 1, 3].length) (baseStart_4021639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4021639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4021639 prefixEnd_4021639 := by exact prefixLift 4021639
  have htrace : WordTrace (prefixWord ++ tailWord_4021639) baseStart_4021639 baseEnd_4021639 := by
    simpa [prefixWord, tailWord_4021639, baseEnd_4021639] using wordTrace_append hprefix tailTrace_4021639
  have hstable : (prefixWord ++ tailWord_4021639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4021639).length < 2 ^ (prefixWord ++ tailWord_4021639).sum := by decide
  have hdescent : baseEnd_4021639 < baseStart_4021639 := by decide
  rcases family_descends (prefixWord ++ tailWord_4021639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4021650 : List Nat := [3, 2, 3, 3, 1, 2, 1, 3, 1, 4]
def baseStart_4021650 : Nat := 118140960795 + 4021650 * 2 ^ 59
def prefixEnd_4021650 : Nat := 4983230072969 + 3 ^ 40 * 4021650 * 2
def baseEnd_4021650 : Nat := 688346491384765169859925

theorem tailTrace_4021650 : CollatzResearch.WordTrace tailWord_4021650 prefixEnd_4021650 688346491384765169859925 := by
  unfold tailWord_4021650
  simp only [CollatzResearch.WordTrace]
  refine ⟨36670406470064091995683601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97787750586837578655156269 36670406470064091995683601)
  ·
    refine ⟨27502804852548068996762701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36670406470064091995683601 27502804852548068996762701)
    ·
      refine ⟨10313551819705525873786013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27502804852548068996762701 10313551819705525873786013)
      ·
        refine ⟨3867581932389572202669755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10313551819705525873786013 3867581932389572202669755)
        ·
          refine ⟨5801372898584358304004633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3867581932389572202669755 5801372898584358304004633)
          ·
            refine ⟨4351029673938268728003475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5801372898584358304004633 4351029673938268728003475)
            ·
              refine ⟨6526544510907403092005213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4351029673938268728003475 6526544510907403092005213)
              ·
                refine ⟨2447454191590276159501955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6526544510907403092005213 2447454191590276159501955)
                ·
                  refine ⟨3671181287385414239252933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2447454191590276159501955 3671181287385414239252933)
                  ·
                    refine ⟨688346491384765169859925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3671181287385414239252933 688346491384765169859925)
                    ·
                      rfl

theorem cell23_4021650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 1, 3, 1, 4].length) (baseStart_4021650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4021650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4021650 prefixEnd_4021650 := by exact prefixLift 4021650
  have htrace : WordTrace (prefixWord ++ tailWord_4021650) baseStart_4021650 baseEnd_4021650 := by
    simpa [prefixWord, tailWord_4021650, baseEnd_4021650] using wordTrace_append hprefix tailTrace_4021650
  have hstable : (prefixWord ++ tailWord_4021650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4021650).length < 2 ^ (prefixWord ++ tailWord_4021650).sum := by decide
  have hdescent : baseEnd_4021650 < baseStart_4021650 := by decide
  rcases family_descends (prefixWord ++ tailWord_4021650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4021655 : List Nat := [1, 1, 3, 3, 1, 1, 1, 3, 3, 6]
def baseStart_4021655 : Nat := 118140960795 + 4021655 * 2 ^ 59
def prefixEnd_4021655 : Nat := 4983230072969 + 3 ^ 40 * 4021655 * 2
def baseEnd_4021655 : Nat := 688347347185855996672417

theorem tailTrace_4021655 : CollatzResearch.WordTrace tailWord_4021655 prefixEnd_4021655 688347347185855996672417 := by
  unfold tailWord_4021655
  simp only [CollatzResearch.WordTrace]
  refine ⟨146681808245238253836666419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97787872163492169224444279 146681808245238253836666419)
  ·
    refine ⟨220022712367857380754999629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146681808245238253836666419 220022712367857380754999629)
    ·
      refine ⟨82508517137946517783124861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220022712367857380754999629 82508517137946517783124861)
      ·
        refine ⟨30940693926729944168671823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82508517137946517783124861 30940693926729944168671823)
        ·
          refine ⟨46411040890094916253007735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30940693926729944168671823 46411040890094916253007735)
          ·
            refine ⟨69616561335142374379511603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46411040890094916253007735 69616561335142374379511603)
            ·
              refine ⟨104424842002713561569267405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69616561335142374379511603 104424842002713561569267405)
              ·
                refine ⟨39159315751017585588475277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104424842002713561569267405 39159315751017585588475277)
                ·
                  refine ⟨14684743406631594595678229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39159315751017585588475277 14684743406631594595678229)
                  ·
                    refine ⟨688347347185855996672417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14684743406631594595678229 688347347185855996672417)
                    ·
                      rfl

theorem cell23_4021655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 3, 3, 6].length) (baseStart_4021655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4021655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4021655 prefixEnd_4021655 := by exact prefixLift 4021655
  have htrace : WordTrace (prefixWord ++ tailWord_4021655) baseStart_4021655 baseEnd_4021655 := by
    simpa [prefixWord, tailWord_4021655, baseEnd_4021655] using wordTrace_append hprefix tailTrace_4021655
  have hstable : (prefixWord ++ tailWord_4021655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4021655).length < 2 ^ (prefixWord ++ tailWord_4021655).sum := by decide
  have hdescent : baseEnd_4021655 < baseStart_4021655 := by decide
  rcases family_descends (prefixWord ++ tailWord_4021655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4021666 : List Nat := [3, 3, 1, 2, 1, 3, 1, 2, 2, 3, 2]
def baseStart_4021666 : Nat := 118140960795 + 4021666 * 2 ^ 59
def prefixEnd_4021666 : Nat := 4983230072969 + 3 ^ 40 * 4021666 * 2
def baseEnd_4021666 : Nat := 2065047689844767446979701

theorem tailTrace_4021666 : CollatzResearch.WordTrace tailWord_4021666 prefixEnd_4021666 2065047689844767446979701 := by
  unfold tailWord_4021666
  simp only [CollatzResearch.WordTrace]
  refine ⟨36670552362049600678829213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97788139632132268476877901 36670552362049600678829213)
  ·
    refine ⟨13751457135768600254560955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36670552362049600678829213 13751457135768600254560955)
    ·
      refine ⟨20627185703652900381841433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13751457135768600254560955 20627185703652900381841433)
      ·
        refine ⟨15470389277739675286381075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20627185703652900381841433 15470389277739675286381075)
        ·
          refine ⟨23205583916609512929571613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15470389277739675286381075 23205583916609512929571613)
          ·
            refine ⟨8702093968728567348589355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23205583916609512929571613 8702093968728567348589355)
            ·
              refine ⟨13053140953092851022884033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8702093968728567348589355 13053140953092851022884033)
              ·
                refine ⟨9789855714819638267163025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13053140953092851022884033 9789855714819638267163025)
                ·
                  refine ⟨7342391786114728700372269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9789855714819638267163025 7342391786114728700372269)
                  ·
                    refine ⟨2753396919793023262639601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7342391786114728700372269 2753396919793023262639601)
                    ·
                      refine ⟨2065047689844767446979701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2753396919793023262639601 2065047689844767446979701)
                      ·
                        rfl

theorem cell23_4021666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 2, 2, 3, 2].length) (baseStart_4021666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4021666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4021666 prefixEnd_4021666 := by exact prefixLift 4021666
  have htrace : WordTrace (prefixWord ++ tailWord_4021666) baseStart_4021666 baseEnd_4021666 := by
    simpa [prefixWord, tailWord_4021666, baseEnd_4021666] using wordTrace_append hprefix tailTrace_4021666
  have hstable : (prefixWord ++ tailWord_4021666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4021666).length < 2 ^ (prefixWord ++ tailWord_4021666).sum := by decide
  have hdescent : baseEnd_4021666 < baseStart_4021666 := by decide
  rcases family_descends (prefixWord ++ tailWord_4021666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4021699 : List Nat := [1, 1, 1, 3, 1, 1, 7, 2, 1, 2, 3]
def baseStart_4021699 : Nat := 118140960795 + 4021699 * 2 ^ 59
def prefixEnd_4021699 : Nat := 4983230072969 + 3 ^ 40 * 4021699 * 2
def baseEnd_4021699 : Nat := 2065064634706365817867049

theorem tailTrace_4021699 : CollatzResearch.WordTrace tailWord_4021699 prefixEnd_4021699 2065064634706365817867049 := by
  unfold tailWord_4021699
  simp only [CollatzResearch.WordTrace]
  refine ⟨146683413057078849351268151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97788942038052566234178767 146683413057078849351268151)
  ·
    refine ⟨220025119585618274026902227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146683413057078849351268151 220025119585618274026902227)
    ·
      refine ⟨330037679378427411040353341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220025119585618274026902227 330037679378427411040353341)
      ·
        refine ⟨123764129766910279140132503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 330037679378427411040353341 123764129766910279140132503)
        ·
          refine ⟨185646194650365418710198755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123764129766910279140132503 185646194650365418710198755)
          ·
            refine ⟨278469291975548128065298133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185646194650365418710198755 278469291975548128065298133)
            ·
              refine ⟨6526624030676909251530425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 278469291975548128065298133 6526624030676909251530425)
              ·
                refine ⟨4894968023007681938647819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6526624030676909251530425 4894968023007681938647819)
                ·
                  refine ⟨7342452034511522907971729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4894968023007681938647819 7342452034511522907971729)
                  ·
                    refine ⟨5506839025883642180978797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7342452034511522907971729 5506839025883642180978797)
                    ·
                      refine ⟨2065064634706365817867049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5506839025883642180978797 2065064634706365817867049)
                      ·
                        rfl

theorem cell23_4021699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 7, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 7, 2, 1, 2, 3].length) (baseStart_4021699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4021699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4021699 prefixEnd_4021699 := by exact prefixLift 4021699
  have htrace : WordTrace (prefixWord ++ tailWord_4021699) baseStart_4021699 baseEnd_4021699 := by
    simpa [prefixWord, tailWord_4021699, baseEnd_4021699] using wordTrace_append hprefix tailTrace_4021699
  have hstable : (prefixWord ++ tailWord_4021699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4021699).length < 2 ^ (prefixWord ++ tailWord_4021699).sum := by decide
  have hdescent : baseEnd_4021699 < baseStart_4021699 := by decide
  rcases family_descends (prefixWord ++ tailWord_4021699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4021712 : List Nat := [2, 1, 1, 1, 1, 2, 2, 6, 1, 3, 3]
def baseStart_4021712 : Nat := 118140960795 + 4021712 * 2 ^ 59
def prefixEnd_4021712 : Nat := 4983230072969 + 3 ^ 40 * 4021712 * 2
def baseEnd_4021712 : Nat := 2065071309954874267004489

theorem tailTrace_4021712 : CollatzResearch.WordTrace tailWord_4021712 prefixEnd_4021712 2065071309954874267004489 := by
  unfold tailWord_4021712
  simp only [CollatzResearch.WordTrace]
  refine ⟨73341943603015876285745695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97789258137354501714327593 73341943603015876285745695)
  ·
    refine ⟨110012915404523814428618543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73341943603015876285745695 110012915404523814428618543)
    ·
      refine ⟨165019373106785721642927815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110012915404523814428618543 165019373106785721642927815)
      ·
        refine ⟨247529059660178582464391723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165019373106785721642927815 247529059660178582464391723)
        ·
          refine ⟨371293589490267873696587585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247529059660178582464391723 371293589490267873696587585)
          ·
            refine ⟨278470192117700905272440689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 371293589490267873696587585 278470192117700905272440689)
            ·
              refine ⟨208852644088275678954330517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 278470192117700905272440689 208852644088275678954330517)
              ·
                refine ⟨9789967691637922450984243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 208852644088275678954330517 9789967691637922450984243)
                ·
                  refine ⟨14684951537456883676476365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9789967691637922450984243 14684951537456883676476365)
                  ·
                    refine ⟨5506856826546331378678637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14684951537456883676476365 5506856826546331378678637)
                    ·
                      refine ⟨2065071309954874267004489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5506856826546331378678637 2065071309954874267004489)
                      ·
                        rfl

theorem cell23_4021712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 6, 1, 3, 3].length) (baseStart_4021712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4021712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4021712 prefixEnd_4021712 := by exact prefixLift 4021712
  have htrace : WordTrace (prefixWord ++ tailWord_4021712) baseStart_4021712 baseEnd_4021712 := by
    simpa [prefixWord, tailWord_4021712, baseEnd_4021712] using wordTrace_append hprefix tailTrace_4021712
  have hstable : (prefixWord ++ tailWord_4021712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4021712).length < 2 ^ (prefixWord ++ tailWord_4021712).sum := by decide
  have hdescent : baseEnd_4021712 < baseStart_4021712 := by decide
  rcases family_descends (prefixWord ++ tailWord_4021712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4021716 : List Nat := [2, 4, 1, 2, 3, 2, 1, 1, 1, 1, 5]
def baseStart_4021716 : Nat := 118140960795 + 4021716 * 2 ^ 59
def prefixEnd_4021716 : Nat := 4983230072969 + 3 ^ 40 * 4021716 * 2
def baseEnd_4021716 : Nat := 2065073363877492251354471

theorem tailTrace_4021716 : CollatzResearch.WordTrace tailWord_4021716 prefixEnd_4021716 2065073363877492251354471 := by
  unfold tailWord_4021716
  simp only [CollatzResearch.WordTrace]
  refine ⟨73342016549008630627318501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97789355398678174169758001 73342016549008630627318501)
  ·
    refine ⟨13751628102939118242622219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73342016549008630627318501 13751628102939118242622219)
    ·
      refine ⟨20627442154408677363933329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13751628102939118242622219 20627442154408677363933329)
      ·
        refine ⟨15470581615806508022949997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20627442154408677363933329 15470581615806508022949997)
        ·
          refine ⟨5801468105927440508606249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15470581615806508022949997 5801468105927440508606249)
          ·
            refine ⟨4351101079445580381454687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5801468105927440508606249 4351101079445580381454687)
            ·
              refine ⟨6526651619168370572182031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4351101079445580381454687 6526651619168370572182031)
              ·
                refine ⟨9789977428752555858273047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6526651619168370572182031 9789977428752555858273047)
                ·
                  refine ⟨14684966143128833787409571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9789977428752555858273047 14684966143128833787409571)
                  ·
                    refine ⟨22027449214693250681114357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14684966143128833787409571 22027449214693250681114357)
                    ·
                      refine ⟨2065073363877492251354471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22027449214693250681114357 2065073363877492251354471)
                      ·
                        rfl

theorem cell23_4021716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 1, 1, 1, 1, 5].length) (baseStart_4021716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4021716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4021716 prefixEnd_4021716 := by exact prefixLift 4021716
  have htrace : WordTrace (prefixWord ++ tailWord_4021716) baseStart_4021716 baseEnd_4021716 := by
    simpa [prefixWord, tailWord_4021716, baseEnd_4021716] using wordTrace_append hprefix tailTrace_4021716
  have hstable : (prefixWord ++ tailWord_4021716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4021716).length < 2 ^ (prefixWord ++ tailWord_4021716).sum := by decide
  have hdescent : baseEnd_4021716 < baseStart_4021716 := by decide
  rcases family_descends (prefixWord ++ tailWord_4021716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4021746 : List Nat := [3, 2, 1, 4, 1, 2, 2, 1, 1, 3, 3]
def baseStart_4021746 : Nat := 118140960795 + 4021746 * 2 ^ 59
def prefixEnd_4021746 : Nat := 4983230072969 + 3 ^ 40 * 4021746 * 2
def baseEnd_4021746 : Nat := 2065088768297127133979333

theorem tailTrace_4021746 : CollatzResearch.WordTrace tailWord_4021746 prefixEnd_4021746 2065088768297127133979333 := by
  unfold tailWord_4021746
  simp only [CollatzResearch.WordTrace]
  refine ⟨36671281821977144094557273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97790084858605717585486061 36671281821977144094557273)
  ·
    refine ⟨27503461366482858070917955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36671281821977144094557273 27503461366482858070917955)
    ·
      refine ⟨41255192049724287106376933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27503461366482858070917955 41255192049724287106376933)
      ·
        refine ⟨7735348509323303832445675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41255192049724287106376933 7735348509323303832445675)
        ·
          refine ⟨11603022763984955748668513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7735348509323303832445675 11603022763984955748668513)
          ·
            refine ⟨8702267072988716811501385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11603022763984955748668513 8702267072988716811501385)
            ·
              refine ⟨6526700304741537608626039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8702267072988716811501385 6526700304741537608626039)
              ·
                refine ⟨9790050457112306412939059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6526700304741537608626039 9790050457112306412939059)
                ·
                  refine ⟨14685075685668459619408589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9790050457112306412939059 14685075685668459619408589)
                  ·
                    refine ⟨5506903382125672357278221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14685075685668459619408589 5506903382125672357278221)
                    ·
                      refine ⟨2065088768297127133979333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5506903382125672357278221 2065088768297127133979333)
                      ·
                        rfl

theorem cell23_4021746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_4021746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4021746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4021746 prefixEnd_4021746 := by exact prefixLift 4021746
  have htrace : WordTrace (prefixWord ++ tailWord_4021746) baseStart_4021746 baseEnd_4021746 := by
    simpa [prefixWord, tailWord_4021746, baseEnd_4021746] using wordTrace_append hprefix tailTrace_4021746
  have hstable : (prefixWord ++ tailWord_4021746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4021746).length < 2 ^ (prefixWord ++ tailWord_4021746).sum := by decide
  have hdescent : baseEnd_4021746 < baseStart_4021746 := by decide
  rcases family_descends (prefixWord ++ tailWord_4021746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4021769 : List Nat := [1, 2, 1, 1, 3, 1, 3, 4, 1, 4, 2]
def baseStart_4021769 : Nat := 118140960795 + 4021769 * 2 ^ 59
def prefixEnd_4021769 : Nat := 4983230072969 + 3 ^ 40 * 4021769 * 2
def baseEnd_4021769 : Nat := 2065100578352180543991727

theorem tailTrace_4021769 : CollatzResearch.WordTrace tailWord_4021769 prefixEnd_4021769 2065100578352180543991727 := by
  unfold tailWord_4021769
  simp only [CollatzResearch.WordTrace]
  refine ⟨146685966166825251306316361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97790644111216834204210907 146685966166825251306316361)
  ·
    refine ⟨110014474625118938479737271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146685966166825251306316361 110014474625118938479737271)
    ·
      refine ⟨165021711937678407719605907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110014474625118938479737271 165021711937678407719605907)
      ·
        refine ⟨247532567906517611579408861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165021711937678407719605907 247532567906517611579408861)
        ·
          refine ⟨92824712964944104342278323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 247532567906517611579408861 92824712964944104342278323)
          ·
            refine ⟨139237069447416156513417485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92824712964944104342278323 139237069447416156513417485)
            ·
              refine ⟨52213901042781058692531557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139237069447416156513417485 52213901042781058692531557)
              ·
                refine ⟨9790106445521448504849667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52213901042781058692531557 9790106445521448504849667)
                ·
                  refine ⟨14685159668282172757274501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9790106445521448504849667 14685159668282172757274501)
                  ·
                    refine ⟨2753467437802907391988969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14685159668282172757274501 2753467437802907391988969)
                    ·
                      refine ⟨2065100578352180543991727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2753467437802907391988969 2065100578352180543991727)
                      ·
                        rfl

theorem cell23_4021769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 4, 1, 4, 2].length) (baseStart_4021769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4021769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4021769 prefixEnd_4021769 := by exact prefixLift 4021769
  have htrace : WordTrace (prefixWord ++ tailWord_4021769) baseStart_4021769 baseEnd_4021769 := by
    simpa [prefixWord, tailWord_4021769, baseEnd_4021769] using wordTrace_append hprefix tailTrace_4021769
  have hstable : (prefixWord ++ tailWord_4021769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4021769).length < 2 ^ (prefixWord ++ tailWord_4021769).sum := by decide
  have hdescent : baseEnd_4021769 < baseStart_4021769 := by decide
  rcases family_descends (prefixWord ++ tailWord_4021769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4021882 : List Nat := [3, 1, 1, 1, 1, 1, 1, 6, 8]
def baseStart_4021882 : Nat := 118140960795 + 4021882 * 2 ^ 59
def prefixEnd_4021882 : Nat := 4983230072969 + 3 ^ 40 * 4021882 * 2
def baseEnd_4021882 : Nat := 229462066851793177986523

theorem tailTrace_4021882 : CollatzResearch.WordTrace tailWord_4021882 prefixEnd_4021882 229462066851793177986523 := by
  unfold tailWord_4021882
  simp only [CollatzResearch.WordTrace]
  refine ⟨36672521903853967901294975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97793391743610581070119933 36672521903853967901294975)
  ·
    refine ⟨55008782855780951851942463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36672521903853967901294975 55008782855780951851942463)
    ·
      refine ⟨82513174283671427777913695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55008782855780951851942463 82513174283671427777913695)
      ·
        refine ⟨123769761425507141666870543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82513174283671427777913695 123769761425507141666870543)
        ·
          refine ⟨185654642138260712500305815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123769761425507141666870543 185654642138260712500305815)
          ·
            refine ⟨278481963207391068750458723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185654642138260712500305815 278481963207391068750458723)
            ·
              refine ⟨417722944811086603125688085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 278481963207391068750458723 417722944811086603125688085)
              ·
                refine ⟨19580763038019684521516629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 417722944811086603125688085 19580763038019684521516629)
                ·
                  refine ⟨229462066851793177986523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19580763038019684521516629 229462066851793177986523)
                  ·
                    rfl

theorem cell23_4021882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 6, 8].length) (baseStart_4021882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4021882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4021882 prefixEnd_4021882 := by exact prefixLift 4021882
  have htrace : WordTrace (prefixWord ++ tailWord_4021882) baseStart_4021882 baseEnd_4021882 := by
    simpa [prefixWord, tailWord_4021882, baseEnd_4021882] using wordTrace_append hprefix tailTrace_4021882
  have hstable : (prefixWord ++ tailWord_4021882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4021882).length < 2 ^ (prefixWord ++ tailWord_4021882).sum := by decide
  have hdescent : baseEnd_4021882 < baseStart_4021882 := by decide
  rcases family_descends (prefixWord ++ tailWord_4021882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4021899 : List Nat := [1, 1, 1, 1, 4, 1, 6, 2, 6]
def baseStart_4021899 : Nat := 118140960795 + 4021899 * 2 ^ 59
def prefixEnd_4021899 : Nat := 4983230072969 + 3 ^ 40 * 4021899 * 2
def baseEnd_4021899 : Nat := 229463036759696115040681

theorem tailTrace_4021899 : CollatzResearch.WordTrace tailWord_4021899 prefixEnd_4021899 229463036759696115040681 := by
  unfold tailWord_4021899
  simp only [CollatzResearch.WordTrace]
  refine ⟨146690707656354283508548751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97793805104236189005699167 146690707656354283508548751)
  ·
    refine ⟨220036061484531425262823127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146690707656354283508548751 220036061484531425262823127)
    ·
      refine ⟨330054092226797137894234691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220036061484531425262823127 330054092226797137894234691)
      ·
        refine ⟨495081138340195706841352037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330054092226797137894234691 495081138340195706841352037)
        ·
          refine ⟨92827713438786695032753507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 495081138340195706841352037 92827713438786695032753507)
          ·
            refine ⟨139241570158180042549130261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92827713438786695032753507 139241570158180042549130261)
            ·
              refine ⟨6526948601164689494490481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 139241570158180042549130261 6526948601164689494490481)
              ·
                refine ⟨4895211450873517120867861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6526948601164689494490481 4895211450873517120867861)
                ·
                  refine ⟨229463036759696115040681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4895211450873517120867861 229463036759696115040681)
                  ·
                    rfl

theorem cell23_4021899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 6, 2, 6].length) (baseStart_4021899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4021899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4021899 prefixEnd_4021899 := by exact prefixLift 4021899
  have htrace : WordTrace (prefixWord ++ tailWord_4021899) baseStart_4021899 baseEnd_4021899 := by
    simpa [prefixWord, tailWord_4021899, baseEnd_4021899] using wordTrace_append hprefix tailTrace_4021899
  have hstable : (prefixWord ++ tailWord_4021899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4021899).length < 2 ^ (prefixWord ++ tailWord_4021899).sum := by decide
  have hdescent : baseEnd_4021899 < baseStart_4021899 := by decide
  rcases family_descends (prefixWord ++ tailWord_4021899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4021946 : List Nat := [3, 1, 1, 1, 2, 5, 1, 3, 1, 5]
def baseStart_4021946 : Nat := 118140960795 + 4021946 * 2 ^ 59
def prefixEnd_4021946 : Nat := 4983230072969 + 3 ^ 40 * 4021946 * 2
def baseEnd_4021946 : Nat := 688397154809342117159471

theorem tailTrace_4021946 : CollatzResearch.WordTrace tailWord_4021946 prefixEnd_4021946 688397154809342117159471 := by
  unfold tailWord_4021946
  simp only [CollatzResearch.WordTrace]
  refine ⟨36673105471796002633877423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97794947924789340357006461 36673105471796002633877423)
  ·
    refine ⟨55009658207694003950816135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36673105471796002633877423 55009658207694003950816135)
    ·
      refine ⟨82514487311541005926224203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55009658207694003950816135 82514487311541005926224203)
      ·
        refine ⟨123771730967311508889336305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82514487311541005926224203 123771730967311508889336305)
        ·
          refine ⟨92828798225483631667002229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123771730967311508889336305 92828798225483631667002229)
          ·
            refine ⟨8702699833639090468781459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 92828798225483631667002229 8702699833639090468781459)
            ·
              refine ⟨13054049750458635703172189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8702699833639090468781459 13054049750458635703172189)
              ·
                refine ⟨4895268656421988388689571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13054049750458635703172189 4895268656421988388689571)
                ·
                  refine ⟨7342902984632982583034357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4895268656421988388689571 7342902984632982583034357)
                  ·
                    refine ⟨688397154809342117159471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7342902984632982583034357 688397154809342117159471)
                    ·
                      rfl

theorem cell23_4021946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 3, 1, 5].length) (baseStart_4021946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4021946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4021946 prefixEnd_4021946 := by exact prefixLift 4021946
  have htrace : WordTrace (prefixWord ++ tailWord_4021946) baseStart_4021946 baseEnd_4021946 := by
    simpa [prefixWord, tailWord_4021946, baseEnd_4021946] using wordTrace_append hprefix tailTrace_4021946
  have hstable : (prefixWord ++ tailWord_4021946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4021946).length < 2 ^ (prefixWord ++ tailWord_4021946).sum := by decide
  have hdescent : baseEnd_4021946 < baseStart_4021946 := by decide
  rcases family_descends (prefixWord ++ tailWord_4021946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4021969 : List Nat := [1, 2, 2, 1, 2, 4, 1, 1, 3, 1, 5]
def baseStart_4021969 : Nat := 118140960795 + 4021969 * 2 ^ 59
def prefixEnd_4021969 : Nat := 4983230072969 + 3 ^ 40 * 4021969 * 2
def baseEnd_4021969 : Nat := 2065203274483079761490807

theorem tailTrace_4021969 : CollatzResearch.WordTrace tailWord_4021969 prefixEnd_4021969 2065203274483079761490807 := by
  unfold tailWord_4021969
  simp only [CollatzResearch.WordTrace]
  refine ⟨146693260766100685463596961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97795507177400456975731307 146693260766100685463596961)
  ·
    refine ⟨110019945574575514097697721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146693260766100685463596961 110019945574575514097697721)
    ·
      refine ⟨82514959180931635573273291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110019945574575514097697721 82514959180931635573273291)
      ·
        refine ⟨123772438771397453359909937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82514959180931635573273291 123772438771397453359909937)
        ·
          refine ⟨92829329078548090019932453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123772438771397453359909937 92829329078548090019932453)
          ·
            refine ⟨17405499202227766878737335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92829329078548090019932453 17405499202227766878737335)
            ·
              refine ⟨26108248803341650318106003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17405499202227766878737335 26108248803341650318106003)
              ·
                refine ⟨39162373205012475477159005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26108248803341650318106003 39162373205012475477159005)
                ·
                  refine ⟨14685889951879678303934627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39162373205012475477159005 14685889951879678303934627)
                  ·
                    refine ⟨22028834927819517455901941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14685889951879678303934627 22028834927819517455901941)
                    ·
                      refine ⟨2065203274483079761490807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22028834927819517455901941 2065203274483079761490807)
                      ·
                        rfl

theorem cell23_4021969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 1, 3, 1, 5].length) (baseStart_4021969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4021969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4021969 prefixEnd_4021969 := by exact prefixLift 4021969
  have htrace : WordTrace (prefixWord ++ tailWord_4021969) baseStart_4021969 baseEnd_4021969 := by
    simpa [prefixWord, tailWord_4021969, baseEnd_4021969] using wordTrace_append hprefix tailTrace_4021969
  have hstable : (prefixWord ++ tailWord_4021969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4021969).length < 2 ^ (prefixWord ++ tailWord_4021969).sum := by decide
  have hdescent : baseEnd_4021969 < baseStart_4021969 := by decide
  rcases family_descends (prefixWord ++ tailWord_4021969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4021980 : List Nat := [2, 2, 5, 1, 2, 1, 2, 2, 1, 5]
def baseStart_4021980 : Nat := 118140960795 + 4021980 * 2 ^ 59
def prefixEnd_4021980 : Nat := 4983230072969 + 3 ^ 40 * 4021980 * 2
def baseEnd_4021980 : Nat := 688402974256759739484419

theorem tailTrace_4021980 : CollatzResearch.WordTrace tailWord_4021980 prefixEnd_4021980 688402974256759739484419 := by
  unfold tailWord_4021980
  simp only [CollatzResearch.WordTrace]
  refine ⟨73346830984530417171123697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97795774646040556228164929 73346830984530417171123697)
  ·
    refine ⟨55010123238397812878342773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73346830984530417171123697 55010123238397812878342773)
    ·
      refine ⟨5157199053599794957344635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 55010123238397812878342773 5157199053599794957344635)
      ·
        refine ⟨7735798580399692436016953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5157199053599794957344635 7735798580399692436016953)
        ·
          refine ⟨5801848935299769327012715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7735798580399692436016953 5801848935299769327012715)
          ·
            refine ⟨8702773402949653990519073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5801848935299769327012715 8702773402949653990519073)
            ·
              refine ⟨6527080052212240492889305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8702773402949653990519073 6527080052212240492889305)
              ·
                refine ⟨4895310039159180369666979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6527080052212240492889305 4895310039159180369666979)
                ·
                  refine ⟨7342965058738770554500469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4895310039159180369666979 7342965058738770554500469)
                  ·
                    refine ⟨688402974256759739484419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7342965058738770554500469 688402974256759739484419)
                    ·
                      rfl

theorem cell23_4021980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_4021980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4021980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4021980 prefixEnd_4021980 := by exact prefixLift 4021980
  have htrace : WordTrace (prefixWord ++ tailWord_4021980) baseStart_4021980 baseEnd_4021980 := by
    simpa [prefixWord, tailWord_4021980, baseEnd_4021980] using wordTrace_append hprefix tailTrace_4021980
  have hstable : (prefixWord ++ tailWord_4021980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4021980).length < 2 ^ (prefixWord ++ tailWord_4021980).sum := by decide
  have hdescent : baseEnd_4021980 < baseStart_4021980 := by decide
  rcases family_descends (prefixWord ++ tailWord_4021980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4021983 : List Nat := [1, 1, 2, 3, 2, 2, 1, 4, 3, 2, 2]
def baseStart_4021983 : Nat := 118140960795 + 4021983 * 2 ^ 59
def prefixEnd_4021983 : Nat := 4983230072969 + 3 ^ 40 * 4021983 * 2
def baseEnd_4021983 : Nat := 2065210463212242706715743

theorem tailTrace_4021983 : CollatzResearch.WordTrace tailWord_4021983 prefixEnd_4021983 2065210463212242706715743 := by
  unfold tailWord_4021983
  simp only [CollatzResearch.WordTrace]
  refine ⟨146693771388049965854606603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97795847592033310569737735 146693771388049965854606603)
  ·
    refine ⟨220040657082074948781909905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146693771388049965854606603 220040657082074948781909905)
    ·
      refine ⟨165030492811556211586432429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220040657082074948781909905 165030492811556211586432429)
      ·
        refine ⟨61886434804333579344912161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165030492811556211586432429 61886434804333579344912161)
        ·
          refine ⟨46414826103250184508684121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61886434804333579344912161 46414826103250184508684121)
          ·
            refine ⟨34811119577437638381513091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46414826103250184508684121 34811119577437638381513091)
            ·
              refine ⟨52216679366156457572269637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34811119577437638381513091 52216679366156457572269637)
              ·
                refine ⟨9790627381154335794800557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52216679366156457572269637 9790627381154335794800557)
                ·
                  refine ⟨3671485267932875923050209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9790627381154335794800557 3671485267932875923050209)
                  ·
                    refine ⟨2753613950949656942287657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3671485267932875923050209 2753613950949656942287657)
                    ·
                      refine ⟨2065210463212242706715743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2753613950949656942287657 2065210463212242706715743)
                      ·
                        rfl

theorem cell23_4021983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 4, 3, 2, 2].length) (baseStart_4021983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4021983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4021983 prefixEnd_4021983 := by exact prefixLift 4021983
  have htrace : WordTrace (prefixWord ++ tailWord_4021983) baseStart_4021983 baseEnd_4021983 := by
    simpa [prefixWord, tailWord_4021983, baseEnd_4021983] using wordTrace_append hprefix tailTrace_4021983
  have hstable : (prefixWord ++ tailWord_4021983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4021983).length < 2 ^ (prefixWord ++ tailWord_4021983).sum := by decide
  have hdescent : baseEnd_4021983 < baseStart_4021983 := by decide
  rcases family_descends (prefixWord ++ tailWord_4021983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4021989 : List Nat := [1, 3, 1, 4, 1, 1, 3, 9]
def baseStart_4021989 : Nat := 118140960795 + 4021989 * 2 ^ 59
def prefixEnd_4021989 : Nat := 4983230072969 + 3 ^ 40 * 4021989 * 2
def baseEnd_4021989 : Nat := 76489390522080358638545

theorem tailTrace_4021989 : CollatzResearch.WordTrace tailWord_4021989 prefixEnd_4021989 76489390522080358638545 := by
  unfold tailWord_4021989
  simp only [CollatzResearch.WordTrace]
  refine ⟨146693990226028228879325021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97795993484018819252883347 146693990226028228879325021)
  ·
    refine ⟨55010246334760585829746883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146693990226028228879325021 55010246334760585829746883)
    ·
      refine ⟨82515369502140878744620325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55010246334760585829746883 82515369502140878744620325)
      ·
        refine ⟨15471631781651414764616311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82515369502140878744620325 15471631781651414764616311)
        ·
          refine ⟨23207447672477122146924467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15471631781651414764616311 23207447672477122146924467)
          ·
            refine ⟨34811171508715683220386701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23207447672477122146924467 34811171508715683220386701)
            ·
              refine ⟨13054189315768381207645013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34811171508715683220386701 13054189315768381207645013)
              ·
                refine ⟨76489390522080358638545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13054189315768381207645013 76489390522080358638545)
                ·
                  rfl

theorem cell23_4021989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 9].length) (baseStart_4021989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4021989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4021989 prefixEnd_4021989 := by exact prefixLift 4021989
  have htrace : WordTrace (prefixWord ++ tailWord_4021989) baseStart_4021989 baseEnd_4021989 := by
    simpa [prefixWord, tailWord_4021989, baseEnd_4021989] using wordTrace_append hprefix tailTrace_4021989
  have hstable : (prefixWord ++ tailWord_4021989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4021989).length < 2 ^ (prefixWord ++ tailWord_4021989).sum := by decide
  have hdescent : baseEnd_4021989 < baseStart_4021989 := by decide
  rcases family_descends (prefixWord ++ tailWord_4021989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4022000 : List Nat := [2, 1, 1, 1, 3, 1, 2, 7, 1, 2, 2]
def baseStart_4022000 : Nat := 118140960795 + 4022000 * 2 ^ 59
def prefixEnd_4022000 : Nat := 4983230072969 + 3 ^ 40 * 4022000 * 2
def baseEnd_4022000 : Nat := 2065219192383369140203165

theorem tailTrace_4022000 : CollatzResearch.WordTrace tailWord_4022000 prefixEnd_4022000 2065219192383369140203165 := by
  unfold tailWord_4022000
  simp only [CollatzResearch.WordTrace]
  refine ⟨73347195714494188878987727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97796260952658918505316969 73347195714494188878987727)
  ·
    refine ⟨110020793571741283318481591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73347195714494188878987727 110020793571741283318481591)
    ·
      refine ⟨165031190357611924977722387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110020793571741283318481591 165031190357611924977722387)
      ·
        refine ⟨247546785536417887466583581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165031190357611924977722387 247546785536417887466583581)
        ·
          refine ⟨92830044576156707799968843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 247546785536417887466583581 92830044576156707799968843)
          ·
            refine ⟨139245066864235061699953265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92830044576156707799968843 139245066864235061699953265)
            ·
              refine ⟨104433800148176296274964949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139245066864235061699953265 104433800148176296274964949)
              ·
                refine ⟨2447667190972881943944491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 104433800148176296274964949 2447667190972881943944491)
                ·
                  refine ⟨3671500786459322915916737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2447667190972881943944491 3671500786459322915916737)
                  ·
                    refine ⟨2753625589844492186937553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3671500786459322915916737 2753625589844492186937553)
                    ·
                      refine ⟨2065219192383369140203165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2753625589844492186937553 2065219192383369140203165)
                      ·
                        rfl

theorem cell23_4022000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 7, 1, 2, 2].length) (baseStart_4022000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4022000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4022000 prefixEnd_4022000 := by exact prefixLift 4022000
  have htrace : WordTrace (prefixWord ++ tailWord_4022000) baseStart_4022000 baseEnd_4022000 := by
    simpa [prefixWord, tailWord_4022000, baseEnd_4022000] using wordTrace_append hprefix tailTrace_4022000
  have hstable : (prefixWord ++ tailWord_4022000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4022000).length < 2 ^ (prefixWord ++ tailWord_4022000).sum := by decide
  have hdescent : baseEnd_4022000 < baseStart_4022000 := by decide
  rcases family_descends (prefixWord ++ tailWord_4022000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4022006 : List Nat := [5, 1, 1, 1, 1, 5, 9]
def baseStart_4022006 : Nat := 118140960795 + 4022006 * 2 ^ 59
def prefixEnd_4022006 : Nat := 4983230072969 + 3 ^ 40 * 4022006 * 2
def baseEnd_4022006 : Nat := 25496571274904890329977

theorem tailTrace_4022006 : CollatzResearch.WordTrace tailWord_4022006 prefixEnd_4022006 25496571274904890329977 := by
  unfold tailWord_4022006
  simp only [CollatzResearch.WordTrace]
  refine ⟨9168413141685415048918367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 97796406844644427188462581 9168413141685415048918367)
  ·
    refine ⟨13752619712528122573377551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9168413141685415048918367 13752619712528122573377551)
    ·
      refine ⟨20628929568792183860066327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13752619712528122573377551 20628929568792183860066327)
      ·
        refine ⟨30943394353188275790099491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20628929568792183860066327 30943394353188275790099491)
        ·
          refine ⟨46415091529782413685149237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30943394353188275790099491 46415091529782413685149237)
          ·
            refine ⟨4351414830917101282982741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 46415091529782413685149237 4351414830917101282982741)
            ·
              refine ⟨25496571274904890329977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4351414830917101282982741 25496571274904890329977)
              ·
                rfl

theorem cell23_4022006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 9].length) (baseStart_4022006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4022006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4022006 prefixEnd_4022006 := by exact prefixLift 4022006
  have htrace : WordTrace (prefixWord ++ tailWord_4022006) baseStart_4022006 baseEnd_4022006 := by
    simpa [prefixWord, tailWord_4022006, baseEnd_4022006] using wordTrace_append hprefix tailTrace_4022006
  have hstable : (prefixWord ++ tailWord_4022006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4022006).length < 2 ^ (prefixWord ++ tailWord_4022006).sum := by decide
  have hdescent : baseEnd_4022006 < baseStart_4022006 := by decide
  rcases family_descends (prefixWord ++ tailWord_4022006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4022059 : List Nat := [1, 1, 1, 1, 2, 1, 2, 2, 6, 1, 5]
def baseStart_4022059 : Nat := 118140960795 + 4022059 * 2 ^ 59
def prefixEnd_4022059 : Nat := 4983230072969 + 3 ^ 40 * 4022059 * 2
def baseEnd_4022059 : Nat := 2065249487741984409365393

theorem tailTrace_4022059 : CollatzResearch.WordTrace tailWord_4022059 prefixEnd_4022059 2065249487741984409365393 := by
  unfold tailWord_4022059
  simp only [CollatzResearch.WordTrace]
  refine ⟨146696543335774630834373231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97797695557183087222915487 146696543335774630834373231)
  ·
    refine ⟨220044815003661946251559847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146696543335774630834373231 220044815003661946251559847)
    ·
      refine ⟨330067222505492919377339771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220044815003661946251559847 330067222505492919377339771)
      ·
        refine ⟨495100833758239379066009657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330067222505492919377339771 495100833758239379066009657)
        ·
          refine ⟨371325625318679534299507243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 495100833758239379066009657 371325625318679534299507243)
          ·
            refine ⟨556988437978019301449260865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 371325625318679534299507243 556988437978019301449260865)
            ·
              refine ⟨417741328483514476086945649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 556988437978019301449260865 417741328483514476086945649)
              ·
                refine ⟨313305996362635857065209237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 417741328483514476086945649 313305996362635857065209237)
                ·
                  refine ⟨14686218579498555799931683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 313305996362635857065209237 14686218579498555799931683)
                  ·
                    refine ⟨22029327869247833699897525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14686218579498555799931683 22029327869247833699897525)
                    ·
                      refine ⟨2065249487741984409365393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22029327869247833699897525 2065249487741984409365393)
                      ·
                        rfl

theorem cell23_4022059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 6, 1, 5].length) (baseStart_4022059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4022059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4022059 prefixEnd_4022059 := by exact prefixLift 4022059
  have htrace : WordTrace (prefixWord ++ tailWord_4022059) baseStart_4022059 baseEnd_4022059 := by
    simpa [prefixWord, tailWord_4022059, baseEnd_4022059] using wordTrace_append hprefix tailTrace_4022059
  have hstable : (prefixWord ++ tailWord_4022059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4022059).length < 2 ^ (prefixWord ++ tailWord_4022059).sum := by decide
  have hdescent : baseEnd_4022059 < baseStart_4022059 := by decide
  rcases family_descends (prefixWord ++ tailWord_4022059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4022076 : List Nat := [2, 2, 2, 2, 1, 1, 3, 1, 2, 4, 3]
def baseStart_4022076 : Nat := 118140960795 + 4022076 * 2 ^ 59
def prefixEnd_4022076 : Nat := 4983230072969 + 3 ^ 40 * 4022076 * 2
def baseEnd_4022076 : Nat := 2065258216913110842852815

theorem tailTrace_4022076 : CollatzResearch.WordTrace tailWord_4022076 prefixEnd_4022076 2065258216913110842852815 := by
  unfold tailWord_4022076
  simp only [CollatzResearch.WordTrace]
  refine ⟨73348581688356521368871041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97798108917808695158494721 73348581688356521368871041)
  ·
    refine ⟨55011436266267391026653281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73348581688356521368871041 55011436266267391026653281)
    ·
      refine ⟨41258577199700543269989961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55011436266267391026653281 41258577199700543269989961)
      ·
        refine ⟨30943932899775407452492471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41258577199700543269989961 30943932899775407452492471)
        ·
          refine ⟨46415899349663111178738707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30943932899775407452492471 46415899349663111178738707)
          ·
            refine ⟨69623849024494666768108061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46415899349663111178738707 69623849024494666768108061)
            ·
              refine ⟨26108943384185500038040523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69623849024494666768108061 26108943384185500038040523)
              ·
                refine ⟨39163415076278250057060785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26108943384185500038040523 39163415076278250057060785)
                ·
                  refine ⟨29372561307208687542795589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39163415076278250057060785 29372561307208687542795589)
                  ·
                    refine ⟨5507355245101628914274173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29372561307208687542795589 5507355245101628914274173)
                    ·
                      refine ⟨2065258216913110842852815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5507355245101628914274173 2065258216913110842852815)
                      ·
                        rfl

theorem cell23_4022076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 1, 2, 4, 3].length) (baseStart_4022076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4022076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4022076 prefixEnd_4022076 := by exact prefixLift 4022076
  have htrace : WordTrace (prefixWord ++ tailWord_4022076) baseStart_4022076 baseEnd_4022076 := by
    simpa [prefixWord, tailWord_4022076, baseEnd_4022076] using wordTrace_append hprefix tailTrace_4022076
  have hstable : (prefixWord ++ tailWord_4022076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4022076).length < 2 ^ (prefixWord ++ tailWord_4022076).sum := by decide
  have hdescent : baseEnd_4022076 < baseStart_4022076 := by decide
  rcases family_descends (prefixWord ++ tailWord_4022076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4022090 : List Nat := [3, 1, 2, 1, 1, 1, 3, 5, 2, 2, 2]
def baseStart_4022090 : Nat := 118140960795 + 4022090 * 2 ^ 59
def prefixEnd_4022090 : Nat := 4983230072969 + 3 ^ 40 * 4022090 * 2
def baseEnd_4022090 : Nat := 2065265405642273788077751

theorem tailTrace_4022090 : CollatzResearch.WordTrace tailWord_4022090 prefixEnd_4022090 2065265405642273788077751 := by
  unfold tailWord_4022090
  simp only [CollatzResearch.WordTrace]
  refine ⟨36674418499665580782187931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97798449332441548752501149 36674418499665580782187931)
  ·
    refine ⟨55011627749498371173281897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36674418499665580782187931 55011627749498371173281897)
    ·
      refine ⟨41258720812123778379961423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55011627749498371173281897 41258720812123778379961423)
      ·
        refine ⟨61888081218185667569942135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41258720812123778379961423 61888081218185667569942135)
        ·
          refine ⟨92832121827278501354913203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61888081218185667569942135 92832121827278501354913203)
          ·
            refine ⟨139248182740917752032369805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92832121827278501354913203 139248182740917752032369805)
            ·
              refine ⟨52218068527844157012138677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139248182740917752032369805 52218068527844157012138677)
              ·
                refine ⟨4895443924485389719888001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52218068527844157012138677 4895443924485389719888001)
                ·
                  refine ⟨3671582943364042289916001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4895443924485389719888001 3671582943364042289916001)
                  ·
                    refine ⟨2753687207523031717437001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3671582943364042289916001 2753687207523031717437001)
                    ·
                      refine ⟨2065265405642273788077751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2753687207523031717437001 2065265405642273788077751)
                      ·
                        rfl

theorem cell23_4022090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 5, 2, 2, 2].length) (baseStart_4022090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4022090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4022090 prefixEnd_4022090 := by exact prefixLift 4022090
  have htrace : WordTrace (prefixWord ++ tailWord_4022090) baseStart_4022090 baseEnd_4022090 := by
    simpa [prefixWord, tailWord_4022090, baseEnd_4022090] using wordTrace_append hprefix tailTrace_4022090
  have hstable : (prefixWord ++ tailWord_4022090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4022090).length < 2 ^ (prefixWord ++ tailWord_4022090).sum := by decide
  have hdescent : baseEnd_4022090 < baseStart_4022090 := by decide
  rcases family_descends (prefixWord ++ tailWord_4022090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4022106 : List Nat := [3, 1, 1, 2, 1, 3, 1, 2, 1, 5, 3]
def baseStart_4022106 : Nat := 118140960795 + 4022106 * 2 ^ 59
def prefixEnd_4022106 : Nat := 4983230072969 + 3 ^ 40 * 4022106 * 2
def baseEnd_4022106 : Nat := 2065273621332745725477677

theorem tailTrace_4022106 : CollatzResearch.WordTrace tailWord_4022106 prefixEnd_4022106 2065273621332745725477677 := by
  unfold tailWord_4022106
  simp only [CollatzResearch.WordTrace]
  refine ⟨36674564391651089465333543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97798838377736238574222781 36674564391651089465333543)
  ·
    refine ⟨55011846587476634198000315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36674564391651089465333543 55011846587476634198000315)
    ·
      refine ⟨82517769881214951297000473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55011846587476634198000315 82517769881214951297000473)
      ·
        refine ⟨61888327410911213472750355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82517769881214951297000473 61888327410911213472750355)
        ·
          refine ⟨92832491116366820209125533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61888327410911213472750355 92832491116366820209125533)
          ·
            refine ⟨34812184168637557578422075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92832491116366820209125533 34812184168637557578422075)
            ·
              refine ⟨52218276252956336367633113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34812184168637557578422075 52218276252956336367633113)
              ·
                refine ⟨39163707189717252275724835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52218276252956336367633113 39163707189717252275724835)
                ·
                  refine ⟨58745560784575878413587253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39163707189717252275724835 58745560784575878413587253)
                  ·
                    refine ⟨5507396323553988601273805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58745560784575878413587253 5507396323553988601273805)
                    ·
                      refine ⟨2065273621332745725477677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5507396323553988601273805 2065273621332745725477677)
                      ·
                        rfl

theorem cell23_4022106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 2, 1, 5, 3].length) (baseStart_4022106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4022106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4022106 prefixEnd_4022106 := by exact prefixLift 4022106
  have htrace : WordTrace (prefixWord ++ tailWord_4022106) baseStart_4022106 baseEnd_4022106 := by
    simpa [prefixWord, tailWord_4022106, baseEnd_4022106] using wordTrace_append hprefix tailTrace_4022106
  have hstable : (prefixWord ++ tailWord_4022106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4022106).length < 2 ^ (prefixWord ++ tailWord_4022106).sum := by decide
  have hdescent : baseEnd_4022106 < baseStart_4022106 := by decide
  rcases family_descends (prefixWord ++ tailWord_4022106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4022113 : List Nat := [1, 2, 3, 1, 1, 1, 6, 3, 5]
def baseStart_4022113 : Nat := 118140960795 + 4022113 * 2 ^ 59
def prefixEnd_4022113 : Nat := 4983230072969 + 3 ^ 40 * 4022113 * 2
def baseEnd_4022113 : Nat := 229475246188591910898905

theorem tailTrace_4022113 : CollatzResearch.WordTrace tailWord_4022113 prefixEnd_4022113 229475246188591910898905 := by
  unfold tailWord_4022113
  simp only [CollatzResearch.WordTrace]
  refine ⟨146698512877578998056838993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97799008585052665371225995 146698512877578998056838993)
  ·
    refine ⟨110023884658184248542629245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146698512877578998056838993 110023884658184248542629245)
    ·
      refine ⟨41258956746819093203485967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110023884658184248542629245 41258956746819093203485967)
      ·
        refine ⟨61888435120228639805228951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41258956746819093203485967 61888435120228639805228951)
        ·
          refine ⟨92832652680342959707843427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61888435120228639805228951 92832652680342959707843427)
          ·
            refine ⟨139248979020514439561765141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92832652680342959707843427 139248979020514439561765141)
            ·
              refine ⟨6527295891586614354457741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 139248979020514439561765141 6527295891586614354457741)
              ·
                refine ⟨2447735959344980382921653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6527295891586614354457741 2447735959344980382921653)
                ·
                  refine ⟨229475246188591910898905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2447735959344980382921653 229475246188591910898905)
                  ·
                    rfl

theorem cell23_4022113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 6, 3, 5].length) (baseStart_4022113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4022113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4022113 prefixEnd_4022113 := by exact prefixLift 4022113
  have htrace : WordTrace (prefixWord ++ tailWord_4022113) baseStart_4022113 baseEnd_4022113 := by
    simpa [prefixWord, tailWord_4022113, baseEnd_4022113] using wordTrace_append hprefix tailTrace_4022113
  have hstable : (prefixWord ++ tailWord_4022113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4022113).length < 2 ^ (prefixWord ++ tailWord_4022113).sum := by decide
  have hdescent : baseEnd_4022113 < baseStart_4022113 := by decide
  rcases family_descends (prefixWord ++ tailWord_4022113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4022283 : List Nat := [1, 1, 1, 1, 6, 1, 1, 4, 1, 2, 4]
def baseStart_4022283 : Nat := 118140960795 + 4022283 * 2 ^ 59
def prefixEnd_4022283 : Nat := 4983230072969 + 3 ^ 40 * 4022283 * 2
def baseEnd_4022283 : Nat := 2065364507408591532964363

theorem tailTrace_4022283 : CollatzResearch.WordTrace tailWord_4022283 prefixEnd_4022283 2065364507408591532964363 := by
  unfold tailWord_4022283
  simp only [CollatzResearch.WordTrace]
  refine ⟨146704713286963117090527503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97803142191308744727018335 146704713286963117090527503)
  ·
    refine ⟨220057069930444675635791255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146704713286963117090527503 220057069930444675635791255)
    ·
      refine ⟨330085604895667013453686883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220057069930444675635791255 330085604895667013453686883)
      ·
        refine ⟨495128407343500520180530325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330085604895667013453686883 495128407343500520180530325)
        ·
          refine ⟨23209144094226586883462359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 495128407343500520180530325 23209144094226586883462359)
          ·
            refine ⟨34813716141339880325193539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23209144094226586883462359 34813716141339880325193539)
            ·
              refine ⟨52220574212009820487790309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34813716141339880325193539 52220574212009820487790309)
              ·
                refine ⟨9791357664751841341460683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52220574212009820487790309 9791357664751841341460683)
                ·
                  refine ⟨14687036497127762012191025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9791357664751841341460683 14687036497127762012191025)
                  ·
                    refine ⟨11015277372845821509143269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14687036497127762012191025 11015277372845821509143269)
                    ·
                      refine ⟨2065364507408591532964363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11015277372845821509143269 2065364507408591532964363)
                      ·
                        rfl

theorem cell23_4022283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 4, 1, 2, 4].length) (baseStart_4022283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4022283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4022283 prefixEnd_4022283 := by exact prefixLift 4022283
  have htrace : WordTrace (prefixWord ++ tailWord_4022283) baseStart_4022283 baseEnd_4022283 := by
    simpa [prefixWord, tailWord_4022283, baseEnd_4022283] using wordTrace_append hprefix tailTrace_4022283
  have hstable : (prefixWord ++ tailWord_4022283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4022283).length < 2 ^ (prefixWord ++ tailWord_4022283).sum := by decide
  have hdescent : baseEnd_4022283 < baseStart_4022283 := by decide
  rcases family_descends (prefixWord ++ tailWord_4022283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4022293 : List Nat := [1, 3, 2, 1, 5, 1, 10]
def baseStart_4022293 : Nat := 118140960795 + 4022293 * 2 ^ 59
def prefixEnd_4022293 : Nat := 4983230072969 + 3 ^ 40 * 4022293 * 2
def baseEnd_4022293 : Nat := 25498390644631314738757

theorem tailTrace_4022293 : CollatzResearch.WordTrace tailWord_4022293 prefixEnd_4022293 25498390644631314738757 := by
  unfold tailWord_4022293
  simp only [CollatzResearch.WordTrace]
  refine ⟨146705078016926888798391533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97803385344617925865594355 146705078016926888798391533)
  ·
    refine ⟨55014404256347583299396825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146705078016926888798391533 55014404256347583299396825)
    ·
      refine ⟨41260803192260687474547619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55014404256347583299396825 41260803192260687474547619)
      ·
        refine ⟨61891204788391031211821429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41260803192260687474547619 61891204788391031211821429)
        ·
          refine ⟨5802300448911659176108259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 61891204788391031211821429 5802300448911659176108259)
          ·
            refine ⟨8703450673367488764162389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5802300448911659176108259 8703450673367488764162389)
            ·
              refine ⟨25498390644631314738757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 8703450673367488764162389 25498390644631314738757)
              ·
                rfl

theorem cell23_4022293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 10].length) (baseStart_4022293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4022293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4022293 prefixEnd_4022293 := by exact prefixLift 4022293
  have htrace : WordTrace (prefixWord ++ tailWord_4022293) baseStart_4022293 baseEnd_4022293 := by
    simpa [prefixWord, tailWord_4022293, baseEnd_4022293] using wordTrace_append hprefix tailTrace_4022293
  have hstable : (prefixWord ++ tailWord_4022293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4022293).length < 2 ^ (prefixWord ++ tailWord_4022293).sum := by decide
  have hdescent : baseEnd_4022293 < baseStart_4022293 := by decide
  rcases family_descends (prefixWord ++ tailWord_4022293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4022314 : List Nat := [3, 1, 4, 1, 2, 2, 3, 1, 2, 4]
def baseStart_4022314 : Nat := 118140960795 + 4022314 * 2 ^ 59
def prefixEnd_4022314 : Nat := 4983230072969 + 3 ^ 40 * 4022314 * 2
def baseEnd_4022314 : Nat := 688460141769626970558907

theorem tailTrace_4022314 : CollatzResearch.WordTrace tailWord_4022314 prefixEnd_4022314 688460141769626970558907 := by
  unfold tailWord_4022314
  simp only [CollatzResearch.WordTrace]
  refine ⟨36676460987462702346226499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97803895966567206256603997 36676460987462702346226499)
  ·
    refine ⟨55014691481194053519339749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36676460987462702346226499 55014691481194053519339749)
    ·
      refine ⟨10315254652723885034876203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55014691481194053519339749 10315254652723885034876203)
      ·
        refine ⟨15472881979085827552314305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10315254652723885034876203 15472881979085827552314305)
        ·
          refine ⟨11604661484314370664235729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15472881979085827552314305 11604661484314370664235729)
          ·
            refine ⟨8703496113235777998176797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11604661484314370664235729 8703496113235777998176797)
            ·
              refine ⟨3263811042463416749316299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8703496113235777998176797 3263811042463416749316299)
              ·
                refine ⟨4895716563695125123974449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3263811042463416749316299 4895716563695125123974449)
                ·
                  refine ⟨3671787422771343842980837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4895716563695125123974449 3671787422771343842980837)
                  ·
                    refine ⟨688460141769626970558907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3671787422771343842980837 688460141769626970558907)
                    ·
                      rfl

theorem cell23_4022314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 3, 1, 2, 4].length) (baseStart_4022314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4022314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4022314 prefixEnd_4022314 := by exact prefixLift 4022314
  have htrace : WordTrace (prefixWord ++ tailWord_4022314) baseStart_4022314 baseEnd_4022314 := by
    simpa [prefixWord, tailWord_4022314, baseEnd_4022314] using wordTrace_append hprefix tailTrace_4022314
  have hstable : (prefixWord ++ tailWord_4022314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4022314).length < 2 ^ (prefixWord ++ tailWord_4022314).sum := by decide
  have hdescent : baseEnd_4022314 < baseStart_4022314 := by decide
  rcases family_descends (prefixWord ++ tailWord_4022314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4022320 : List Nat := [2, 1, 1, 1, 2, 5, 3, 1, 1, 3, 3]
def baseStart_4022320 : Nat := 118140960795 + 4022320 * 2 ^ 59
def prefixEnd_4022320 : Nat := 4983230072969 + 3 ^ 40 * 4022320 * 2
def baseEnd_4022320 : Nat := 2065383506192807888201693

theorem tailTrace_4022320 : CollatzResearch.WordTrace tailWord_4022320 prefixEnd_4022320 2065383506192807888201693 := by
  unfold tailWord_4022320
  simp only [CollatzResearch.WordTrace]
  refine ⟨73353031393914536204812207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97804041858552714939749609 73353031393914536204812207)
  ·
    refine ⟨110029547090871804307218311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73353031393914536204812207 110029547090871804307218311)
    ·
      refine ⟨165044320636307706460827467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110029547090871804307218311 165044320636307706460827467)
      ·
        refine ⟨247566480954461559691241201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165044320636307706460827467 247566480954461559691241201)
        ·
          refine ⟨185674860715846169768430901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 247566480954461559691241201 185674860715846169768430901)
          ·
            refine ⟨17407018192110578415790397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 185674860715846169768430901 17407018192110578415790397)
            ·
              refine ⟨6527631822041466905921399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17407018192110578415790397 6527631822041466905921399)
              ·
                refine ⟨9791447733062200358882099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6527631822041466905921399 9791447733062200358882099)
                ·
                  refine ⟨14687171599593300538323149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9791447733062200358882099 14687171599593300538323149)
                  ·
                    refine ⟨5507689349847487701871181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14687171599593300538323149 5507689349847487701871181)
                    ·
                      refine ⟨2065383506192807888201693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5507689349847487701871181 2065383506192807888201693)
                      ·
                        rfl

theorem cell23_4022320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 3, 1, 1, 3, 3].length) (baseStart_4022320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4022320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4022320 prefixEnd_4022320 := by exact prefixLift 4022320
  have htrace : WordTrace (prefixWord ++ tailWord_4022320) baseStart_4022320 baseEnd_4022320 := by
    simpa [prefixWord, tailWord_4022320, baseEnd_4022320] using wordTrace_append hprefix tailTrace_4022320
  have hstable : (prefixWord ++ tailWord_4022320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4022320).length < 2 ^ (prefixWord ++ tailWord_4022320).sum := by decide
  have hdescent : baseEnd_4022320 < baseStart_4022320 := by decide
  rcases family_descends (prefixWord ++ tailWord_4022320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4022333 : List Nat := [1, 4, 1, 3, 1, 1, 1, 1, 1, 4, 5]
def baseStart_4022333 : Nat := 118140960795 + 4022333 * 2 ^ 59
def prefixEnd_4022333 : Nat := 4983230072969 + 3 ^ 40 * 4022333 * 2
def baseEnd_4022333 : Nat := 2065390181441316337339133

theorem tailTrace_4022333 : CollatzResearch.WordTrace tailWord_4022333 prefixEnd_4022333 2065390181441316337339133 := by
  unfold tailWord_4022333
  simp only [CollatzResearch.WordTrace]
  refine ⟨146706536936781975629847653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97804357957854650419898435 146706536936781975629847653)
  ·
    refine ⟨27507475675646620430596435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146706536936781975629847653 27507475675646620430596435)
    ·
      refine ⟨41261213513469930645894653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27507475675646620430596435 41261213513469930645894653)
      ·
        refine ⟨15472955067551223992210495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41261213513469930645894653 15472955067551223992210495)
        ·
          refine ⟨23209432601326835988315743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15472955067551223992210495 23209432601326835988315743)
          ·
            refine ⟨34814148901990253982473615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23209432601326835988315743 34814148901990253982473615)
            ·
              refine ⟨52221223352985380973710423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34814148901990253982473615 52221223352985380973710423)
              ·
                refine ⟨78331835029478071460565635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52221223352985380973710423 78331835029478071460565635)
                ·
                  refine ⟨117497752544217107190848453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78331835029478071460565635 117497752544217107190848453)
                  ·
                    refine ⟨22030828602040707598284085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 117497752544217107190848453 22030828602040707598284085)
                    ·
                      refine ⟨2065390181441316337339133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22030828602040707598284085 2065390181441316337339133)
                      ·
                        rfl

theorem cell23_4022333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_4022333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4022333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4022333 prefixEnd_4022333 := by exact prefixLift 4022333
  have htrace : WordTrace (prefixWord ++ tailWord_4022333) baseStart_4022333 baseEnd_4022333 := by
    simpa [prefixWord, tailWord_4022333, baseEnd_4022333] using wordTrace_append hprefix tailTrace_4022333
  have hstable : (prefixWord ++ tailWord_4022333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4022333).length < 2 ^ (prefixWord ++ tailWord_4022333).sum := by decide
  have hdescent : baseEnd_4022333 < baseStart_4022333 := by decide
  rcases family_descends (prefixWord ++ tailWord_4022333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4022337 : List Nat := [1, 2, 5, 1, 2, 1, 1, 2, 4, 1, 3]
def baseStart_4022337 : Nat := 118140960795 + 4022337 * 2 ^ 59
def prefixEnd_4022337 : Nat := 4983230072969 + 3 ^ 40 * 4022337 * 2
def baseEnd_4022337 : Nat := 2065392235363934321689115

theorem tailTrace_4022337 : CollatzResearch.WordTrace tailWord_4022337 prefixEnd_4022337 2065392235363934321689115 := by
  unfold tailWord_4022337
  simp only [CollatzResearch.WordTrace]
  refine ⟨146706682828767484312993265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97804455219178322875328843 146706682828767484312993265)
  ·
    refine ⟨110030012121575613234744949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146706682828767484312993265 110030012121575613234744949)
    ·
      refine ⟨10315313636397713740757339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 110030012121575613234744949 10315313636397713740757339)
      ·
        refine ⟨15472970454596570611136009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10315313636397713740757339 15472970454596570611136009)
        ·
          refine ⟨11604727840947427958352007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15472970454596570611136009 11604727840947427958352007)
          ·
            refine ⟨17407091761421141937528011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11604727840947427958352007 17407091761421141937528011)
            ·
              refine ⟨26110637642131712906292017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17407091761421141937528011 26110637642131712906292017)
              ·
                refine ⟨19582978231598784679719013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26110637642131712906292017 19582978231598784679719013)
                ·
                  refine ⟨3671808418424772127447315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19582978231598784679719013 3671808418424772127447315)
                  ·
                    refine ⟨5507712627637158191170973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3671808418424772127447315 5507712627637158191170973)
                    ·
                      refine ⟨2065392235363934321689115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5507712627637158191170973 2065392235363934321689115)
                      ·
                        rfl

theorem cell23_4022337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 2, 4, 1, 3].length) (baseStart_4022337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4022337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4022337 prefixEnd_4022337 := by exact prefixLift 4022337
  have htrace : WordTrace (prefixWord ++ tailWord_4022337) baseStart_4022337 baseEnd_4022337 := by
    simpa [prefixWord, tailWord_4022337, baseEnd_4022337] using wordTrace_append hprefix tailTrace_4022337
  have hstable : (prefixWord ++ tailWord_4022337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4022337).length < 2 ^ (prefixWord ++ tailWord_4022337).sum := by decide
  have hdescent : baseEnd_4022337 < baseStart_4022337 := by decide
  rcases family_descends (prefixWord ++ tailWord_4022337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4022400 : List Nat := [2, 1, 1, 2, 1, 3, 1, 7, 5]
def baseStart_4022400 : Nat := 118140960795 + 4022400 * 2 ^ 59
def prefixEnd_4022400 : Nat := 4983230072969 + 3 ^ 40 * 4022400 * 2
def baseEnd_4022400 : Nat := 229491620516129730577925

theorem tailTrace_4022400 : CollatzResearch.WordTrace tailWord_4022400 prefixEnd_4022400 229491620516129730577925 := by
  unfold tailWord_4022400
  simp only [CollatzResearch.WordTrace]
  refine ⟨73354490313769623036268327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97805987085026164048357769 73354490313769623036268327)
  ·
    refine ⟨110031735470654434554402491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73354490313769623036268327 110031735470654434554402491)
    ·
      refine ⟨165047603205981651831603737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110031735470654434554402491 165047603205981651831603737)
      ·
        refine ⟨123785702404486238873702803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165047603205981651831603737 123785702404486238873702803)
        ·
          refine ⟨185678553606729358310554205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123785702404486238873702803 185678553606729358310554205)
          ·
            refine ⟨69629457602523509366457827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 185678553606729358310554205 69629457602523509366457827)
            ·
              refine ⟨104444186403785264049686741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69629457602523509366457827 104444186403785264049686741)
              ·
                refine ⟨2447910618838717126164533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 104444186403785264049686741 2447910618838717126164533)
                ·
                  refine ⟨229491620516129730577925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2447910618838717126164533 229491620516129730577925)
                  ·
                    rfl

theorem cell23_4022400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 7, 5].length) (baseStart_4022400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4022400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4022400 prefixEnd_4022400 := by exact prefixLift 4022400
  have htrace : WordTrace (prefixWord ++ tailWord_4022400) baseStart_4022400 baseEnd_4022400 := by
    simpa [prefixWord, tailWord_4022400, baseEnd_4022400] using wordTrace_append hprefix tailTrace_4022400
  have hstable : (prefixWord ++ tailWord_4022400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4022400).length < 2 ^ (prefixWord ++ tailWord_4022400).sum := by decide
  have hdescent : baseEnd_4022400 < baseStart_4022400 := by decide
  rcases family_descends (prefixWord ++ tailWord_4022400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4022450 : List Nat := [3, 2, 1, 1, 1, 3, 3, 1, 1, 3, 4]
def baseStart_4022450 : Nat := 118140960795 + 4022450 * 2 ^ 59
def prefixEnd_4022450 : Nat := 4983230072969 + 3 ^ 40 * 4022450 * 2
def baseEnd_4022450 : Nat := 2065450258677892379576095

theorem tailTrace_4022450 : CollatzResearch.WordTrace tailWord_4022450 prefixEnd_4022450 2065450258677892379576095 := by
  unfold tailWord_4022450
  simp only [CollatzResearch.WordTrace]
  refine ⟨36677701069339526152964201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97807202851572069741237869 36677701069339526152964201)
  ·
    refine ⟨27508275802004644614723151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36677701069339526152964201 27508275802004644614723151)
    ·
      refine ⟨41262413703006966922084727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27508275802004644614723151 41262413703006966922084727)
      ·
        refine ⟨61893620554510450383127091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41262413703006966922084727 61893620554510450383127091)
        ·
          refine ⟨92840430831765675574690637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61893620554510450383127091 92840430831765675574690637)
          ·
            refine ⟨34815161561912128340508989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92840430831765675574690637 34815161561912128340508989)
            ·
              refine ⟨13055685585717048127690871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34815161561912128340508989 13055685585717048127690871)
              ·
                refine ⟨19583528378575572191536307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13055685585717048127690871 19583528378575572191536307)
                ·
                  refine ⟨29375292567863358287304461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19583528378575572191536307 29375292567863358287304461)
                  ·
                    refine ⟨11015734712948759357739173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29375292567863358287304461 11015734712948759357739173)
                    ·
                      refine ⟨2065450258677892379576095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11015734712948759357739173 2065450258677892379576095)
                      ·
                        rfl

theorem cell23_4022450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 1, 1, 3, 4].length) (baseStart_4022450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4022450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4022450 prefixEnd_4022450 := by exact prefixLift 4022450
  have htrace : WordTrace (prefixWord ++ tailWord_4022450) baseStart_4022450 baseEnd_4022450 := by
    simpa [prefixWord, tailWord_4022450, baseEnd_4022450] using wordTrace_append hprefix tailTrace_4022450
  have hstable : (prefixWord ++ tailWord_4022450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4022450).length < 2 ^ (prefixWord ++ tailWord_4022450).sum := by decide
  have hdescent : baseEnd_4022450 < baseStart_4022450 := by decide
  rcases family_descends (prefixWord ++ tailWord_4022450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4022490 : List Nat := [3, 1, 1, 2, 2, 1, 2, 5, 6]
def baseStart_4022490 : Nat := 118140960795 + 4022490 * 2 ^ 59
def prefixEnd_4022490 : Nat := 4983230072969 + 3 ^ 40 * 4022490 * 2
def baseEnd_4022490 : Nat := 229496755322674691452879

theorem tailTrace_4022490 : CollatzResearch.WordTrace tailWord_4022490 prefixEnd_4022490 229496755322674691452879 := by
  unfold tailWord_4022490
  simp only [CollatzResearch.WordTrace]
  refine ⟨36678065799303297860828231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97808175464808794295541949 36678065799303297860828231)
  ·
    refine ⟨55017098698954946791242347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36678065799303297860828231 55017098698954946791242347)
    ·
      refine ⟨82525648048432420186863521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55017098698954946791242347 82525648048432420186863521)
      ·
        refine ⟨61894236036324315140147641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82525648048432420186863521 61894236036324315140147641)
        ·
          refine ⟨46420677027243236355110731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61894236036324315140147641 46420677027243236355110731)
          ·
            refine ⟨69631015540864854532666097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46420677027243236355110731 69631015540864854532666097)
            ·
              refine ⟨52223261655648640899499573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69631015540864854532666097 52223261655648640899499573)
              ·
                refine ⟨4895930780217060084328085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52223261655648640899499573 4895930780217060084328085)
                ·
                  refine ⟨229496755322674691452879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4895930780217060084328085 229496755322674691452879)
                  ·
                    rfl

theorem cell23_4022490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 5, 6].length) (baseStart_4022490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4022490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4022490 prefixEnd_4022490 := by exact prefixLift 4022490
  have htrace : WordTrace (prefixWord ++ tailWord_4022490) baseStart_4022490 baseEnd_4022490 := by
    simpa [prefixWord, tailWord_4022490, baseEnd_4022490] using wordTrace_append hprefix tailTrace_4022490
  have hstable : (prefixWord ++ tailWord_4022490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4022490).length < 2 ^ (prefixWord ++ tailWord_4022490).sum := by decide
  have hdescent : baseEnd_4022490 < baseStart_4022490 := by decide
  rcases family_descends (prefixWord ++ tailWord_4022490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4022500 : List Nat := [2, 3, 1, 1, 1, 2, 1, 1, 1, 7, 3]
def baseStart_4022500 : Nat := 118140960795 + 4022500 * 2 ^ 59
def prefixEnd_4022500 : Nat := 4983230072969 + 3 ^ 40 * 4022500 * 2
def baseEnd_4022500 : Nat := 2065475932710617183950865

theorem tailTrace_4022500 : CollatzResearch.WordTrace tailWord_4022500 prefixEnd_4022500 2065475932710617183950865 := by
  unfold tailWord_4022500
  simp only [CollatzResearch.WordTrace]
  refine ⟨73356313963588481575588477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97808418618117975434117969 73356313963588481575588477)
  ·
    refine ⟨27508617736345680590845679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73356313963588481575588477 27508617736345680590845679)
    ·
      refine ⟨41262926604518520886268519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27508617736345680590845679 41262926604518520886268519)
      ·
        refine ⟨61894389906777781329402779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41262926604518520886268519 61894389906777781329402779)
        ·
          refine ⟨92841584860166671994104169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61894389906777781329402779 92841584860166671994104169)
          ·
            refine ⟨69631188645125003995578127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92841584860166671994104169 69631188645125003995578127)
            ·
              refine ⟨104446782967687505993367191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69631188645125003995578127 104446782967687505993367191)
              ·
                refine ⟨156670174451531258990050787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104446782967687505993367191 156670174451531258990050787)
                ·
                  refine ⟨235005261677296888485076181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 156670174451531258990050787 235005261677296888485076181)
                  ·
                    refine ⟨5507935820561645823868973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 235005261677296888485076181 5507935820561645823868973)
                    ·
                      refine ⟨2065475932710617183950865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5507935820561645823868973 2065475932710617183950865)
                      ·
                        rfl

theorem cell23_4022500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 1, 7, 3].length) (baseStart_4022500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4022500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4022500 prefixEnd_4022500 := by exact prefixLift 4022500
  have htrace : WordTrace (prefixWord ++ tailWord_4022500) baseStart_4022500 baseEnd_4022500 := by
    simpa [prefixWord, tailWord_4022500, baseEnd_4022500] using wordTrace_append hprefix tailTrace_4022500
  have hstable : (prefixWord ++ tailWord_4022500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4022500).length < 2 ^ (prefixWord ++ tailWord_4022500).sum := by decide
  have hdescent : baseEnd_4022500 < baseStart_4022500 := by decide
  rcases family_descends (prefixWord ++ tailWord_4022500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4022511 : List Nat := [1, 1, 2, 1, 6, 3, 1, 3, 1, 4]
def baseStart_4022511 : Nat := 118140960795 + 4022511 * 2 ^ 59
def prefixEnd_4022511 : Nat := 4983230072969 + 3 ^ 40 * 4022511 * 2
def baseEnd_4022511 : Nat := 688493860332605546971105

theorem tailTrace_4022511 : CollatzResearch.WordTrace tailWord_4022511 prefixEnd_4022511 688493860332605546971105 := by
  unfold tailWord_4022511
  simp only [CollatzResearch.WordTrace]
  refine ⟨146713029130137112029827387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97808686086758074686551591 146713029130137112029827387)
  ·
    refine ⟨220069543695205668044741081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146713029130137112029827387 220069543695205668044741081)
    ·
      refine ⟨165052157771404251033555811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220069543695205668044741081 165052157771404251033555811)
      ·
        refine ⟨247578236657106376550333717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165052157771404251033555811 247578236657106376550333717)
        ·
          refine ⟨11605229843301861400796893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 247578236657106376550333717 11605229843301861400796893)
          ·
            refine ⟨4351961191238198025298835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11605229843301861400796893 4351961191238198025298835)
            ·
              refine ⟨6527941786857297037948253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4351961191238198025298835 6527941786857297037948253)
              ·
                refine ⟨2447978170071486389230595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6527941786857297037948253 2447978170071486389230595)
                ·
                  refine ⟨3671967255107229583845893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2447978170071486389230595 3671967255107229583845893)
                  ·
                    refine ⟨688493860332605546971105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3671967255107229583845893 688493860332605546971105)
                    ·
                      rfl

theorem cell23_4022511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 1, 3, 1, 4].length) (baseStart_4022511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4022511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4022511 prefixEnd_4022511 := by exact prefixLift 4022511
  have htrace : WordTrace (prefixWord ++ tailWord_4022511) baseStart_4022511 baseEnd_4022511 := by
    simpa [prefixWord, tailWord_4022511, baseEnd_4022511] using wordTrace_append hprefix tailTrace_4022511
  have hstable : (prefixWord ++ tailWord_4022511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4022511).length < 2 ^ (prefixWord ++ tailWord_4022511).sum := by decide
  have hdescent : baseEnd_4022511 < baseStart_4022511 := by decide
  rcases family_descends (prefixWord ++ tailWord_4022511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4022585 : List Nat := [1, 2, 1, 6, 1, 3, 2, 2, 1, 1, 3]
def baseStart_4022585 : Nat := 118140960795 + 4022585 * 2 ^ 59
def prefixEnd_4022585 : Nat := 4983230072969 + 3 ^ 40 * 4022585 * 2
def baseEnd_4022585 : Nat := 2065519578566249351387975

theorem tailTrace_4022585 : CollatzResearch.WordTrace tailWord_4022585 prefixEnd_4022585 2065519578566249351387975 := by
  unfold tailWord_4022585
  simp only [CollatzResearch.WordTrace]
  refine ⟨146715728131869022668021209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97810485421246015112014139 146715728131869022668021209)
  ·
    refine ⟨110036796098901767001015907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146715728131869022668021209 110036796098901767001015907)
    ·
      refine ⟨165055194148352650501523861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110036796098901767001015907 165055194148352650501523861)
      ·
        refine ⟨7736962225704030492258931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 165055194148352650501523861 7736962225704030492258931)
        ·
          refine ⟨11605443338556045738388397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7736962225704030492258931 11605443338556045738388397)
          ·
            refine ⟨4352041251958517151895649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11605443338556045738388397 4352041251958517151895649)
            ·
              refine ⟨3264030938968887863921737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4352041251958517151895649 3264030938968887863921737)
              ·
                refine ⟨2448023204226665897941303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3264030938968887863921737 2448023204226665897941303)
                ·
                  refine ⟨3672034806339998846911955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2448023204226665897941303 3672034806339998846911955)
                  ·
                    refine ⟨5508052209509998270367933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3672034806339998846911955 5508052209509998270367933)
                    ·
                      refine ⟨2065519578566249351387975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5508052209509998270367933 2065519578566249351387975)
                      ·
                        rfl

theorem cell23_4022585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 2, 2, 1, 1, 3].length) (baseStart_4022585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4022585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4022585 prefixEnd_4022585 := by exact prefixLift 4022585
  have htrace : WordTrace (prefixWord ++ tailWord_4022585) baseStart_4022585 baseEnd_4022585 := by
    simpa [prefixWord, tailWord_4022585, baseEnd_4022585] using wordTrace_append hprefix tailTrace_4022585
  have hstable : (prefixWord ++ tailWord_4022585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4022585).length < 2 ^ (prefixWord ++ tailWord_4022585).sum := by decide
  have hdescent : baseEnd_4022585 < baseStart_4022585 := by decide
  rcases family_descends (prefixWord ++ tailWord_4022585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4022600 : List Nat := [2, 1, 3, 1, 1, 2, 2, 1, 2, 2, 6]
def baseStart_4022600 : Nat := 118140960795 + 4022600 * 2 ^ 59
def prefixEnd_4022600 : Nat := 4983230072969 + 3 ^ 40 * 4022600 * 2
def baseEnd_4022600 : Nat := 2065527280776066792700405

theorem tailTrace_4022600 : CollatzResearch.WordTrace tailWord_4022600 prefixEnd_4022600 2065527280776066792700405 := by
  unfold tailWord_4022600
  simp only [CollatzResearch.WordTrace]
  refine ⟨73358137613407340114908627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97810850151209786819878169 73358137613407340114908627)
  ·
    refine ⟨110037206420111010172362941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73358137613407340114908627 110037206420111010172362941)
    ·
      refine ⟨41263952407541628814636103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110037206420111010172362941 41263952407541628814636103)
      ·
        refine ⟨61895928611312443221954155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41263952407541628814636103 61895928611312443221954155)
        ·
          refine ⟨92843892916968664832931233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61895928611312443221954155 92843892916968664832931233)
          ·
            refine ⟨69632919687726498624698425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92843892916968664832931233 69632919687726498624698425)
            ·
              refine ⟨52224689765794873968523819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69632919687726498624698425 52224689765794873968523819)
              ·
                refine ⟨78337034648692310952785729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52224689765794873968523819 78337034648692310952785729)
                ·
                  refine ⟨58752775986519233214589297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78337034648692310952785729 58752775986519233214589297)
                  ·
                    refine ⟨44064581989889424910941973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58752775986519233214589297 44064581989889424910941973)
                    ·
                      refine ⟨2065527280776066792700405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44064581989889424910941973 2065527280776066792700405)
                      ·
                        rfl

theorem cell23_4022600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 2, 2, 6].length) (baseStart_4022600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4022600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4022600 prefixEnd_4022600 := by exact prefixLift 4022600
  have htrace : WordTrace (prefixWord ++ tailWord_4022600) baseStart_4022600 baseEnd_4022600 := by
    simpa [prefixWord, tailWord_4022600, baseEnd_4022600] using wordTrace_append hprefix tailTrace_4022600
  have hstable : (prefixWord ++ tailWord_4022600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4022600).length < 2 ^ (prefixWord ++ tailWord_4022600).sum := by decide
  have hdescent : baseEnd_4022600 < baseStart_4022600 := by decide
  rcases family_descends (prefixWord ++ tailWord_4022600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4022697 : List Nat := [1, 2, 1, 1, 1, 1, 3, 3, 4, 3, 3]
def baseStart_4022697 : Nat := 118140960795 + 4022697 * 2 ^ 59
def prefixEnd_4022697 : Nat := 4983230072969 + 3 ^ 40 * 4022697 * 2
def baseEnd_4022697 : Nat := 2065577088399552913187459

theorem tailTrace_4022697 : CollatzResearch.WordTrace tailWord_4022697 prefixEnd_4022697 2065577088399552913187459 := by
  unfold tailWord_4022697
  simp only [CollatzResearch.WordTrace]
  refine ⟨146719813107463265796098345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97813208738308843864065563 146719813107463265796098345)
  ·
    refine ⟨110039859830597449347073759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146719813107463265796098345 110039859830597449347073759)
    ·
      refine ⟨165059789745896174020610639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110039859830597449347073759 165059789745896174020610639)
      ·
        refine ⟨247589684618844261030915959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165059789745896174020610639 247589684618844261030915959)
        ·
          refine ⟨371384526928266391546373939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247589684618844261030915959 371384526928266391546373939)
          ·
            refine ⟨557076790392399587319560909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 371384526928266391546373939 557076790392399587319560909)
            ·
              refine ⟨208903796397149845244835341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 557076790392399587319560909 208903796397149845244835341)
              ·
                refine ⟨78338923648931191966813253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 208903796397149845244835341 78338923648931191966813253)
                ·
                  refine ⟨14688548184174598493777485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78338923648931191966813253 14688548184174598493777485)
                  ·
                    refine ⟨5508205569065474435166557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14688548184174598493777485 5508205569065474435166557)
                    ·
                      refine ⟨2065577088399552913187459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5508205569065474435166557 2065577088399552913187459)
                      ·
                        rfl

theorem cell23_4022697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 4, 3, 3].length) (baseStart_4022697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4022697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4022697 prefixEnd_4022697 := by exact prefixLift 4022697
  have htrace : WordTrace (prefixWord ++ tailWord_4022697) baseStart_4022697 baseEnd_4022697 := by
    simpa [prefixWord, tailWord_4022697, baseEnd_4022697] using wordTrace_append hprefix tailTrace_4022697
  have hstable : (prefixWord ++ tailWord_4022697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4022697).length < 2 ^ (prefixWord ++ tailWord_4022697).sum := by decide
  have hdescent : baseEnd_4022697 < baseStart_4022697 := by decide
  rcases family_descends (prefixWord ++ tailWord_4022697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4022737 : List Nat := [1, 2, 2, 1, 2, 1, 1, 5, 1, 3, 4]
def baseStart_4022737 : Nat := 118140960795 + 4022737 * 2 ^ 59
def prefixEnd_4022737 : Nat := 4983230072969 + 3 ^ 40 * 4022737 * 2
def baseEnd_4022737 : Nat := 2065597627625732756687275

theorem tailTrace_4022737 : CollatzResearch.WordTrace tailWord_4022737 prefixEnd_4022737 2065597627625732756687275 := by
  unfold tailWord_4022737
  simp only [CollatzResearch.WordTrace]
  refine ⟨146721272027318352627554465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97814181351545568418369643 146721272027318352627554465)
  ·
    refine ⟨110040954020488764470665849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146721272027318352627554465 110040954020488764470665849)
    ·
      refine ⟨82530715515366573352999387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110040954020488764470665849 82530715515366573352999387)
      ·
        refine ⟨123796073273049860029499081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82530715515366573352999387 123796073273049860029499081)
        ·
          refine ⟨92847054954787395022124311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123796073273049860029499081 92847054954787395022124311)
          ·
            refine ⟨139270582432181092533186467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92847054954787395022124311 139270582432181092533186467)
            ·
              refine ⟨208905873648271638799779701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139270582432181092533186467 208905873648271638799779701)
              ·
                refine ⟨19584925654525466137479347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 208905873648271638799779701 19584925654525466137479347)
                ·
                  refine ⟨29377388481788199206219021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19584925654525466137479347 29377388481788199206219021)
                  ·
                    refine ⟨11016520680670574702332133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29377388481788199206219021 11016520680670574702332133)
                    ·
                      refine ⟨2065597627625732756687275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11016520680670574702332133 2065597627625732756687275)
                      ·
                        rfl

theorem cell23_4022737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 5, 1, 3, 4].length) (baseStart_4022737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4022737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4022737 prefixEnd_4022737 := by exact prefixLift 4022737
  have htrace : WordTrace (prefixWord ++ tailWord_4022737) baseStart_4022737 baseEnd_4022737 := by
    simpa [prefixWord, tailWord_4022737, baseEnd_4022737] using wordTrace_append hprefix tailTrace_4022737
  have hstable : (prefixWord ++ tailWord_4022737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4022737).length < 2 ^ (prefixWord ++ tailWord_4022737).sum := by decide
  have hdescent : baseEnd_4022737 < baseStart_4022737 := by decide
  rcases family_descends (prefixWord ++ tailWord_4022737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4022755 : List Nat := [1, 1, 1, 6, 4, 1, 2, 2, 5]
def baseStart_4022755 : Nat := 118140960795 + 4022755 * 2 ^ 59
def prefixEnd_4022755 : Nat := 4983230072969 + 3 ^ 40 * 4022755 * 2
def baseEnd_4022755 : Nat := 229511874475279298473577

theorem tailTrace_4022755 : CollatzResearch.WordTrace tailWord_4022755 prefixEnd_4022755 229511874475279298473577 := by
  unfold tailWord_4022755
  simp only [CollatzResearch.WordTrace]
  refine ⟨146721928541253141701709719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97814619027502094467806479 146721928541253141701709719)
  ·
    refine ⟨220082892811879712552564579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146721928541253141701709719 220082892811879712552564579)
    ·
      refine ⟨330124339217819568828846869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220082892811879712552564579 330124339217819568828846869)
      ·
        refine ⟨15474578400835292288852197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 330124339217819568828846869 15474578400835292288852197)
        ·
          refine ⟨2901483450156617304159787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15474578400835292288852197 2901483450156617304159787)
          ·
            refine ⟨4352225175234925956239681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2901483450156617304159787 4352225175234925956239681)
            ·
              refine ⟨3264168881426194467179761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4352225175234925956239681 3264168881426194467179761)
              ·
                refine ⟨2448126661069645850384821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3264168881426194467179761 2448126661069645850384821)
                ·
                  refine ⟨229511874475279298473577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2448126661069645850384821 229511874475279298473577)
                  ·
                    rfl

theorem cell23_4022755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 2, 2, 5].length) (baseStart_4022755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4022755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4022755 prefixEnd_4022755 := by exact prefixLift 4022755
  have htrace : WordTrace (prefixWord ++ tailWord_4022755) baseStart_4022755 baseEnd_4022755 := by
    simpa [prefixWord, tailWord_4022755, baseEnd_4022755] using wordTrace_append hprefix tailTrace_4022755
  have hstable : (prefixWord ++ tailWord_4022755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4022755).length < 2 ^ (prefixWord ++ tailWord_4022755).sum := by decide
  have hdescent : baseEnd_4022755 < baseStart_4022755 := by decide
  rcases family_descends (prefixWord ++ tailWord_4022755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4022764 : List Nat := [2, 2, 1, 1, 2, 1, 4, 3, 3, 4]
def baseStart_4022764 : Nat := 118140960795 + 4022764 * 2 ^ 59
def prefixEnd_4022764 : Nat := 4983230072969 + 3 ^ 40 * 4022764 * 2
def baseEnd_4022764 : Nat := 688537163867801383683217

theorem tailTrace_4022764 : CollatzResearch.WordTrace tailWord_4022764 prefixEnd_4022764 688537163867801383683217 := by
  unfold tailWord_4022764
  simp only [CollatzResearch.WordTrace]
  refine ⟨73361128399110268119393673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97814837865480357492524897 73361128399110268119393673)
  ·
    refine ⟨55020846299332701089545255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73361128399110268119393673 55020846299332701089545255)
    ·
      refine ⟨82531269448999051634317883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55020846299332701089545255 82531269448999051634317883)
      ·
        refine ⟨123796904173498577451476825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82531269448999051634317883 123796904173498577451476825)
        ·
          refine ⟨92847678130123933088607619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123796904173498577451476825 92847678130123933088607619)
          ·
            refine ⟨139271517195185899632911429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92847678130123933088607619 139271517195185899632911429)
            ·
              refine ⟨26113409474097356181170893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 139271517195185899632911429 26113409474097356181170893)
              ·
                refine ⟨9792528552786508567939085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26113409474097356181170893 9792528552786508567939085)
                ·
                  refine ⟨3672198207294940712977157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9792528552786508567939085 3672198207294940712977157)
                  ·
                    refine ⟨688537163867801383683217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3672198207294940712977157 688537163867801383683217)
                    ·
                      rfl

theorem cell23_4022764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 4].length) (baseStart_4022764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4022764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4022764 prefixEnd_4022764 := by exact prefixLift 4022764
  have htrace : WordTrace (prefixWord ++ tailWord_4022764) baseStart_4022764 baseEnd_4022764 := by
    simpa [prefixWord, tailWord_4022764, baseEnd_4022764] using wordTrace_append hprefix tailTrace_4022764
  have hstable : (prefixWord ++ tailWord_4022764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4022764).length < 2 ^ (prefixWord ++ tailWord_4022764).sum := by decide
  have hdescent : baseEnd_4022764 < baseStart_4022764 := by decide
  rcases family_descends (prefixWord ++ tailWord_4022764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4022767 : List Nat := [1, 1, 2, 1, 4, 1, 1, 2, 2, 4, 4]
def baseStart_4022767 : Nat := 118140960795 + 4022767 * 2 ^ 59
def prefixEnd_4022767 : Nat := 4983230072969 + 3 ^ 40 * 4022767 * 2
def baseEnd_4022767 : Nat := 2065613032045367639312137

theorem tailTrace_4022767 : CollatzResearch.WordTrace tailWord_4022767 prefixEnd_4022767 2065613032045367639312137 := by
  unfold tailWord_4022767
  simp only [CollatzResearch.WordTrace]
  refine ⟨146722366217209667751146555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97814910811473111834097703 146722366217209667751146555)
  ·
    refine ⟨220083549325814501626719833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146722366217209667751146555 220083549325814501626719833)
    ·
      refine ⟨165062661994360876220039875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220083549325814501626719833 165062661994360876220039875)
      ·
        refine ⟨247593992991541314330059813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165062661994360876220039875 247593992991541314330059813)
        ·
          refine ⟨46423873685913996436886215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 247593992991541314330059813 46423873685913996436886215)
          ·
            refine ⟨69635810528870994655329323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46423873685913996436886215 69635810528870994655329323)
            ·
              refine ⟨104453715793306491982993985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69635810528870994655329323 104453715793306491982993985)
              ·
                refine ⟨78340286844979868987245489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104453715793306491982993985 78340286844979868987245489)
                ·
                  refine ⟨58755215133734901740434117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78340286844979868987245489 58755215133734901740434117)
                  ·
                    refine ⟨11016602837575294076331397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58755215133734901740434117 11016602837575294076331397)
                    ·
                      refine ⟨2065613032045367639312137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11016602837575294076331397 2065613032045367639312137)
                      ·
                        rfl

theorem cell23_4022767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 2, 4, 4].length) (baseStart_4022767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4022767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4022767 prefixEnd_4022767 := by exact prefixLift 4022767
  have htrace : WordTrace (prefixWord ++ tailWord_4022767) baseStart_4022767 baseEnd_4022767 := by
    simpa [prefixWord, tailWord_4022767, baseEnd_4022767] using wordTrace_append hprefix tailTrace_4022767
  have hstable : (prefixWord ++ tailWord_4022767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4022767).length < 2 ^ (prefixWord ++ tailWord_4022767).sum := by decide
  have hdescent : baseEnd_4022767 < baseStart_4022767 := by decide
  rcases family_descends (prefixWord ++ tailWord_4022767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4022788 : List Nat := [2, 3, 2, 3, 1, 3, 1, 1, 2, 1, 4]
def baseStart_4022788 : Nat := 118140960795 + 4022788 * 2 ^ 59
def prefixEnd_4022788 : Nat := 4983230072969 + 3 ^ 40 * 4022788 * 2
def baseEnd_4022788 : Nat := 2065623815139112057149541

theorem tailTrace_4022788 : CollatzResearch.WordTrace tailWord_4022788 prefixEnd_4022788 2065623815139112057149541 := by
  unfold tailWord_4022788
  simp only [CollatzResearch.WordTrace]
  refine ⟨73361566075066794168830509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97815421433422392225107345 73361566075066794168830509)
  ·
    refine ⟨27510587278150047813311441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73361566075066794168830509 27510587278150047813311441)
    ·
      refine ⟨20632940458612535859983581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27510587278150047813311441 20632940458612535859983581)
      ·
        refine ⟨7737352671979700947493843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20632940458612535859983581 7737352671979700947493843)
        ·
          refine ⟨11606029007969551421240765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7737352671979700947493843 11606029007969551421240765)
          ·
            refine ⟨4352260877988581782965287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11606029007969551421240765 4352260877988581782965287)
            ·
              refine ⟨6528391316982872674447931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4352260877988581782965287 6528391316982872674447931)
              ·
                refine ⟨9792586975474309011671897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6528391316982872674447931 9792586975474309011671897)
                ·
                  refine ⟨7344440231605731758753923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9792586975474309011671897 7344440231605731758753923)
                  ·
                    refine ⟨11016660347408597638130885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7344440231605731758753923 11016660347408597638130885)
                    ·
                      refine ⟨2065623815139112057149541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11016660347408597638130885 2065623815139112057149541)
                      ·
                        rfl

theorem cell23_4022788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_4022788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4022788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4022788 prefixEnd_4022788 := by exact prefixLift 4022788
  have htrace : WordTrace (prefixWord ++ tailWord_4022788) baseStart_4022788 baseEnd_4022788 := by
    simpa [prefixWord, tailWord_4022788, baseEnd_4022788] using wordTrace_append hprefix tailTrace_4022788
  have hstable : (prefixWord ++ tailWord_4022788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4022788).length < 2 ^ (prefixWord ++ tailWord_4022788).sum := by decide
  have hdescent : baseEnd_4022788 < baseStart_4022788 := by decide
  rcases family_descends (prefixWord ++ tailWord_4022788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4022791 : List Nat := [1, 1, 4, 3, 3, 1, 1, 1, 1, 4, 3]
def baseStart_4022791 : Nat := 118140960795 + 4022791 * 2 ^ 59
def prefixEnd_4022791 : Nat := 4983230072969 + 3 ^ 40 * 4022791 * 2
def baseEnd_4022791 : Nat := 2065625355581075545412027

theorem tailTrace_4022791 : CollatzResearch.WordTrace tailWord_4022791 prefixEnd_4022791 2065625355581075545412027 := by
  unfold tailWord_4022791
  simp only [CollatzResearch.WordTrace]
  refine ⟨146723241569122719850020227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97815494379415146566680151 146723241569122719850020227)
  ·
    refine ⟨220084862353684079775030341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146723241569122719850020227 220084862353684079775030341)
    ·
      refine ⟨41265911691315764957818189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 220084862353684079775030341 41265911691315764957818189)
      ·
        refine ⟨15474716884243411859181821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41265911691315764957818189 15474716884243411859181821)
        ·
          refine ⟨5803018831591279447193183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15474716884243411859181821 5803018831591279447193183)
          ·
            refine ⟨8704528247386919170789775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5803018831591279447193183 8704528247386919170789775)
            ·
              refine ⟨13056792371080378756184663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8704528247386919170789775 13056792371080378756184663)
              ·
                refine ⟨19585188556620568134276995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13056792371080378756184663 19585188556620568134276995)
                ·
                  refine ⟨29377782834930852201415493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19585188556620568134276995 29377782834930852201415493)
                  ·
                    refine ⟨5508334281549534787765405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29377782834930852201415493 5508334281549534787765405)
                    ·
                      refine ⟨2065625355581075545412027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5508334281549534787765405 2065625355581075545412027)
                      ·
                        rfl

theorem cell23_4022791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 1, 1, 4, 3].length) (baseStart_4022791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4022791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4022791 prefixEnd_4022791 := by exact prefixLift 4022791
  have htrace : WordTrace (prefixWord ++ tailWord_4022791) baseStart_4022791 baseEnd_4022791 := by
    simpa [prefixWord, tailWord_4022791, baseEnd_4022791] using wordTrace_append hprefix tailTrace_4022791
  have hstable : (prefixWord ++ tailWord_4022791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4022791).length < 2 ^ (prefixWord ++ tailWord_4022791).sum := by decide
  have hdescent : baseEnd_4022791 < baseStart_4022791 := by decide
  rcases family_descends (prefixWord ++ tailWord_4022791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4022798 : List Nat := [4, 1, 1, 2, 3, 1, 1, 5, 1, 4]
def baseStart_4022798 : Nat := 118140960795 + 4022798 * 2 ^ 59
def prefixEnd_4022798 : Nat := 4983230072969 + 3 ^ 40 * 4022798 * 2
def baseEnd_4022798 : Nat := 688542983315219006008165

theorem tailTrace_4022798 : CollatzResearch.WordTrace tailWord_4022798 prefixEnd_4022798 688542983315219006008165 := by
  unfold tailWord_4022798
  simp only [CollatzResearch.WordTrace]
  refine ⟨18340437110012170005690631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97815664586731573363683365 18340437110012170005690631)
  ·
    refine ⟨27510655665018255008535947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18340437110012170005690631 27510655665018255008535947)
    ·
      refine ⟨41265983497527382512803921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27510655665018255008535947 41265983497527382512803921)
      ·
        refine ⟨30949487623145536884602941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41265983497527382512803921 30949487623145536884602941)
        ·
          refine ⟨11606057858679576331726103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30949487623145536884602941 11606057858679576331726103)
          ·
            refine ⟨17409086788019364497589155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11606057858679576331726103 17409086788019364497589155)
            ·
              refine ⟨26113630182029046746383733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17409086788019364497589155 26113630182029046746383733)
              ·
                refine ⟨2448152829565223132473475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26113630182029046746383733 2448152829565223132473475)
                ·
                  refine ⟨3672229244347834698710213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2448152829565223132473475 3672229244347834698710213)
                  ·
                    refine ⟨688542983315219006008165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3672229244347834698710213 688542983315219006008165)
                    ·
                      rfl

theorem cell23_4022798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 5, 1, 4].length) (baseStart_4022798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4022798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4022798 prefixEnd_4022798 := by exact prefixLift 4022798
  have htrace : WordTrace (prefixWord ++ tailWord_4022798) baseStart_4022798 baseEnd_4022798 := by
    simpa [prefixWord, tailWord_4022798, baseEnd_4022798] using wordTrace_append hprefix tailTrace_4022798
  have hstable : (prefixWord ++ tailWord_4022798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4022798).length < 2 ^ (prefixWord ++ tailWord_4022798).sum := by decide
  have hdescent : baseEnd_4022798 < baseStart_4022798 := by decide
  rcases family_descends (prefixWord ++ tailWord_4022798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4022821 : List Nat := [1, 3, 1, 2, 2, 1, 3, 3, 3, 1, 3]
def baseStart_4022821 : Nat := 118140960795 + 4022821 * 2 ^ 59
def prefixEnd_4022821 : Nat := 4983230072969 + 3 ^ 40 * 4022821 * 2
def baseEnd_4022821 : Nat := 2065640760000710428036889

theorem tailTrace_4022821 : CollatzResearch.WordTrace tailWord_4022821 prefixEnd_4022821 2065640760000710428036889 := by
  unfold tailWord_4022821
  simp only [CollatzResearch.WordTrace]
  refine ⟨146724335759014034973612317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97816223839342689982408211 146724335759014034973612317)
  ·
    refine ⟨55021625909630263115104619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146724335759014034973612317 55021625909630263115104619)
    ·
      refine ⟨82532438864445394672656929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55021625909630263115104619 82532438864445394672656929)
      ·
        refine ⟨61899329148334046004492697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82532438864445394672656929 61899329148334046004492697)
        ·
          refine ⟨46424496861250534503369523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61899329148334046004492697 46424496861250534503369523)
          ·
            refine ⟨69636745291875801755054285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46424496861250534503369523 69636745291875801755054285)
            ·
              refine ⟨26113779484453425658145357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69636745291875801755054285 26113779484453425658145357)
              ·
                refine ⟨9792667306670034621804509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26113779484453425658145357 9792667306670034621804509)
                ·
                  refine ⟨3672250240001262983176691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9792667306670034621804509 3672250240001262983176691)
                  ·
                    refine ⟨5508375360001894474765037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3672250240001262983176691 5508375360001894474765037)
                    ·
                      refine ⟨2065640760000710428036889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5508375360001894474765037 2065640760000710428036889)
                      ·
                        rfl

theorem cell23_4022821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 3, 3, 1, 3].length) (baseStart_4022821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4022821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4022821 prefixEnd_4022821 := by exact prefixLift 4022821
  have htrace : WordTrace (prefixWord ++ tailWord_4022821) baseStart_4022821 baseEnd_4022821 := by
    simpa [prefixWord, tailWord_4022821, baseEnd_4022821] using wordTrace_append hprefix tailTrace_4022821
  have hstable : (prefixWord ++ tailWord_4022821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4022821).length < 2 ^ (prefixWord ++ tailWord_4022821).sum := by decide
  have hdescent : baseEnd_4022821 < baseStart_4022821 := by decide
  rcases family_descends (prefixWord ++ tailWord_4022821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4022841 : List Nat := [1, 2, 1, 5, 1, 1, 4, 2, 1, 5]
def baseStart_4022841 : Nat := 118140960795 + 4022841 * 2 ^ 59
def prefixEnd_4022841 : Nat := 4983230072969 + 3 ^ 40 * 4022841 * 2
def baseEnd_4022841 : Nat := 688550343204600116595599

theorem tailTrace_4022841 : CollatzResearch.WordTrace tailWord_4022841 prefixEnd_4022841 688550343204600116595599 := by
  unfold tailWord_4022841
  simp only [CollatzResearch.WordTrace]
  refine ⟨146725065218941578389340377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97816710145961052259560251 146725065218941578389340377)
  ·
    refine ⟨110043798914206183792005283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146725065218941578389340377 110043798914206183792005283)
    ·
      refine ⟨165065698371309275688007925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110043798914206183792005283 165065698371309275688007925)
      ·
        refine ⟨15474909222310244595750743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 165065698371309275688007925 15474909222310244595750743)
        ·
          refine ⟨23212363833465366893626115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15474909222310244595750743 23212363833465366893626115)
          ·
            refine ⟨34818545750198050340439173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23212363833465366893626115 34818545750198050340439173)
            ·
              refine ⟨6528477328162134438832345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34818545750198050340439173 6528477328162134438832345)
              ·
                refine ⟨4896357996121600829124259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6528477328162134438832345 4896357996121600829124259)
                ·
                  refine ⟨7344536994182401243686389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4896357996121600829124259 7344536994182401243686389)
                  ·
                    refine ⟨688550343204600116595599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7344536994182401243686389 688550343204600116595599)
                    ·
                      rfl

theorem cell23_4022841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 4, 2, 1, 5].length) (baseStart_4022841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4022841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4022841 prefixEnd_4022841 := by exact prefixLift 4022841
  have htrace : WordTrace (prefixWord ++ tailWord_4022841) baseStart_4022841 baseEnd_4022841 := by
    simpa [prefixWord, tailWord_4022841, baseEnd_4022841] using wordTrace_append hprefix tailTrace_4022841
  have hstable : (prefixWord ++ tailWord_4022841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4022841).length < 2 ^ (prefixWord ++ tailWord_4022841).sum := by decide
  have hdescent : baseEnd_4022841 < baseStart_4022841 := by decide
  rcases family_descends (prefixWord ++ tailWord_4022841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4022855 : List Nat := [1, 1, 4, 1, 4, 1, 3, 3, 1, 1, 3]
def baseStart_4022855 : Nat := 118140960795 + 4022855 * 2 ^ 59
def prefixEnd_4022855 : Nat := 4983230072969 + 3 ^ 40 * 4022855 * 2
def baseEnd_4022855 : Nat := 2065658218342963295011733

theorem tailTrace_4022855 : CollatzResearch.WordTrace tailWord_4022855 prefixEnd_4022855 2065658218342963295011733 := by
  unfold tailWord_4022855
  simp only [CollatzResearch.WordTrace]
  refine ⟨146725575840890858780350019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97817050560593905853566679 146725575840890858780350019)
  ·
    refine ⟨220088363761336288170525029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146725575840890858780350019 220088363761336288170525029)
    ·
      refine ⟨41266568205250554031973443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 220088363761336288170525029 41266568205250554031973443)
      ·
        refine ⟨61899852307875831047960165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41266568205250554031973443 61899852307875831047960165)
        ·
          refine ⟨11606222307726718321492531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61899852307875831047960165 11606222307726718321492531)
          ·
            refine ⟨17409333461590077482238797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11606222307726718321492531 17409333461590077482238797)
            ·
              refine ⟨6528500048096279055839549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17409333461590077482238797 6528500048096279055839549)
              ·
                refine ⟨2448187518036104645939831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6528500048096279055839549 2448187518036104645939831)
                ·
                  refine ⟨3672281277054156968909747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2448187518036104645939831 3672281277054156968909747)
                  ·
                    refine ⟨5508421915581235453364621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3672281277054156968909747 5508421915581235453364621)
                    ·
                      refine ⟨2065658218342963295011733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5508421915581235453364621 2065658218342963295011733)
                      ·
                        rfl

theorem cell23_4022855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 3, 3, 1, 1, 3].length) (baseStart_4022855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4022855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4022855 prefixEnd_4022855 := by exact prefixLift 4022855
  have htrace : WordTrace (prefixWord ++ tailWord_4022855) baseStart_4022855 baseEnd_4022855 := by
    simpa [prefixWord, tailWord_4022855, baseEnd_4022855] using wordTrace_append hprefix tailTrace_4022855
  have hstable : (prefixWord ++ tailWord_4022855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4022855).length < 2 ^ (prefixWord ++ tailWord_4022855).sum := by decide
  have hdescent : baseEnd_4022855 < baseStart_4022855 := by decide
  rcases family_descends (prefixWord ++ tailWord_4022855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4022871 : List Nat := [1, 1, 3, 2, 2, 2, 2, 4, 2, 4]
def baseStart_4022871 : Nat := 118140960795 + 4022871 * 2 ^ 59
def prefixEnd_4022871 : Nat := 4983230072969 + 3 ^ 40 * 4022871 * 2
def baseEnd_4022871 : Nat := 688555478011145077470553

theorem tailTrace_4022871 : CollatzResearch.WordTrace tailWord_4022871 prefixEnd_4022871 688555478011145077470553 := by
  unfold tailWord_4022871
  simp only [CollatzResearch.WordTrace]
  refine ⟨146726159408832893512932467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97817439605888595675288311 146726159408832893512932467)
  ·
    refine ⟨220089239113249340269398701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146726159408832893512932467 220089239113249340269398701)
    ·
      refine ⟨82533464667468502601024513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220089239113249340269398701 82533464667468502601024513)
      ·
        refine ⟨61900098500601376950768385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82533464667468502601024513 61900098500601376950768385)
        ·
          refine ⟨46425073875451032713076289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61900098500601376950768385 46425073875451032713076289)
          ·
            refine ⟨34818805406588274534807217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46425073875451032713076289 34818805406588274534807217)
            ·
              refine ⟨26114104054941205901105413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34818805406588274534807217 26114104054941205901105413)
              ·
                refine ⟨4896394510301476106457265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26114104054941205901105413 4896394510301476106457265)
                ·
                  refine ⟨3672295882726107079842949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4896394510301476106457265 3672295882726107079842949)
                  ·
                    refine ⟨688555478011145077470553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3672295882726107079842949 688555478011145077470553)
                    ·
                      rfl

theorem cell23_4022871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 4, 2, 4].length) (baseStart_4022871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4022871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4022871 prefixEnd_4022871 := by exact prefixLift 4022871
  have htrace : WordTrace (prefixWord ++ tailWord_4022871) baseStart_4022871 baseEnd_4022871 := by
    simpa [prefixWord, tailWord_4022871, baseEnd_4022871] using wordTrace_append hprefix tailTrace_4022871
  have hstable : (prefixWord ++ tailWord_4022871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4022871).length < 2 ^ (prefixWord ++ tailWord_4022871).sum := by decide
  have hdescent : baseEnd_4022871 < baseStart_4022871 := by decide
  rcases family_descends (prefixWord ++ tailWord_4022871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4022884 : List Nat := [2, 3, 1, 1, 2, 2, 4, 8]
def baseStart_4022884 : Nat := 118140960795 + 4022884 * 2 ^ 59
def prefixEnd_4022884 : Nat := 4983230072969 + 3 ^ 40 * 4022884 * 2
def baseEnd_4022884 : Nat := 76506411454886803020337

theorem tailTrace_4022884 : CollatzResearch.WordTrace tailWord_4022884 prefixEnd_4022884 76506411454886803020337 := by
  unfold tailWord_4022884
  simp only [CollatzResearch.WordTrace]
  refine ⟨73363316778892898366577853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97817755705190531155437137 73363316778892898366577853)
  ·
    refine ⟨27511243792084836887466695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73363316778892898366577853 27511243792084836887466695)
    ·
      refine ⟨41266865688127255331200043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27511243792084836887466695 41266865688127255331200043)
      ·
        refine ⟨61900298532190882996800065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41266865688127255331200043 61900298532190882996800065)
        ·
          refine ⟨46425223899143162247600049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61900298532190882996800065 46425223899143162247600049)
          ·
            refine ⟨34818917924357371685700037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46425223899143162247600049 34818917924357371685700037)
            ·
              refine ⟨6528547110817007191068757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34818917924357371685700037 6528547110817007191068757)
              ·
                refine ⟨76506411454886803020337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6528547110817007191068757 76506411454886803020337)
                ·
                  rfl

theorem cell23_4022884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 4, 8].length) (baseStart_4022884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4022884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4022884 prefixEnd_4022884 := by exact prefixLift 4022884
  have htrace : WordTrace (prefixWord ++ tailWord_4022884) baseStart_4022884 baseEnd_4022884 := by
    simpa [prefixWord, tailWord_4022884, baseEnd_4022884] using wordTrace_append hprefix tailTrace_4022884
  have hstable : (prefixWord ++ tailWord_4022884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4022884).length < 2 ^ (prefixWord ++ tailWord_4022884).sum := by decide
  have hdescent : baseEnd_4022884 < baseStart_4022884 := by decide
  rcases family_descends (prefixWord ++ tailWord_4022884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4022898 : List Nat := [3, 2, 1, 2, 4, 1, 1, 1, 3, 2, 3]
def baseStart_4022898 : Nat := 118140960795 + 4022898 * 2 ^ 59
def prefixEnd_4022898 : Nat := 4983230072969 + 3 ^ 40 * 4022898 * 2
def baseEnd_4022898 : Nat := 2065680298011106626774035

theorem tailTrace_4022898 : CollatzResearch.WordTrace tailWord_4022898 prefixEnd_4022898 2065680298011106626774035 := by
  unfold tailWord_4022898
  simp only [CollatzResearch.WordTrace]
  refine ⟨36681786044933769281041337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97818096119823384749443565 36681786044933769281041337)
  ·
    refine ⟨27511339533700326960781003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36681786044933769281041337 27511339533700326960781003)
    ·
      refine ⟨41267009300550490441171505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27511339533700326960781003 41267009300550490441171505)
      ·
        refine ⟨30950256975412867830878629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41267009300550490441171505 30950256975412867830878629)
        ·
          refine ⟨5803173182889912718289743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30950256975412867830878629 5803173182889912718289743)
          ·
            refine ⟨8704759774334869077434615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5803173182889912718289743 8704759774334869077434615)
            ·
              refine ⟨13057139661502303616151923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8704759774334869077434615 13057139661502303616151923)
              ·
                refine ⟨19585709492253455424227885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13057139661502303616151923 19585709492253455424227885)
                ·
                  refine ⟨7344641059595045784085457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19585709492253455424227885 7344641059595045784085457)
                  ·
                    refine ⟨5508480794696284338064093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7344641059595045784085457 5508480794696284338064093)
                    ·
                      refine ⟨2065680298011106626774035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5508480794696284338064093 2065680298011106626774035)
                      ·
                        rfl

theorem cell23_4022898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 1, 3, 2, 3].length) (baseStart_4022898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4022898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4022898 prefixEnd_4022898 := by exact prefixLift 4022898
  have htrace : WordTrace (prefixWord ++ tailWord_4022898) baseStart_4022898 baseEnd_4022898 := by
    simpa [prefixWord, tailWord_4022898, baseEnd_4022898] using wordTrace_append hprefix tailTrace_4022898
  have hstable : (prefixWord ++ tailWord_4022898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4022898).length < 2 ^ (prefixWord ++ tailWord_4022898).sum := by decide
  have hdescent : baseEnd_4022898 < baseStart_4022898 := by decide
  rcases family_descends (prefixWord ++ tailWord_4022898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4022911 : List Nat := [1, 1, 2, 2, 1, 1, 1, 6, 4, 1, 3]
def baseStart_4022911 : Nat := 118140960795 + 4022911 * 2 ^ 59
def prefixEnd_4022911 : Nat := 4983230072969 + 3 ^ 40 * 4022911 * 2
def baseEnd_4022911 : Nat := 2065686973259615075911475

theorem tailTrace_4022911 : CollatzResearch.WordTrace tailWord_4022911 prefixEnd_4022911 2065686973259615075911475 := by
  unfold tailWord_4022911
  simp only [CollatzResearch.WordTrace]
  refine ⟨146727618328687980344388587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97818412219125320229592391 146727618328687980344388587)
  ·
    refine ⟨220091427493031970516582881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146727618328687980344388587 220091427493031970516582881)
    ·
      refine ⟨165068570619773977887437161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220091427493031970516582881 165068570619773977887437161)
      ·
        refine ⟨123801427964830483415577871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165068570619773977887437161 123801427964830483415577871)
        ·
          refine ⟨185702141947245725123366807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123801427964830483415577871 185702141947245725123366807)
          ·
            refine ⟨278553212920868587685050211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185702141947245725123366807 278553212920868587685050211)
            ·
              refine ⟨417829819381302881527575317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 278553212920868587685050211 417829819381302881527575317)
              ·
                refine ⟨19585772783498572571605093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 417829819381302881527575317 19585772783498572571605093)
                ·
                  refine ⟨3672332396905982357175955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19585772783498572571605093 3672332396905982357175955)
                  ·
                    refine ⟨5508498595358973535763933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3672332396905982357175955 5508498595358973535763933)
                    ·
                      refine ⟨2065686973259615075911475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5508498595358973535763933 2065686973259615075911475)
                      ·
                        rfl

theorem cell23_4022911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 6, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 6, 4, 1, 3].length) (baseStart_4022911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4022911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4022911 prefixEnd_4022911 := by exact prefixLift 4022911
  have htrace : WordTrace (prefixWord ++ tailWord_4022911) baseStart_4022911 baseEnd_4022911 := by
    simpa [prefixWord, tailWord_4022911, baseEnd_4022911] using wordTrace_append hprefix tailTrace_4022911
  have hstable : (prefixWord ++ tailWord_4022911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4022911).length < 2 ^ (prefixWord ++ tailWord_4022911).sum := by decide
  have hdescent : baseEnd_4022911 < baseStart_4022911 := by decide
  rcases family_descends (prefixWord ++ tailWord_4022911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4022966 : List Nat := [5, 1, 3, 1, 3, 1, 2, 1, 1, 2, 3]
def baseStart_4022966 : Nat := 118140960795 + 4022966 * 2 ^ 59
def prefixEnd_4022966 : Nat := 4983230072969 + 3 ^ 40 * 4022966 * 2
def baseEnd_4022966 : Nat := 2065715214695612360723723

theorem tailTrace_4022966 : CollatzResearch.WordTrace tailWord_4022966 prefixEnd_4022966 2065715214695612360723723 := by
  unfold tailWord_4022966
  simp only [CollatzResearch.WordTrace]
  refine ⟨9170601521468045296102547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 97819749562325816491760501 9170601521468045296102547)
  ·
    refine ⟨13755902282202067944153821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9170601521468045296102547 13755902282202067944153821)
    ·
      refine ⟨5158463355825775479057683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13755902282202067944153821 5158463355825775479057683)
      ·
        refine ⟨7737695033738663218586525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5158463355825775479057683 7737695033738663218586525)
        ·
          refine ⟨2901635637651998706969947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7737695033738663218586525 2901635637651998706969947)
          ·
            refine ⟨4352453456477998060454921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2901635637651998706969947 4352453456477998060454921)
            ·
              refine ⟨3264340092358498545341191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4352453456477998060454921 3264340092358498545341191)
              ·
                refine ⟨4896510138537747818011787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3264340092358498545341191 4896510138537747818011787)
                ·
                  refine ⟨7344765207806621727017681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4896510138537747818011787 7344765207806621727017681)
                  ·
                    refine ⟨5508573905854966295263261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7344765207806621727017681 5508573905854966295263261)
                    ·
                      refine ⟨2065715214695612360723723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5508573905854966295263261 2065715214695612360723723)
                      ·
                        rfl

theorem cell23_4022966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 2, 1, 1, 2, 3].length) (baseStart_4022966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4022966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4022966 prefixEnd_4022966 := by exact prefixLift 4022966
  have htrace : WordTrace (prefixWord ++ tailWord_4022966) baseStart_4022966 baseEnd_4022966 := by
    simpa [prefixWord, tailWord_4022966, baseEnd_4022966] using wordTrace_append hprefix tailTrace_4022966
  have hstable : (prefixWord ++ tailWord_4022966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4022966).length < 2 ^ (prefixWord ++ tailWord_4022966).sum := by decide
  have hdescent : baseEnd_4022966 < baseStart_4022966 := by decide
  rcases family_descends (prefixWord ++ tailWord_4022966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4023001 : List Nat := [1, 2, 1, 2, 3, 2, 1, 3, 2, 3, 3]
def baseStart_4023001 : Nat := 118140960795 + 4023001 * 2 ^ 59
def prefixEnd_4023001 : Nat := 4983230072969 + 3 ^ 40 * 4023001 * 2
def baseEnd_4023001 : Nat := 2065733186518519723786061

theorem tailTrace_4023001 : CollatzResearch.WordTrace tailWord_4023001 prefixEnd_4023001 2065733186518519723786061 := by
  unfold tailWord_4023001
  simp only [CollatzResearch.WordTrace]
  refine ⟨146730900898361925715164857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97820600598907950476776571 146730900898361925715164857)
  ·
    refine ⟨110048175673771444286373643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146730900898361925715164857 110048175673771444286373643)
    ·
      refine ⟨165072263510657166429560465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110048175673771444286373643 165072263510657166429560465)
      ·
        refine ⟨123804197632992874822170349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165072263510657166429560465 123804197632992874822170349)
        ·
          refine ⟨46426574112372328058313881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123804197632992874822170349 46426574112372328058313881)
          ·
            refine ⟨34819930584279246043735411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46426574112372328058313881 34819930584279246043735411)
            ·
              refine ⟨52229895876418869065603117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34819930584279246043735411 52229895876418869065603117)
              ·
                refine ⟨19586210953657075899601169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52229895876418869065603117 19586210953657075899601169)
                ·
                  refine ⟨14689658215242806924700877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19586210953657075899601169 14689658215242806924700877)
                  ·
                    refine ⟨5508621830716052596762829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14689658215242806924700877 5508621830716052596762829)
                    ·
                      refine ⟨2065733186518519723786061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5508621830716052596762829 2065733186518519723786061)
                      ·
                        rfl

theorem cell23_4023001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 3, 2, 3, 3].length) (baseStart_4023001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4023001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4023001 prefixEnd_4023001 := by exact prefixLift 4023001
  have htrace : WordTrace (prefixWord ++ tailWord_4023001) baseStart_4023001 baseEnd_4023001 := by
    simpa [prefixWord, tailWord_4023001, baseEnd_4023001] using wordTrace_append hprefix tailTrace_4023001
  have hstable : (prefixWord ++ tailWord_4023001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4023001).length < 2 ^ (prefixWord ++ tailWord_4023001).sum := by decide
  have hdescent : baseEnd_4023001 < baseStart_4023001 := by decide
  rcases family_descends (prefixWord ++ tailWord_4023001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4023002 : List Nat := [3, 1, 1, 2, 2, 2, 5, 1, 2, 2, 2]
def baseStart_4023002 : Nat := 118140960795 + 4023002 * 2 ^ 59
def prefixEnd_4023002 : Nat := 4983230072969 + 3 ^ 40 * 4023002 * 2
def baseEnd_4023002 : Nat := 2065733699999174219873557

theorem tailTrace_4023002 : CollatzResearch.WordTrace tailWord_4023002 prefixEnd_4023002 2065733699999174219873557 := by
  unfold tailWord_4023002
  simp only [CollatzResearch.WordTrace]
  refine ⟨36682734342839575721487815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97820624914238868590634173 36682734342839575721487815)
  ·
    refine ⟨55024101514259363582231723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36682734342839575721487815 55024101514259363582231723)
    ·
      refine ⟨82536152271389045373347585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55024101514259363582231723 82536152271389045373347585)
      ·
        refine ⟨61902114203541784030010689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82536152271389045373347585 61902114203541784030010689)
        ·
          refine ⟨46426585652656338022508017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61902114203541784030010689 46426585652656338022508017)
          ·
            refine ⟨34819939239492253516881013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46426585652656338022508017 34819939239492253516881013)
            ·
              refine ⟨3264369303702398767207595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34819939239492253516881013 3264369303702398767207595)
              ·
                refine ⟨4896553955553598150811393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3264369303702398767207595 4896553955553598150811393)
                ·
                  refine ⟨3672415466665198613108545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4896553955553598150811393 3672415466665198613108545)
                  ·
                    refine ⟨2754311599998898959831409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3672415466665198613108545 2754311599998898959831409)
                    ·
                      refine ⟨2065733699999174219873557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2754311599998898959831409 2065733699999174219873557)
                      ·
                        rfl

theorem cell23_4023002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 5, 1, 2, 2, 2].length) (baseStart_4023002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4023002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4023002 prefixEnd_4023002 := by exact prefixLift 4023002
  have htrace : WordTrace (prefixWord ++ tailWord_4023002) baseStart_4023002 baseEnd_4023002 := by
    simpa [prefixWord, tailWord_4023002, baseEnd_4023002] using wordTrace_append hprefix tailTrace_4023002
  have hstable : (prefixWord ++ tailWord_4023002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4023002).length < 2 ^ (prefixWord ++ tailWord_4023002).sum := by decide
  have hdescent : baseEnd_4023002 < baseStart_4023002 := by decide
  rcases family_descends (prefixWord ++ tailWord_4023002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4023021 : List Nat := [1, 5, 1, 2, 1, 1, 1, 3, 1, 7]
def baseStart_4023021 : Nat := 118140960795 + 4023021 * 2 ^ 59
def prefixEnd_4023021 : Nat := 4983230072969 + 3 ^ 40 * 4023021 * 2
def baseEnd_4023021 : Nat := 688581152043869881845323

theorem tailTrace_4023021 : CollatzResearch.WordTrace tailWord_4023021 prefixEnd_4023021 688581152043869881845323 := by
  unfold tailWord_4023021
  simp only [CollatzResearch.WordTrace]
  refine ⟨146731630358289469130892917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97821086905526312753928611 146731630358289469130892917)
  ·
    refine ⟨13756090346089637731021211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 146731630358289469130892917 13756090346089637731021211)
    ·
      refine ⟨20634135519134456596531817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13756090346089637731021211 20634135519134456596531817)
      ·
        refine ⟨15475601639350842447398863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20634135519134456596531817 15475601639350842447398863)
        ·
          refine ⟨23213402459026263671098295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15475601639350842447398863 23213402459026263671098295)
          ·
            refine ⟨34820103688539395506647443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23213402459026263671098295 34820103688539395506647443)
            ·
              refine ⟨52230155532809093259971165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34820103688539395506647443 52230155532809093259971165)
              ·
                refine ⟨19586308324803409972489187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52230155532809093259971165 19586308324803409972489187)
                ·
                  refine ⟨29379462487205114958733781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19586308324803409972489187 29379462487205114958733781)
                  ·
                    refine ⟨688581152043869881845323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29379462487205114958733781 688581152043869881845323)
                    ·
                      rfl

theorem cell23_4023021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 3, 1, 7].length) (baseStart_4023021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4023021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4023021 prefixEnd_4023021 := by exact prefixLift 4023021
  have htrace : WordTrace (prefixWord ++ tailWord_4023021) baseStart_4023021 baseEnd_4023021 := by
    simpa [prefixWord, tailWord_4023021, baseEnd_4023021] using wordTrace_append hprefix tailTrace_4023021
  have hstable : (prefixWord ++ tailWord_4023021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4023021).length < 2 ^ (prefixWord ++ tailWord_4023021).sum := by decide
  have hdescent : baseEnd_4023021 < baseStart_4023021 := by decide
  rcases family_descends (prefixWord ++ tailWord_4023021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4023038 : List Nat := [4, 2, 2, 1, 2, 1, 1, 1, 4, 5]
def baseStart_4023038 : Nat := 118140960795 + 4023038 * 2 ^ 59
def prefixEnd_4023038 : Nat := 4983230072969 + 3 ^ 40 * 4023038 * 2
def baseEnd_4023038 : Nat := 688584061767578693007797

theorem tailTrace_4023038 : CollatzResearch.WordTrace tailWord_4023038 prefixEnd_4023038 688584061767578693007797 := by
  unfold tailWord_4023038
  simp only [CollatzResearch.WordTrace]
  refine ⟨18341531299903485129282721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97821500266151920689507845 18341531299903485129282721)
  ·
    refine ⟨13756148474927613846962041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18341531299903485129282721 13756148474927613846962041)
    ·
      refine ⟨10317111356195710385221531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13756148474927613846962041 10317111356195710385221531)
      ·
        refine ⟨15475667034293565577832297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10317111356195710385221531 15475667034293565577832297)
        ·
          refine ⟨11606750275720174183374223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15475667034293565577832297 11606750275720174183374223)
          ·
            refine ⟨17410125413580261275061335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11606750275720174183374223 17410125413580261275061335)
            ·
              refine ⟨26115188120370391912592003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17410125413580261275061335 26115188120370391912592003)
              ·
                refine ⟨39172782180555587868888005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26115188120370391912592003 39172782180555587868888005)
                ·
                  refine ⟨7344896658854172725416501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39172782180555587868888005 7344896658854172725416501)
                  ·
                    refine ⟨688584061767578693007797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7344896658854172725416501 688584061767578693007797)
                    ·
                      rfl

theorem cell23_4023038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 1, 4, 5].length) (baseStart_4023038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4023038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4023038 prefixEnd_4023038 := by exact prefixLift 4023038
  have htrace : WordTrace (prefixWord ++ tailWord_4023038) baseStart_4023038 baseEnd_4023038 := by
    simpa [prefixWord, tailWord_4023038, baseEnd_4023038] using wordTrace_append hprefix tailTrace_4023038
  have hstable : (prefixWord ++ tailWord_4023038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4023038).length < 2 ^ (prefixWord ++ tailWord_4023038).sum := by decide
  have hdescent : baseEnd_4023038 < baseStart_4023038 := by decide
  rcases family_descends (prefixWord ++ tailWord_4023038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4023042 : List Nat := [3, 4, 1, 1, 1, 3, 3, 2, 5]
def baseStart_4023042 : Nat := 118140960795 + 4023042 * 2 ^ 59
def prefixEnd_4023042 : Nat := 4983230072969 + 3 ^ 40 * 4023042 * 2
def baseEnd_4023042 : Nat := 229528248802817118152597

theorem tailTrace_4023042 : CollatzResearch.WordTrace tailWord_4023042 prefixEnd_4023042 229528248802817118152597 := by
  unfold tailWord_4023042
  simp only [CollatzResearch.WordTrace]
  refine ⟨36683099072803347429351845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97821597527475593144938253 36683099072803347429351845)
  ·
    refine ⟨6878081076150627643003471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36683099072803347429351845 6878081076150627643003471)
    ·
      refine ⟨10317121614225941464505207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6878081076150627643003471 10317121614225941464505207)
      ·
        refine ⟨15475682421338912196757811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10317121614225941464505207 15475682421338912196757811)
        ·
          refine ⟨23213523632008368295136717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15475682421338912196757811 23213523632008368295136717)
          ·
            refine ⟨8705071362003138110676269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23213523632008368295136717 8705071362003138110676269)
            ·
              refine ⟨3264401760751176791503601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8705071362003138110676269 3264401760751176791503601)
              ·
                refine ⟨2448301320563382593627701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3264401760751176791503601 2448301320563382593627701)
                ·
                  refine ⟨229528248802817118152597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2448301320563382593627701 229528248802817118152597)
                  ·
                    rfl

theorem cell23_4023042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 3, 2, 5].length) (baseStart_4023042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4023042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4023042 prefixEnd_4023042 := by exact prefixLift 4023042
  have htrace : WordTrace (prefixWord ++ tailWord_4023042) baseStart_4023042 baseEnd_4023042 := by
    simpa [prefixWord, tailWord_4023042, baseEnd_4023042] using wordTrace_append hprefix tailTrace_4023042
  have hstable : (prefixWord ++ tailWord_4023042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4023042).length < 2 ^ (prefixWord ++ tailWord_4023042).sum := by decide
  have hdescent : baseEnd_4023042 < baseStart_4023042 := by decide
  rcases family_descends (prefixWord ++ tailWord_4023042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4023125 : List Nat := [1, 3, 2, 2, 2, 1, 3, 2, 3, 1, 3]
def baseStart_4023125 : Nat := 118140960795 + 4023125 * 2 ^ 59
def prefixEnd_4023125 : Nat := 4983230072969 + 3 ^ 40 * 4023125 * 2
def baseEnd_4023125 : Nat := 2065796858119677238635491

theorem tailTrace_4023125 : CollatzResearch.WordTrace tailWord_4023125 prefixEnd_4023125 2065796858119677238635491 := by
  unfold tailWord_4023125
  simp only [CollatzResearch.WordTrace]
  refine ⟨146735423549912694892678829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97823615699941796595119219 146735423549912694892678829)
  ·
    refine ⟨55025783831217260584754561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146735423549912694892678829 55025783831217260584754561)
    ·
      refine ⟨41269337873412945438565921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55025783831217260584754561 41269337873412945438565921)
      ·
        refine ⟨30952003405059709078924441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41269337873412945438565921 30952003405059709078924441)
        ·
          refine ⟨23214002553794781809193331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30952003405059709078924441 23214002553794781809193331)
          ·
            refine ⟨34821003830692172713789997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23214002553794781809193331 34821003830692172713789997)
            ·
              refine ⟨13057876436509564767671249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34821003830692172713789997 13057876436509564767671249)
              ·
                refine ⟨9793407327382173575753437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13057876436509564767671249 9793407327382173575753437)
                ·
                  refine ⟨3672527747768315090907539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9793407327382173575753437 3672527747768315090907539)
                  ·
                    refine ⟨5508791621652472636361309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3672527747768315090907539 5508791621652472636361309)
                    ·
                      refine ⟨2065796858119677238635491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5508791621652472636361309 2065796858119677238635491)
                      ·
                        rfl

theorem cell23_4023125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 2, 3, 1, 3].length) (baseStart_4023125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4023125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4023125 prefixEnd_4023125 := by exact prefixLift 4023125
  have htrace : WordTrace (prefixWord ++ tailWord_4023125) baseStart_4023125 baseEnd_4023125 := by
    simpa [prefixWord, tailWord_4023125, baseEnd_4023125] using wordTrace_append hprefix tailTrace_4023125
  have hstable : (prefixWord ++ tailWord_4023125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4023125).length < 2 ^ (prefixWord ++ tailWord_4023125).sum := by decide
  have hdescent : baseEnd_4023125 < baseStart_4023125 := by decide
  rcases family_descends (prefixWord ++ tailWord_4023125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4023151 : List Nat := [1, 1, 2, 1, 3, 1, 1, 2, 5, 1, 5]
def baseStart_4023151 : Nat := 118140960795 + 4023151 * 2 ^ 59
def prefixEnd_4023151 : Nat := 4983230072969 + 3 ^ 40 * 4023151 * 2
def baseEnd_4023151 : Nat := 2065810208616694136910371

theorem tailTrace_4023151 : CollatzResearch.WordTrace tailWord_4023151 prefixEnd_4023151 2065810208616694136910371 := by
  unfold tailWord_4023151
  simp only [CollatzResearch.WordTrace]
  refine ⟨146736371847818501333125307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97824247898545667555416871 146736371847818501333125307)
  ·
    refine ⟨220104557771727751999687961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146736371847818501333125307 220104557771727751999687961)
    ·
      refine ⟨165078418328795813999765971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220104557771727751999687961 165078418328795813999765971)
      ·
        refine ⟨247617627493193720999648957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165078418328795813999765971 247617627493193720999648957)
        ·
          refine ⟨92856610309947645374868359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 247617627493193720999648957 92856610309947645374868359)
          ·
            refine ⟨139284915464921468062302539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92856610309947645374868359 139284915464921468062302539)
            ·
              refine ⟨208927373197382202093453809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139284915464921468062302539 208927373197382202093453809)
              ·
                refine ⟨156695529898036651570090357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 208927373197382202093453809 156695529898036651570090357)
                ·
                  refine ⟨14690205927940936084695971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 156695529898036651570090357 14690205927940936084695971)
                  ·
                    refine ⟨22035308891911404127043957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14690205927940936084695971 22035308891911404127043957)
                    ·
                      refine ⟨2065810208616694136910371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22035308891911404127043957 2065810208616694136910371)
                      ·
                        rfl

theorem cell23_4023151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 5, 1, 5].length) (baseStart_4023151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4023151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4023151 prefixEnd_4023151 := by exact prefixLift 4023151
  have htrace : WordTrace (prefixWord ++ tailWord_4023151) baseStart_4023151 baseEnd_4023151 := by
    simpa [prefixWord, tailWord_4023151, baseEnd_4023151] using wordTrace_append hprefix tailTrace_4023151
  have hstable : (prefixWord ++ tailWord_4023151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4023151).length < 2 ^ (prefixWord ++ tailWord_4023151).sum := by decide
  have hdescent : baseEnd_4023151 < baseStart_4023151 := by decide
  rcases family_descends (prefixWord ++ tailWord_4023151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4023168 : List Nat := [2, 1, 1, 2, 1, 2, 2, 4, 3, 2, 3]
def baseStart_4023168 : Nat := 118140960795 + 4023168 * 2 ^ 59
def prefixEnd_4023168 : Nat := 4983230072969 + 3 ^ 40 * 4023168 * 2
def baseEnd_4023168 : Nat := 2065818937787820570397793

theorem tailTrace_4023168 : CollatzResearch.WordTrace tailWord_4023168 prefixEnd_4023168 2065818937787820570397793 := by
  unfold tailWord_4023168
  simp only [CollatzResearch.WordTrace]
  refine ⟨73368495944378456618247079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97824661259171275490996105 73368495944378456618247079)
  ·
    refine ⟨110052743916567684927370619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73368495944378456618247079 110052743916567684927370619)
    ·
      refine ⟨165079115874851527391055929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110052743916567684927370619 165079115874851527391055929)
      ·
        refine ⟨123809336906138645543291947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165079115874851527391055929 123809336906138645543291947)
        ·
          refine ⟨185714005359207968314937921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123809336906138645543291947 185714005359207968314937921)
          ·
            refine ⟨139285504019405976236203441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185714005359207968314937921 139285504019405976236203441)
            ·
              refine ⟨104464128014554482177152581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139285504019405976236203441 104464128014554482177152581)
              ·
                refine ⟨19587024002728965408216109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104464128014554482177152581 19587024002728965408216109)
                ·
                  refine ⟨7345134001023362028081041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19587024002728965408216109 7345134001023362028081041)
                  ·
                    refine ⟨5508850500767521521060781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7345134001023362028081041 5508850500767521521060781)
                    ·
                      refine ⟨2065818937787820570397793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5508850500767521521060781 2065818937787820570397793)
                      ·
                        rfl

theorem cell23_4023168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 4, 3, 2, 3].length) (baseStart_4023168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4023168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4023168 prefixEnd_4023168 := by exact prefixLift 4023168
  have htrace : WordTrace (prefixWord ++ tailWord_4023168) baseStart_4023168 baseEnd_4023168 := by
    simpa [prefixWord, tailWord_4023168, baseEnd_4023168] using wordTrace_append hprefix tailTrace_4023168
  have hstable : (prefixWord ++ tailWord_4023168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4023168).length < 2 ^ (prefixWord ++ tailWord_4023168).sum := by decide
  have hdescent : baseEnd_4023168 < baseStart_4023168 := by decide
  rcases family_descends (prefixWord ++ tailWord_4023168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4023171 : List Nat := [1, 1, 1, 3, 4, 1, 2, 10]
def baseStart_4023171 : Nat := 118140960795 + 4023171 * 2 ^ 59
def prefixEnd_4023171 : Nat := 4983230072969 + 3 ^ 40 * 4023171 * 2
def baseEnd_4023171 : Nat := 76511869564066076246677

theorem tailTrace_4023171 : CollatzResearch.WordTrace tailWord_4023171 prefixEnd_4023171 76511869564066076246677 := by
  unfold tailWord_4023171
  simp only [CollatzResearch.WordTrace]
  refine ⟨146737101307746044748853367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97824734205164029832568911 146737101307746044748853367)
  ·
    refine ⟨220105651961619067123280051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146737101307746044748853367 220105651961619067123280051)
    ·
      refine ⟨330158477942428600684920077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220105651961619067123280051 330158477942428600684920077)
      ·
        refine ⟨123809429228410725256845029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 330158477942428600684920077 123809429228410725256845029)
        ·
          refine ⟨23214267980327010985658443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 123809429228410725256845029 23214267980327010985658443)
          ·
            refine ⟨34821401970490516478487665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23214267980327010985658443 34821401970490516478487665)
            ·
              refine ⟨26116051477867887358865749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34821401970490516478487665 26116051477867887358865749)
              ·
                refine ⟨76511869564066076246677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 26116051477867887358865749 76511869564066076246677)
                ·
                  rfl

theorem cell23_4023171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 10].length) (baseStart_4023171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4023171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4023171 prefixEnd_4023171 := by exact prefixLift 4023171
  have htrace : WordTrace (prefixWord ++ tailWord_4023171) baseStart_4023171 baseEnd_4023171 := by
    simpa [prefixWord, tailWord_4023171, baseEnd_4023171] using wordTrace_append hprefix tailTrace_4023171
  have hstable : (prefixWord ++ tailWord_4023171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4023171).length < 2 ^ (prefixWord ++ tailWord_4023171).sum := by decide
  have hdescent : baseEnd_4023171 < baseStart_4023171 := by decide
  rcases family_descends (prefixWord ++ tailWord_4023171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4023175 : List Nat := [1, 1, 4, 2, 3, 3, 1, 1, 1, 6]
def baseStart_4023175 : Nat := 118140960795 + 4023175 * 2 ^ 59
def prefixEnd_4023175 : Nat := 4983230072969 + 3 ^ 40 * 4023175 * 2
def baseEnd_4023175 : Nat := 688607510717467347670087

theorem tailTrace_4023175 : CollatzResearch.WordTrace tailWord_4023175 prefixEnd_4023175 688607510717467347670087 := by
  unfold tailWord_4023175
  simp only [CollatzResearch.WordTrace]
  refine ⟨146737247199731553431998979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97824831466487702287999319 146737247199731553431998979)
  ·
    refine ⟨220105870799597330147998469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146737247199731553431998979 220105870799597330147998469)
    ·
      refine ⟨41269850774924499402749713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 220105870799597330147998469 41269850774924499402749713)
      ·
        refine ⟨30952388081193374552062285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41269850774924499402749713 30952388081193374552062285)
        ·
          refine ⟨11607145530447515457023357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30952388081193374552062285 11607145530447515457023357)
          ·
            refine ⟨4352679573917818296383759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11607145530447515457023357 4352679573917818296383759)
            ·
              refine ⟨6529019360876727444575639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4352679573917818296383759 6529019360876727444575639)
              ·
                refine ⟨9793529041315091166863459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6529019360876727444575639 9793529041315091166863459)
                ·
                  refine ⟨14690293561972636750295189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9793529041315091166863459 14690293561972636750295189)
                  ·
                    refine ⟨688607510717467347670087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14690293561972636750295189 688607510717467347670087)
                    ·
                      rfl

theorem cell23_4023175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 1, 1, 1, 6].length) (baseStart_4023175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4023175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4023175 prefixEnd_4023175 := by exact prefixLift 4023175
  have htrace : WordTrace (prefixWord ++ tailWord_4023175) baseStart_4023175 baseEnd_4023175 := by
    simpa [prefixWord, tailWord_4023175, baseEnd_4023175] using wordTrace_append hprefix tailTrace_4023175
  have hstable : (prefixWord ++ tailWord_4023175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4023175).length < 2 ^ (prefixWord ++ tailWord_4023175).sum := by decide
  have hdescent : baseEnd_4023175 < baseStart_4023175 := by decide
  rcases family_descends (prefixWord ++ tailWord_4023175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4023188 : List Nat := [2, 4, 2, 1, 1, 1, 3, 9]
def baseStart_4023188 : Nat := 118140960795 + 4023188 * 2 ^ 59
def prefixEnd_4023188 : Nat := 4983230072969 + 3 ^ 40 * 4023188 * 2
def baseEnd_4023188 : Nat := 76512192866700388598063

theorem tailTrace_4023188 : CollatzResearch.WordTrace tailWord_4023188 prefixEnd_4023188 76512192866700388598063 := by
  unfold tailWord_4023188
  simp only [CollatzResearch.WordTrace]
  refine ⟨73368860674342228326111109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97825147565789637768148145 73368860674342228326111109)
  ·
    refine ⟨13756661376439167811145833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73368860674342228326111109 13756661376439167811145833)
    ·
      refine ⟨10317496032329375858359375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13756661376439167811145833 10317496032329375858359375)
      ·
        refine ⟨15476244048494063787539063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10317496032329375858359375 15476244048494063787539063)
        ·
          refine ⟨23214366072741095681308595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15476244048494063787539063 23214366072741095681308595)
          ·
            refine ⟨34821549109111643521962893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23214366072741095681308595 34821549109111643521962893)
            ·
              refine ⟨13058080915916866320736085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34821549109111643521962893 13058080915916866320736085)
              ·
                refine ⟨76512192866700388598063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13058080915916866320736085 76512192866700388598063)
                ·
                  rfl

theorem cell23_4023188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 9].length) (baseStart_4023188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4023188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4023188 prefixEnd_4023188 := by exact prefixLift 4023188
  have htrace : WordTrace (prefixWord ++ tailWord_4023188) baseStart_4023188 baseEnd_4023188 := by
    simpa [prefixWord, tailWord_4023188, baseEnd_4023188] using wordTrace_append hprefix tailTrace_4023188
  have hstable : (prefixWord ++ tailWord_4023188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4023188).length < 2 ^ (prefixWord ++ tailWord_4023188).sum := by decide
  have hdescent : baseEnd_4023188 < baseStart_4023188 := by decide
  rcases family_descends (prefixWord ++ tailWord_4023188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4023202 : List Nat := [3, 3, 1, 2, 2, 1, 2, 3, 1, 2, 3]
def baseStart_4023202 : Nat := 118140960795 + 4023202 * 2 ^ 59
def prefixEnd_4023202 : Nat := 4983230072969 + 3 ^ 40 * 4023202 * 2
def baseEnd_4023202 : Nat := 2065836396130073437372637

theorem tailTrace_4023202 : CollatzResearch.WordTrace tailWord_4023202 prefixEnd_4023202 2065836396130073437372637 := by
  unfold tailWord_4023202
  simp only [CollatzResearch.WordTrace]
  refine ⟨36684557992658434260807965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97825487980422491362154573 36684557992658434260807965)
  ·
    refine ⟨13756709247246912847802987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36684557992658434260807965 13756709247246912847802987)
    ·
      refine ⟨20635063870870369271704481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13756709247246912847802987 20635063870870369271704481)
      ·
        refine ⟨15476297903152776953778361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20635063870870369271704481 15476297903152776953778361)
        ·
          refine ⟨11607223427364582715333771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15476297903152776953778361 11607223427364582715333771)
          ·
            refine ⟨17410835141046874073000657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11607223427364582715333771 17410835141046874073000657)
            ·
              refine ⟨13058126355785155554750493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17410835141046874073000657 13058126355785155554750493)
              ·
                refine ⟨4896797383419433333031435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13058126355785155554750493 4896797383419433333031435)
                ·
                  refine ⟨7345196075129149999547153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4896797383419433333031435 7345196075129149999547153)
                  ·
                    refine ⟨5508897056346862499660365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7345196075129149999547153 5508897056346862499660365)
                    ·
                      refine ⟨2065836396130073437372637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5508897056346862499660365 2065836396130073437372637)
                      ·
                        rfl

theorem cell23_4023202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 3, 1, 2, 3].length) (baseStart_4023202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4023202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4023202 prefixEnd_4023202 := by exact prefixLift 4023202
  have htrace : WordTrace (prefixWord ++ tailWord_4023202) baseStart_4023202 baseEnd_4023202 := by
    simpa [prefixWord, tailWord_4023202, baseEnd_4023202] using wordTrace_append hprefix tailTrace_4023202
  have hstable : (prefixWord ++ tailWord_4023202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4023202).length < 2 ^ (prefixWord ++ tailWord_4023202).sum := by decide
  have hdescent : baseEnd_4023202 < baseStart_4023202 := by decide
  rcases family_descends (prefixWord ++ tailWord_4023202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4023232 : List Nat := [2, 1, 1, 2, 3, 4, 1, 3, 2, 1, 3]
def baseStart_4023232 : Nat := 118140960795 + 4023232 * 2 ^ 59
def prefixEnd_4023232 : Nat := 4983230072969 + 3 ^ 40 * 4023232 * 2
def baseEnd_4023232 : Nat := 2065851800549708319997499

theorem tailTrace_4023232 : CollatzResearch.WordTrace tailWord_4023232 prefixEnd_4023232 2065851800549708319997499 := by
  unfold tailWord_4023232
  simp only [CollatzResearch.WordTrace]
  refine ⟨73369663080262526083411975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97826217440350034777882633 73369663080262526083411975)
  ·
    refine ⟨110054494620393789125117963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73369663080262526083411975 110054494620393789125117963)
    ·
      refine ⟨165081741930590683687676945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110054494620393789125117963 165081741930590683687676945)
      ·
        refine ⟨123811306447943012765757709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165081741930590683687676945 123811306447943012765757709)
        ·
          refine ⟨46429239917978629787159141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123811306447943012765757709 46429239917978629787159141)
          ·
            refine ⟨8705482484620993085092339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46429239917978629787159141 8705482484620993085092339)
            ·
              refine ⟨13058223726931489627638509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8705482484620993085092339 13058223726931489627638509)
              ·
                refine ⟨4896833897599308610364441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13058223726931489627638509 4896833897599308610364441)
                ·
                  refine ⟨3672625423199481457773331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4896833897599308610364441 3672625423199481457773331)
                  ·
                    refine ⟨5508938134799222186659997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3672625423199481457773331 5508938134799222186659997)
                    ·
                      refine ⟨2065851800549708319997499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5508938134799222186659997 2065851800549708319997499)
                      ·
                        rfl

theorem cell23_4023232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 3, 2, 1, 3].length) (baseStart_4023232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4023232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4023232 prefixEnd_4023232 := by exact prefixLift 4023232
  have htrace : WordTrace (prefixWord ++ tailWord_4023232) baseStart_4023232 baseEnd_4023232 := by
    simpa [prefixWord, tailWord_4023232, baseEnd_4023232] using wordTrace_append hprefix tailTrace_4023232
  have hstable : (prefixWord ++ tailWord_4023232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4023232).length < 2 ^ (prefixWord ++ tailWord_4023232).sum := by decide
  have hdescent : baseEnd_4023232 < baseStart_4023232 := by decide
  rcases family_descends (prefixWord ++ tailWord_4023232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4023236 : List Nat := [2, 3, 3, 3, 1, 2, 1, 2, 1, 2, 3]
def baseStart_4023236 : Nat := 118140960795 + 4023236 * 2 ^ 59
def prefixEnd_4023236 : Nat := 4983230072969 + 3 ^ 40 * 4023236 * 2
def baseEnd_4023236 : Nat := 2065853854472326304347481

theorem tailTrace_4023236 : CollatzResearch.WordTrace tailWord_4023236 prefixEnd_4023236 2065853854472326304347481 := by
  unfold tailWord_4023236
  simp only [CollatzResearch.WordTrace]
  refine ⟨73369736026255280424984781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97826314701673707233313041 73369736026255280424984781)
  ·
    refine ⟨27513651009845730159369293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73369736026255280424984781 27513651009845730159369293)
    ·
      refine ⟨10317619128692148809763485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27513651009845730159369293 10317619128692148809763485)
      ·
        refine ⟨3869107173259555803661307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10317619128692148809763485 3869107173259555803661307)
        ·
          refine ⟨5803660759889333705491961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3869107173259555803661307 5803660759889333705491961)
          ·
            refine ⟨4352745569917000279118971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5803660759889333705491961 4352745569917000279118971)
            ·
              refine ⟨6529118354875500418678457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4352745569917000279118971 6529118354875500418678457)
              ·
                refine ⟨4896838766156625314008843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6529118354875500418678457 4896838766156625314008843)
                ·
                  refine ⟨7345258149234937971013265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4896838766156625314008843 7345258149234937971013265)
                  ·
                    refine ⟨5508943611926203478259949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7345258149234937971013265 5508943611926203478259949)
                    ·
                      refine ⟨2065853854472326304347481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5508943611926203478259949 2065853854472326304347481)
                      ·
                        rfl

theorem cell23_4023236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_4023236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4023236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4023236 prefixEnd_4023236 := by exact prefixLift 4023236
  have htrace : WordTrace (prefixWord ++ tailWord_4023236) baseStart_4023236 baseEnd_4023236 := by
    simpa [prefixWord, tailWord_4023236, baseEnd_4023236] using wordTrace_append hprefix tailTrace_4023236
  have hstable : (prefixWord ++ tailWord_4023236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4023236).length < 2 ^ (prefixWord ++ tailWord_4023236).sum := by decide
  have hdescent : baseEnd_4023236 < baseStart_4023236 := by decide
  rcases family_descends (prefixWord ++ tailWord_4023236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4023266 : List Nat := [3, 3, 3, 1, 1, 2, 2, 2, 2, 1, 3]
def baseStart_4023266 : Nat := 118140960795 + 4023266 * 2 ^ 59
def prefixEnd_4023266 : Nat := 4983230072969 + 3 ^ 40 * 4023266 * 2
def baseEnd_4023266 : Nat := 2065869258891961186972343

theorem tailTrace_4023266 : CollatzResearch.WordTrace tailWord_4023266 prefixEnd_4023266 2065869258891961186972343 := by
  unfold tailWord_4023266
  simp only [CollatzResearch.WordTrace]
  refine ⟨36685141560600468993390413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97827044161601250649041101 36685141560600468993390413)
  ·
    refine ⟨13756928085225175872521405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36685141560600468993390413 13756928085225175872521405)
    ·
      refine ⟨5158848031959440952195527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13756928085225175872521405 5158848031959440952195527)
      ·
        refine ⟨7738272047939161428293291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5158848031959440952195527 7738272047939161428293291)
        ·
          refine ⟨11607408071908742142439937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7738272047939161428293291 11607408071908742142439937)
          ·
            refine ⟨8705556053931556606829953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11607408071908742142439937 8705556053931556606829953)
            ·
              refine ⟨6529167040448667455122465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8705556053931556606829953 6529167040448667455122465)
              ·
                refine ⟨4896875280336500591341849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6529167040448667455122465 4896875280336500591341849)
                ·
                  refine ⟨3672656460252375443506387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4896875280336500591341849 3672656460252375443506387)
                  ·
                    refine ⟨5508984690378563165259581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3672656460252375443506387 5508984690378563165259581)
                    ·
                      refine ⟨2065869258891961186972343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5508984690378563165259581 2065869258891961186972343)
                      ·
                        rfl

theorem cell23_4023266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_4023266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4023266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4023266 prefixEnd_4023266 := by exact prefixLift 4023266
  have htrace : WordTrace (prefixWord ++ tailWord_4023266) baseStart_4023266 baseEnd_4023266 := by
    simpa [prefixWord, tailWord_4023266, baseEnd_4023266] using wordTrace_append hprefix tailTrace_4023266
  have hstable : (prefixWord ++ tailWord_4023266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4023266).length < 2 ^ (prefixWord ++ tailWord_4023266).sum := by decide
  have hdescent : baseEnd_4023266 < baseStart_4023266 := by decide
  rcases family_descends (prefixWord ++ tailWord_4023266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4023272 : List Nat := [2, 1, 4, 1, 1, 1, 2, 3, 4, 2, 2]
def baseStart_4023272 : Nat := 118140960795 + 4023272 * 2 ^ 59
def prefixEnd_4023272 : Nat := 4983230072969 + 3 ^ 40 * 4023272 * 2
def baseEnd_4023272 : Nat := 2065872339775888163497315

theorem tailTrace_4023272 : CollatzResearch.WordTrace tailWord_4023272 prefixEnd_4023272 2065872339775888163497315 := by
  unfold tailWord_4023272
  simp only [CollatzResearch.WordTrace]
  refine ⟨73370392540190069499140035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97827190053586759332186713 73370392540190069499140035)
  ·
    refine ⟨110055588810285104248710053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73370392540190069499140035 110055588810285104248710053)
    ·
      refine ⟨20635422901928457046633135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110055588810285104248710053 20635422901928457046633135)
      ·
        refine ⟨30953134352892685569949703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20635422901928457046633135 30953134352892685569949703)
        ·
          refine ⟨46429701529339028354924555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30953134352892685569949703 46429701529339028354924555)
          ·
            refine ⟨69644552294008542532386833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46429701529339028354924555 69644552294008542532386833)
            ·
              refine ⟨52233414220506406899290125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69644552294008542532386833 52233414220506406899290125)
              ·
                refine ⟨19587530332689902587233797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52233414220506406899290125 19587530332689902587233797)
                ·
                  refine ⟨3672661937379356735106337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19587530332689902587233797 3672661937379356735106337)
                  ·
                    refine ⟨2754496453034517551329753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3672661937379356735106337 2754496453034517551329753)
                    ·
                      refine ⟨2065872339775888163497315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2754496453034517551329753 2065872339775888163497315)
                      ·
                        rfl

theorem cell23_4023272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 3, 4, 2, 2].length) (baseStart_4023272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4023272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4023272 prefixEnd_4023272 := by exact prefixLift 4023272
  have htrace : WordTrace (prefixWord ++ tailWord_4023272) baseStart_4023272 baseEnd_4023272 := by
    simpa [prefixWord, tailWord_4023272, baseEnd_4023272] using wordTrace_append hprefix tailTrace_4023272
  have hstable : (prefixWord ++ tailWord_4023272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4023272).length < 2 ^ (prefixWord ++ tailWord_4023272).sum := by decide
  have hdescent : baseEnd_4023272 < baseStart_4023272 := by decide
  rcases family_descends (prefixWord ++ tailWord_4023272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4023282 : List Nat := [3, 2, 1, 5, 1, 1, 1, 1, 2, 6]
def baseStart_4023282 : Nat := 118140960795 + 4023282 * 2 ^ 59
def prefixEnd_4023282 : Nat := 4983230072969 + 3 ^ 40 * 4023282 * 2
def baseEnd_4023282 : Nat := 688625824860811041457423

theorem tailTrace_4023282 : CollatzResearch.WordTrace tailWord_4023282 prefixEnd_4023282 688625824860811041457423 := by
  unfold tailWord_4023282
  simp only [CollatzResearch.WordTrace]
  refine ⟨36685287452585977676536025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97827433206895940470762733 36685287452585977676536025)
  ·
    refine ⟨27513965589439483257402019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36685287452585977676536025 27513965589439483257402019)
    ·
      refine ⟨41270948384159224886103029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27513965589439483257402019 41270948384159224886103029)
      ·
        refine ⟨3869151411014927333072159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41270948384159224886103029 3869151411014927333072159)
        ·
          refine ⟨5803727116522390999608239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3869151411014927333072159 5803727116522390999608239)
          ·
            refine ⟨8705590674783586499412359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5803727116522390999608239 8705590674783586499412359)
            ·
              refine ⟨13058386012175379749118539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8705590674783586499412359 13058386012175379749118539)
              ·
                refine ⟨19587579018263069623677809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13058386012175379749118539 19587579018263069623677809)
                ·
                  refine ⟨14690684263697302217758357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19587579018263069623677809 14690684263697302217758357)
                  ·
                    refine ⟨688625824860811041457423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14690684263697302217758357 688625824860811041457423)
                    ·
                      rfl

theorem cell23_4023282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 1, 2, 6].length) (baseStart_4023282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4023282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4023282 prefixEnd_4023282 := by exact prefixLift 4023282
  have htrace : WordTrace (prefixWord ++ tailWord_4023282) baseStart_4023282 baseEnd_4023282 := by
    simpa [prefixWord, tailWord_4023282, baseEnd_4023282] using wordTrace_append hprefix tailTrace_4023282
  have hstable : (prefixWord ++ tailWord_4023282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4023282).length < 2 ^ (prefixWord ++ tailWord_4023282).sum := by decide
  have hdescent : baseEnd_4023282 < baseStart_4023282 := by decide
  rcases family_descends (prefixWord ++ tailWord_4023282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4023365 : List Nat := [1, 3, 1, 1, 1, 3, 4, 1, 1, 4, 3]
def baseStart_4023365 : Nat := 118140960795 + 4023365 * 2 ^ 59
def prefixEnd_4023365 : Nat := 4983230072969 + 3 ^ 40 * 4023365 * 2
def baseEnd_4023365 : Nat := 2065920093476756299634387

theorem tailTrace_4023365 : CollatzResearch.WordTrace tailWord_4023365 prefixEnd_4023365 2065920093476756299634387 := by
  unfold tailWord_4023365
  simp only [CollatzResearch.WordTrace]
  refine ⟨146744177069043215881415549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97829451379362143920943699 146744177069043215881415549)
  ·
    refine ⟨55029066400891205955530831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146744177069043215881415549 55029066400891205955530831)
    ·
      refine ⟨82543599601336808933296247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55029066400891205955530831 82543599601336808933296247)
      ·
        refine ⟨123815399402005213399944371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82543599601336808933296247 123815399402005213399944371)
        ·
          refine ⟨185723099103007820099916557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123815399402005213399944371 185723099103007820099916557)
          ·
            refine ⟨69646162163627932537468709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 185723099103007820099916557 69646162163627932537468709)
            ·
              refine ⟨13058655405680237350775383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69646162163627932537468709 13058655405680237350775383)
              ·
                refine ⟨19587983108520356026163075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13058655405680237350775383 19587983108520356026163075)
                ·
                  refine ⟨29381974662780534039244613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19587983108520356026163075 29381974662780534039244613)
                  ·
                    refine ⟨5509120249271350132358365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29381974662780534039244613 5509120249271350132358365)
                    ·
                      refine ⟨2065920093476756299634387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5509120249271350132358365 2065920093476756299634387)
                      ·
                        rfl

theorem cell23_4023365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 1, 1, 4, 3].length) (baseStart_4023365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4023365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4023365 prefixEnd_4023365 := by exact prefixLift 4023365
  have htrace : WordTrace (prefixWord ++ tailWord_4023365) baseStart_4023365 baseEnd_4023365 := by
    simpa [prefixWord, tailWord_4023365, baseEnd_4023365] using wordTrace_append hprefix tailTrace_4023365
  have hstable : (prefixWord ++ tailWord_4023365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4023365).length < 2 ^ (prefixWord ++ tailWord_4023365).sum := by decide
  have hdescent : baseEnd_4023365 < baseStart_4023365 := by decide
  rcases family_descends (prefixWord ++ tailWord_4023365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4023368 : List Nat := [2, 1, 3, 1, 1, 1, 3, 1, 10]
def baseStart_4023368 : Nat := 118140960795 + 4023368 * 2 ^ 59
def prefixEnd_4023368 : Nat := 4983230072969 + 3 ^ 40 * 4023368 * 2
def baseEnd_4023368 : Nat := 229546848213191087544097

theorem tailTrace_4023368 : CollatzResearch.WordTrace tailWord_4023368 prefixEnd_4023368 229546848213191087544097 := by
  unfold tailWord_4023368
  simp only [CollatzResearch.WordTrace]
  refine ⟨73372143244016173696887379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97829524325354898262516505 73372143244016173696887379)
  ·
    refine ⟨110058214866024260545331069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73372143244016173696887379 110058214866024260545331069)
    ·
      refine ⟨41271830574759097704499151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110058214866024260545331069 41271830574759097704499151)
      ·
        refine ⟨61907745862138646556748727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41271830574759097704499151 61907745862138646556748727)
        ·
          refine ⟨92861618793207969835123091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61907745862138646556748727 92861618793207969835123091)
          ·
            refine ⟨139292428189811954752684637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92861618793207969835123091 139292428189811954752684637)
            ·
              refine ⟨52234660571179483032256739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139292428189811954752684637 52234660571179483032256739)
              ·
                refine ⟨78351990856769224548385109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52234660571179483032256739 78351990856769224548385109)
                ·
                  refine ⟨229546848213191087544097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 78351990856769224548385109 229546848213191087544097)
                  ·
                    rfl

theorem cell23_4023368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 10].length) (baseStart_4023368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4023368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4023368 prefixEnd_4023368 := by exact prefixLift 4023368
  have htrace : WordTrace (prefixWord ++ tailWord_4023368) baseStart_4023368 baseEnd_4023368 := by
    simpa [prefixWord, tailWord_4023368, baseEnd_4023368] using wordTrace_append hprefix tailTrace_4023368
  have hstable : (prefixWord ++ tailWord_4023368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4023368).length < 2 ^ (prefixWord ++ tailWord_4023368).sum := by decide
  have hdescent : baseEnd_4023368 < baseStart_4023368 := by decide
  rcases family_descends (prefixWord ++ tailWord_4023368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4023402 : List Nat := [3, 1, 3, 2, 2, 2, 1, 3, 6]
def baseStart_4023402 : Nat := 118140960795 + 4023402 * 2 ^ 59
def prefixEnd_4023402 : Nat := 4983230072969 + 3 ^ 40 * 4023402 * 2
def baseEnd_4023402 : Nat := 229548788028996961652413

theorem tailTrace_4023402 : CollatzResearch.WordTrace tailWord_4023402 prefixEnd_4023402 229548788028996961652413 := by
  unfold tailWord_4023402
  simp only [CollatzResearch.WordTrace]
  refine ⟨36686381642477292800128115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97830351046606114133674973 36686381642477292800128115)
  ·
    refine ⟨55029572463715939200192173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36686381642477292800128115 55029572463715939200192173)
    ·
      refine ⟨20636089673893477200072065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55029572463715939200192173 20636089673893477200072065)
      ·
        refine ⟨15477067255420107900054049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20636089673893477200072065 15477067255420107900054049)
        ·
          refine ⟨11607800441565080925040537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15477067255420107900054049 11607800441565080925040537)
          ·
            refine ⟨8705850331173810693780403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11607800441565080925040537 8705850331173810693780403)
            ·
              refine ⟨13058775496760716040670605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8705850331173810693780403 13058775496760716040670605)
              ·
                refine ⟨4897040811285268515251477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13058775496760716040670605 4897040811285268515251477)
                ·
                  refine ⟨229548788028996961652413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4897040811285268515251477 229548788028996961652413)
                  ·
                    rfl

theorem cell23_4023402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 3, 6].length) (baseStart_4023402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4023402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4023402 prefixEnd_4023402 := by exact prefixLift 4023402
  have htrace : WordTrace (prefixWord ++ tailWord_4023402) baseStart_4023402 baseEnd_4023402 := by
    simpa [prefixWord, tailWord_4023402, baseEnd_4023402] using wordTrace_append hprefix tailTrace_4023402
  have hstable : (prefixWord ++ tailWord_4023402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4023402).length < 2 ^ (prefixWord ++ tailWord_4023402).sum := by decide
  have hdescent : baseEnd_4023402 < baseStart_4023402 := by decide
  rcases family_descends (prefixWord ++ tailWord_4023402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4023415 : List Nat := [1, 1, 3, 1, 1, 4, 3, 1, 3, 5]
def baseStart_4023415 : Nat := 118140960795 + 4023415 * 2 ^ 59
def prefixEnd_4023415 : Nat := 4983230072969 + 3 ^ 40 * 4023415 * 2
def baseEnd_4023415 : Nat := 688648589169827034669719

theorem tailTrace_4023415 : CollatzResearch.WordTrace tailWord_4023415 prefixEnd_4023415 688648589169827034669719 := by
  unfold tailWord_4023415
  simp only [CollatzResearch.WordTrace]
  refine ⟨146746000718862074420735699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97830667145908049613823799 146746000718862074420735699)
  ·
    refine ⟨220119001078293111631103549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146746000718862074420735699 220119001078293111631103549)
    ·
      refine ⟨82544625404359916861663831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220119001078293111631103549 82544625404359916861663831)
      ·
        refine ⟨123816938106539875292495747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82544625404359916861663831 123816938106539875292495747)
        ·
          refine ⟨185725407159809812938743621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123816938106539875292495747 185725407159809812938743621)
          ·
            refine ⟨34823513842464339926014429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 185725407159809812938743621 34823513842464339926014429)
            ·
              refine ⟨13058817690924127472255411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34823513842464339926014429 13058817690924127472255411)
              ·
                refine ⟨19588226536386191208383117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13058817690924127472255411 19588226536386191208383117)
                ·
                  refine ⟨7345584951144821703143669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19588226536386191208383117 7345584951144821703143669)
                  ·
                    refine ⟨688648589169827034669719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7345584951144821703143669 688648589169827034669719)
                    ·
                      rfl

theorem cell23_4023415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 1, 3, 5].length) (baseStart_4023415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4023415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4023415 prefixEnd_4023415 := by exact prefixLift 4023415
  have htrace : WordTrace (prefixWord ++ tailWord_4023415) baseStart_4023415 baseEnd_4023415 := by
    simpa [prefixWord, tailWord_4023415, baseEnd_4023415] using wordTrace_append hprefix tailTrace_4023415
  have hstable : (prefixWord ++ tailWord_4023415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4023415).length < 2 ^ (prefixWord ++ tailWord_4023415).sum := by decide
  have hdescent : baseEnd_4023415 < baseStart_4023415 := by decide
  rcases family_descends (prefixWord ++ tailWord_4023415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4023452 : List Nat := [2, 2, 3, 2, 1, 2, 1, 2, 3, 1, 4]
def baseStart_4023452 : Nat := 118140960795 + 4023452 * 2 ^ 59
def prefixEnd_4023452 : Nat := 4983230072969 + 3 ^ 40 * 4023452 * 2
def baseEnd_4023452 : Nat := 2065964766293697459246487

theorem tailTrace_4023452 : CollatzResearch.WordTrace tailWord_4023452 prefixEnd_4023452 2065964766293697459246487 := by
  unfold tailWord_4023452
  simp only [CollatzResearch.WordTrace]
  refine ⟨73373675109864014869916305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97831566813152019826555073 73373675109864014869916305)
  ·
    refine ⟨55030256332398011152437229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73373675109864014869916305 55030256332398011152437229)
    ·
      refine ⟨20636346124649254182163961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55030256332398011152437229 20636346124649254182163961)
      ·
        refine ⟨15477259593486940636622971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20636346124649254182163961 15477259593486940636622971)
        ·
          refine ⟨23215889390230410954934457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15477259593486940636622971 23215889390230410954934457)
          ·
            refine ⟨17411917042672808216200843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23215889390230410954934457 17411917042672808216200843)
            ·
              refine ⟨26117875564009212324301265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17411917042672808216200843 26117875564009212324301265)
              ·
                refine ⟨19588406673006909243225949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26117875564009212324301265 19588406673006909243225949)
                ·
                  refine ⟨7345652502377590966209731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19588406673006909243225949 7345652502377590966209731)
                  ·
                    refine ⟨11018478753566386449314597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7345652502377590966209731 11018478753566386449314597)
                    ·
                      refine ⟨2065964766293697459246487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11018478753566386449314597 2065964766293697459246487)
                      ·
                        rfl

theorem cell23_4023452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_4023452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4023452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4023452 prefixEnd_4023452 := by exact prefixLift 4023452
  have htrace : WordTrace (prefixWord ++ tailWord_4023452) baseStart_4023452 baseEnd_4023452 := by
    simpa [prefixWord, tailWord_4023452, baseEnd_4023452] using wordTrace_append hprefix tailTrace_4023452
  have hstable : (prefixWord ++ tailWord_4023452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4023452).length < 2 ^ (prefixWord ++ tailWord_4023452).sum := by decide
  have hdescent : baseEnd_4023452 < baseStart_4023452 := by decide
  rcases family_descends (prefixWord ++ tailWord_4023452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4023486 : List Nat := [4, 2, 1, 1, 3, 1, 4, 1, 1, 1, 4]
def baseStart_4023486 : Nat := 118140960795 + 4023486 * 2 ^ 59
def prefixEnd_4023486 : Nat := 4983230072969 + 3 ^ 40 * 4023486 * 2
def baseEnd_4023486 : Nat := 2065982224635950326221331

theorem tailTrace_4023486 : CollatzResearch.WordTrace tailWord_4023486 prefixEnd_4023486 2065982224635950326221331 := by
  unfold tailWord_4023486
  simp only [CollatzResearch.WordTrace]
  refine ⟨18343573787700606693321289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97832393534403235697713541 18343573787700606693321289)
  ·
    refine ⟨13757680340775455019990967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18343573787700606693321289 13757680340775455019990967)
    ·
      refine ⟨20636520511163182529986451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13757680340775455019990967 20636520511163182529986451)
      ·
        refine ⟨30954780766744773794979677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20636520511163182529986451 30954780766744773794979677)
        ·
          refine ⟨11608042787529290173117379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30954780766744773794979677 11608042787529290173117379)
          ·
            refine ⟨17412064181293935259676069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11608042787529290173117379 17412064181293935259676069)
            ·
              refine ⟨3264762033992612861189263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17412064181293935259676069 3264762033992612861189263)
              ·
                refine ⟨4897143050988919291783895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3264762033992612861189263 4897143050988919291783895)
                ·
                  refine ⟨7345714576483378937675843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4897143050988919291783895 7345714576483378937675843)
                  ·
                    refine ⟨11018571864725068406513765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7345714576483378937675843 11018571864725068406513765)
                    ·
                      refine ⟨2065982224635950326221331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11018571864725068406513765 2065982224635950326221331)
                      ·
                        rfl

theorem cell23_4023486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 4, 1, 1, 1, 4].length) (baseStart_4023486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4023486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4023486 prefixEnd_4023486 := by exact prefixLift 4023486
  have htrace : WordTrace (prefixWord ++ tailWord_4023486) baseStart_4023486 baseEnd_4023486 := by
    simpa [prefixWord, tailWord_4023486, baseEnd_4023486] using wordTrace_append hprefix tailTrace_4023486
  have hstable : (prefixWord ++ tailWord_4023486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4023486).length < 2 ^ (prefixWord ++ tailWord_4023486).sum := by decide
  have hdescent : baseEnd_4023486 < baseStart_4023486 := by decide
  rcases family_descends (prefixWord ++ tailWord_4023486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4023492 : List Nat := [2, 3, 3, 1, 3, 1, 10]
def baseStart_4023492 : Nat := 118140960795 + 4023492 * 2 ^ 59
def prefixEnd_4023492 : Nat := 4983230072969 + 3 ^ 40 * 4023492 * 2
def baseEnd_4023492 : Nat := 25505991426171324725263

theorem tailTrace_4023492 : CollatzResearch.WordTrace tailWord_4023492 prefixEnd_4023492 25505991426171324725263 := by
  unfold tailWord_4023492
  simp only [CollatzResearch.WordTrace]
  refine ⟨73374404569791558285644365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97832539426388744380859153 73374404569791558285644365)
  ·
    refine ⟨27515401713671834357116637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73374404569791558285644365 27515401713671834357116637)
    ·
      refine ⟨10318275642626937883918739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27515401713671834357116637 10318275642626937883918739)
      ·
        refine ⟨15477413463940406825878109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10318275642626937883918739 15477413463940406825878109)
        ·
          refine ⟨5804030048977652559704291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15477413463940406825878109 5804030048977652559704291)
          ·
            refine ⟨8706045073466478839556437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5804030048977652559704291 8706045073466478839556437)
            ·
              refine ⟨25505991426171324725263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 8706045073466478839556437 25505991426171324725263)
              ·
                rfl

theorem cell23_4023492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 10].length) (baseStart_4023492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4023492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4023492 prefixEnd_4023492 := by exact prefixLift 4023492
  have htrace : WordTrace (prefixWord ++ tailWord_4023492) baseStart_4023492 baseEnd_4023492 := by
    simpa [prefixWord, tailWord_4023492, baseEnd_4023492] using wordTrace_append hprefix tailTrace_4023492
  have hstable : (prefixWord ++ tailWord_4023492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4023492).length < 2 ^ (prefixWord ++ tailWord_4023492).sum := by decide
  have hdescent : baseEnd_4023492 < baseStart_4023492 := by decide
  rcases family_descends (prefixWord ++ tailWord_4023492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4023519 : List Nat := [1, 1, 2, 3, 2, 1, 2, 5, 2, 1, 3]
def baseStart_4023519 : Nat := 118140960795 + 4023519 * 2 ^ 59
def prefixEnd_4023519 : Nat := 4983230072969 + 3 ^ 40 * 4023519 * 2
def baseEnd_4023519 : Nat := 2065999169497548697108679

theorem tailTrace_4023519 : CollatzResearch.WordTrace tailWord_4023519 prefixEnd_4023519 2065999169497548697108679 := by
  unfold tailWord_4023519
  simp only [CollatzResearch.WordTrace]
  refine ⟨146749793910485300182521611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97833195940323533455014407 146749793910485300182521611)
  ·
    refine ⟨220124690865727950273782417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146749793910485300182521611 220124690865727950273782417)
    ·
      refine ⟨165093518149295962705336813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220124690865727950273782417 165093518149295962705336813)
      ·
        refine ⟨61910069305985986014501305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165093518149295962705336813 61910069305985986014501305)
        ·
          refine ⟨46432551979489489510875979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61910069305985986014501305 46432551979489489510875979)
          ·
            refine ⟨69648827969234234266313969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46432551979489489510875979 69648827969234234266313969)
            ·
              refine ⟨52236620976925675699735477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69648827969234234266313969 52236620976925675699735477)
              ·
                refine ⟨4897183216586782096850201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52236620976925675699735477 4897183216586782096850201)
                ·
                  refine ⟨3672887412440086572637651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4897183216586782096850201 3672887412440086572637651)
                  ·
                    refine ⟨5509331118660129858956477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3672887412440086572637651 5509331118660129858956477)
                    ·
                      refine ⟨2065999169497548697108679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5509331118660129858956477 2065999169497548697108679)
                      ·
                        rfl

theorem cell23_4023519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 5, 2, 1, 3].length) (baseStart_4023519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4023519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4023519 prefixEnd_4023519 := by exact prefixLift 4023519
  have htrace : WordTrace (prefixWord ++ tailWord_4023519) baseStart_4023519 baseEnd_4023519 := by
    simpa [prefixWord, tailWord_4023519, baseEnd_4023519] using wordTrace_append hprefix tailTrace_4023519
  have hstable : (prefixWord ++ tailWord_4023519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4023519).length < 2 ^ (prefixWord ++ tailWord_4023519).sum := by decide
  have hdescent : baseEnd_4023519 < baseStart_4023519 := by decide
  rcases family_descends (prefixWord ++ tailWord_4023519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4023542 : List Nat := [5, 1, 1, 1, 1, 1, 1, 2, 1, 5, 4]
def baseStart_4023542 : Nat := 118140960795 + 4023542 * 2 ^ 59
def prefixEnd_4023542 : Nat := 4983230072969 + 3 ^ 40 * 4023542 * 2
def baseEnd_4023542 : Nat := 2066010979552602107121073

theorem tailTrace_4023542 : CollatzResearch.WordTrace tailWord_4023542 prefixEnd_4023542 2066010979552602107121073 := by
  unfold tailWord_4023542
  simp only [CollatzResearch.WordTrace]
  refine ⟨9171914549337623444413055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 97833755192934650073739253 9171914549337623444413055)
  ·
    refine ⟨13757871824006435166619583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9171914549337623444413055 13757871824006435166619583)
    ·
      refine ⟨20636807736009652749929375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13757871824006435166619583 20636807736009652749929375)
      ·
        refine ⟨30955211604014479124894063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20636807736009652749929375 30955211604014479124894063)
        ·
          refine ⟨46432817406021718687341095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30955211604014479124894063 46432817406021718687341095)
          ·
            refine ⟨69649226109032578031011643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46432817406021718687341095 69649226109032578031011643)
            ·
              refine ⟨104473839163548867046517465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69649226109032578031011643 104473839163548867046517465)
              ·
                refine ⟨78355379372661650284888099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104473839163548867046517465 78355379372661650284888099)
                ·
                  refine ⟨117533069058992475427332149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78355379372661650284888099 117533069058992475427332149)
                  ·
                    refine ⟨11018725224280544571312389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 117533069058992475427332149 11018725224280544571312389)
                    ·
                      refine ⟨2066010979552602107121073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11018725224280544571312389 2066010979552602107121073)
                      ·
                        rfl

theorem cell23_4023542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 1, 5, 4].length) (baseStart_4023542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4023542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4023542 prefixEnd_4023542 := by exact prefixLift 4023542
  have htrace : WordTrace (prefixWord ++ tailWord_4023542) baseStart_4023542 baseEnd_4023542 := by
    simpa [prefixWord, tailWord_4023542, baseEnd_4023542] using wordTrace_append hprefix tailTrace_4023542
  have hstable : (prefixWord ++ tailWord_4023542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4023542).length < 2 ^ (prefixWord ++ tailWord_4023542).sum := by decide
  have hdescent : baseEnd_4023542 < baseStart_4023542 := by decide
  rcases family_descends (prefixWord ++ tailWord_4023542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4023562 : List Nat := [3, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3]
def baseStart_4023562 : Nat := 118140960795 + 4023562 * 2 ^ 59
def prefixEnd_4023562 : Nat := 4983230072969 + 3 ^ 40 * 4023562 * 2
def baseEnd_4023562 : Nat := 2066021249165692028870981

theorem tailTrace_4023562 : CollatzResearch.WordTrace tailWord_4023562 prefixEnd_4023562 2066021249165692028870981 := by
  unfold tailWord_4023562
  simp only [CollatzResearch.WordTrace]
  refine ⟨36687840562332379631584235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97834241499553012350891293 36687840562332379631584235)
  ·
    refine ⟨55031760843498569447376353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36687840562332379631584235 55031760843498569447376353)
    ·
      refine ⟨41273820632623927085532265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55031760843498569447376353 41273820632623927085532265)
      ·
        refine ⟨30955365474467945314149199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41273820632623927085532265 30955365474467945314149199)
        ·
          refine ⟨46433048211701917971223799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30955365474467945314149199 46433048211701917971223799)
          ·
            refine ⟨69649572317552876956835699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46433048211701917971223799 69649572317552876956835699)
            ·
              refine ⟨104474358476329315435253549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69649572317552876956835699 104474358476329315435253549)
              ·
                refine ⟨39177884428623493288220081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104474358476329315435253549 39177884428623493288220081)
                ·
                  refine ⟨29383413321467619966165061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39177884428623493288220081 29383413321467619966165061)
                  ·
                    refine ⟨5509389997775178743655949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29383413321467619966165061 5509389997775178743655949)
                    ·
                      refine ⟨2066021249165692028870981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5509389997775178743655949 2066021249165692028870981)
                      ·
                        rfl

theorem cell23_4023562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3].length) (baseStart_4023562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4023562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4023562 prefixEnd_4023562 := by exact prefixLift 4023562
  have htrace : WordTrace (prefixWord ++ tailWord_4023562) baseStart_4023562 baseEnd_4023562 := by
    simpa [prefixWord, tailWord_4023562, baseEnd_4023562] using wordTrace_append hprefix tailTrace_4023562
  have hstable : (prefixWord ++ tailWord_4023562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4023562).length < 2 ^ (prefixWord ++ tailWord_4023562).sum := by decide
  have hdescent : baseEnd_4023562 < baseStart_4023562 := by decide
  rcases family_descends (prefixWord ++ tailWord_4023562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4023570 : List Nat := [3, 2, 4, 2, 1, 1, 1, 3, 2, 1, 3]
def baseStart_4023570 : Nat := 118140960795 + 4023570 * 2 ^ 59
def prefixEnd_4023570 : Nat := 4983230072969 + 3 ^ 40 * 4023570 * 2
def baseEnd_4023570 : Nat := 2066025357010927997570945

theorem tailTrace_4023570 : CollatzResearch.WordTrace tailWord_4023570 prefixEnd_4023570 2066025357010927997570945 := by
  unfold tailWord_4023570
  simp only [CollatzResearch.WordTrace]
  refine ⟨36687913508325133973157041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97834436022200357261752109 36687913508325133973157041)
  ·
    refine ⟨27515935131243850479867781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36687913508325133973157041 27515935131243850479867781)
    ·
      refine ⟨5159237837108221964975209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27515935131243850479867781 5159237837108221964975209)
      ·
        refine ⟨3869428377831166473731407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5159237837108221964975209 3869428377831166473731407)
        ·
          refine ⟨5804142566746749710597111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3869428377831166473731407 5804142566746749710597111)
          ·
            refine ⟨8706213850120124565895667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5804142566746749710597111 8706213850120124565895667)
            ·
              refine ⟨13059320775180186848843501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8706213850120124565895667 13059320775180186848843501)
              ·
                refine ⟨4897245290692570068316313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13059320775180186848843501 4897245290692570068316313)
                ·
                  refine ⟨3672933968019427551237235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4897245290692570068316313 3672933968019427551237235)
                  ·
                    refine ⟨5509400952029141326855853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3672933968019427551237235 5509400952029141326855853)
                    ·
                      refine ⟨2066025357010927997570945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5509400952029141326855853 2066025357010927997570945)
                      ·
                        rfl

theorem cell23_4023570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_4023570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4023570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4023570 prefixEnd_4023570 := by exact prefixLift 4023570
  have htrace : WordTrace (prefixWord ++ tailWord_4023570) baseStart_4023570 baseEnd_4023570 := by
    simpa [prefixWord, tailWord_4023570, baseEnd_4023570] using wordTrace_append hprefix tailTrace_4023570
  have hstable : (prefixWord ++ tailWord_4023570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4023570).length < 2 ^ (prefixWord ++ tailWord_4023570).sum := by decide
  have hdescent : baseEnd_4023570 < baseStart_4023570 := by decide
  rcases family_descends (prefixWord ++ tailWord_4023570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4023632 : List Nat := [2, 1, 1, 1, 1, 5, 2, 2, 1, 3, 4]
def baseStart_4023632 : Nat := 118140960795 + 4023632 * 2 ^ 59
def prefixEnd_4023632 : Nat := 4983230072969 + 3 ^ 40 * 4023632 * 2
def baseEnd_4023632 : Nat := 2066057192811506754995659

theorem tailTrace_4023632 : CollatzResearch.WordTrace tailWord_4023632 prefixEnd_4023632 2066057192811506754995659 := by
  unfold tailWord_4023632
  simp only [CollatzResearch.WordTrace]
  refine ⟨73376957679537960240692575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97835943572717280320923433 73376957679537960240692575)
  ·
    refine ⟨110065436519306940361038863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73376957679537960240692575 110065436519306940361038863)
    ·
      refine ⟨165098154778960410541558295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110065436519306940361038863 165098154778960410541558295)
      ·
        refine ⟨247647232168440615812337443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165098154778960410541558295 247647232168440615812337443)
        ·
          refine ⟨371470848252660923718506165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247647232168440615812337443 371470848252660923718506165)
          ·
            refine ⟨34825392023686961598609953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 371470848252660923718506165 34825392023686961598609953)
            ·
              refine ⟨26119044017765221198957465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34825392023686961598609953 26119044017765221198957465)
              ·
                refine ⟨19589283013323915899218099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26119044017765221198957465 19589283013323915899218099)
                ·
                  refine ⟨29383924519985873848827149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19589283013323915899218099 29383924519985873848827149)
                  ·
                    refine ⟨11018971694994702693310181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29383924519985873848827149 11018971694994702693310181)
                    ·
                      refine ⟨2066057192811506754995659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11018971694994702693310181 2066057192811506754995659)
                      ·
                        rfl

theorem cell23_4023632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 2, 1, 3, 4].length) (baseStart_4023632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4023632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4023632 prefixEnd_4023632 := by exact prefixLift 4023632
  have htrace : WordTrace (prefixWord ++ tailWord_4023632) baseStart_4023632 baseEnd_4023632 := by
    simpa [prefixWord, tailWord_4023632, baseEnd_4023632] using wordTrace_append hprefix tailTrace_4023632
  have hstable : (prefixWord ++ tailWord_4023632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4023632).length < 2 ^ (prefixWord ++ tailWord_4023632).sum := by decide
  have hdescent : baseEnd_4023632 < baseStart_4023632 := by decide
  rcases family_descends (prefixWord ++ tailWord_4023632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4023676 : List Nat := [2, 2, 2, 1, 1, 1, 3, 6, 1, 4]
def baseStart_4023676 : Nat := 118140960795 + 4023676 * 2 ^ 59
def prefixEnd_4023676 : Nat := 4983230072969 + 3 ^ 40 * 4023676 * 2
def baseEnd_4023676 : Nat := 688693261986768194281819

theorem tailTrace_4023676 : CollatzResearch.WordTrace tailWord_4023676 prefixEnd_4023676 688693261986768194281819 := by
  unfold tailWord_4023676
  simp only [CollatzResearch.WordTrace]
  refine ⟨73377760085458257997993441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97837013447277677330657921 73377760085458257997993441)
  ·
    refine ⟨55033320064093693498495081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73377760085458257997993441 55033320064093693498495081)
    ·
      refine ⟨41274990048070270123871311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55033320064093693498495081 41274990048070270123871311)
      ·
        refine ⟨61912485072105405185806967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41274990048070270123871311 61912485072105405185806967)
        ·
          refine ⟨92868727608158107778710451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61912485072105405185806967 92868727608158107778710451)
          ·
            refine ⟨139303091412237161668065677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92868727608158107778710451 139303091412237161668065677)
            ·
              refine ⟨52238659279588935625524629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139303091412237161668065677 52238659279588935625524629)
              ·
                refine ⟨2448687153730731357446467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 52238659279588935625524629 2448687153730731357446467)
                ·
                  refine ⟨3673030730596097036169701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2448687153730731357446467 3673030730596097036169701)
                  ·
                    refine ⟨688693261986768194281819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3673030730596097036169701 688693261986768194281819)
                    ·
                      rfl

theorem cell23_4023676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 6, 1, 4].length) (baseStart_4023676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4023676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4023676 prefixEnd_4023676 := by exact prefixLift 4023676
  have htrace : WordTrace (prefixWord ++ tailWord_4023676) baseStart_4023676 baseEnd_4023676 := by
    simpa [prefixWord, tailWord_4023676, baseEnd_4023676] using wordTrace_append hprefix tailTrace_4023676
  have hstable : (prefixWord ++ tailWord_4023676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4023676).length < 2 ^ (prefixWord ++ tailWord_4023676).sum := by decide
  have hdescent : baseEnd_4023676 < baseStart_4023676 := by decide
  rcases family_descends (prefixWord ++ tailWord_4023676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4023692 : List Nat := [2, 2, 1, 2, 1, 3, 1, 2, 1, 2, 6]
def baseStart_4023692 : Nat := 118140960795 + 4023692 * 2 ^ 59
def prefixEnd_4023692 : Nat := 4983230072969 + 3 ^ 40 * 4023692 * 2
def baseEnd_4023692 : Nat := 2066088001650776520245383

theorem tailTrace_4023692 : CollatzResearch.WordTrace tailWord_4023692 prefixEnd_4023692 2066088001650776520245383 := by
  unfold tailWord_4023692
  simp only [CollatzResearch.WordTrace]
  refine ⟨73378051869429275364284665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97837402492572367152379553 73378051869429275364284665)
  ·
    refine ⟨55033538902071956523213499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73378051869429275364284665 55033538902071956523213499)
    ·
      refine ⟨82550308353107934784820249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55033538902071956523213499 82550308353107934784820249)
      ·
        refine ⟨61912731264830951088615187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82550308353107934784820249 61912731264830951088615187)
        ·
          refine ⟨92869096897246426632922781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61912731264830951088615187 92869096897246426632922781)
          ·
            refine ⟨34825911336467409987346043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92869096897246426632922781 34825911336467409987346043)
            ·
              refine ⟨52238867004701114981019065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34825911336467409987346043 52238867004701114981019065)
              ·
                refine ⟨39179150253525836235764299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52238867004701114981019065 39179150253525836235764299)
                ·
                  refine ⟨58768725380288754353646449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39179150253525836235764299 58768725380288754353646449)
                  ·
                    refine ⟨44076544035216565765234837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58768725380288754353646449 44076544035216565765234837)
                    ·
                      refine ⟨2066088001650776520245383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44076544035216565765234837 2066088001650776520245383)
                      ·
                        rfl

theorem cell23_4023692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 2, 1, 2, 6].length) (baseStart_4023692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4023692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4023692 prefixEnd_4023692 := by exact prefixLift 4023692
  have htrace : WordTrace (prefixWord ++ tailWord_4023692) baseStart_4023692 baseEnd_4023692 := by
    simpa [prefixWord, tailWord_4023692, baseEnd_4023692] using wordTrace_append hprefix tailTrace_4023692
  have hstable : (prefixWord ++ tailWord_4023692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4023692).length < 2 ^ (prefixWord ++ tailWord_4023692).sum := by decide
  have hdescent : baseEnd_4023692 < baseStart_4023692 := by decide
  rcases family_descends (prefixWord ++ tailWord_4023692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4023733 : List Nat := [1, 3, 3, 2, 2, 1, 3, 1, 3, 1, 3]
def baseStart_4023733 : Nat := 118140960795 + 4023733 * 2 ^ 59
def prefixEnd_4023733 : Nat := 4983230072969 + 3 ^ 40 * 4023733 * 2
def baseEnd_4023733 : Nat := 2066109054357610859832695

theorem tailTrace_4023733 : CollatzResearch.WordTrace tailWord_4023733 prefixEnd_4023733 2066109054357610859832695 := by
  unfold tailWord_4023733
  simp only [CollatzResearch.WordTrace]
  refine ⟨146757599131710014730811853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97838399421140009820541235 146757599131710014730811853)
  ·
    refine ⟨55034099674391255524054445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146757599131710014730811853 55034099674391255524054445)
    ·
      refine ⟨20637787377896720821520417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55034099674391255524054445 20637787377896720821520417)
      ·
        refine ⟨15478340533422540616140313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20637787377896720821520417 15478340533422540616140313)
        ·
          refine ⟨11608755400066905462105235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15478340533422540616140313 11608755400066905462105235)
          ·
            refine ⟨17413133100100358193157853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11608755400066905462105235 17413133100100358193157853)
            ·
              refine ⟨6529924912537634322434195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17413133100100358193157853 6529924912537634322434195)
              ·
                refine ⟨9794887368806451483651293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6529924912537634322434195 9794887368806451483651293)
                ·
                  refine ⟨3673082763302419306369235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9794887368806451483651293 3673082763302419306369235)
                  ·
                    refine ⟨5509624144953628959553853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3673082763302419306369235 5509624144953628959553853)
                    ·
                      refine ⟨2066109054357610859832695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5509624144953628959553853 2066109054357610859832695)
                      ·
                        rfl

theorem cell23_4023733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 3, 1, 3, 1, 3].length) (baseStart_4023733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4023733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4023733 prefixEnd_4023733 := by exact prefixLift 4023733
  have htrace : WordTrace (prefixWord ++ tailWord_4023733) baseStart_4023733 baseEnd_4023733 := by
    simpa [prefixWord, tailWord_4023733, baseEnd_4023733] using wordTrace_append hprefix tailTrace_4023733
  have hstable : (prefixWord ++ tailWord_4023733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4023733).length < 2 ^ (prefixWord ++ tailWord_4023733).sum := by decide
  have hdescent : baseEnd_4023733 < baseStart_4023733 := by decide
  rcases family_descends (prefixWord ++ tailWord_4023733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4023740 : List Nat := [2, 2, 2, 4, 3, 1, 2, 1, 6]
def baseStart_4023740 : Nat := 118140960795 + 4023740 * 2 ^ 59
def prefixEnd_4023740 : Nat := 4983230072969 + 3 ^ 40 * 4023740 * 2
def baseEnd_4023740 : Nat := 229568072080243592493907

theorem tailTrace_4023740 : CollatzResearch.WordTrace tailWord_4023740 prefixEnd_4023740 229568072080243592493907 := by
  unfold tailWord_4023740
  simp only [CollatzResearch.WordTrace]
  refine ⟨73378927221342327463158337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97838569628456436617544449 73378927221342327463158337)
  ·
    refine ⟨55034195416006745597368753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73378927221342327463158337 55034195416006745597368753)
    ·
      refine ⟨41275646562005059198026565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55034195416006745597368753 41275646562005059198026565)
      ·
        refine ⟨7739183730375948599629981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41275646562005059198026565 7739183730375948599629981)
        ·
          refine ⟨2902193898890980724861243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7739183730375948599629981 2902193898890980724861243)
          ·
            refine ⟨4353290848336471087291865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2902193898890980724861243 4353290848336471087291865)
            ·
              refine ⟨3264968136252353315468899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4353290848336471087291865 3264968136252353315468899)
              ·
                refine ⟨4897452204378529973203349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3264968136252353315468899 4897452204378529973203349)
                ·
                  refine ⟨229568072080243592493907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4897452204378529973203349 229568072080243592493907)
                  ·
                    rfl

theorem cell23_4023740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 2, 1, 6].length) (baseStart_4023740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4023740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4023740 prefixEnd_4023740 := by exact prefixLift 4023740
  have htrace : WordTrace (prefixWord ++ tailWord_4023740) baseStart_4023740 baseEnd_4023740 := by
    simpa [prefixWord, tailWord_4023740, baseEnd_4023740] using wordTrace_append hprefix tailTrace_4023740
  have hstable : (prefixWord ++ tailWord_4023740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4023740).length < 2 ^ (prefixWord ++ tailWord_4023740).sum := by decide
  have hdescent : baseEnd_4023740 < baseStart_4023740 := by decide
  rcases family_descends (prefixWord ++ tailWord_4023740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4023756 : List Nat := [2, 2, 1, 4, 2, 2, 1, 1, 3, 1, 4]
def baseStart_4023756 : Nat := 118140960795 + 4023756 * 2 ^ 59
def prefixEnd_4023756 : Nat := 4983230072969 + 3 ^ 40 * 4023756 * 2
def baseEnd_4023756 : Nat := 2066120864412664269845089

theorem tailTrace_4023756 : CollatzResearch.WordTrace tailWord_4023756 prefixEnd_4023756 2066120864412664269845089 := by
  unfold tailWord_4023756
  simp only [CollatzResearch.WordTrace]
  refine ⟨73379219005313344829449561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97838958673751126439266081 73379219005313344829449561)
  ·
    refine ⟨55034414253985008622087171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73379219005313344829449561 55034414253985008622087171)
    ·
      refine ⟨82551621380977512933130757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55034414253985008622087171 82551621380977512933130757)
      ·
        refine ⟨15478429008933283674962017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82551621380977512933130757 15478429008933283674962017)
        ·
          refine ⟨11608821756699962756221513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15478429008933283674962017 11608821756699962756221513)
          ·
            refine ⟨8706616317524972067166135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11608821756699962756221513 8706616317524972067166135)
            ·
              refine ⟨13059924476287458100749203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8706616317524972067166135 13059924476287458100749203)
              ·
                refine ⟨19589886714431187151123805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13059924476287458100749203 19589886714431187151123805)
                ·
                  refine ⟨7346207517911695181671427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19589886714431187151123805 7346207517911695181671427)
                  ·
                    refine ⟨11019311276867542772507141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7346207517911695181671427 11019311276867542772507141)
                    ·
                      refine ⟨2066120864412664269845089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11019311276867542772507141 2066120864412664269845089)
                      ·
                        rfl

theorem cell23_4023756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_4023756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4023756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4023756 prefixEnd_4023756 := by exact prefixLift 4023756
  have htrace : WordTrace (prefixWord ++ tailWord_4023756) baseStart_4023756 baseEnd_4023756 := by
    simpa [prefixWord, tailWord_4023756, baseEnd_4023756] using wordTrace_append hprefix tailTrace_4023756
  have hstable : (prefixWord ++ tailWord_4023756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4023756).length < 2 ^ (prefixWord ++ tailWord_4023756).sum := by decide
  have hdescent : baseEnd_4023756 < baseStart_4023756 := by decide
  rcases family_descends (prefixWord ++ tailWord_4023756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4023766 : List Nat := [5, 2, 1, 1, 1, 2, 1, 1, 3, 6]
def baseStart_4023766 : Nat := 118140960795 + 4023766 * 2 ^ 59
def prefixEnd_4023766 : Nat := 4983230072969 + 3 ^ 40 * 4023766 * 2
def baseEnd_4023766 : Nat := 688708666406403076906681

theorem tailTrace_4023766 : CollatzResearch.WordTrace tailWord_4023766 prefixEnd_4023766 688708666406403076906681 := by
  unfold tailWord_4023766
  simp only [CollatzResearch.WordTrace]
  refine ⟨9172425171286903835422697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 97839201827060307577842101 9172425171286903835422697)
  ·
    refine ⟨6879318878465177876567023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9172425171286903835422697 6879318878465177876567023)
    ·
      refine ⟨10318978317697766814850535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6879318878465177876567023 10318978317697766814850535)
      ·
        refine ⟨15478467476546650222275803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10318978317697766814850535 15478467476546650222275803)
        ·
          refine ⟨23217701214819975333413705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15478467476546650222275803 23217701214819975333413705)
          ·
            refine ⟨17413275911114981500060279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23217701214819975333413705 17413275911114981500060279)
            ·
              refine ⟨26119913866672472250090419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17413275911114981500060279 26119913866672472250090419)
              ·
                refine ⟨39179870800008708375135629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26119913866672472250090419 39179870800008708375135629)
                ·
                  refine ⟨14692451550003265640675861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39179870800008708375135629 14692451550003265640675861)
                  ·
                    refine ⟨688708666406403076906681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14692451550003265640675861 688708666406403076906681)
                    ·
                      rfl

theorem cell23_4023766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 1, 3, 6].length) (baseStart_4023766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4023766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4023766 prefixEnd_4023766 := by exact prefixLift 4023766
  have htrace : WordTrace (prefixWord ++ tailWord_4023766) baseStart_4023766 baseEnd_4023766 := by
    simpa [prefixWord, tailWord_4023766, baseEnd_4023766] using wordTrace_append hprefix tailTrace_4023766
  have hstable : (prefixWord ++ tailWord_4023766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4023766).length < 2 ^ (prefixWord ++ tailWord_4023766).sum := by decide
  have hdescent : baseEnd_4023766 < baseStart_4023766 := by decide
  rcases family_descends (prefixWord ++ tailWord_4023766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4023769 : List Nat := [1, 2, 1, 2, 4, 2, 1, 1, 3, 2, 4]
def baseStart_4023769 : Nat := 118140960795 + 4023769 * 2 ^ 59
def prefixEnd_4023769 : Nat := 4983230072969 + 3 ^ 40 * 4023769 * 2
def baseEnd_4023769 : Nat := 2066127539661172718982529

theorem tailTrace_4023769 : CollatzResearch.WordTrace tailWord_4023769 prefixEnd_4023769 2066127539661172718982529 := by
  unfold tailWord_4023769
  simp only [CollatzResearch.WordTrace]
  refine ⟨146758912159579592879122361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97839274773053061919414907 146758912159579592879122361)
  ·
    refine ⟨110069184119684694659341771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146758912159579592879122361 110069184119684694659341771)
    ·
      refine ⟨165103776179527041989012657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110069184119684694659341771 165103776179527041989012657)
      ·
        refine ⟨123827832134645281491759493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165103776179527041989012657 123827832134645281491759493)
        ·
          refine ⟨23217718525245990279704905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 123827832134645281491759493 23217718525245990279704905)
          ·
            refine ⟨17413288893934492709778679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23217718525245990279704905 17413288893934492709778679)
            ·
              refine ⟨26119933340901739064668019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17413288893934492709778679 26119933340901739064668019)
              ·
                refine ⟨39179900011352608597002029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26119933340901739064668019 39179900011352608597002029)
                ·
                  refine ⟨14692462504257228223875761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39179900011352608597002029 14692462504257228223875761)
                  ·
                    refine ⟨11019346878192921167906821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14692462504257228223875761 11019346878192921167906821)
                    ·
                      refine ⟨2066127539661172718982529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11019346878192921167906821 2066127539661172718982529)
                      ·
                        rfl

theorem cell23_4023769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 1, 3, 2, 4].length) (baseStart_4023769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4023769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4023769 prefixEnd_4023769 := by exact prefixLift 4023769
  have htrace : WordTrace (prefixWord ++ tailWord_4023769) baseStart_4023769 baseEnd_4023769 := by
    simpa [prefixWord, tailWord_4023769, baseEnd_4023769] using wordTrace_append hprefix tailTrace_4023769
  have hstable : (prefixWord ++ tailWord_4023769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4023769).length < 2 ^ (prefixWord ++ tailWord_4023769).sum := by decide
  have hdescent : baseEnd_4023769 < baseStart_4023769 := by decide
  rcases family_descends (prefixWord ++ tailWord_4023769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4023783 : List Nat := [1, 1, 5, 2, 1, 3, 2, 2, 2, 4]
def baseStart_4023783 : Nat := 118140960795 + 4023783 * 2 ^ 59
def prefixEnd_4023783 : Nat := 4983230072969 + 3 ^ 40 * 4023783 * 2
def baseEnd_4023783 : Nat := 688711576130111888069155

theorem tailTrace_4023783 : CollatzResearch.WordTrace tailWord_4023783 prefixEnd_4023783 688711576130111888069155 := by
  unfold tailWord_4023783
  simp only [CollatzResearch.WordTrace]
  refine ⟨146759422781528873270132003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97839615187685915513421335 146759422781528873270132003)
  ·
    refine ⟨220139134172293309905198005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146759422781528873270132003 220139134172293309905198005)
    ·
      refine ⟨20638043828652497803612313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 220139134172293309905198005 20638043828652497803612313)
      ·
        refine ⟨15478532871489373352709235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20638043828652497803612313 15478532871489373352709235)
        ·
          refine ⟨23217799307234060029063853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15478532871489373352709235 23217799307234060029063853)
          ·
            refine ⟨8706674740212772510898945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23217799307234060029063853 8706674740212772510898945)
            ·
              refine ⟨6530006055159579383174209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8706674740212772510898945 6530006055159579383174209)
              ·
                refine ⟨4897504541369684537380657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6530006055159579383174209 4897504541369684537380657)
                ·
                  refine ⟨3673128406027263403035493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4897504541369684537380657 3673128406027263403035493)
                  ·
                    refine ⟨688711576130111888069155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3673128406027263403035493 688711576130111888069155)
                    ·
                      rfl

theorem cell23_4023783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 2, 2, 2, 4].length) (baseStart_4023783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4023783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4023783 prefixEnd_4023783 := by exact prefixLift 4023783
  have htrace : WordTrace (prefixWord ++ tailWord_4023783) baseStart_4023783 baseEnd_4023783 := by
    simpa [prefixWord, tailWord_4023783, baseEnd_4023783] using wordTrace_append hprefix tailTrace_4023783
  have hstable : (prefixWord ++ tailWord_4023783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4023783).length < 2 ^ (prefixWord ++ tailWord_4023783).sum := by decide
  have hdescent : baseEnd_4023783 < baseStart_4023783 := by decide
  rcases family_descends (prefixWord ++ tailWord_4023783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4023839 : List Nat := [1, 1, 2, 4, 1, 1, 3, 2, 2, 6]
def baseStart_4023839 : Nat := 118140960795 + 4023839 * 2 ^ 59
def prefixEnd_4023839 : Nat := 4983230072969 + 3 ^ 40 * 4023839 * 2
def baseEnd_4023839 : Nat := 688721161102329148369069

theorem tailTrace_4023839 : CollatzResearch.WordTrace tailWord_4023839 prefixEnd_4023839 688721161102329148369069 := by
  unfold tailWord_4023839
  simp only [CollatzResearch.WordTrace]
  refine ⟨146761465269325994834170571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97840976846217329889447047 146761465269325994834170571)
  ·
    refine ⟨220142197903988992251255857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146761465269325994834170571 220142197903988992251255857)
    ·
      refine ⟨165106648427991744188441893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220142197903988992251255857 165106648427991744188441893)
      ·
        refine ⟨30957496580248452035332855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 165106648427991744188441893 30957496580248452035332855)
        ·
          refine ⟨46436244870372678052999283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30957496580248452035332855 46436244870372678052999283)
          ·
            refine ⟨69654367305559017079498925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46436244870372678052999283 69654367305559017079498925)
            ·
              refine ⟨26120387739584631404812097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69654367305559017079498925 26120387739584631404812097)
              ·
                refine ⟨19590290804688473553609073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26120387739584631404812097 19590290804688473553609073)
                ·
                  refine ⟨14692718103516355165206805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19590290804688473553609073 14692718103516355165206805)
                  ·
                    refine ⟨688721161102329148369069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14692718103516355165206805 688721161102329148369069)
                    ·
                      rfl

theorem cell23_4023839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 2, 2, 6].length) (baseStart_4023839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4023839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4023839 prefixEnd_4023839 := by exact prefixLift 4023839
  have htrace : WordTrace (prefixWord ++ tailWord_4023839) baseStart_4023839 baseEnd_4023839 := by
    simpa [prefixWord, tailWord_4023839, baseEnd_4023839] using wordTrace_append hprefix tailTrace_4023839
  have hstable : (prefixWord ++ tailWord_4023839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4023839).length < 2 ^ (prefixWord ++ tailWord_4023839).sum := by decide
  have hdescent : baseEnd_4023839 < baseStart_4023839 := by decide
  rcases family_descends (prefixWord ++ tailWord_4023839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4023840 : List Nat := [2, 1, 1, 6, 1, 1, 3, 2, 2, 1, 3]
def baseStart_4023840 : Nat := 118140960795 + 4023840 * 2 ^ 59
def prefixEnd_4023840 : Nat := 4983230072969 + 3 ^ 40 * 4023840 * 2
def baseEnd_4023840 : Nat := 2066163996787641941194703

theorem tailTrace_4023840 : CollatzResearch.WordTrace tailWord_4023840 prefixEnd_4023840 2066163996787641941194703 := by
  unfold tailWord_4023840
  simp only [CollatzResearch.WordTrace]
  refine ⟨73380750871161186002478487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97841001161548248003304649 73380750871161186002478487)
  ·
    refine ⟨110071126306741779003717731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73380750871161186002478487 110071126306741779003717731)
    ·
      refine ⟨165106689460112668505576597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110071126306741779003717731 165106689460112668505576597)
      ·
        refine ⟨7739376068442781336198903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 165106689460112668505576597 7739376068442781336198903)
        ·
          refine ⟨11609064102664172004298355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7739376068442781336198903 11609064102664172004298355)
          ·
            refine ⟨17413596153996258006447533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11609064102664172004298355 17413596153996258006447533)
            ·
              refine ⟨6530098557748596752417825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17413596153996258006447533 6530098557748596752417825)
              ·
                refine ⟨4897573918311447564313369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6530098557748596752417825 4897573918311447564313369)
                ·
                  refine ⟨3673180438733585673235027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4897573918311447564313369 3673180438733585673235027)
                  ·
                    refine ⟨5509770658100378509852541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3673180438733585673235027 5509770658100378509852541)
                    ·
                      refine ⟨2066163996787641941194703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5509770658100378509852541 2066163996787641941194703)
                      ·
                        rfl

theorem cell23_4023840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_4023840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4023840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4023840 prefixEnd_4023840 := by exact prefixLift 4023840
  have htrace : WordTrace (prefixWord ++ tailWord_4023840) baseStart_4023840 baseEnd_4023840 := by
    simpa [prefixWord, tailWord_4023840, baseEnd_4023840] using wordTrace_append hprefix tailTrace_4023840
  have hstable : (prefixWord ++ tailWord_4023840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4023840).length < 2 ^ (prefixWord ++ tailWord_4023840).sum := by decide
  have hdescent : baseEnd_4023840 < baseStart_4023840 := by decide
  rcases family_descends (prefixWord ++ tailWord_4023840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4023863 : List Nat := [1, 1, 3, 1, 2, 4, 3, 1, 1, 4, 2]
def baseStart_4023863 : Nat := 118140960795 + 4023863 * 2 ^ 59
def prefixEnd_4023863 : Nat := 4983230072969 + 3 ^ 40 * 4023863 * 2
def baseEnd_4023863 : Nat := 2066175806842695351207097

theorem tailTrace_4023863 : CollatzResearch.WordTrace tailWord_4023863 prefixEnd_4023863 2066175806842695351207097 := by
  unfold tailWord_4023863
  simp only [CollatzResearch.WordTrace]
  refine ⟨146762340621239046933044243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97841560414159364622029495 146762340621239046933044243)
  ·
    refine ⟨220143510931858570399566365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146762340621239046933044243 220143510931858570399566365)
    ·
      refine ⟨82553816599446963899837387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220143510931858570399566365 82553816599446963899837387)
      ·
        refine ⟨123830724899170445849756081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82553816599446963899837387 123830724899170445849756081)
        ·
          refine ⟨92873043674377834387317061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123830724899170445849756081 92873043674377834387317061)
          ·
            refine ⟨17413695688945843947621949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92873043674377834387317061 17413695688945843947621949)
            ·
              refine ⟨6530135883354691480358231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17413695688945843947621949 6530135883354691480358231)
              ·
                refine ⟨9795203825032037220537347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6530135883354691480358231 9795203825032037220537347)
                ·
                  refine ⟨14692805737548055830806021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9795203825032037220537347 14692805737548055830806021)
                  ·
                    refine ⟨2754901075790260468276129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14692805737548055830806021 2754901075790260468276129)
                    ·
                      refine ⟨2066175806842695351207097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2754901075790260468276129 2066175806842695351207097)
                      ·
                        rfl

theorem cell23_4023863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 3, 1, 1, 4, 2].length) (baseStart_4023863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4023863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4023863 prefixEnd_4023863 := by exact prefixLift 4023863
  have htrace : WordTrace (prefixWord ++ tailWord_4023863) baseStart_4023863 baseEnd_4023863 := by
    simpa [prefixWord, tailWord_4023863, baseEnd_4023863] using wordTrace_append hprefix tailTrace_4023863
  have hstable : (prefixWord ++ tailWord_4023863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4023863).length < 2 ^ (prefixWord ++ tailWord_4023863).sum := by decide
  have hdescent : baseEnd_4023863 < baseStart_4023863 := by decide
  rcases family_descends (prefixWord ++ tailWord_4023863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4023914 : List Nat := [3, 1, 3, 2, 1, 4, 2, 1, 2, 2, 2]
def baseStart_4023914 : Nat := 118140960795 + 4023914 * 2 ^ 59
def prefixEnd_4023914 : Nat := 4983230072969 + 3 ^ 40 * 4023914 * 2
def baseEnd_4023914 : Nat := 2066201994356074651669363

theorem tailTrace_4023914 : CollatzResearch.WordTrace tailWord_4023914 prefixEnd_4023914 2066201994356074651669363 := by
  unfold tailWord_4023914
  simp only [CollatzResearch.WordTrace]
  refine ⟨36691050186013570660787699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97842800496036188428767197 36691050186013570660787699)
  ·
    refine ⟨55036575279020355991181549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36691050186013570660787699 55036575279020355991181549)
    ·
      refine ⟨20638715729632633496693081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55036575279020355991181549 20638715729632633496693081)
      ·
        refine ⟨15479036797224475122519811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20638715729632633496693081 15479036797224475122519811)
        ·
          refine ⟨23218555195836712683779717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15479036797224475122519811 23218555195836712683779717)
          ·
            refine ⟨4353479099219383628208697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23218555195836712683779717 4353479099219383628208697)
            ·
              refine ⟨3265109324414537721156523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4353479099219383628208697 3265109324414537721156523)
              ·
                refine ⟨4897663986621806581734785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3265109324414537721156523 4897663986621806581734785)
                ·
                  refine ⟨3673247989966354936301089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4897663986621806581734785 3673247989966354936301089)
                  ·
                    refine ⟨2754935992474766202225817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3673247989966354936301089 2754935992474766202225817)
                    ·
                      refine ⟨2066201994356074651669363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2754935992474766202225817 2066201994356074651669363)
                      ·
                        rfl

theorem cell23_4023914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 2, 1, 2, 2, 2].length) (baseStart_4023914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4023914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4023914 prefixEnd_4023914 := by exact prefixLift 4023914
  have htrace : WordTrace (prefixWord ++ tailWord_4023914) baseStart_4023914 baseEnd_4023914 := by
    simpa [prefixWord, tailWord_4023914, baseEnd_4023914] using wordTrace_append hprefix tailTrace_4023914
  have hstable : (prefixWord ++ tailWord_4023914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4023914).length < 2 ^ (prefixWord ++ tailWord_4023914).sum := by decide
  have hdescent : baseEnd_4023914 < baseStart_4023914 := by decide
  rcases family_descends (prefixWord ++ tailWord_4023914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4023933 : List Nat := [1, 4, 1, 1, 4, 2, 2, 1, 2, 5]
def baseStart_4023933 : Nat := 118140960795 + 4023933 * 2 ^ 59
def prefixEnd_4023933 : Nat := 4983230072969 + 3 ^ 40 * 4023933 * 2
def baseEnd_4023933 : Nat := 688737250162836692443925

theorem tailTrace_4023933 : CollatzResearch.WordTrace tailWord_4023933 prefixEnd_4023933 688737250162836692443925 := by
  unfold tailWord_4023933
  simp only [CollatzResearch.WordTrace]
  refine ⟨146764893730985448888092453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97843262487323632592061635 146764893730985448888092453)
  ·
    refine ⟨27518417574559771666517335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146764893730985448888092453 27518417574559771666517335)
    ·
      refine ⟨41277626361839657499776003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27518417574559771666517335 41277626361839657499776003)
      ·
        refine ⟨61916439542759486249664005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41277626361839657499776003 61916439542759486249664005)
        ·
          refine ⟨11609332414267403671812001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61916439542759486249664005 11609332414267403671812001)
          ·
            refine ⟨8706999310700552753859001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11609332414267403671812001 8706999310700552753859001)
            ·
              refine ⟨6530249483025414565394251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8706999310700552753859001 6530249483025414565394251)
              ·
                refine ⟨9795374224538121848091377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6530249483025414565394251 9795374224538121848091377)
                ·
                  refine ⟨7346530668403591386068533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9795374224538121848091377 7346530668403591386068533)
                  ·
                    refine ⟨688737250162836692443925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7346530668403591386068533 688737250162836692443925)
                    ·
                      rfl

theorem cell23_4023933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 2, 1, 2, 5].length) (baseStart_4023933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4023933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4023933 prefixEnd_4023933 := by exact prefixLift 4023933
  have htrace : WordTrace (prefixWord ++ tailWord_4023933) baseStart_4023933 baseEnd_4023933 := by
    simpa [prefixWord, tailWord_4023933, baseEnd_4023933] using wordTrace_append hprefix tailTrace_4023933
  have hstable : (prefixWord ++ tailWord_4023933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4023933).length < 2 ^ (prefixWord ++ tailWord_4023933).sum := by decide
  have hdescent : baseEnd_4023933 < baseStart_4023933 := by decide
  rcases family_descends (prefixWord ++ tailWord_4023933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4023954 : List Nat := [3, 2, 3, 1, 4, 1, 2, 2, 5]
def baseStart_4023954 : Nat := 118140960795 + 4023954 * 2 ^ 59
def prefixEnd_4023954 : Nat := 4983230072969 + 3 ^ 40 * 4023954 * 2
def baseEnd_4023954 : Nat := 229580281509139388352131

theorem tailTrace_4023954 : CollatzResearch.WordTrace tailWord_4023954 prefixEnd_4023954 229580281509139388352131 := by
  unfold tailWord_4023954
  simp only [CollatzResearch.WordTrace]
  refine ⟨36691414915977342368651729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97843773109272912983071277 36691414915977342368651729)
  ·
    refine ⟨27518561186983006776488797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36691414915977342368651729 27518561186983006776488797)
    ·
      refine ⟨10319460445118627541183299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27518561186983006776488797 10319460445118627541183299)
      ·
        refine ⟨15479190667677941311774949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10319460445118627541183299 15479190667677941311774949)
        ·
          refine ⟨2902348250189613995957803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15479190667677941311774949 2902348250189613995957803)
          ·
            refine ⟨4353522375284420993936705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2902348250189613995957803 4353522375284420993936705)
            ·
              refine ⟨3265141781463315745452529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4353522375284420993936705 3265141781463315745452529)
              ·
                refine ⟨2448856336097486809089397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3265141781463315745452529 2448856336097486809089397)
                ·
                  refine ⟨229580281509139388352131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2448856336097486809089397 229580281509139388352131)
                  ·
                    rfl

theorem cell23_4023954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 2, 2, 5].length) (baseStart_4023954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4023954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4023954 prefixEnd_4023954 := by exact prefixLift 4023954
  have htrace : WordTrace (prefixWord ++ tailWord_4023954) baseStart_4023954 baseEnd_4023954 := by
    simpa [prefixWord, tailWord_4023954, baseEnd_4023954] using wordTrace_append hprefix tailTrace_4023954
  have hstable : (prefixWord ++ tailWord_4023954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4023954).length < 2 ^ (prefixWord ++ tailWord_4023954).sum := by decide
  have hdescent : baseEnd_4023954 < baseStart_4023954 := by decide
  rcases family_descends (prefixWord ++ tailWord_4023954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4024010 : List Nat := [3, 1, 2, 1, 5, 2, 1, 2, 6]
def baseStart_4024010 : Nat := 118140960795 + 4024010 * 2 ^ 59
def prefixEnd_4024010 : Nat := 4983230072969 + 3 ^ 40 * 4024010 * 2
def baseEnd_4024010 : Nat := 229583476499878475118769

theorem tailTrace_4024010 : CollatzResearch.WordTrace tailWord_4024010 prefixEnd_4024010 229583476499878475118769 := by
  unfold tailWord_4024010
  simp only [CollatzResearch.WordTrace]
  refine ⟨36691925537926622759661371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97845134767804327359096989 36691925537926622759661371)
  ·
    refine ⟨55037888306889934139492057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36691925537926622759661371 55037888306889934139492057)
    ·
      refine ⟨41278416230167450604619043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55037888306889934139492057 41278416230167450604619043)
      ·
        refine ⟨61917624345251175906928565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41278416230167450604619043 61917624345251175906928565)
        ·
          refine ⟨5804777282367297741274553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 61917624345251175906928565 5804777282367297741274553)
          ·
            refine ⟨4353582961775473305955915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5804777282367297741274553 4353582961775473305955915)
            ·
              refine ⟨6530374442663209958933873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4353582961775473305955915 6530374442663209958933873)
              ·
                refine ⟨4897780831997407469200405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6530374442663209958933873 4897780831997407469200405)
                ·
                  refine ⟨229583476499878475118769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4897780831997407469200405 229583476499878475118769)
                  ·
                    rfl

theorem cell23_4024010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 1, 2, 6].length) (baseStart_4024010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4024010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4024010 prefixEnd_4024010 := by exact prefixLift 4024010
  have htrace : WordTrace (prefixWord ++ tailWord_4024010) baseStart_4024010 baseEnd_4024010 := by
    simpa [prefixWord, tailWord_4024010, baseEnd_4024010] using wordTrace_append hprefix tailTrace_4024010
  have hstable : (prefixWord ++ tailWord_4024010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4024010).length < 2 ^ (prefixWord ++ tailWord_4024010).sum := by decide
  have hdescent : baseEnd_4024010 < baseStart_4024010 := by decide
  rcases family_descends (prefixWord ++ tailWord_4024010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4024040 : List Nat := [2, 1, 4, 1, 3, 2, 2, 2, 1, 5]
def baseStart_4024040 : Nat := 118140960795 + 4024040 * 2 ^ 59
def prefixEnd_4024040 : Nat := 4983230072969 + 3 ^ 40 * 4024040 * 2
def baseEnd_4024040 : Nat := 688755564306180386231261

theorem tailTrace_4024040 : CollatzResearch.WordTrace tailWord_4024040 prefixEnd_4024040 688755564306180386231261 := by
  unfold tailWord_4024040
  simp only [CollatzResearch.WordTrace]
  refine ⟨73384398170798903081118787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97845864227731870774825049 73384398170798903081118787)
  ·
    refine ⟨110076597256198354621678181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73384398170798903081118787 110076597256198354621678181)
    ·
      refine ⟨20639361985537191491564659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110076597256198354621678181 20639361985537191491564659)
      ·
        refine ⟨30959042978305787237346989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20639361985537191491564659 30959042978305787237346989)
        ·
          refine ⟨11609641116864670214005121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30959042978305787237346989 11609641116864670214005121)
          ·
            refine ⟨8707230837648502660503841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11609641116864670214005121 8707230837648502660503841)
            ·
              refine ⟨6530423128236376995377881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8707230837648502660503841 6530423128236376995377881)
              ·
                refine ⟨4897817346177282746533411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6530423128236376995377881 4897817346177282746533411)
                ·
                  refine ⟨7346726019265924119800117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4897817346177282746533411 7346726019265924119800117)
                  ·
                    refine ⟨688755564306180386231261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7346726019265924119800117 688755564306180386231261)
                    ·
                      rfl

theorem cell23_4024040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 2, 2, 1, 5].length) (baseStart_4024040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4024040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4024040 prefixEnd_4024040 := by exact prefixLift 4024040
  have htrace : WordTrace (prefixWord ++ tailWord_4024040) baseStart_4024040 baseEnd_4024040 := by
    simpa [prefixWord, tailWord_4024040, baseEnd_4024040] using wordTrace_append hprefix tailTrace_4024040
  have hstable : (prefixWord ++ tailWord_4024040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4024040).length < 2 ^ (prefixWord ++ tailWord_4024040).sum := by decide
  have hdescent : baseEnd_4024040 < baseStart_4024040 := by decide
  rcases family_descends (prefixWord ++ tailWord_4024040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4024043 : List Nat := [1, 1, 1, 1, 2, 4, 3, 4, 1, 1, 4]
def baseStart_4024043 : Nat := 118140960795 + 4024043 * 2 ^ 59
def prefixEnd_4024043 : Nat := 4983230072969 + 3 ^ 40 * 4024043 * 2
def baseEnd_4024043 : Nat := 2066268233360504646956269

theorem tailTrace_4024043 : CollatzResearch.WordTrace tailWord_4024043 prefixEnd_4024043 2066268233360504646956269 := by
  unfold tailWord_4024043
  simp only [CollatzResearch.WordTrace]
  refine ⟨146768905760586937674596783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97845937173724625116397855 146768905760586937674596783)
  ·
    refine ⟨220153358640880406511895175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146768905760586937674596783 220153358640880406511895175)
    ·
      refine ⟨330230037961320609767842763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220153358640880406511895175 330230037961320609767842763)
      ·
        refine ⟨495345056941980914651764145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330230037961320609767842763 495345056941980914651764145)
        ·
          refine ⟨371508792706485685988823109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 495345056941980914651764145 371508792706485685988823109)
          ·
            refine ⟨69657898632466066122904333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 371508792706485685988823109 69657898632466066122904333)
            ·
              refine ⟨26121711987174774796089125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69657898632466066122904333 26121711987174774796089125)
              ·
                refine ⟨4897820997595270274266711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26121711987174774796089125 4897820997595270274266711)
                ·
                  refine ⟨7346731496392905411400067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4897820997595270274266711 7346731496392905411400067)
                  ·
                    refine ⟨11020097244589358117100101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7346731496392905411400067 11020097244589358117100101)
                    ·
                      refine ⟨2066268233360504646956269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11020097244589358117100101 2066268233360504646956269)
                      ·
                        rfl

theorem cell23_4024043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 4, 1, 1, 4].length) (baseStart_4024043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4024043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4024043 prefixEnd_4024043 := by exact prefixLift 4024043
  have htrace : WordTrace (prefixWord ++ tailWord_4024043) baseStart_4024043 baseEnd_4024043 := by
    simpa [prefixWord, tailWord_4024043, baseEnd_4024043] using wordTrace_append hprefix tailTrace_4024043
  have hstable : (prefixWord ++ tailWord_4024043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4024043).length < 2 ^ (prefixWord ++ tailWord_4024043).sum := by decide
  have hdescent : baseEnd_4024043 < baseStart_4024043 := by decide
  rcases family_descends (prefixWord ++ tailWord_4024043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4024054 : List Nat := [5, 1, 1, 1, 1, 3, 3, 3, 1, 1, 3]
def baseStart_4024054 : Nat := 118140960795 + 4024054 * 2 ^ 59
def prefixEnd_4024054 : Nat := 4983230072969 + 3 ^ 40 * 4024054 * 2
def baseEnd_4024054 : Nat := 2066273881647704103918719

theorem tailTrace_4024054 : CollatzResearch.WordTrace tailWord_4024054 prefixEnd_4024054 2066273881647704103918719 := by
  unfold tailWord_4024054
  simp only [CollatzResearch.WordTrace]
  refine ⟨9173081685221692909577951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 97846204642364724368831477 9173081685221692909577951)
  ·
    refine ⟨13759622527832539364366927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9173081685221692909577951 13759622527832539364366927)
    ·
      refine ⟨20639433791748809046550391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13759622527832539364366927 20639433791748809046550391)
      ·
        refine ⟨30959150687623213569825587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20639433791748809046550391 30959150687623213569825587)
        ·
          refine ⟨46438726031434820354738381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30959150687623213569825587 46438726031434820354738381)
          ·
            refine ⟨17414522261788057633026893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46438726031434820354738381 17414522261788057633026893)
            ·
              refine ⟨6530445848170521612385085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17414522261788057633026893 6530445848170521612385085)
              ·
                refine ⟨2448917193063945604644407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6530445848170521612385085 2448917193063945604644407)
                ·
                  refine ⟨3673375789595918406966611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2448917193063945604644407 3673375789595918406966611)
                  ·
                    refine ⟨5510063684393877610449917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3673375789595918406966611 5510063684393877610449917)
                    ·
                      refine ⟨2066273881647704103918719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5510063684393877610449917 2066273881647704103918719)
                      ·
                        rfl

theorem cell23_4024054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 3, 3, 1, 1, 3].length) (baseStart_4024054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4024054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4024054 prefixEnd_4024054 := by exact prefixLift 4024054
  have htrace : WordTrace (prefixWord ++ tailWord_4024054) baseStart_4024054 baseEnd_4024054 := by
    simpa [prefixWord, tailWord_4024054, baseEnd_4024054] using wordTrace_append hprefix tailTrace_4024054
  have hstable : (prefixWord ++ tailWord_4024054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4024054).length < 2 ^ (prefixWord ++ tailWord_4024054).sum := by decide
  have hdescent : baseEnd_4024054 < baseStart_4024054 := by decide
  rcases family_descends (prefixWord ++ tailWord_4024054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4024071 : List Nat := [1, 1, 4, 4, 2, 1, 3, 2, 1, 1, 3]
def baseStart_4024071 : Nat := 118140960795 + 4024071 * 2 ^ 59
def prefixEnd_4024071 : Nat := 4983230072969 + 3 ^ 40 * 4024071 * 2
def baseEnd_4024071 : Nat := 2066282610818830537406141

theorem tailTrace_4024071 : CollatzResearch.WordTrace tailWord_4024071 prefixEnd_4024071 2066282610818830537406141 := by
  unfold tailWord_4024071
  simp only [CollatzResearch.WordTrace]
  refine ⟨146769927004485498456616067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97846618002990332304410711 146769927004485498456616067)
  ·
    refine ⟨220154890506728247684924101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146769927004485498456616067 220154890506728247684924101)
    ·
      refine ⟨41279041970011546440923269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 220154890506728247684924101 41279041970011546440923269)
      ·
        refine ⟨7739820369377164957673113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41279041970011546440923269 7739820369377164957673113)
        ·
          refine ⟨5804865277032873718254835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7739820369377164957673113 5804865277032873718254835)
          ·
            refine ⟨8707297915549310577382253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5804865277032873718254835 8707297915549310577382253)
            ·
              refine ⟨3265236718330991466518345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8707297915549310577382253 3265236718330991466518345)
              ·
                refine ⟨2448927538748243599888759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3265236718330991466518345 2448927538748243599888759)
                ·
                  refine ⟨3673391308122365399833139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2448927538748243599888759 3673391308122365399833139)
                  ·
                    refine ⟨5510086962183548099749709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3673391308122365399833139 5510086962183548099749709)
                    ·
                      refine ⟨2066282610818830537406141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5510086962183548099749709 2066282610818830537406141)
                      ·
                        rfl

theorem cell23_4024071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 3, 2, 1, 1, 3].length) (baseStart_4024071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4024071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4024071 prefixEnd_4024071 := by exact prefixLift 4024071
  have htrace : WordTrace (prefixWord ++ tailWord_4024071) baseStart_4024071 baseEnd_4024071 := by
    simpa [prefixWord, tailWord_4024071, baseEnd_4024071] using wordTrace_append hprefix tailTrace_4024071
  have hstable : (prefixWord ++ tailWord_4024071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4024071).length < 2 ^ (prefixWord ++ tailWord_4024071).sum := by decide
  have hdescent : baseEnd_4024071 < baseStart_4024071 := by decide
  rcases family_descends (prefixWord ++ tailWord_4024071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4024087 : List Nat := [1, 1, 3, 4, 2, 1, 4, 1, 2, 4]
def baseStart_4024087 : Nat := 118140960795 + 4024087 * 2 ^ 59
def prefixEnd_4024087 : Nat := 4983230072969 + 3 ^ 40 * 4024087 * 2
def baseEnd_4024087 : Nat := 688763608836434158268689

theorem tailTrace_4024087 : CollatzResearch.WordTrace tailWord_4024087 prefixEnd_4024087 688763608836434158268689 := by
  unfold tailWord_4024087
  simp only [CollatzResearch.WordTrace]
  refine ⟨146770510572427533189198515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97847007048285022126132343 146770510572427533189198515)
  ·
    refine ⟨220155765858641299783797773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146770510572427533189198515 220155765858641299783797773)
    ·
      refine ⟨82558412196990487418924165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220155765858641299783797773 82558412196990487418924165)
      ·
        refine ⟨15479702286935716391048281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82558412196990487418924165 15479702286935716391048281)
        ·
          refine ⟨11609776715201787293286211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15479702286935716391048281 11609776715201787293286211)
          ·
            refine ⟨17414665072802680939929317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11609776715201787293286211 17414665072802680939929317)
            ·
              refine ⟨3265249701150502676236747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17414665072802680939929317 3265249701150502676236747)
              ·
                refine ⟨4897874551725754014355121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3265249701150502676236747 4897874551725754014355121)
                ·
                  refine ⟨3673405913794315510766341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4897874551725754014355121 3673405913794315510766341)
                  ·
                    refine ⟨688763608836434158268689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3673405913794315510766341 688763608836434158268689)
                    ·
                      rfl

theorem cell23_4024087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 4, 1, 2, 4].length) (baseStart_4024087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4024087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4024087 prefixEnd_4024087 := by exact prefixLift 4024087
  have htrace : WordTrace (prefixWord ++ tailWord_4024087) baseStart_4024087 baseEnd_4024087 := by
    simpa [prefixWord, tailWord_4024087, baseEnd_4024087] using wordTrace_append hprefix tailTrace_4024087
  have hstable : (prefixWord ++ tailWord_4024087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4024087).length < 2 ^ (prefixWord ++ tailWord_4024087).sum := by decide
  have hdescent : baseEnd_4024087 < baseStart_4024087 := by decide
  rcases family_descends (prefixWord ++ tailWord_4024087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4024094 : List Nat := [4, 3, 2, 2, 1, 1, 1, 1, 3, 1, 4]
def baseStart_4024094 : Nat := 118140960795 + 4024094 * 2 ^ 59
def prefixEnd_4024094 : Nat := 4983230072969 + 3 ^ 40 * 4024094 * 2
def baseEnd_4024094 : Nat := 2066294420873883947418535

theorem tailTrace_4024094 : CollatzResearch.WordTrace tailWord_4024094 prefixEnd_4024094 2066294420873883947418535 := by
  unfold tailWord_4024094
  simp only [CollatzResearch.WordTrace]
  refine ⟨18346345735425271673087917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97847177255601448923135557 18346345735425271673087917)
  ·
    refine ⟨6879879650784476877407969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18346345735425271673087917 6879879650784476877407969)
    ·
      refine ⟨5159909738088357658055977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6879879650784476877407969 5159909738088357658055977)
      ·
        refine ⟨3869932303566268243541983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5159909738088357658055977 3869932303566268243541983)
        ·
          refine ⟨5804898455349402365312975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3869932303566268243541983 5804898455349402365312975)
          ·
            refine ⟨8707347683024103547969463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5804898455349402365312975 8707347683024103547969463)
            ·
              refine ⟨13061021524536155321954195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8707347683024103547969463 13061021524536155321954195)
              ·
                refine ⟨19591532286804232982931293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13061021524536155321954195 19591532286804232982931293)
                ·
                  refine ⟨7346824607551587368599235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19591532286804232982931293 7346824607551587368599235)
                  ·
                    refine ⟨11020236911327381052898853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7346824607551587368599235 11020236911327381052898853)
                    ·
                      refine ⟨2066294420873883947418535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11020236911327381052898853 2066294420873883947418535)
                      ·
                        rfl

theorem cell23_4024094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_4024094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4024094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4024094 prefixEnd_4024094 := by exact prefixLift 4024094
  have htrace : WordTrace (prefixWord ++ tailWord_4024094) baseStart_4024094 baseEnd_4024094 := by
    simpa [prefixWord, tailWord_4024094, baseEnd_4024094] using wordTrace_append hprefix tailTrace_4024094
  have hstable : (prefixWord ++ tailWord_4024094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4024094).length < 2 ^ (prefixWord ++ tailWord_4024094).sum := by decide
  have hdescent : baseEnd_4024094 < baseStart_4024094 := by decide
  rcases family_descends (prefixWord ++ tailWord_4024094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4024097 : List Nat := [1, 2, 3, 2, 1, 5, 1, 2, 1, 2, 3]
def baseStart_4024097 : Nat := 118140960795 + 4024097 * 2 ^ 59
def prefixEnd_4024097 : Nat := 4983230072969 + 3 ^ 40 * 4024097 * 2
def baseEnd_4024097 : Nat := 2066295961315847435681021

theorem tailTrace_4024097 : CollatzResearch.WordTrace tailWord_4024097 prefixEnd_4024097 2066295961315847435681021 := by
  unfold tailWord_4024097
  simp only [CollatzResearch.WordTrace]
  refine ⟨146770875302391304897062545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97847250201594203264708363 146770875302391304897062545)
  ·
    refine ⟨110078156476793478672796909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146770875302391304897062545 110078156476793478672796909)
    ·
      refine ⟨41279308678797554502298841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110078156476793478672796909 41279308678797554502298841)
      ·
        refine ⟨30959481509098165876724131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41279308678797554502298841 30959481509098165876724131)
        ·
          refine ⟨46439222263647248815086197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30959481509098165876724131 46439222263647248815086197)
          ·
            refine ⟨4353677087216929576414331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 46439222263647248815086197 4353677087216929576414331)
            ·
              refine ⟨6530515630825394364621497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4353677087216929576414331 6530515630825394364621497)
              ·
                refine ⟨4897886723119045773466123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6530515630825394364621497 4897886723119045773466123)
                ·
                  refine ⟨7346830084678568660199185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4897886723119045773466123 7346830084678568660199185)
                  ·
                    refine ⟨5510122563508926495149389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7346830084678568660199185 5510122563508926495149389)
                    ·
                      refine ⟨2066295961315847435681021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5510122563508926495149389 2066295961315847435681021)
                      ·
                        rfl

theorem cell23_4024097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 1, 2, 1, 2, 3].length) (baseStart_4024097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4024097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4024097 prefixEnd_4024097 := by exact prefixLift 4024097
  have htrace : WordTrace (prefixWord ++ tailWord_4024097) baseStart_4024097 baseEnd_4024097 := by
    simpa [prefixWord, tailWord_4024097, baseEnd_4024097] using wordTrace_append hprefix tailTrace_4024097
  have hstable : (prefixWord ++ tailWord_4024097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4024097).length < 2 ^ (prefixWord ++ tailWord_4024097).sum := by decide
  have hdescent : baseEnd_4024097 < baseStart_4024097 := by decide
  rcases family_descends (prefixWord ++ tailWord_4024097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4024153 : List Nat := [1, 2, 1, 2, 2, 3, 1, 2, 2, 4, 3]
def baseStart_4024153 : Nat := 118140960795 + 4024153 * 2 ^ 59
def prefixEnd_4024153 : Nat := 4983230072969 + 3 ^ 40 * 4024153 * 2
def baseEnd_4024153 : Nat := 2066324716232499216580763

theorem tailTrace_4024153 : CollatzResearch.WordTrace tailWord_4024153 prefixEnd_4024153 2066324716232499216580763 := by
  unfold tailWord_4024153
  simp only [CollatzResearch.WordTrace]
  refine ⟨146772917790188426461101113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97848611860125617640734075 146772917790188426461101113)
  ·
    refine ⟨110079688342641319845825835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146772917790188426461101113 110079688342641319845825835)
    ·
      refine ⟨165119532513961979768738753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110079688342641319845825835 165119532513961979768738753)
      ·
        refine ⟨123839649385471484826554065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165119532513961979768738753 123839649385471484826554065)
        ·
          refine ⟨92879737039103613619915549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123839649385471484826554065 92879737039103613619915549)
          ·
            refine ⟨34829901389663855107468331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92879737039103613619915549 34829901389663855107468331)
            ·
              refine ⟨52244852084495782661202497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34829901389663855107468331 52244852084495782661202497)
              ·
                refine ⟨39183639063371836995901873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52244852084495782661202497 39183639063371836995901873)
                ·
                  refine ⟨29387729297528877746926405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39183639063371836995901873 29387729297528877746926405)
                  ·
                    refine ⟨5510199243286664577548701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29387729297528877746926405 5510199243286664577548701)
                    ·
                      refine ⟨2066324716232499216580763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5510199243286664577548701 2066324716232499216580763)
                      ·
                        rfl

theorem cell23_4024153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 4, 3].length) (baseStart_4024153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4024153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4024153 prefixEnd_4024153 := by exact prefixLift 4024153
  have htrace : WordTrace (prefixWord ++ tailWord_4024153) baseStart_4024153 baseEnd_4024153 := by
    simpa [prefixWord, tailWord_4024153, baseEnd_4024153] using wordTrace_append hprefix tailTrace_4024153
  have hstable : (prefixWord ++ tailWord_4024153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4024153).length < 2 ^ (prefixWord ++ tailWord_4024153).sum := by decide
  have hdescent : baseEnd_4024153 < baseStart_4024153 := by decide
  rcases family_descends (prefixWord ++ tailWord_4024153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4024167 : List Nat := [1, 1, 5, 1, 2, 1, 2, 2, 4, 2, 2]
def baseStart_4024167 : Nat := 118140960795 + 4024167 * 2 ^ 59
def prefixEnd_4024167 : Nat := 4983230072969 + 3 ^ 40 * 4024167 * 2
def baseEnd_4024167 : Nat := 2066331904961662161805699

theorem tailTrace_4024167 : CollatzResearch.WordTrace tailWord_4024167 prefixEnd_4024167 2066331904961662161805699 := by
  unfold tailWord_4024167
  simp only [CollatzResearch.WordTrace]
  refine ⟨146773428412137706852110755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97848952274758471234740503 146773428412137706852110755)
  ·
    refine ⟨220160142618206560278166133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146773428412137706852110755 220160142618206560278166133)
    ·
      refine ⟨20640013370456865026078075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 220160142618206560278166133 20640013370456865026078075)
      ·
        refine ⟨30960020055685297539117113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20640013370456865026078075 30960020055685297539117113)
        ·
          refine ⟨23220015041763973154337835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30960020055685297539117113 23220015041763973154337835)
          ·
            refine ⟨34830022562645959731506753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23220015041763973154337835 34830022562645959731506753)
            ·
              refine ⟨26122516921984469798630065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34830022562645959731506753 26122516921984469798630065)
              ·
                refine ⟨19591887691488352348972549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26122516921984469798630065 19591887691488352348972549)
                ·
                  refine ⟨3673478942154066065432353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19591887691488352348972549 3673478942154066065432353)
                  ·
                    refine ⟨2755109206615549549074265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3673478942154066065432353 2755109206615549549074265)
                    ·
                      refine ⟨2066331904961662161805699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2755109206615549549074265 2066331904961662161805699)
                      ·
                        rfl

theorem cell23_4024167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 2, 4, 2, 2].length) (baseStart_4024167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4024167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4024167 prefixEnd_4024167 := by exact prefixLift 4024167
  have htrace : WordTrace (prefixWord ++ tailWord_4024167) baseStart_4024167 baseEnd_4024167 := by
    simpa [prefixWord, tailWord_4024167, baseEnd_4024167] using wordTrace_append hprefix tailTrace_4024167
  have hstable : (prefixWord ++ tailWord_4024167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4024167).length < 2 ^ (prefixWord ++ tailWord_4024167).sum := by decide
  have hdescent : baseEnd_4024167 < baseStart_4024167 := by decide
  rcases family_descends (prefixWord ++ tailWord_4024167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4024220 : List Nat := [2, 2, 3, 3, 1, 1, 2, 1, 1, 7]
def baseStart_4024220 : Nat := 118140960795 + 4024220 * 2 ^ 59
def prefixEnd_4024220 : Nat := 4983230072969 + 3 ^ 40 * 4024220 * 2
def baseEnd_4024220 : Nat := 688786373145450151480985

theorem tailTrace_4024220 : CollatzResearch.WordTrace tailWord_4024220 prefixEnd_4024220 688786373145450151480985 := by
  unfold tailWord_4024220
  simp only [CollatzResearch.WordTrace]
  refine ⟨73387680740472848451895057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97850240987297131269193409 73387680740472848451895057)
  ·
    refine ⟨55040760555354636338921293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73387680740472848451895057 55040760555354636338921293)
    ·
      refine ⟨20640285208257988627095485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55040760555354636338921293 20640285208257988627095485)
      ·
        refine ⟨7740106953096745735160807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20640285208257988627095485 7740106953096745735160807)
        ·
          refine ⟨11610160429645118602741211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7740106953096745735160807 11610160429645118602741211)
          ·
            refine ⟨17415240644467677904111817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11610160429645118602741211 17415240644467677904111817)
            ·
              refine ⟨13061430483350758428083863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17415240644467677904111817 13061430483350758428083863)
              ·
                refine ⟨19592145725026137642125795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13061430483350758428083863 19592145725026137642125795)
                ·
                  refine ⟨29388218587539206463188693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19592145725026137642125795 29388218587539206463188693)
                  ·
                    refine ⟨688786373145450151480985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29388218587539206463188693 688786373145450151480985)
                    ·
                      rfl

theorem cell23_4024220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 1, 1, 7].length) (baseStart_4024220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4024220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4024220 prefixEnd_4024220 := by exact prefixLift 4024220
  have htrace : WordTrace (prefixWord ++ tailWord_4024220) baseStart_4024220 baseEnd_4024220 := by
    simpa [prefixWord, tailWord_4024220, baseEnd_4024220] using wordTrace_append hprefix tailTrace_4024220
  have hstable : (prefixWord ++ tailWord_4024220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4024220).length < 2 ^ (prefixWord ++ tailWord_4024220).sum := by decide
  have hdescent : baseEnd_4024220 < baseStart_4024220 := by decide
  rcases family_descends (prefixWord ++ tailWord_4024220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4024250 : List Nat := [3, 1, 1, 1, 2, 1, 2, 5, 3, 4]
def baseStart_4024250 : Nat := 118140960795 + 4024250 * 2 ^ 59
def prefixEnd_4024250 : Nat := 4983230072969 + 3 ^ 40 * 4024250 * 2
def baseEnd_4024250 : Nat := 688791507951995112355939

theorem tailTrace_4024250 : CollatzResearch.WordTrace tailWord_4024250 prefixEnd_4024250 688791507951995112355939 := by
  unfold tailWord_4024250
  simp only [CollatzResearch.WordTrace]
  refine ⟨36694113917709253006845551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97850970447224674684921469 36694113917709253006845551)
  ·
    refine ⟨55041170876563879510268327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36694113917709253006845551 55041170876563879510268327)
    ·
      refine ⟨82561756314845819265402491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55041170876563879510268327 82561756314845819265402491)
      ·
        refine ⟨123842634472268728898103737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82561756314845819265402491 123842634472268728898103737)
        ·
          refine ⟨92881975854201546673577803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123842634472268728898103737 92881975854201546673577803)
          ·
            refine ⟨139322963781302320010366705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92881975854201546673577803 139322963781302320010366705)
            ·
              refine ⟨104492222835976740007775029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139322963781302320010366705 104492222835976740007775029)
              ·
                refine ⟨9796145890872819375728909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 104492222835976740007775029 9796145890872819375728909)
                ·
                  refine ⟨3673554709077307265898341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9796145890872819375728909 3673554709077307265898341)
                  ·
                    refine ⟨688791507951995112355939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3673554709077307265898341 688791507951995112355939)
                    ·
                      rfl

theorem cell23_4024250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 5, 3, 4].length) (baseStart_4024250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4024250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4024250 prefixEnd_4024250 := by exact prefixLift 4024250
  have htrace : WordTrace (prefixWord ++ tailWord_4024250) baseStart_4024250 baseEnd_4024250 := by
    simpa [prefixWord, tailWord_4024250, baseEnd_4024250] using wordTrace_append hprefix tailTrace_4024250
  have hstable : (prefixWord ++ tailWord_4024250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4024250).length < 2 ^ (prefixWord ++ tailWord_4024250).sum := by decide
  have hdescent : baseEnd_4024250 < baseStart_4024250 := by decide
  rcases family_descends (prefixWord ++ tailWord_4024250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4024274 : List Nat := [3, 2, 2, 3, 2, 1, 2, 1, 2, 1, 4]
def baseStart_4024274 : Nat := 118140960795 + 4024274 * 2 ^ 59
def prefixEnd_4024274 : Nat := 4983230072969 + 3 ^ 40 * 4024274 * 2
def baseEnd_4024274 : Nat := 2066386847391693243167707

theorem tailTrace_4024274 : CollatzResearch.WordTrace tailWord_4024274 prefixEnd_4024274 2066386847391693243167707 := by
  unfold tailWord_4024274
  simp only [CollatzResearch.WordTrace]
  refine ⟨36694332755687516031563969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97851554015166709417503917 36694332755687516031563969)
  ·
    refine ⟨27520749566765637023672977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36694332755687516031563969 27520749566765637023672977)
    ·
      refine ⟨20640562175074227767754733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27520749566765637023672977 20640562175074227767754733)
      ·
        refine ⟨7740210815652835412908025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20640562175074227767754733 7740210815652835412908025)
        ·
          refine ⟨5805158111739626559681019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7740210815652835412908025 5805158111739626559681019)
          ·
            refine ⟨8707737167609439839521529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5805158111739626559681019 8707737167609439839521529)
            ·
              refine ⟨6530802875707079879641147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8707737167609439839521529 6530802875707079879641147)
              ·
                refine ⟨9796204313560619819461721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6530802875707079879641147 9796204313560619819461721)
                ·
                  refine ⟨7347153235170464864596291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9796204313560619819461721 7347153235170464864596291)
                  ·
                    refine ⟨11020729852755697296894437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7347153235170464864596291 11020729852755697296894437)
                    ·
                      refine ⟨2066386847391693243167707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11020729852755697296894437 2066386847391693243167707)
                      ·
                        rfl

theorem cell23_4024274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_4024274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4024274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4024274 prefixEnd_4024274 := by exact prefixLift 4024274
  have htrace : WordTrace (prefixWord ++ tailWord_4024274) baseStart_4024274 baseEnd_4024274 := by
    simpa [prefixWord, tailWord_4024274, baseEnd_4024274] using wordTrace_append hprefix tailTrace_4024274
  have hstable : (prefixWord ++ tailWord_4024274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4024274).length < 2 ^ (prefixWord ++ tailWord_4024274).sum := by decide
  have hdescent : baseEnd_4024274 < baseStart_4024274 := by decide
  rcases family_descends (prefixWord ++ tailWord_4024274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4024277 : List Nat := [1, 3, 2, 3, 2, 1, 1, 3, 2, 2, 3]
def baseStart_4024277 : Nat := 118140960795 + 4024277 * 2 ^ 59
def prefixEnd_4024277 : Nat := 4983230072969 + 3 ^ 40 * 4024277 * 2
def baseEnd_4024277 : Nat := 2066388387833656731430193

theorem tailTrace_4024277 : CollatzResearch.WordTrace tailWord_4024277 prefixEnd_4024277 2066388387833656731430193 := by
  unfold tailWord_4024277
  simp only [CollatzResearch.WordTrace]
  refine ⟨146777440441739195638615085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97851626961159463759076723 146777440441739195638615085)
  ·
    refine ⟨55041540165652198364480657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146777440441739195638615085 55041540165652198364480657)
    ·
      refine ⟨41281155124239148773360493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55041540165652198364480657 41281155124239148773360493)
      ·
        refine ⟨15480433171589680790010185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41281155124239148773360493 15480433171589680790010185)
        ·
          refine ⟨11610324878692260592507639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15480433171589680790010185 11610324878692260592507639)
          ·
            refine ⟨17415487318038390888761459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11610324878692260592507639 17415487318038390888761459)
            ·
              refine ⟨26123230977057586333142189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17415487318038390888761459 26123230977057586333142189)
              ·
                refine ⟨9796211616396594874928321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26123230977057586333142189 9796211616396594874928321)
                ·
                  refine ⟨7347158712297446156196241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9796211616396594874928321 7347158712297446156196241)
                  ·
                    refine ⟨5510369034223084617147181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7347158712297446156196241 5510369034223084617147181)
                    ·
                      refine ⟨2066388387833656731430193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5510369034223084617147181 2066388387833656731430193)
                      ·
                        rfl

theorem cell23_4024277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 3, 2, 2, 3].length) (baseStart_4024277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4024277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4024277 prefixEnd_4024277 := by exact prefixLift 4024277
  have htrace : WordTrace (prefixWord ++ tailWord_4024277) baseStart_4024277 baseEnd_4024277 := by
    simpa [prefixWord, tailWord_4024277, baseEnd_4024277] using wordTrace_append hprefix tailTrace_4024277
  have hstable : (prefixWord ++ tailWord_4024277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4024277).length < 2 ^ (prefixWord ++ tailWord_4024277).sum := by decide
  have hdescent : baseEnd_4024277 < baseStart_4024277 := by decide
  rcases family_descends (prefixWord ++ tailWord_4024277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4024317 : List Nat := [1, 4, 1, 1, 1, 2, 2, 2, 4, 3, 2]
def baseStart_4024317 : Nat := 118140960795 + 4024317 * 2 ^ 59
def prefixEnd_4024317 : Nat := 4983230072969 + 3 ^ 40 * 4024317 * 2
def baseEnd_4024317 : Nat := 2066408927059836574930009

theorem tailTrace_4024317 : CollatzResearch.WordTrace tailWord_4024317 prefixEnd_4024317 2066408927059836574930009 := by
  unfold tailWord_4024317
  simp only [CollatzResearch.WordTrace]
  refine ⟨146778899361594282470071205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97852599574396188313380803 146778899361594282470071205)
  ·
    refine ⟨27521043630298927963138351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146778899361594282470071205 27521043630298927963138351)
    ·
      refine ⟨41281565445448391944707527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27521043630298927963138351 41281565445448391944707527)
      ·
        refine ⟨61922348168172587917061291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41281565445448391944707527 61922348168172587917061291)
        ·
          refine ⟨92883522252258881875591937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61922348168172587917061291 92883522252258881875591937)
          ·
            refine ⟨69662641689194161406693953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92883522252258881875591937 69662641689194161406693953)
            ·
              refine ⟨52246981266895621055020465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69662641689194161406693953 52246981266895621055020465)
              ·
                refine ⟨39185235950171715791265349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52246981266895621055020465 39185235950171715791265349)
                ·
                  refine ⟨7347231740657196710862253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39185235950171715791265349 7347231740657196710862253)
                  ·
                    refine ⟨2755211902746448766573345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7347231740657196710862253 2755211902746448766573345)
                    ·
                      refine ⟨2066408927059836574930009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2755211902746448766573345 2066408927059836574930009)
                      ·
                        rfl

theorem cell23_4024317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 2, 4, 3, 2].length) (baseStart_4024317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4024317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4024317 prefixEnd_4024317 := by exact prefixLift 4024317
  have htrace : WordTrace (prefixWord ++ tailWord_4024317) baseStart_4024317 baseEnd_4024317 := by
    simpa [prefixWord, tailWord_4024317, baseEnd_4024317] using wordTrace_append hprefix tailTrace_4024317
  have hstable : (prefixWord ++ tailWord_4024317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4024317).length < 2 ^ (prefixWord ++ tailWord_4024317).sum := by decide
  have hdescent : baseEnd_4024317 < baseStart_4024317 := by decide
  rcases family_descends (prefixWord ++ tailWord_4024317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4024357 : List Nat := [1, 3, 1, 2, 2, 4, 1, 1, 4, 4]
def baseStart_4024357 : Nat := 118140960795 + 4024357 * 2 ^ 59
def prefixEnd_4024357 : Nat := 4983230072969 + 3 ^ 40 * 4024357 * 2
def baseEnd_4024357 : Nat := 688809822095338806143275

theorem tailTrace_4024357 : CollatzResearch.WordTrace tailWord_4024357 prefixEnd_4024357 688809822095338806143275 := by
  unfold tailWord_4024357
  simp only [CollatzResearch.WordTrace]
  refine ⟨146780358281449369301527325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97853572187632912867684883 146780358281449369301527325)
  ·
    refine ⟨55042634355543513488072747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146780358281449369301527325 55042634355543513488072747)
    ·
      refine ⟨82563951533315270232109121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55042634355543513488072747 82563951533315270232109121)
      ·
        refine ⟨61922963649986452674081841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82563951533315270232109121 61922963649986452674081841)
        ·
          refine ⟨46442222737489839505561381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61922963649986452674081841 46442222737489839505561381)
          ·
            refine ⟨8707916763279344907292759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46442222737489839505561381 8707916763279344907292759)
            ·
              refine ⟨13061875144919017360939139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8707916763279344907292759 13061875144919017360939139)
              ·
                refine ⟨19592812717378526041408709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13061875144919017360939139 19592812717378526041408709)
                ·
                  refine ⟨3673652384508473632764133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19592812717378526041408709 3673652384508473632764133)
                  ·
                    refine ⟨688809822095338806143275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3673652384508473632764133 688809822095338806143275)
                    ·
                      rfl

theorem cell23_4024357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 1, 4, 4].length) (baseStart_4024357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4024357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4024357 prefixEnd_4024357 := by exact prefixLift 4024357
  have htrace : WordTrace (prefixWord ++ tailWord_4024357) baseStart_4024357 baseEnd_4024357 := by
    simpa [prefixWord, tailWord_4024357, baseEnd_4024357] using wordTrace_append hprefix tailTrace_4024357
  have hstable : (prefixWord ++ tailWord_4024357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4024357).length < 2 ^ (prefixWord ++ tailWord_4024357).sum := by decide
  have hdescent : baseEnd_4024357 < baseStart_4024357 := by decide
  rcases family_descends (prefixWord ++ tailWord_4024357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4024377 : List Nat := [1, 2, 1, 5, 3, 1, 1, 1, 1, 1, 6]
def baseStart_4024377 : Nat := 118140960795 + 4024377 * 2 ^ 59
def prefixEnd_4024377 : Nat := 4983230072969 + 3 ^ 40 * 4024377 * 2
def baseEnd_4024377 : Nat := 2066439735899106340179733

theorem tailTrace_4024377 : CollatzResearch.WordTrace tailWord_4024377 prefixEnd_4024377 2066439735899106340179733 := by
  unfold tailWord_4024377
  simp only [CollatzResearch.WordTrace]
  refine ⟨146781087741376912717255385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97854058494251275144836923 146781087741376912717255385)
  ·
    refine ⟨110085815806032684537941539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146781087741376912717255385 110085815806032684537941539)
    ·
      refine ⟨165128723709049026806912309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110085815806032684537941539 165128723709049026806912309)
      ·
        refine ⟨15480817847723346263148029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 165128723709049026806912309 15480817847723346263148029)
        ·
          refine ⟨5805306692896254848680511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15480817847723346263148029 5805306692896254848680511)
          ·
            refine ⟨8707960039344382273020767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5805306692896254848680511 8707960039344382273020767)
            ·
              refine ⟨13061940059016573409531151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8707960039344382273020767 13061940059016573409531151)
              ·
                refine ⟨19592910088524860114296727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13061940059016573409531151 19592910088524860114296727)
                ·
                  refine ⟨29389365132787290171445091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19592910088524860114296727 29389365132787290171445091)
                  ·
                    refine ⟨44084047699180935257167637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29389365132787290171445091 44084047699180935257167637)
                    ·
                      refine ⟨2066439735899106340179733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44084047699180935257167637 2066439735899106340179733)
                      ·
                        rfl

theorem cell23_4024377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 1, 1, 1, 6].length) (baseStart_4024377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4024377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4024377 prefixEnd_4024377 := by exact prefixLift 4024377
  have htrace : WordTrace (prefixWord ++ tailWord_4024377) baseStart_4024377 baseEnd_4024377 := by
    simpa [prefixWord, tailWord_4024377, baseEnd_4024377] using wordTrace_append hprefix tailTrace_4024377
  have hstable : (prefixWord ++ tailWord_4024377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4024377).length < 2 ^ (prefixWord ++ tailWord_4024377).sum := by decide
  have hdescent : baseEnd_4024377 < baseStart_4024377 := by decide
  rcases family_descends (prefixWord ++ tailWord_4024377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4024384 : List Nat := [2, 1, 1, 2, 2, 5, 2, 2, 1, 2, 3]
def baseStart_4024384 : Nat := 118140960795 + 4024384 * 2 ^ 59
def prefixEnd_4024384 : Nat := 4983230072969 + 3 ^ 40 * 4024384 * 2
def baseEnd_4024384 : Nat := 2066443330263687812792201

theorem tailTrace_4024384 : CollatzResearch.WordTrace tailWord_4024384 prefixEnd_4024384 2066443330263687812792201 := by
  unfold tailWord_4024384
  simp only [CollatzResearch.WordTrace]
  refine ⟨73390671526175776456380103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97854228701567701941840137 73390671526175776456380103)
  ·
    refine ⟨110086007289263664684570155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73390671526175776456380103 110086007289263664684570155)
    ·
      refine ⟨165129010933895497026855233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110086007289263664684570155 165129010933895497026855233)
      ·
        refine ⟨123846758200421622770141425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165129010933895497026855233 123846758200421622770141425)
        ·
          refine ⟨92885068650316217077606069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123846758200421622770141425 92885068650316217077606069)
          ·
            refine ⟨8707975185967145351025569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 92885068650316217077606069 8707975185967145351025569)
            ·
              refine ⟨6530981389475359013269177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8707975185967145351025569 6530981389475359013269177)
              ·
                refine ⟨4898236042106519259951883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6530981389475359013269177 4898236042106519259951883)
                ·
                  refine ⟨7347354063159778889927825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4898236042106519259951883 7347354063159778889927825)
                  ·
                    refine ⟨5510515547369834167445869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7347354063159778889927825 5510515547369834167445869)
                    ·
                      refine ⟨2066443330263687812792201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5510515547369834167445869 2066443330263687812792201)
                      ·
                        rfl

theorem cell23_4024384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 2, 2, 1, 2, 3].length) (baseStart_4024384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4024384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4024384 prefixEnd_4024384 := by exact prefixLift 4024384
  have htrace : WordTrace (prefixWord ++ tailWord_4024384) baseStart_4024384 baseEnd_4024384 := by
    simpa [prefixWord, tailWord_4024384, baseEnd_4024384] using wordTrace_append hprefix tailTrace_4024384
  have hstable : (prefixWord ++ tailWord_4024384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4024384).length < 2 ^ (prefixWord ++ tailWord_4024384).sum := by decide
  have hdescent : baseEnd_4024384 < baseStart_4024384 := by decide
  rcases family_descends (prefixWord ++ tailWord_4024384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4024398 : List Nat := [4, 1, 1, 1, 1, 4, 3, 3, 1, 2, 2]
def baseStart_4024398 : Nat := 118140960795 + 4024398 * 2 ^ 59
def prefixEnd_4024398 : Nat := 4983230072969 + 3 ^ 40 * 4024398 * 2
def baseEnd_4024398 : Nat := 2066450518992850758017137

theorem tailTrace_4024398 : CollatzResearch.WordTrace tailWord_4024398 prefixEnd_4024398 2066450518992850758017137 := by
  unfold tailWord_4024398
  simp only [CollatzResearch.WordTrace]
  refine ⟨18347731709287604162971231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97854569116200555535846565 18347731709287604162971231)
  ·
    refine ⟨27521597563931406244456847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18347731709287604162971231 27521597563931406244456847)
    ·
      refine ⟨41282396345897109366685271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27521597563931406244456847 41282396345897109366685271)
      ·
        refine ⟨61923594518845664050027907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41282396345897109366685271 61923594518845664050027907)
        ·
          refine ⟨92885391778268496075041861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61923594518845664050027907 92885391778268496075041861)
          ·
            refine ⟨17416010958425343014070349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92885391778268496075041861 17416010958425343014070349)
            ·
              refine ⟨6531004109409503630276381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17416010958425343014070349 6531004109409503630276381)
              ·
                refine ⟨2449126541028563861353643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6531004109409503630276381 2449126541028563861353643)
                ·
                  refine ⟨3673689811542845792030465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2449126541028563861353643 3673689811542845792030465)
                  ·
                    refine ⟨2755267358657134344022849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3673689811542845792030465 2755267358657134344022849)
                    ·
                      refine ⟨2066450518992850758017137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2755267358657134344022849 2066450518992850758017137)
                      ·
                        rfl

theorem cell23_4024398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 3, 3, 1, 2, 2].length) (baseStart_4024398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4024398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4024398 prefixEnd_4024398 := by exact prefixLift 4024398
  have htrace : WordTrace (prefixWord ++ tailWord_4024398) baseStart_4024398 baseEnd_4024398 := by
    simpa [prefixWord, tailWord_4024398, baseEnd_4024398] using wordTrace_append hprefix tailTrace_4024398
  have hstable : (prefixWord ++ tailWord_4024398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4024398).length < 2 ^ (prefixWord ++ tailWord_4024398).sum := by decide
  have hdescent : baseEnd_4024398 < baseStart_4024398 := by decide
  rcases family_descends (prefixWord ++ tailWord_4024398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4024410 : List Nat := [3, 1, 1, 2, 1, 1, 3, 2, 2, 2, 5]
def baseStart_4024410 : Nat := 118140960795 + 4024410 * 2 ^ 59
def prefixEnd_4024410 : Nat := 4983230072969 + 3 ^ 40 * 4024410 * 2
def baseEnd_4024410 : Nat := 2066456680760704711067081

theorem tailTrace_4024410 : CollatzResearch.WordTrace tailWord_4024410 prefixEnd_4024410 2066456680760704711067081 := by
  unfold tailWord_4024410
  simp only [CollatzResearch.WordTrace]
  refine ⟨36695572837564339838301671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97854860900171572902137789 36695572837564339838301671)
  ·
    refine ⟨55043359256346509757452507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36695572837564339838301671 55043359256346509757452507)
    ·
      refine ⟨82565038884519764636178761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55043359256346509757452507 82565038884519764636178761)
      ·
        refine ⟨61923779163389823477134071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82565038884519764636178761 61923779163389823477134071)
        ·
          refine ⟨92885668745084735215701107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61923779163389823477134071 92885668745084735215701107)
          ·
            refine ⟨139328503117627102823551661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92885668745084735215701107 139328503117627102823551661)
            ·
              refine ⟨52248188669110163558831873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139328503117627102823551661 52248188669110163558831873)
              ·
                refine ⟨39186141501832622669123905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52248188669110163558831873 39186141501832622669123905)
                ·
                  refine ⟨29389606126374467001842929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39186141501832622669123905 29389606126374467001842929)
                  ·
                    refine ⟨22042204594780850251382197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29389606126374467001842929 22042204594780850251382197)
                    ·
                      refine ⟨2066456680760704711067081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22042204594780850251382197 2066456680760704711067081)
                      ·
                        rfl

theorem cell23_4024410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 2, 2, 2, 5].length) (baseStart_4024410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4024410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4024410 prefixEnd_4024410 := by exact prefixLift 4024410
  have htrace : WordTrace (prefixWord ++ tailWord_4024410) baseStart_4024410 baseEnd_4024410 := by
    simpa [prefixWord, tailWord_4024410, baseEnd_4024410] using wordTrace_append hprefix tailTrace_4024410
  have hstable : (prefixWord ++ tailWord_4024410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4024410).length < 2 ^ (prefixWord ++ tailWord_4024410).sum := by decide
  have hdescent : baseEnd_4024410 < baseStart_4024410 := by decide
  rcases family_descends (prefixWord ++ tailWord_4024410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4024431 : List Nat := [1, 1, 2, 1, 3, 4, 4, 1, 2, 1, 3]
def baseStart_4024431 : Nat := 118140960795 + 4024431 * 2 ^ 59
def prefixEnd_4024431 : Nat := 4983230072969 + 3 ^ 40 * 4024431 * 2
def baseEnd_4024431 : Nat := 2066467463854449128904485

theorem tailTrace_4024431 : CollatzResearch.WordTrace tailWord_4024431 prefixEnd_4024431 2066467463854449128904485 := by
  unfold tailWord_4024431
  simp only [CollatzResearch.WordTrace]
  refine ⟨146783057283181279939721147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97855371522120853293147431 146783057283181279939721147)
  ·
    refine ⟨220174585924771919909581721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146783057283181279939721147 220174585924771919909581721)
    ·
      refine ⟨165130939443578939932186291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220174585924771919909581721 165130939443578939932186291)
      ·
        refine ⟨247696409165368409898279437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165130939443578939932186291 247696409165368409898279437)
        ·
          refine ⟨92886153437013153711854789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 247696409165368409898279437 92886153437013153711854789)
          ·
            refine ⟨17416153769439966320972773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92886153437013153711854789 17416153769439966320972773)
            ·
              refine ⟨3265528831769993685182395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17416153769439966320972773 3265528831769993685182395)
              ·
                refine ⟨4898293247654990527773593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3265528831769993685182395 4898293247654990527773593)
                ·
                  refine ⟨3673719935741242895830195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4898293247654990527773593 3673719935741242895830195)
                  ·
                    refine ⟨5510579903611864343745293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3673719935741242895830195 5510579903611864343745293)
                    ·
                      refine ⟨2066467463854449128904485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5510579903611864343745293 2066467463854449128904485)
                      ·
                        rfl

theorem cell23_4024431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 4, 1, 2, 1, 3].length) (baseStart_4024431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4024431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4024431 prefixEnd_4024431 := by exact prefixLift 4024431
  have htrace : WordTrace (prefixWord ++ tailWord_4024431) baseStart_4024431 baseEnd_4024431 := by
    simpa [prefixWord, tailWord_4024431, baseEnd_4024431] using wordTrace_append hprefix tailTrace_4024431
  have hstable : (prefixWord ++ tailWord_4024431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4024431).length < 2 ^ (prefixWord ++ tailWord_4024431).sum := by decide
  have hdescent : baseEnd_4024431 < baseStart_4024431 := by decide
  rcases family_descends (prefixWord ++ tailWord_4024431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4024441 : List Nat := [1, 2, 1, 3, 4, 1, 3, 2, 1, 3, 2]
def baseStart_4024441 : Nat := 118140960795 + 4024441 * 2 ^ 59
def prefixEnd_4024441 : Nat := 4983230072969 + 3 ^ 40 * 4024441 * 2
def baseEnd_4024441 : Nat := 2066472598660994089779439

theorem tailTrace_4024441 : CollatzResearch.WordTrace tailWord_4024441 prefixEnd_4024441 2066472598660994089779439 := by
  unfold tailWord_4024441
  simp only [CollatzResearch.WordTrace]
  refine ⟨146783422013145051647585177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97855614675430034431723451 146783422013145051647585177)
  ·
    refine ⟨110087566509858788735688883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146783422013145051647585177 110087566509858788735688883)
    ·
      refine ⟨165131349764788183103533325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110087566509858788735688883 165131349764788183103533325)
      ·
        refine ⟨61924256161795568663824997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165131349764788183103533325 61924256161795568663824997)
        ·
          refine ⟨11610798030336669124467187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61924256161795568663824997 11610798030336669124467187)
          ·
            refine ⟨17416197045505003686700781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11610798030336669124467187 17416197045505003686700781)
            ·
              refine ⟨6531073892064376382512793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17416197045505003686700781 6531073892064376382512793)
              ·
                refine ⟨4898305419048282286884595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6531073892064376382512793 4898305419048282286884595)
                ·
                  refine ⟨7347458128572423430326893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4898305419048282286884595 7347458128572423430326893)
                  ·
                    refine ⟨2755296798214658786372585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7347458128572423430326893 2755296798214658786372585)
                    ·
                      refine ⟨2066472598660994089779439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2755296798214658786372585 2066472598660994089779439)
                      ·
                        rfl

theorem cell23_4024441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 3, 2, 1, 3, 2].length) (baseStart_4024441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4024441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4024441 prefixEnd_4024441 := by exact prefixLift 4024441
  have htrace : WordTrace (prefixWord ++ tailWord_4024441) baseStart_4024441 baseEnd_4024441 := by
    simpa [prefixWord, tailWord_4024441, baseEnd_4024441] using wordTrace_append hprefix tailTrace_4024441
  have hstable : (prefixWord ++ tailWord_4024441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4024441).length < 2 ^ (prefixWord ++ tailWord_4024441).sum := by decide
  have hdescent : baseEnd_4024441 < baseStart_4024441 := by decide
  rcases family_descends (prefixWord ++ tailWord_4024441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4024458 : List Nat := [3, 1, 2, 3, 1, 3, 3, 1, 1, 3, 2]
def baseStart_4024458 : Nat := 118140960795 + 4024458 * 2 ^ 59
def prefixEnd_4024458 : Nat := 4983230072969 + 3 ^ 40 * 4024458 * 2
def baseEnd_4024458 : Nat := 2066481327832120523266861

theorem tailTrace_4024458 : CollatzResearch.WordTrace tailWord_4024458 prefixEnd_4024458 2066481327832120523266861 := by
  unfold tailWord_4024458
  simp only [CollatzResearch.WordTrace]
  refine ⟨36696010513520865887738507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97856028036055642367302685 36696010513520865887738507)
  ·
    refine ⟨55044015770281298831607761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36696010513520865887738507 55044015770281298831607761)
    ·
      refine ⟨41283011827710974123705821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55044015770281298831607761 41283011827710974123705821)
      ·
        refine ⟨15481129435391615296389683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41283011827710974123705821 15481129435391615296389683)
        ·
          refine ⟨23221694153087422944584525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15481129435391615296389683 23221694153087422944584525)
          ·
            refine ⟨8708135307407783604219197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23221694153087422944584525 8708135307407783604219197)
            ·
              refine ⟨3265550740277918851582199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8708135307407783604219197 3265550740277918851582199)
              ·
                refine ⟨4898326110416878277373299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3265550740277918851582199 4898326110416878277373299)
                ·
                  refine ⟨7347489165625317416059949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4898326110416878277373299 7347489165625317416059949)
                  ·
                    refine ⟨2755308437109494031022481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7347489165625317416059949 2755308437109494031022481)
                    ·
                      refine ⟨2066481327832120523266861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2755308437109494031022481 2066481327832120523266861)
                      ·
                        rfl

theorem cell23_4024458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 3, 1, 1, 3, 2].length) (baseStart_4024458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4024458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4024458 prefixEnd_4024458 := by exact prefixLift 4024458
  have htrace : WordTrace (prefixWord ++ tailWord_4024458) baseStart_4024458 baseEnd_4024458 := by
    simpa [prefixWord, tailWord_4024458, baseEnd_4024458] using wordTrace_append hprefix tailTrace_4024458
  have hstable : (prefixWord ++ tailWord_4024458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4024458).length < 2 ^ (prefixWord ++ tailWord_4024458).sum := by decide
  have hdescent : baseEnd_4024458 < baseStart_4024458 := by decide
  rcases family_descends (prefixWord ++ tailWord_4024458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4024484 : List Nat := [2, 3, 1, 2, 4, 1, 1, 1, 2, 2, 4]
def baseStart_4024484 : Nat := 118140960795 + 4024484 * 2 ^ 59
def prefixEnd_4024484 : Nat := 4983230072969 + 3 ^ 40 * 4024484 * 2
def baseEnd_4024484 : Nat := 2066494678329137421541741

theorem tailTrace_4024484 : CollatzResearch.WordTrace tailWord_4024484 prefixEnd_4024484 2066494678329137421541741 := by
  unfold tailWord_4024484
  simp only [CollatzResearch.WordTrace]
  refine ⟨73392495175994634995700253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97856660234659513327600337 73392495175994634995700253)
  ·
    refine ⟨27522185690997988123387595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73392495175994634995700253 27522185690997988123387595)
    ·
      refine ⟨41283278536496982185081393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27522185690997988123387595 41283278536496982185081393)
      ·
        refine ⟨30962458902372736638811045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41283278536496982185081393 30962458902372736638811045)
        ·
          refine ⟨5805461044194888119777071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30962458902372736638811045 5805461044194888119777071)
          ·
            refine ⟨8708191566292332179665607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5805461044194888119777071 8708191566292332179665607)
            ·
              refine ⟨13062287349438498269498411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8708191566292332179665607 13062287349438498269498411)
              ·
                refine ⟨19593431024157747404247617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13062287349438498269498411 19593431024157747404247617)
                ·
                  refine ⟨14695073268118310553185713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19593431024157747404247617 14695073268118310553185713)
                  ·
                    refine ⟨11021304951088732914889285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14695073268118310553185713 11021304951088732914889285)
                    ·
                      refine ⟨2066494678329137421541741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11021304951088732914889285 2066494678329137421541741)
                      ·
                        rfl

theorem cell23_4024484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 1, 2, 2, 4].length) (baseStart_4024484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4024484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4024484 prefixEnd_4024484 := by exact prefixLift 4024484
  have htrace : WordTrace (prefixWord ++ tailWord_4024484) baseStart_4024484 baseEnd_4024484 := by
    simpa [prefixWord, tailWord_4024484, baseEnd_4024484] using wordTrace_append hprefix tailTrace_4024484
  have hstable : (prefixWord ++ tailWord_4024484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4024484).length < 2 ^ (prefixWord ++ tailWord_4024484).sum := by decide
  have hdescent : baseEnd_4024484 < baseStart_4024484 := by decide
  rcases family_descends (prefixWord ++ tailWord_4024484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4024527 : List Nat := [1, 1, 2, 1, 1, 3, 4, 1, 4, 1, 4]
def baseStart_4024527 : Nat := 118140960795 + 4024527 * 2 ^ 59
def prefixEnd_4024527 : Nat := 4983230072969 + 3 ^ 40 * 4024527 * 2
def baseEnd_4024527 : Nat := 2066516757997280753304043

theorem tailTrace_4024527 : CollatzResearch.WordTrace tailWord_4024527 prefixEnd_4024527 2066516757997280753304043 := by
  unfold tailWord_4024527
  simp only [CollatzResearch.WordTrace]
  refine ⟨146786558690833488335215835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97857705793888992223477223 146786558690833488335215835)
  ·
    refine ⟨220179838036250232502823753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146786558690833488335215835 220179838036250232502823753)
    ·
      refine ⟨165134878527187674377117815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220179838036250232502823753 165134878527187674377117815)
      ·
        refine ⟨247702317790781511565676723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165134878527187674377117815 247702317790781511565676723)
        ·
          refine ⟨371553476686172267348515085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247702317790781511565676723 371553476686172267348515085)
          ·
            refine ⟨139332553757314600255693157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 371553476686172267348515085 139332553757314600255693157)
            ·
              refine ⟨26124853829496487547942467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 139332553757314600255693157 26124853829496487547942467)
              ·
                refine ⟨39187280744244731321913701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26124853829496487547942467 39187280744244731321913701)
                ·
                  refine ⟨7347615139545887122858819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39187280744244731321913701 7347615139545887122858819)
                  ·
                    refine ⟨11021422709318830684288229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7347615139545887122858819 11021422709318830684288229)
                    ·
                      refine ⟨2066516757997280753304043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11021422709318830684288229 2066516757997280753304043)
                      ·
                        rfl

theorem cell23_4024527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 1, 4, 1, 4].length) (baseStart_4024527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4024527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4024527 prefixEnd_4024527 := by exact prefixLift 4024527
  have htrace : WordTrace (prefixWord ++ tailWord_4024527) baseStart_4024527 baseEnd_4024527 := by
    simpa [prefixWord, tailWord_4024527, baseEnd_4024527] using wordTrace_append hprefix tailTrace_4024527
  have hstable : (prefixWord ++ tailWord_4024527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4024527).length < 2 ^ (prefixWord ++ tailWord_4024527).sum := by decide
  have hdescent : baseEnd_4024527 < baseStart_4024527 := by decide
  rcases family_descends (prefixWord ++ tailWord_4024527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4024544 : List Nat := [2, 1, 1, 3, 1, 3, 1, 3, 2, 4, 2]
def baseStart_4024544 : Nat := 118140960795 + 4024544 * 2 ^ 59
def prefixEnd_4024544 : Nat := 4983230072969 + 3 ^ 40 * 4024544 * 2
def baseEnd_4024544 : Nat := 2066525487168407186791465

theorem tailTrace_4024544 : CollatzResearch.WordTrace tailWord_4024544 prefixEnd_4024544 2066525487168407186791465 := by
  unfold tailWord_4024544
  simp only [CollatzResearch.WordTrace]
  refine ⟨73393589365885950119292343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97858119154514600159056457 73393589365885950119292343)
  ·
    refine ⟨110090384048828925178938515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73393589365885950119292343 110090384048828925178938515)
    ·
      refine ⟨165135576073243387768407773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110090384048828925178938515 165135576073243387768407773)
      ·
        refine ⟨61925841027466270413152915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165135576073243387768407773 61925841027466270413152915)
        ·
          refine ⟨92888761541199405619729373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61925841027466270413152915 92888761541199405619729373)
          ·
            refine ⟨34833285577949777107398515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92888761541199405619729373 34833285577949777107398515)
            ·
              refine ⟨52249928366924665661097773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34833285577949777107398515 52249928366924665661097773)
              ·
                refine ⟨19593723137596749622911665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52249928366924665661097773 19593723137596749622911665)
                ·
                  refine ⟨14695292353197562217183749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19593723137596749622911665 14695292353197562217183749)
                  ·
                    refine ⟨2755367316224542915721953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14695292353197562217183749 2755367316224542915721953)
                    ·
                      refine ⟨2066525487168407186791465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2755367316224542915721953 2066525487168407186791465)
                      ·
                        rfl

theorem cell23_4024544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 3, 2, 4, 2].length) (baseStart_4024544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4024544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4024544 prefixEnd_4024544 := by exact prefixLift 4024544
  have htrace : WordTrace (prefixWord ++ tailWord_4024544) baseStart_4024544 baseEnd_4024544 := by
    simpa [prefixWord, tailWord_4024544, baseEnd_4024544] using wordTrace_append hprefix tailTrace_4024544
  have hstable : (prefixWord ++ tailWord_4024544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4024544).length < 2 ^ (prefixWord ++ tailWord_4024544).sum := by decide
  have hdescent : baseEnd_4024544 < baseStart_4024544 := by decide
  rcases family_descends (prefixWord ++ tailWord_4024544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4024554 : List Nat := [3, 1, 3, 1, 1, 2, 1, 4, 3, 4]
def baseStart_4024554 : Nat := 118140960795 + 4024554 * 2 ^ 59
def prefixEnd_4024554 : Nat := 4983230072969 + 3 ^ 40 * 4024554 * 2
def baseEnd_4024554 : Nat := 688843540658317382555473

theorem tailTrace_4024554 : CollatzResearch.WordTrace tailWord_4024554 prefixEnd_4024554 688843540658317382555473 := by
  unfold tailWord_4024554
  simp only [CollatzResearch.WordTrace]
  refine ⟨36696885865433917986612179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97858362307823781297632477 36696885865433917986612179)
  ·
    refine ⟨55045328798150876979918269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36696885865433917986612179 55045328798150876979918269)
    ·
      refine ⟨20641998299306578867469351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55045328798150876979918269 20641998299306578867469351)
      ·
        refine ⟨30962997448959868301204027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20641998299306578867469351 30962997448959868301204027)
        ·
          refine ⟨46444496173439802451806041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30962997448959868301204027 46444496173439802451806041)
          ·
            refine ⟨34833372130079851838854531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46444496173439802451806041 34833372130079851838854531)
            ·
              refine ⟨52250058195119777758281797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34833372130079851838854531 52250058195119777758281797)
              ·
                refine ⟨9796885911584958329677837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52250058195119777758281797 9796885911584958329677837)
                ·
                  refine ⟨3673832216844359373629189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9796885911584958329677837 3673832216844359373629189)
                  ·
                    refine ⟨688843540658317382555473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3673832216844359373629189 688843540658317382555473)
                    ·
                      rfl

theorem cell23_4024554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 4, 3, 4].length) (baseStart_4024554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4024554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4024554 prefixEnd_4024554 := by exact prefixLift 4024554
  have htrace : WordTrace (prefixWord ++ tailWord_4024554) baseStart_4024554 baseEnd_4024554 := by
    simpa [prefixWord, tailWord_4024554, baseEnd_4024554] using wordTrace_append hprefix tailTrace_4024554
  have hstable : (prefixWord ++ tailWord_4024554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4024554).length < 2 ^ (prefixWord ++ tailWord_4024554).sum := by decide
  have hdescent : baseEnd_4024554 < baseStart_4024554 := by decide
  rcases family_descends (prefixWord ++ tailWord_4024554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4024588 : List Nat := [2, 2, 1, 2, 2, 2, 5, 2, 1, 4]
def baseStart_4024588 : Nat := 118140960795 + 4024588 * 2 ^ 59
def prefixEnd_4024588 : Nat := 4983230072969 + 3 ^ 40 * 4024588 * 2
def baseEnd_4024588 : Nat := 688849360105735004880421

theorem tailTrace_4024588 : CollatzResearch.WordTrace tailWord_4024588 prefixEnd_4024588 688849360105735004880421 := by
  unfold tailWord_4024588
  simp only [CollatzResearch.WordTrace]
  refine ⟨73394391771806247876593209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97859189029074997168790945 73394391771806247876593209)
  ·
    refine ⟨55045793828854685907444907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73394391771806247876593209 55045793828854685907444907)
    ·
      refine ⟨82568690743282028861167361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55045793828854685907444907 82568690743282028861167361)
      ·
        refine ⟨61926518057461521645875521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82568690743282028861167361 61926518057461521645875521)
        ·
          refine ⟨46444888543096141234406641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61926518057461521645875521 46444888543096141234406641)
          ·
            refine ⟨34833666407322105925804981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46444888543096141234406641 34833666407322105925804981)
            ·
              refine ⟨3265656225686447430544217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34833666407322105925804981 3265656225686447430544217)
              ·
                refine ⟨2449242169264835572908163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3265656225686447430544217 2449242169264835572908163)
                ·
                  refine ⟨3673863253897253359362245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2449242169264835572908163 3673863253897253359362245)
                  ·
                    refine ⟨688849360105735004880421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3673863253897253359362245 688849360105735004880421)
                    ·
                      rfl

theorem cell23_4024588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 5, 2, 1, 4].length) (baseStart_4024588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4024588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4024588 prefixEnd_4024588 := by exact prefixLift 4024588
  have htrace : WordTrace (prefixWord ++ tailWord_4024588) baseStart_4024588 baseEnd_4024588 := by
    simpa [prefixWord, tailWord_4024588, baseEnd_4024588] using wordTrace_append hprefix tailTrace_4024588
  have hstable : (prefixWord ++ tailWord_4024588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4024588).length < 2 ^ (prefixWord ++ tailWord_4024588).sum := by decide
  have hdescent : baseEnd_4024588 < baseStart_4024588 := by decide
  rcases family_descends (prefixWord ++ tailWord_4024588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4024638 : List Nat := [4, 2, 1, 2, 1, 2, 2, 2, 2, 3, 2]
def baseStart_4024638 : Nat := 118140960795 + 4024638 * 2 ^ 59
def prefixEnd_4024638 : Nat := 4983230072969 + 3 ^ 40 * 4024638 * 2
def baseEnd_4024638 : Nat := 2066573754349929819016033

theorem tailTrace_4024638 : CollatzResearch.WordTrace tailWord_4024638 prefixEnd_4024638 2066573754349929819016033 := by
  unfold tailWord_4024638
  simp only [CollatzResearch.WordTrace]
  refine ⟨18348825899178919286563321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97860404795620902861671045 18348825899178919286563321)
  ·
    refine ⟨13761619424384189464922491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18348825899178919286563321 13761619424384189464922491)
    ·
      refine ⟨20642429136576284197383737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13761619424384189464922491 20642429136576284197383737)
      ·
        refine ⟨15481821852432213148037803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20642429136576284197383737 15481821852432213148037803)
        ·
          refine ⟨23222732778648319722056705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15481821852432213148037803 23222732778648319722056705)
          ·
            refine ⟨17417049583986239791542529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23222732778648319722056705 17417049583986239791542529)
            ·
              refine ⟨13062787187989679843656897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17417049583986239791542529 13062787187989679843656897)
              ·
                refine ⟨9797090390992259882742673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13062787187989679843656897 9797090390992259882742673)
                ·
                  refine ⟨7347817793244194912057005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9797090390992259882742673 7347817793244194912057005)
                  ·
                    refine ⟨2755431672466573092021377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7347817793244194912057005 2755431672466573092021377)
                    ·
                      refine ⟨2066573754349929819016033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2755431672466573092021377 2066573754349929819016033)
                      ·
                        rfl

theorem cell23_4024638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 2, 2, 3, 2].length) (baseStart_4024638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4024638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4024638 prefixEnd_4024638 := by exact prefixLift 4024638
  have htrace : WordTrace (prefixWord ++ tailWord_4024638) baseStart_4024638 baseEnd_4024638 := by
    simpa [prefixWord, tailWord_4024638, baseEnd_4024638] using wordTrace_append hprefix tailTrace_4024638
  have hstable : (prefixWord ++ tailWord_4024638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4024638).length < 2 ^ (prefixWord ++ tailWord_4024638).sum := by decide
  have hdescent : baseEnd_4024638 < baseStart_4024638 := by decide
  rcases family_descends (prefixWord ++ tailWord_4024638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4024661 : List Nat := [1, 3, 2, 2, 4, 1, 2, 1, 1, 6]
def baseStart_4024661 : Nat := 118140960795 + 4024661 * 2 ^ 59
def prefixEnd_4024661 : Nat := 4983230072969 + 3 ^ 40 * 4024661 * 2
def baseEnd_4024661 : Nat := 688861854801661076342809

theorem tailTrace_4024661 : CollatzResearch.WordTrace tailWord_4024661 prefixEnd_4024661 688861854801661076342809 := by
  unfold tailWord_4024661
  simp only [CollatzResearch.WordTrace]
  refine ⟨146791446072348029220593837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97860964048232019480395891 146791446072348029220593837)
  ·
    refine ⟨55046792277130510957722689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146791446072348029220593837 55046792277130510957722689)
    ·
      refine ⟨41285094207847883218292017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55046792277130510957722689 41285094207847883218292017)
      ·
        refine ⟨30963820655885912413719013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41285094207847883218292017 30963820655885912413719013)
        ·
          refine ⟨5805716372978608577572315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30963820655885912413719013 5805716372978608577572315)
          ·
            refine ⟨8708574559467912866358473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5805716372978608577572315 8708574559467912866358473)
            ·
              refine ⟨6531430919600934649768855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8708574559467912866358473 6531430919600934649768855)
              ·
                refine ⟨9797146379401401974653283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6531430919600934649768855 9797146379401401974653283)
                ·
                  refine ⟨14695719569102102961979925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9797146379401401974653283 14695719569102102961979925)
                  ·
                    refine ⟨688861854801661076342809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14695719569102102961979925 688861854801661076342809)
                    ·
                      rfl

theorem cell23_4024661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 2, 1, 1, 6].length) (baseStart_4024661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4024661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4024661 prefixEnd_4024661 := by exact prefixLift 4024661
  have htrace : WordTrace (prefixWord ++ tailWord_4024661) baseStart_4024661 baseEnd_4024661 := by
    simpa [prefixWord, tailWord_4024661, baseEnd_4024661] using wordTrace_append hprefix tailTrace_4024661
  have hstable : (prefixWord ++ tailWord_4024661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4024661).length < 2 ^ (prefixWord ++ tailWord_4024661).sum := by decide
  have hdescent : baseEnd_4024661 < baseStart_4024661 := by decide
  rcases family_descends (prefixWord ++ tailWord_4024661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4024687 : List Nat := [1, 1, 2, 1, 3, 1, 2, 2, 1, 9]
def baseStart_4024687 : Nat := 118140960795 + 4024687 * 2 ^ 59
def prefixEnd_4024687 : Nat := 4983230072969 + 3 ^ 40 * 4024687 * 2
def baseEnd_4024687 : Nat := 688866304967333375767769

theorem tailTrace_4024687 : CollatzResearch.WordTrace tailWord_4024687 prefixEnd_4024687 688866304967333375767769 := by
  unfold tailWord_4024687
  simp only [CollatzResearch.WordTrace]
  refine ⟨146792394370253835661040315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97861596246835890440693543 146792394370253835661040315)
  ·
    refine ⟨220188591555380753491560473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146792394370253835661040315 220188591555380753491560473)
    ·
      refine ⟨165141443666535565118670355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220188591555380753491560473 165141443666535565118670355)
      ·
        refine ⟨247712165499803347678005533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165141443666535565118670355 247712165499803347678005533)
        ·
          refine ⟨92892062062426255379252075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 247712165499803347678005533 92892062062426255379252075)
          ·
            refine ⟨139338093093639383068878113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92892062062426255379252075 139338093093639383068878113)
            ·
              refine ⟨104503569820229537301658585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139338093093639383068878113 104503569820229537301658585)
              ·
                refine ⟨78377677365172152976243939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104503569820229537301658585 78377677365172152976243939)
                ·
                  refine ⟨117566516047758229464365909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78377677365172152976243939 117566516047758229464365909)
                  ·
                    refine ⟨688866304967333375767769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 117566516047758229464365909 688866304967333375767769)
                    ·
                      rfl

theorem cell23_4024687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 9].length) (baseStart_4024687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4024687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4024687 prefixEnd_4024687 := by exact prefixLift 4024687
  have htrace : WordTrace (prefixWord ++ tailWord_4024687) baseStart_4024687 baseEnd_4024687 := by
    simpa [prefixWord, tailWord_4024687, baseEnd_4024687] using wordTrace_append hprefix tailTrace_4024687
  have hstable : (prefixWord ++ tailWord_4024687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4024687).length < 2 ^ (prefixWord ++ tailWord_4024687).sum := by decide
  have hdescent : baseEnd_4024687 < baseStart_4024687 := by decide
  rcases family_descends (prefixWord ++ tailWord_4024687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4024688 : List Nat := [2, 1, 1, 1, 4, 3, 4, 1, 1, 2, 3]
def baseStart_4024688 : Nat := 118140960795 + 4024688 * 2 ^ 59
def prefixEnd_4024688 : Nat := 4983230072969 + 3 ^ 40 * 4024688 * 2
def baseEnd_4024688 : Nat := 2066599428382654623390803

theorem tailTrace_4024688 : CollatzResearch.WordTrace tailWord_4024688 prefixEnd_4024688 2066599428382654623390803 := by
  unfold tailWord_4024688
  simp only [CollatzResearch.WordTrace]
  refine ⟨73396215421625106415913359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97861620562166808554551145 73396215421625106415913359)
  ·
    refine ⟨110094323132437659623870039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73396215421625106415913359 110094323132437659623870039)
    ·
      refine ⟨165141484698656489435805059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110094323132437659623870039 165141484698656489435805059)
      ·
        refine ⟨247712227047984734153707589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165141484698656489435805059 247712227047984734153707589)
        ·
          refine ⟨46446042571497137653820173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 247712227047984734153707589 46446042571497137653820173)
          ·
            refine ⟨17417265964311426620182565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46446042571497137653820173 17417265964311426620182565)
            ·
              refine ⟨3265737368308392491284231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17417265964311426620182565 3265737368308392491284231)
              ·
                refine ⟨4898606052462588736926347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3265737368308392491284231 4898606052462588736926347)
                ·
                  refine ⟨7347909078693883105389521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4898606052462588736926347 7347909078693883105389521)
                  ·
                    refine ⟨5510931809020412329042141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7347909078693883105389521 5510931809020412329042141)
                    ·
                      refine ⟨2066599428382654623390803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5510931809020412329042141 2066599428382654623390803)
                      ·
                        rfl

theorem cell23_4024688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 4, 1, 1, 2, 3].length) (baseStart_4024688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4024688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4024688 prefixEnd_4024688 := by exact prefixLift 4024688
  have htrace : WordTrace (prefixWord ++ tailWord_4024688) baseStart_4024688 baseEnd_4024688 := by
    simpa [prefixWord, tailWord_4024688, baseEnd_4024688] using wordTrace_append hprefix tailTrace_4024688
  have hstable : (prefixWord ++ tailWord_4024688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4024688).length < 2 ^ (prefixWord ++ tailWord_4024688).sum := by decide
  have hdescent : baseEnd_4024688 < baseStart_4024688 := by decide
  rcases family_descends (prefixWord ++ tailWord_4024688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4024718 : List Nat := [4, 1, 1, 4, 1, 1, 3, 1, 1, 3, 3]
def baseStart_4024718 : Nat := 118140960795 + 4024718 * 2 ^ 59
def prefixEnd_4024718 : Nat := 4983230072969 + 3 ^ 40 * 4024718 * 2
def baseEnd_4024718 : Nat := 2066614832802289506015665

theorem tailTrace_4024718 : CollatzResearch.WordTrace tailWord_4024718 prefixEnd_4024718 2066614832802289506015665 := by
  unfold tailWord_4024718
  simp only [CollatzResearch.WordTrace]
  refine ⟨18349190629142690994427351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97862350022094351970279205 18349190629142690994427351)
  ·
    refine ⟨27523785943714036491641027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18349190629142690994427351 27523785943714036491641027)
    ·
      refine ⟨41285678915571054737461541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27523785943714036491641027 41285678915571054737461541)
      ·
        refine ⟨7741064796669572763274039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41285678915571054737461541 7741064796669572763274039)
        ·
          refine ⟨11611597195004359144911059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7741064796669572763274039 11611597195004359144911059)
          ·
            refine ⟨17417395792506538717366589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11611597195004359144911059 17417395792506538717366589)
            ·
              refine ⟨6531523422189952019012471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17417395792506538717366589 6531523422189952019012471)
              ·
                refine ⟨9797285133284928028518707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6531523422189952019012471 9797285133284928028518707)
                ·
                  refine ⟨14695927699927392042778061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9797285133284928028518707 14695927699927392042778061)
                  ·
                    refine ⟨5510972887472772016041773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14695927699927392042778061 5510972887472772016041773)
                    ·
                      refine ⟨2066614832802289506015665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5510972887472772016041773 2066614832802289506015665)
                      ·
                        rfl

theorem cell23_4024718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_4024718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4024718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4024718 prefixEnd_4024718 := by exact prefixLift 4024718
  have htrace : WordTrace (prefixWord ++ tailWord_4024718) baseStart_4024718 baseEnd_4024718 := by
    simpa [prefixWord, tailWord_4024718, baseEnd_4024718] using wordTrace_append hprefix tailTrace_4024718
  have hstable : (prefixWord ++ tailWord_4024718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4024718).length < 2 ^ (prefixWord ++ tailWord_4024718).sum := by decide
  have hdescent : baseEnd_4024718 < baseStart_4024718 := by decide
  rcases family_descends (prefixWord ++ tailWord_4024718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4024741 : List Nat := [1, 3, 1, 2, 1, 1, 4, 1, 3, 4, 2]
def baseStart_4024741 : Nat := 118140960795 + 4024741 * 2 ^ 59
def prefixEnd_4024741 : Nat := 4983230072969 + 3 ^ 40 * 4024741 * 2
def baseEnd_4024741 : Nat := 2066626642857342916028059

theorem tailTrace_4024741 : CollatzResearch.WordTrace tailWord_4024741 prefixEnd_4024741 2066626642857342916028059 := by
  unfold tailWord_4024741
  simp only [CollatzResearch.WordTrace]
  refine ⟨146794363912058202883506077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97862909274705468589004051 146794363912058202883506077)
  ·
    refine ⟨55047886467021826081314779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146794363912058202883506077 55047886467021826081314779)
    ·
      refine ⟨82571829700532739121972169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55047886467021826081314779 82571829700532739121972169)
      ·
        refine ⟨61928872275399554341479127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82571829700532739121972169 61928872275399554341479127)
        ·
          refine ⟨92893308413099331512218691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61928872275399554341479127 92893308413099331512218691)
          ·
            refine ⟨139339962619648997268328037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92893308413099331512218691 139339962619648997268328037)
            ·
              refine ⟨26126242991184186987811507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 139339962619648997268328037 26126242991184186987811507)
              ·
                refine ⟨39189364486776280481717261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26126242991184186987811507 39189364486776280481717261)
                ·
                  refine ⟨14696011682541105180643973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39189364486776280481717261 14696011682541105180643973)
                  ·
                    refine ⟨2755502190476457221370745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14696011682541105180643973 2755502190476457221370745)
                    ·
                      refine ⟨2066626642857342916028059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2755502190476457221370745 2066626642857342916028059)
                      ·
                        rfl

theorem cell23_4024741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 1, 3, 4, 2].length) (baseStart_4024741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4024741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4024741 prefixEnd_4024741 := by exact prefixLift 4024741
  have htrace : WordTrace (prefixWord ++ tailWord_4024741) baseStart_4024741 baseEnd_4024741 := by
    simpa [prefixWord, tailWord_4024741, baseEnd_4024741] using wordTrace_append hprefix tailTrace_4024741
  have hstable : (prefixWord ++ tailWord_4024741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4024741).length < 2 ^ (prefixWord ++ tailWord_4024741).sum := by decide
  have hdescent : baseEnd_4024741 < baseStart_4024741 := by decide
  rcases family_descends (prefixWord ++ tailWord_4024741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4024769 : List Nat := [1, 2, 7, 1, 1, 1, 1, 3, 2, 1, 3]
def baseStart_4024769 : Nat := 118140960795 + 4024769 * 2 ^ 59
def prefixEnd_4024769 : Nat := 4983230072969 + 3 ^ 40 * 4024769 * 2
def baseEnd_4024769 : Nat := 2066641020315668806477931

theorem tailTrace_4024769 : CollatzResearch.WordTrace tailWord_4024769 prefixEnd_4024769 2066641020315668806477931 := by
  unfold tailWord_4024769
  simp only [CollatzResearch.WordTrace]
  refine ⟨146795385155956763665525361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97863590103971175777016907 146795385155956763665525361)
  ·
    refine ⟨110096538866967572749144021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146795385155956763665525361 110096538866967572749144021)
    ·
      refine ⟨2580387629694552486308063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 110096538866967572749144021 2580387629694552486308063)
      ·
        refine ⟨3870581444541828729462095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2580387629694552486308063 3870581444541828729462095)
        ·
          refine ⟨5805872166812743094193143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3870581444541828729462095 5805872166812743094193143)
          ·
            refine ⟨8708808250219114641289715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5805872166812743094193143 8708808250219114641289715)
            ·
              refine ⟨13063212375328671961934573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8708808250219114641289715 13063212375328671961934573)
              ·
                refine ⟨4898704640748251985725465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13063212375328671961934573 4898704640748251985725465)
                ·
                  refine ⟨3674028480561188989294099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4898704640748251985725465 3674028480561188989294099)
                  ·
                    refine ⟨5511042720841783483941149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3674028480561188989294099 5511042720841783483941149)
                    ·
                      refine ⟨2066641020315668806477931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5511042720841783483941149 2066641020315668806477931)
                      ·
                        rfl

theorem cell23_4024769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_4024769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4024769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4024769 prefixEnd_4024769 := by exact prefixLift 4024769
  have htrace : WordTrace (prefixWord ++ tailWord_4024769) baseStart_4024769 baseEnd_4024769 := by
    simpa [prefixWord, tailWord_4024769, baseEnd_4024769] using wordTrace_append hprefix tailTrace_4024769
  have hstable : (prefixWord ++ tailWord_4024769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4024769).length < 2 ^ (prefixWord ++ tailWord_4024769).sum := by decide
  have hdescent : baseEnd_4024769 < baseStart_4024769 := by decide
  rcases family_descends (prefixWord ++ tailWord_4024769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4024775 : List Nat := [1, 1, 4, 1, 1, 5, 1, 3, 2, 2, 2]
def baseStart_4024775 : Nat := 118140960795 + 4024775 * 2 ^ 59
def prefixEnd_4024775 : Nat := 4983230072969 + 3 ^ 40 * 4024775 * 2
def baseEnd_4024775 : Nat := 2066644101199595783002903

theorem tailTrace_4024775 : CollatzResearch.WordTrace tailWord_4024775 prefixEnd_4024775 2066644101199595783002903 := by
  unfold tailWord_4024775
  simp only [CollatzResearch.WordTrace]
  refine ⟨146795603993935026690243779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97863735995956684460162519 146795603993935026690243779)
  ·
    refine ⟨220193405990902540035365669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146795603993935026690243779 220193405990902540035365669)
    ·
      refine ⟨41286263623294226256631063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 220193405990902540035365669 41286263623294226256631063)
      ·
        refine ⟨61929395434941339384946595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41286263623294226256631063 61929395434941339384946595)
        ·
          refine ⟨92894093152412009077419893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61929395434941339384946595 92894093152412009077419893)
          ·
            refine ⟨8708821233038625851008115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 92894093152412009077419893 8708821233038625851008115)
            ·
              refine ⟨13063231849557938776512173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8708821233038625851008115 13063231849557938776512173)
              ·
                refine ⟨4898711943584227041192065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13063231849557938776512173 4898711943584227041192065)
                ·
                  refine ⟨3674033957688170280894049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4898711943584227041192065 3674033957688170280894049)
                  ·
                    refine ⟨2755525468266127710670537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3674033957688170280894049 2755525468266127710670537)
                    ·
                      refine ⟨2066644101199595783002903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2755525468266127710670537 2066644101199595783002903)
                      ·
                        rfl

theorem cell23_4024775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 3, 2, 2, 2].length) (baseStart_4024775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4024775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4024775 prefixEnd_4024775 := by exact prefixLift 4024775
  have htrace : WordTrace (prefixWord ++ tailWord_4024775) baseStart_4024775 baseEnd_4024775 := by
    simpa [prefixWord, tailWord_4024775, baseEnd_4024775] using wordTrace_append hprefix tailTrace_4024775
  have hstable : (prefixWord ++ tailWord_4024775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4024775).length < 2 ^ (prefixWord ++ tailWord_4024775).sum := by decide
  have hdescent : baseEnd_4024775 < baseStart_4024775 := by decide
  rcases family_descends (prefixWord ++ tailWord_4024775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4024845 : List Nat := [1, 7, 1, 1, 1, 2, 1, 1, 1, 7]
def baseStart_4024845 : Nat := 118140960795 + 4024845 * 2 ^ 59
def prefixEnd_4024845 : Nat := 4983230072969 + 3 ^ 40 * 4024845 * 2
def baseEnd_4024845 : Nat := 688893348281803503042527

theorem tailTrace_4024845 : CollatzResearch.WordTrace tailWord_4024845 prefixEnd_4024845 688893348281803503042527 := by
  unfold tailWord_4024845
  simp only [CollatzResearch.WordTrace]
  refine ⟨146798157103681428645291989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97865438069120952430194659 146798157103681428645291989)
  ·
    refine ⟨3440581807117533483874031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 146798157103681428645291989 3440581807117533483874031)
    ·
      refine ⟨5160872710676300225811047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3440581807117533483874031 5160872710676300225811047)
      ·
        refine ⟨7741309066014450338716571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5160872710676300225811047 7741309066014450338716571)
        ·
          refine ⟨11611963599021675508074857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7741309066014450338716571 11611963599021675508074857)
          ·
            refine ⟨8708972699266256631056143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11611963599021675508074857 8708972699266256631056143)
            ·
              refine ⟨13063459048899384946584215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8708972699266256631056143 13063459048899384946584215)
              ·
                refine ⟨19595188573349077419876323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13063459048899384946584215 19595188573349077419876323)
                ·
                  refine ⟨29392782860023616129814485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19595188573349077419876323 29392782860023616129814485)
                  ·
                    refine ⟨688893348281803503042527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29392782860023616129814485 688893348281803503042527)
                    ·
                      rfl

theorem cell23_4024845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_4024845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4024845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4024845 prefixEnd_4024845 := by exact prefixLift 4024845
  have htrace : WordTrace (prefixWord ++ tailWord_4024845) baseStart_4024845 baseEnd_4024845 := by
    simpa [prefixWord, tailWord_4024845, baseEnd_4024845] using wordTrace_append hprefix tailTrace_4024845
  have hstable : (prefixWord ++ tailWord_4024845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4024845).length < 2 ^ (prefixWord ++ tailWord_4024845).sum := by decide
  have hdescent : baseEnd_4024845 < baseStart_4024845 := by decide
  rcases family_descends (prefixWord ++ tailWord_4024845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4024851 : List Nat := [1, 1, 1, 2, 1, 5, 3, 1, 1, 4, 3]
def baseStart_4024851 : Nat := 118140960795 + 4024851 * 2 ^ 59
def prefixEnd_4024851 : Nat := 4983230072969 + 3 ^ 40 * 4024851 * 2
def baseEnd_4024851 : Nat := 2066683125729337485652553

theorem tailTrace_4024851 : CollatzResearch.WordTrace tailWord_4024851 prefixEnd_4024851 2066683125729337485652553 := by
  unfold tailWord_4024851
  simp only [CollatzResearch.WordTrace]
  refine ⟨146798375941659691670010407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97865583961106461113340271 146798375941659691670010407)
  ·
    refine ⟨220197563912489537505015611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146798375941659691670010407 220197563912489537505015611)
    ·
      refine ⟨330296345868734306257523417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220197563912489537505015611 330296345868734306257523417)
      ·
        refine ⟨247722259401550729693142563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 330296345868734306257523417 247722259401550729693142563)
        ·
          refine ⟨371583389102326094539713845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247722259401550729693142563 371583389102326094539713845)
          ·
            refine ⟨34835942728343071363098173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 371583389102326094539713845 34835942728343071363098173)
            ·
              refine ⟨13063478523128651761161815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34835942728343071363098173 13063478523128651761161815)
              ·
                refine ⟨19595217784692977641742723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13063478523128651761161815 19595217784692977641742723)
                ·
                  refine ⟨29392826677039466462614085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19595217784692977641742723 29392826677039466462614085)
                  ·
                    refine ⟨5511155001944899961740141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29392826677039466462614085 5511155001944899961740141)
                    ·
                      refine ⟨2066683125729337485652553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5511155001944899961740141 2066683125729337485652553)
                      ·
                        rfl

theorem cell23_4024851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 1, 1, 4, 3].length) (baseStart_4024851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4024851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4024851 prefixEnd_4024851 := by exact prefixLift 4024851
  have htrace : WordTrace (prefixWord ++ tailWord_4024851) baseStart_4024851 baseEnd_4024851 := by
    simpa [prefixWord, tailWord_4024851, baseEnd_4024851] using wordTrace_append hprefix tailTrace_4024851
  have hstable : (prefixWord ++ tailWord_4024851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4024851).length < 2 ^ (prefixWord ++ tailWord_4024851).sum := by decide
  have hdescent : baseEnd_4024851 < baseStart_4024851 := by decide
  rcases family_descends (prefixWord ++ tailWord_4024851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4024861 : List Nat := [1, 4, 2, 2, 1, 2, 1, 1, 2, 1, 6]
def baseStart_4024861 : Nat := 118140960795 + 4024861 * 2 ^ 59
def prefixEnd_4024861 : Nat := 4983230072969 + 3 ^ 40 * 4024861 * 2
def baseEnd_4024861 : Nat := 2066688260535882446527507

theorem tailTrace_4024861 : CollatzResearch.WordTrace tailWord_4024861 prefixEnd_4024861 2066688260535882446527507 := by
  unfold tailWord_4024861
  simp only [CollatzResearch.WordTrace]
  refine ⟨146798740671623463377874437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97865827114415642251916291 146798740671623463377874437)
  ·
    refine ⟨27524763875929399383351457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146798740671623463377874437 27524763875929399383351457)
    ·
      refine ⟨20643572906947049537513593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27524763875929399383351457 20643572906947049537513593)
      ·
        refine ⟨15482679680210287153135195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20643572906947049537513593 15482679680210287153135195)
        ·
          refine ⟨23224019520315430729702793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15482679680210287153135195 23224019520315430729702793)
          ·
            refine ⟨17418014640236573047277095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23224019520315430729702793 17418014640236573047277095)
            ·
              refine ⟨26127021960354859570915643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17418014640236573047277095 26127021960354859570915643)
              ·
                refine ⟨39190532940532289356373465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26127021960354859570915643 39190532940532289356373465)
                ·
                  refine ⟨29392899705399217017280099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39190532940532289356373465 29392899705399217017280099)
                  ·
                    refine ⟨44089349558098825525920149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29392899705399217017280099 44089349558098825525920149)
                    ·
                      refine ⟨2066688260535882446527507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44089349558098825525920149 2066688260535882446527507)
                      ·
                        rfl

theorem cell23_4024861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_4024861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4024861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4024861 prefixEnd_4024861 := by exact prefixLift 4024861
  have htrace : WordTrace (prefixWord ++ tailWord_4024861) baseStart_4024861 baseEnd_4024861 := by
    simpa [prefixWord, tailWord_4024861, baseEnd_4024861] using wordTrace_append hprefix tailTrace_4024861
  have hstable : (prefixWord ++ tailWord_4024861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4024861).length < 2 ^ (prefixWord ++ tailWord_4024861).sum := by decide
  have hdescent : baseEnd_4024861 < baseStart_4024861 := by decide
  rcases family_descends (prefixWord ++ tailWord_4024861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4024888 : List Nat := [2, 1, 2, 1, 4, 1, 5, 1, 6]
def baseStart_4024888 : Nat := 118140960795 + 4024888 * 2 ^ 59
def prefixEnd_4024888 : Nat := 4983230072969 + 3 ^ 40 * 4024888 * 2
def baseEnd_4024888 : Nat := 229633569390394871209987

theorem tailTrace_4024888 : CollatzResearch.WordTrace tailWord_4024888 prefixEnd_4024888 229633569390394871209987 := by
  unfold tailWord_4024888
  simp only [CollatzResearch.WordTrace]
  refine ⟨73399862721262823494553659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97866483628350431326071545 73399862721262823494553659)
  ·
    refine ⟨110099794081894235241830489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73399862721262823494553659 110099794081894235241830489)
    ·
      refine ⟨82574845561420676431372867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110099794081894235241830489 82574845561420676431372867)
      ·
        refine ⟨123862268342131014647059301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82574845561420676431372867 123862268342131014647059301)
        ·
          refine ⟨23224175314149565246323619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 123862268342131014647059301 23224175314149565246323619)
          ·
            refine ⟨34836262971224347869485429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23224175314149565246323619 34836262971224347869485429)
            ·
              refine ⟨3265899653552282612764259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34836262971224347869485429 3265899653552282612764259)
              ·
                refine ⟨4898849480328423919146389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3265899653552282612764259 4898849480328423919146389)
                ·
                  refine ⟨229633569390394871209987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4898849480328423919146389 229633569390394871209987)
                  ·
                    rfl

theorem cell23_4024888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 5, 1, 6].length) (baseStart_4024888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4024888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4024888 prefixEnd_4024888 := by exact prefixLift 4024888
  have htrace : WordTrace (prefixWord ++ tailWord_4024888) baseStart_4024888 baseEnd_4024888 := by
    simpa [prefixWord, tailWord_4024888, baseEnd_4024888] using wordTrace_append hprefix tailTrace_4024888
  have hstable : (prefixWord ++ tailWord_4024888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4024888).length < 2 ^ (prefixWord ++ tailWord_4024888).sum := by decide
  have hdescent : baseEnd_4024888 < baseStart_4024888 := by decide
  rcases family_descends (prefixWord ++ tailWord_4024888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4024908 : List Nat := [2, 2, 1, 3, 1, 2, 1, 3, 1, 5, 2]
def baseStart_4024908 : Nat := 118140960795 + 4024908 * 2 ^ 59
def prefixEnd_4024908 : Nat := 4983230072969 + 3 ^ 40 * 4024908 * 2
def baseEnd_4024908 : Nat := 2066712394126643762639791

theorem tailTrace_4024908 : CollatzResearch.WordTrace tailWord_4024908 prefixEnd_4024908 2066712394126643762639791 := by
  unfold tailWord_4024908
  simp only [CollatzResearch.WordTrace]
  refine ⟨73400227451226595202417689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97866969934968793603223585 73400227451226595202417689)
  ·
    refine ⟨55050170588419946401813267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73400227451226595202417689 55050170588419946401813267)
    ·
      refine ⟨82575255882629919602719901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55050170588419946401813267 82575255882629919602719901)
      ·
        refine ⟨30965720955986219851019963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82575255882629919602719901 30965720955986219851019963)
        ·
          refine ⟨46448581433979329776529945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30965720955986219851019963 46448581433979329776529945)
          ·
            refine ⟨34836436075484497332397459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46448581433979329776529945 34836436075484497332397459)
            ·
              refine ⟨52254654113226745998596189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34836436075484497332397459 52254654113226745998596189)
              ·
                refine ⟨19595495292460029749473571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52254654113226745998596189 19595495292460029749473571)
                ·
                  refine ⟨29393242938690044624210357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19595495292460029749473571 29393242938690044624210357)
                  ·
                    refine ⟨2755616525502191683519721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29393242938690044624210357 2755616525502191683519721)
                    ·
                      refine ⟨2066712394126643762639791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2755616525502191683519721 2066712394126643762639791)
                      ·
                        rfl

theorem cell23_4024908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 3, 1, 5, 2].length) (baseStart_4024908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4024908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4024908 prefixEnd_4024908 := by exact prefixLift 4024908
  have htrace : WordTrace (prefixWord ++ tailWord_4024908) baseStart_4024908 baseEnd_4024908 := by
    simpa [prefixWord, tailWord_4024908, baseEnd_4024908] using wordTrace_append hprefix tailTrace_4024908
  have hstable : (prefixWord ++ tailWord_4024908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4024908).length < 2 ^ (prefixWord ++ tailWord_4024908).sum := by decide
  have hdescent : baseEnd_4024908 < baseStart_4024908 := by decide
  rcases family_descends (prefixWord ++ tailWord_4024908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4024909 : List Nat := [1, 6, 1, 1, 2, 3, 1, 3, 1, 4]
def baseStart_4024909 : Nat := 118140960795 + 4024909 * 2 ^ 59
def prefixEnd_4024909 : Nat := 4983230072969 + 3 ^ 40 * 4024909 * 2
def baseEnd_4024909 : Nat := 688904302535766086242429

theorem tailTrace_4024909 : CollatzResearch.WordTrace tailWord_4024909 prefixEnd_4024909 688904302535766086242429 := by
  unfold tailWord_4024909
  simp only [CollatzResearch.WordTrace]
  refine ⟨146800491375449567575621781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97866994250299711717081187 146800491375449567575621781)
  ·
    refine ⟨6881273033224198480107271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 146800491375449567575621781 6881273033224198480107271)
    ·
      refine ⟨10321909549836297720160907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6881273033224198480107271 10321909549836297720160907)
      ·
        refine ⟨15482864324754446580241361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10321909549836297720160907 15482864324754446580241361)
        ·
          refine ⟨11612148243565834935181021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15482864324754446580241361 11612148243565834935181021)
          ·
            refine ⟨4354555591337188100692883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11612148243565834935181021 4354555591337188100692883)
            ·
              refine ⟨6531833387005782151039325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4354555591337188100692883 6531833387005782151039325)
              ·
                refine ⟨2449437520127168306639747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6531833387005782151039325 2449437520127168306639747)
                ·
                  refine ⟨3674156280190752459959621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2449437520127168306639747 3674156280190752459959621)
                  ·
                    refine ⟨688904302535766086242429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3674156280190752459959621 688904302535766086242429)
                    ·
                      rfl

theorem cell23_4024909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 1, 3, 1, 4].length) (baseStart_4024909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4024909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4024909 prefixEnd_4024909 := by exact prefixLift 4024909
  have htrace : WordTrace (prefixWord ++ tailWord_4024909) baseStart_4024909 baseEnd_4024909 := by
    simpa [prefixWord, tailWord_4024909, baseEnd_4024909] using wordTrace_append hprefix tailTrace_4024909
  have hstable : (prefixWord ++ tailWord_4024909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4024909).length < 2 ^ (prefixWord ++ tailWord_4024909).sum := by decide
  have hdescent : baseEnd_4024909 < baseStart_4024909 := by decide
  rcases family_descends (prefixWord ++ tailWord_4024909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4024921 : List Nat := [1, 2, 1, 2, 2, 1, 1, 1, 7, 1, 4]
def baseStart_4024921 : Nat := 118140960795 + 4024921 * 2 ^ 59
def prefixEnd_4024921 : Nat := 4983230072969 + 3 ^ 40 * 4024921 * 2
def baseEnd_4024921 : Nat := 2066719069375152211777231

theorem tailTrace_4024921 : CollatzResearch.WordTrace tailWord_4024921 prefixEnd_4024921 2066719069375152211777231 := by
  unfold tailWord_4024921
  simp only [CollatzResearch.WordTrace]
  refine ⟨146800929051406093625058617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97867286034270729083372411 146800929051406093625058617)
  ·
    refine ⟨110100696788554570218793963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146800929051406093625058617 110100696788554570218793963)
    ·
      refine ⟨165151045182831855328190945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110100696788554570218793963 165151045182831855328190945)
      ·
        refine ⟨123863283887123891496143209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165151045182831855328190945 123863283887123891496143209)
        ·
          refine ⟨92897462915342918622107407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123863283887123891496143209 92897462915342918622107407)
          ·
            refine ⟨139346194373014377933161111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92897462915342918622107407 139346194373014377933161111)
            ·
              refine ⟨209019291559521566899741667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139346194373014377933161111 209019291559521566899741667)
              ·
                refine ⟨313528937339282350349612501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 209019291559521566899741667 313528937339282350349612501)
                ·
                  refine ⟨7348334468889430086319043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 313528937339282350349612501 7348334468889430086319043)
                  ·
                    refine ⟨11022501703334145129478565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7348334468889430086319043 11022501703334145129478565)
                    ·
                      refine ⟨2066719069375152211777231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11022501703334145129478565 2066719069375152211777231)
                      ·
                        rfl

theorem cell23_4024921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 7, 1, 4].length) (baseStart_4024921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4024921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4024921 prefixEnd_4024921 := by exact prefixLift 4024921
  have htrace : WordTrace (prefixWord ++ tailWord_4024921) baseStart_4024921 baseEnd_4024921 := by
    simpa [prefixWord, tailWord_4024921, baseEnd_4024921] using wordTrace_append hprefix tailTrace_4024921
  have hstable : (prefixWord ++ tailWord_4024921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4024921).length < 2 ^ (prefixWord ++ tailWord_4024921).sum := by decide
  have hdescent : baseEnd_4024921 < baseStart_4024921 := by decide
  rcases family_descends (prefixWord ++ tailWord_4024921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4024926 : List Nat := [4, 4, 1, 2, 1, 2, 1, 1, 3, 4]
def baseStart_4024926 : Nat := 118140960795 + 4024926 * 2 ^ 59
def prefixEnd_4024926 : Nat := 4983230072969 + 3 ^ 40 * 4024926 * 2
def baseEnd_4024926 : Nat := 688907212259474897404903

theorem tailTrace_4024926 : CollatzResearch.WordTrace tailWord_4024926 prefixEnd_4024926 688907212259474897404903 := by
  unfold tailWord_4024926
  simp only [CollatzResearch.WordTrace]
  refine ⟨18350138927048497434873829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97867407610925319652660421 18350138927048497434873829)
  ·
    refine ⟨3440651048821593269038843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18350138927048497434873829 3440651048821593269038843)
    ·
      refine ⟨5160976573232389903558265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3440651048821593269038843 5160976573232389903558265)
      ·
        refine ⟨3870732429924292427668699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5160976573232389903558265 3870732429924292427668699)
        ·
          refine ⟨5806098644886438641503049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3870732429924292427668699 5806098644886438641503049)
          ·
            refine ⟨4354573983664828981127287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5806098644886438641503049 4354573983664828981127287)
            ·
              refine ⟨6531860975497243471690931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4354573983664828981127287 6531860975497243471690931)
              ·
                refine ⟨9797791463245865207536397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6531860975497243471690931 9797791463245865207536397)
                ·
                  refine ⟨3674171798717199452826149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9797791463245865207536397 3674171798717199452826149)
                  ·
                    refine ⟨688907212259474897404903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3674171798717199452826149 688907212259474897404903)
                    ·
                      rfl

theorem cell23_4024926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_4024926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4024926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4024926 prefixEnd_4024926 := by exact prefixLift 4024926
  have htrace : WordTrace (prefixWord ++ tailWord_4024926) baseStart_4024926 baseEnd_4024926 := by
    simpa [prefixWord, tailWord_4024926, baseEnd_4024926] using wordTrace_append hprefix tailTrace_4024926
  have hstable : (prefixWord ++ tailWord_4024926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4024926).length < 2 ^ (prefixWord ++ tailWord_4024926).sum := by decide
  have hdescent : baseEnd_4024926 < baseStart_4024926 := by decide
  rcases family_descends (prefixWord ++ tailWord_4024926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4024938 : List Nat := [3, 1, 3, 2, 1, 1, 2, 2, 3, 1, 4]
def baseStart_4024938 : Nat := 118140960795 + 4024938 * 2 ^ 59
def prefixEnd_4024938 : Nat := 4983230072969 + 3 ^ 40 * 4024938 * 2
def baseEnd_4024938 : Nat := 2066727798546278645264653

theorem tailTrace_4024938 : CollatzResearch.WordTrace tailWord_4024938 prefixEnd_4024938 2066727798546278645264653 := by
  unfold tailWord_4024938
  simp only [CollatzResearch.WordTrace]
  refine ⟨36700387273086126382106867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97867699394896337018951645 36700387273086126382106867)
  ·
    refine ⟨55050580909629189573160301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36700387273086126382106867 55050580909629189573160301)
    ·
      refine ⟨20643967841110946089935113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55050580909629189573160301 20643967841110946089935113)
      ·
        refine ⟨15482975880833209567451335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20643967841110946089935113 15482975880833209567451335)
        ·
          refine ⟨23224463821249814351177003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15482975880833209567451335 23224463821249814351177003)
          ·
            refine ⟨34836695731874721526765505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23224463821249814351177003 34836695731874721526765505)
            ·
              refine ⟨26127521798906041145074129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34836695731874721526765505 26127521798906041145074129)
              ·
                refine ⟨19595641349179530858805597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26127521798906041145074129 19595641349179530858805597)
                ·
                  refine ⟨7348365505942324072052099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19595641349179530858805597 7348365505942324072052099)
                  ·
                    refine ⟨11022548258913486108078149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7348365505942324072052099 11022548258913486108078149)
                    ·
                      refine ⟨2066727798546278645264653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11022548258913486108078149 2066727798546278645264653)
                      ·
                        rfl

theorem cell23_4024938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_4024938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4024938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4024938 prefixEnd_4024938 := by exact prefixLift 4024938
  have htrace : WordTrace (prefixWord ++ tailWord_4024938) baseStart_4024938 baseEnd_4024938 := by
    simpa [prefixWord, tailWord_4024938, baseEnd_4024938] using wordTrace_append hprefix tailTrace_4024938
  have hstable : (prefixWord ++ tailWord_4024938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4024938).length < 2 ^ (prefixWord ++ tailWord_4024938).sum := by decide
  have hdescent : baseEnd_4024938 < baseStart_4024938 := by decide
  rcases family_descends (prefixWord ++ tailWord_4024938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4024951 : List Nat := [1, 1, 3, 1, 1, 3, 4, 1, 1, 1, 6]
def baseStart_4024951 : Nat := 118140960795 + 4024951 * 2 ^ 59
def prefixEnd_4024951 : Nat := 4983230072969 + 3 ^ 40 * 4024951 * 2
def baseEnd_4024951 : Nat := 2066734473794787094402093

theorem tailTrace_4024951 : CollatzResearch.WordTrace tailWord_4024951 prefixEnd_4024951 2066734473794787094402093 := by
  unfold tailWord_4024951
  simp only [CollatzResearch.WordTrace]
  refine ⟨146802023241297408748650707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97868015494198272499100471 146802023241297408748650707)
  ·
    refine ⟨220203034861946113122976061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146802023241297408748650707 220203034861946113122976061)
    ·
      refine ⟨82576138073229792421116023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220203034861946113122976061 82576138073229792421116023)
      ·
        refine ⟨123864207109844688631674035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82576138073229792421116023 123864207109844688631674035)
        ·
          refine ⟨185796310664767032947511053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123864207109844688631674035 185796310664767032947511053)
          ·
            refine ⟨69673616499287637355316645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 185796310664767032947511053 69673616499287637355316645)
            ·
              refine ⟨13063803093616432004121871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69673616499287637355316645 13063803093616432004121871)
              ·
                refine ⟨19595704640424648006182807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13063803093616432004121871 19595704640424648006182807)
                ·
                  refine ⟨29393556960636972009274211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19595704640424648006182807 29393556960636972009274211)
                  ·
                    refine ⟨44090335440955458013911317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29393556960636972009274211 44090335440955458013911317)
                    ·
                      refine ⟨2066734473794787094402093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44090335440955458013911317 2066734473794787094402093)
                      ·
                        rfl

theorem cell23_4024951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 1, 1, 1, 6].length) (baseStart_4024951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4024951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4024951 prefixEnd_4024951 := by exact prefixLift 4024951
  have htrace : WordTrace (prefixWord ++ tailWord_4024951) baseStart_4024951 baseEnd_4024951 := by
    simpa [prefixWord, tailWord_4024951, baseEnd_4024951] using wordTrace_append hprefix tailTrace_4024951
  have hstable : (prefixWord ++ tailWord_4024951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4024951).length < 2 ^ (prefixWord ++ tailWord_4024951).sum := by decide
  have hdescent : baseEnd_4024951 < baseStart_4024951 := by decide
  rcases family_descends (prefixWord ++ tailWord_4024951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4024961 : List Nat := [1, 2, 4, 2, 1, 1, 1, 11]
def baseStart_4024961 : Nat := 118140960795 + 4024961 * 2 ^ 59
def prefixEnd_4024961 : Nat := 4983230072969 + 3 ^ 40 * 4024961 * 2
def baseEnd_4024961 : Nat := 76545911429678965010261

theorem tailTrace_4024961 : CollatzResearch.WordTrace tailWord_4024961 prefixEnd_4024961 76545911429678965010261 := by
  unfold tailWord_4024961
  simp only [CollatzResearch.WordTrace]
  refine ⟨146802387971261180456514737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97868258647507453637676491 146802387971261180456514737)
  ·
    refine ⟨110101790978445885342386053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146802387971261180456514737 110101790978445885342386053)
    ·
      refine ⟨20644085808458603501697385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110101790978445885342386053 20644085808458603501697385)
      ·
        refine ⟨15483064356343952626273039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20644085808458603501697385 15483064356343952626273039)
        ·
          refine ⟨23224596534515928939409559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15483064356343952626273039 23224596534515928939409559)
          ·
            refine ⟨34836894801773893409114339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23224596534515928939409559 34836894801773893409114339)
            ·
              refine ⟨52255342202660840113671509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34836894801773893409114339 52255342202660840113671509)
              ·
                refine ⟨76545911429678965010261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 52255342202660840113671509 76545911429678965010261)
                ·
                  rfl

theorem cell23_4024961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 11].length) (baseStart_4024961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4024961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4024961 prefixEnd_4024961 := by exact prefixLift 4024961
  have htrace : WordTrace (prefixWord ++ tailWord_4024961) baseStart_4024961 baseEnd_4024961 := by
    simpa [prefixWord, tailWord_4024961, baseEnd_4024961] using wordTrace_append hprefix tailTrace_4024961
  have hstable : (prefixWord ++ tailWord_4024961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4024961).length < 2 ^ (prefixWord ++ tailWord_4024961).sum := by decide
  have hdescent : baseEnd_4024961 < baseStart_4024961 := by decide
  rcases family_descends (prefixWord ++ tailWord_4024961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4025005 : List Nat := [1, 5, 2, 1, 1, 2, 1, 3, 1, 3, 3]
def baseStart_4025005 : Nat := 118140960795 + 4025005 * 2 ^ 59
def prefixEnd_4025005 : Nat := 4983230072969 + 3 ^ 40 * 4025005 * 2
def baseEnd_4025005 : Nat := 2066762201750129883126845

theorem tailTrace_4025005 : CollatzResearch.WordTrace tailWord_4025005 prefixEnd_4025005 2066762201750129883126845 := by
  unfold tailWord_4025005
  simp only [CollatzResearch.WordTrace]
  refine ⟨146803992783101775971116469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97869328522067850647410979 146803992783101775971116469)
  ·
    refine ⟨13762874323415791497292169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 146803992783101775971116469 13762874323415791497292169)
    ·
      refine ⟨10322155742561843622969127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13762874323415791497292169 10322155742561843622969127)
      ·
        refine ⟨15483233613842765434453691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10322155742561843622969127 15483233613842765434453691)
        ·
          refine ⟨23224850420764148151680537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15483233613842765434453691 23224850420764148151680537)
          ·
            refine ⟨17418637815573111113760403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23224850420764148151680537 17418637815573111113760403)
            ·
              refine ⟨26127956723359666670640605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17418637815573111113760403 26127956723359666670640605)
              ·
                refine ⟨9797983771259875001490227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26127956723359666670640605 9797983771259875001490227)
                ·
                  refine ⟨14696975656889812502235341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9797983771259875001490227 14696975656889812502235341)
                  ·
                    refine ⟨5511365871333679688338253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14696975656889812502235341 5511365871333679688338253)
                    ·
                      refine ⟨2066762201750129883126845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5511365871333679688338253 2066762201750129883126845)
                      ·
                        rfl

theorem cell23_4025005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 3, 1, 3, 3].length) (baseStart_4025005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4025005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4025005 prefixEnd_4025005 := by exact prefixLift 4025005
  have htrace : WordTrace (prefixWord ++ tailWord_4025005) baseStart_4025005 baseEnd_4025005 := by
    simpa [prefixWord, tailWord_4025005, baseEnd_4025005] using wordTrace_append hprefix tailTrace_4025005
  have hstable : (prefixWord ++ tailWord_4025005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4025005).length < 2 ^ (prefixWord ++ tailWord_4025005).sum := by decide
  have hdescent : baseEnd_4025005 < baseStart_4025005 := by decide
  rcases family_descends (prefixWord ++ tailWord_4025005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4025032 : List Nat := [2, 1, 3, 1, 2, 4, 1, 3, 1, 3, 2]
def baseStart_4025032 : Nat := 118140960795 + 4025032 * 2 ^ 59
def prefixEnd_4025032 : Nat := 4983230072969 + 3 ^ 40 * 4025032 * 2
def baseEnd_4025032 : Nat := 2066776065727801277489221

theorem tailTrace_4025032 : CollatzResearch.WordTrace tailWord_4025032 prefixEnd_4025032 2066776065727801277489221 := by
  unfold tailWord_4025032
  simp only [CollatzResearch.WordTrace]
  refine ⟨73402488777001979791174675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97869985036002639721566233 73402488777001979791174675)
  ·
    refine ⟨110103733165502969686762013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73402488777001979791174675 110103733165502969686762013)
    ·
      refine ⟨41288899937063613632535755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110103733165502969686762013 41288899937063613632535755)
      ·
        refine ⟨61933349905595420448803633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41288899937063613632535755 61933349905595420448803633)
        ·
          refine ⟨46450012429196565336602725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61933349905595420448803633 46450012429196565336602725)
          ·
            refine ⟨8709377330474356000613011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46450012429196565336602725 8709377330474356000613011)
            ·
              refine ⟨13064065995711534000919517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8709377330474356000613011 13064065995711534000919517)
              ·
                refine ⟨4899024748391825250344819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13064065995711534000919517 4899024748391825250344819)
                ·
                  refine ⟨7348537122587737875517229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4899024748391825250344819 7348537122587737875517229)
                  ·
                    refine ⟨2755701420970401703318961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7348537122587737875517229 2755701420970401703318961)
                    ·
                      refine ⟨2066776065727801277489221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2755701420970401703318961 2066776065727801277489221)
                      ·
                        rfl

theorem cell23_4025032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 3, 1, 3, 2].length) (baseStart_4025032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4025032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4025032 prefixEnd_4025032 := by exact prefixLift 4025032
  have htrace : WordTrace (prefixWord ++ tailWord_4025032) baseStart_4025032 baseEnd_4025032 := by
    simpa [prefixWord, tailWord_4025032, baseEnd_4025032] using wordTrace_append hprefix tailTrace_4025032
  have hstable : (prefixWord ++ tailWord_4025032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4025032).length < 2 ^ (prefixWord ++ tailWord_4025032).sum := by decide
  have hdescent : baseEnd_4025032 < baseStart_4025032 := by decide
  rcases family_descends (prefixWord ++ tailWord_4025032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4025038 : List Nat := [4, 1, 1, 1, 3, 2, 1, 2, 2, 6]
def baseStart_4025038 : Nat := 118140960795 + 4025038 * 2 ^ 59
def prefixEnd_4025038 : Nat := 4983230072969 + 3 ^ 40 * 4025038 * 2
def baseEnd_4025038 : Nat := 688926382203909418004731

theorem tailTrace_4025038 : CollatzResearch.WordTrace tailWord_4025038 prefixEnd_4025038 688926382203909418004731 := by
  unfold tailWord_4025038
  simp only [CollatzResearch.WordTrace]
  refine ⟨18350649548997777825883471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97870130927988148404711845 18350649548997777825883471)
  ·
    refine ⟨27525974323496666738825207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18350649548997777825883471 27525974323496666738825207)
    ·
      refine ⟨41288961485245000108237811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27525974323496666738825207 41288961485245000108237811)
      ·
        refine ⟨61933442227867500162356717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41288961485245000108237811 61933442227867500162356717)
        ·
          refine ⟨23225040835450312560883769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61933442227867500162356717 23225040835450312560883769)
          ·
            refine ⟨17418780626587734420662827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23225040835450312560883769 17418780626587734420662827)
            ·
              refine ⟨26128170939881601630994241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17418780626587734420662827 26128170939881601630994241)
              ·
                refine ⟨19596128204911201223245681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26128170939881601630994241 19596128204911201223245681)
                ·
                  refine ⟨14697096153683400917434261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19596128204911201223245681 14697096153683400917434261)
                  ·
                    refine ⟨688926382203909418004731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14697096153683400917434261 688926382203909418004731)
                    ·
                      rfl

theorem cell23_4025038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 2, 2, 6].length) (baseStart_4025038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4025038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4025038 prefixEnd_4025038 := by exact prefixLift 4025038
  have htrace : WordTrace (prefixWord ++ tailWord_4025038) baseStart_4025038 baseEnd_4025038 := by
    simpa [prefixWord, tailWord_4025038, baseEnd_4025038] using wordTrace_append hprefix tailTrace_4025038
  have hstable : (prefixWord ++ tailWord_4025038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4025038).length < 2 ^ (prefixWord ++ tailWord_4025038).sum := by decide
  have hdescent : baseEnd_4025038 < baseStart_4025038 := by decide
  rcases family_descends (prefixWord ++ tailWord_4025038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4025148 : List Nat := [2, 2, 2, 2, 1, 1, 1, 3, 2, 1, 6]
def baseStart_4025148 : Nat := 118140960795 + 4025148 * 2 ^ 59
def prefixEnd_4025148 : Nat := 4983230072969 + 3 ^ 40 * 4025148 * 2
def baseEnd_4025148 : Nat := 2066835629483722823638687

theorem tailTrace_4025148 : CollatzResearch.WordTrace tailWord_4025148 prefixEnd_4025148 2066835629483722823638687 := by
  unfold tailWord_4025148
  simp only [CollatzResearch.WordTrace]
  refine ⟨73404604210791855696786049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97872805614389140929048065 73404604210791855696786049)
  ·
    refine ⟨55053453158093891772589537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73404604210791855696786049 55053453158093891772589537)
    ·
      refine ⟨41290089868570418829442153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55053453158093891772589537 41290089868570418829442153)
      ·
        refine ⟨30967567401427814122081615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41290089868570418829442153 30967567401427814122081615)
        ·
          refine ⟨46451351102141721183122423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30967567401427814122081615 46451351102141721183122423)
          ·
            refine ⟨69677026653212581774683635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46451351102141721183122423 69677026653212581774683635)
            ·
              refine ⟨104515539979818872662025453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69677026653212581774683635 104515539979818872662025453)
              ·
                refine ⟨39193327492432077248259545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104515539979818872662025453 39193327492432077248259545)
                ·
                  refine ⟨29394995619324057936194659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39193327492432077248259545 29394995619324057936194659)
                  ·
                    refine ⟨44092493428986086904291989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29394995619324057936194659 44092493428986086904291989)
                    ·
                      refine ⟨2066835629483722823638687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44092493428986086904291989 2066835629483722823638687)
                      ·
                        rfl

theorem cell23_4025148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 3, 2, 1, 6].length) (baseStart_4025148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4025148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4025148 prefixEnd_4025148 := by exact prefixLift 4025148
  have htrace : WordTrace (prefixWord ++ tailWord_4025148) baseStart_4025148 baseEnd_4025148 := by
    simpa [prefixWord, tailWord_4025148, baseEnd_4025148] using wordTrace_append hprefix tailTrace_4025148
  have hstable : (prefixWord ++ tailWord_4025148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4025148).length < 2 ^ (prefixWord ++ tailWord_4025148).sum := by decide
  have hdescent : baseEnd_4025148 < baseStart_4025148 := by decide
  rcases family_descends (prefixWord ++ tailWord_4025148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4025153 : List Nat := [1, 2, 5, 3, 2, 1, 2, 2, 5]
def baseStart_4025153 : Nat := 118140960795 + 4025153 * 2 ^ 59
def prefixEnd_4025153 : Nat := 4983230072969 + 3 ^ 40 * 4025153 * 2
def baseEnd_4025153 : Nat := 229648688542999478230685

theorem tailTrace_4025153 : CollatzResearch.WordTrace tailWord_4025153 prefixEnd_4025153 229648688542999478230685 := by
  unfold tailWord_4025153
  simp only [CollatzResearch.WordTrace]
  refine ⟨146809390786565597247504113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97872927191043731498336075 146809390786565597247504113)
  ·
    refine ⟨110107043089924197935628085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146809390786565597247504113 110107043089924197935628085)
    ·
      refine ⟨10322535289680393556465133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 110107043089924197935628085 10322535289680393556465133)
      ·
        refine ⟨3870950733630147583674425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10322535289680393556465133 3870950733630147583674425)
        ·
          refine ⟨2903213050222610687755819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3870950733630147583674425 2903213050222610687755819)
          ·
            refine ⟨4354819575333916031633729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2903213050222610687755819 4354819575333916031633729)
            ·
              refine ⟨3266114681500437023725297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4354819575333916031633729 3266114681500437023725297)
              ·
                refine ⟨2449586011125327767793973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3266114681500437023725297 2449586011125327767793973)
                ·
                  refine ⟨229648688542999478230685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2449586011125327767793973 229648688542999478230685)
                  ·
                    rfl

theorem cell23_4025153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 2, 2, 5].length) (baseStart_4025153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4025153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4025153 prefixEnd_4025153 := by exact prefixLift 4025153
  have htrace : WordTrace (prefixWord ++ tailWord_4025153) baseStart_4025153 baseEnd_4025153 := by
    simpa [prefixWord, tailWord_4025153, baseEnd_4025153] using wordTrace_append hprefix tailTrace_4025153
  have hstable : (prefixWord ++ tailWord_4025153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4025153).length < 2 ^ (prefixWord ++ tailWord_4025153).sum := by decide
  have hdescent : baseEnd_4025153 < baseStart_4025153 := by decide
  rcases family_descends (prefixWord ++ tailWord_4025153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4025155 : List Nat := [1, 1, 1, 3, 1, 4, 1, 4, 2, 2, 3]
def baseStart_4025155 : Nat := 118140960795 + 4025155 * 2 ^ 59
def prefixEnd_4025155 : Nat := 4983230072969 + 3 ^ 40 * 4025155 * 2
def baseEnd_4025155 : Nat := 2066839223848304296251155

theorem tailTrace_4025155 : CollatzResearch.WordTrace tailWord_4025155 prefixEnd_4025155 2066839223848304296251155 := by
  unfold tailWord_4025155
  simp only [CollatzResearch.WordTrace]
  refine ⟨146809463732558351589076919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97872975821705567726051279 146809463732558351589076919)
  ·
    refine ⟨220214195598837527383615379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146809463732558351589076919 220214195598837527383615379)
    ·
      refine ⟨330321293398256291075423069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220214195598837527383615379 330321293398256291075423069)
      ·
        refine ⟨123870485024346109153283651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 330321293398256291075423069 123870485024346109153283651)
        ·
          refine ⟨185805727536519163729925477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123870485024346109153283651 185805727536519163729925477)
          ·
            refine ⟨34838573913097343199361027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 185805727536519163729925477 34838573913097343199361027)
            ·
              refine ⟨52257860869646014799041541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34838573913097343199361027 52257860869646014799041541)
              ·
                refine ⟨9798348913058627774820289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52257860869646014799041541 9798348913058627774820289)
                ·
                  refine ⟨7348761684793970831115217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9798348913058627774820289 7348761684793970831115217)
                  ·
                    refine ⟨5511571263595478123336413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7348761684793970831115217 5511571263595478123336413)
                    ·
                      refine ⟨2066839223848304296251155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5511571263595478123336413 2066839223848304296251155)
                      ·
                        rfl

theorem cell23_4025155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 4, 2, 2, 3].length) (baseStart_4025155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4025155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4025155 prefixEnd_4025155 := by exact prefixLift 4025155
  have htrace : WordTrace (prefixWord ++ tailWord_4025155) baseStart_4025155 baseEnd_4025155 := by
    simpa [prefixWord, tailWord_4025155, baseEnd_4025155] using wordTrace_append hprefix tailTrace_4025155
  have hstable : (prefixWord ++ tailWord_4025155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4025155).length < 2 ^ (prefixWord ++ tailWord_4025155).sum := by decide
  have hdescent : baseEnd_4025155 < baseStart_4025155 := by decide
  rcases family_descends (prefixWord ++ tailWord_4025155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4025175 : List Nat := [1, 1, 3, 2, 4, 1, 2, 3, 6]
def baseStart_4025175 : Nat := 118140960795 + 4025175 * 2 ^ 59
def prefixEnd_4025175 : Nat := 4983230072969 + 3 ^ 40 * 4025175 * 2
def baseEnd_4025175 : Nat := 229649943717932690889007

theorem tailTrace_4025175 : CollatzResearch.WordTrace tailWord_4025175 prefixEnd_4025175 229649943717932690889007 := by
  unfold tailWord_4025175
  simp only [CollatzResearch.WordTrace]
  refine ⟨146810193192485895004804979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97873462128323930003203319 146810193192485895004804979)
  ·
    refine ⟨220215289788728842507207469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146810193192485895004804979 220215289788728842507207469)
    ·
      refine ⟨82580733670773315940202801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220215289788728842507207469 82580733670773315940202801)
      ·
        refine ⟨61935550253079986955152101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82580733670773315940202801 61935550253079986955152101)
        ·
          refine ⟨11612915672452497554091019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61935550253079986955152101 11612915672452497554091019)
          ·
            refine ⟨17419373508678746331136529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11612915672452497554091019 17419373508678746331136529)
            ·
              refine ⟨13064530131509059748352397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17419373508678746331136529 13064530131509059748352397)
              ·
                refine ⟨4899198799315897405632149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13064530131509059748352397 4899198799315897405632149)
                ·
                  refine ⟨229649943717932690889007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4899198799315897405632149 229649943717932690889007)
                  ·
                    rfl

theorem cell23_4025175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 3, 6].length) (baseStart_4025175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4025175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4025175 prefixEnd_4025175 := by exact prefixLift 4025175
  have htrace : WordTrace (prefixWord ++ tailWord_4025175) baseStart_4025175 baseEnd_4025175 := by
    simpa [prefixWord, tailWord_4025175, baseEnd_4025175] using wordTrace_append hprefix tailTrace_4025175
  have hstable : (prefixWord ++ tailWord_4025175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4025175).length < 2 ^ (prefixWord ++ tailWord_4025175).sum := by decide
  have hdescent : baseEnd_4025175 < baseStart_4025175 := by decide
  rcases family_descends (prefixWord ++ tailWord_4025175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4025186 : List Nat := [3, 3, 2, 1, 4, 1, 1, 1, 2, 1, 4]
def baseStart_4025186 : Nat := 118140960795 + 4025186 * 2 ^ 59
def prefixEnd_4025186 : Nat := 4983230072969 + 3 ^ 40 * 4025186 * 2
def baseEnd_4025186 : Nat := 2066855141748593674963513

theorem tailTrace_4025186 : CollatzResearch.WordTrace tailWord_4025186 prefixEnd_4025186 2066855141748593674963513 := by
  unfold tailWord_4025186
  simp only [CollatzResearch.WordTrace]
  refine ⟨36702648598861510970863853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97873729596964029255636941 36702648598861510970863853)
  ·
    refine ⟨13763493224573066614073945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36702648598861510970863853 13763493224573066614073945)
    ·
      refine ⟨10322619918429799960555459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13763493224573066614073945 10322619918429799960555459)
      ·
        refine ⟨15483929877644699940833189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10322619918429799960555459 15483929877644699940833189)
        ·
          refine ⟨2903236852058381238906223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15483929877644699940833189 2903236852058381238906223)
          ·
            refine ⟨4354855278087571858359335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2903236852058381238906223 4354855278087571858359335)
            ·
              refine ⟨6532282917131357787539003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4354855278087571858359335 6532282917131357787539003)
              ·
                refine ⟨9798424375697036681308505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6532282917131357787539003 9798424375697036681308505)
                ·
                  refine ⟨7348818281772777510981379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9798424375697036681308505 7348818281772777510981379)
                  ·
                    refine ⟨11023227422659166266472069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7348818281772777510981379 11023227422659166266472069)
                    ·
                      refine ⟨2066855141748593674963513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11023227422659166266472069 2066855141748593674963513)
                      ·
                        rfl

theorem cell23_4025186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 1, 1, 2, 1, 4].length) (baseStart_4025186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4025186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4025186 prefixEnd_4025186 := by exact prefixLift 4025186
  have htrace : WordTrace (prefixWord ++ tailWord_4025186) baseStart_4025186 baseEnd_4025186 := by
    simpa [prefixWord, tailWord_4025186, baseEnd_4025186] using wordTrace_append hprefix tailTrace_4025186
  have hstable : (prefixWord ++ tailWord_4025186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4025186).length < 2 ^ (prefixWord ++ tailWord_4025186).sum := by decide
  have hdescent : baseEnd_4025186 < baseStart_4025186 := by decide
  rcases family_descends (prefixWord ++ tailWord_4025186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4025212 : List Nat := [2, 2, 2, 1, 1, 1, 1, 6, 2, 3, 2]
def baseStart_4025212 : Nat := 118140960795 + 4025212 * 2 ^ 59
def prefixEnd_4025212 : Nat := 4983230072969 + 3 ^ 40 * 4025212 * 2
def baseEnd_4025212 : Nat := 2066868492245610573238393

theorem tailTrace_4025212 : CollatzResearch.WordTrace tailWord_4025212 prefixEnd_4025212 2066868492245610573238393 := by
  unfold tailWord_4025212
  simp only [CollatzResearch.WordTrace]
  refine ⟨73405771346675925161950945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97874361795567900215934593 73405771346675925161950945)
  ·
    refine ⟨55054328510006943871463209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73405771346675925161950945 55054328510006943871463209)
    ·
      refine ⟨41290746382505207903597407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55054328510006943871463209 41290746382505207903597407)
      ·
        refine ⟨61936119573757811855396111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41290746382505207903597407 61936119573757811855396111)
        ·
          refine ⟨92904179360636717783094167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61936119573757811855396111 92904179360636717783094167)
          ·
            refine ⟨139356269040955076674641251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92904179360636717783094167 139356269040955076674641251)
            ·
              refine ⟨209034403561432615011961877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139356269040955076674641251 209034403561432615011961877)
              ·
                refine ⟨9798487666942153828685713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 209034403561432615011961877 9798487666942153828685713)
                ·
                  refine ⟨7348865750206615371514285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9798487666942153828685713 7348865750206615371514285)
                  ·
                    refine ⟨2755824656327480764317857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7348865750206615371514285 2755824656327480764317857)
                    ·
                      refine ⟨2066868492245610573238393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2755824656327480764317857 2066868492245610573238393)
                      ·
                        rfl

theorem cell23_4025212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 6, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 6, 2, 3, 2].length) (baseStart_4025212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4025212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4025212 prefixEnd_4025212 := by exact prefixLift 4025212
  have htrace : WordTrace (prefixWord ++ tailWord_4025212) baseStart_4025212 baseEnd_4025212 := by
    simpa [prefixWord, tailWord_4025212, baseEnd_4025212] using wordTrace_append hprefix tailTrace_4025212
  have hstable : (prefixWord ++ tailWord_4025212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4025212).length < 2 ^ (prefixWord ++ tailWord_4025212).sum := by decide
  have hdescent : baseEnd_4025212 < baseStart_4025212 := by decide
  rcases family_descends (prefixWord ++ tailWord_4025212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4025219 : List Nat := [1, 1, 1, 3, 4, 1, 1, 6, 1, 1, 3]
def baseStart_4025219 : Nat := 118140960795 + 4025219 * 2 ^ 59
def prefixEnd_4025219 : Nat := 4983230072969 + 3 ^ 40 * 4025219 * 2
def baseEnd_4025219 : Nat := 2066872086610192045850861

theorem tailTrace_4025219 : CollatzResearch.WordTrace tailWord_4025219 prefixEnd_4025219 2066872086610192045850861 := by
  unfold tailWord_4025219
  simp only [CollatzResearch.WordTrace]
  refine ⟨146811798004326490519406711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97874532002884327012937807 146811798004326490519406711)
  ·
    refine ⟨220217697006489735779110067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146811798004326490519406711 220217697006489735779110067)
    ·
      refine ⟨330326545509734603668665101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220217697006489735779110067 330326545509734603668665101)
      ·
        refine ⟨123872454566150476375749413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 330326545509734603668665101 123872454566150476375749413)
        ·
          refine ⟨23226085231153214320453015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 123872454566150476375749413 23226085231153214320453015)
          ·
            refine ⟨34839127846729821480679523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23226085231153214320453015 34839127846729821480679523)
            ·
              refine ⟨52258691770094732221019285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34839127846729821480679523 52258691770094732221019285)
              ·
                refine ⟨2449626176723190572860279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 52258691770094732221019285 2449626176723190572860279)
                ·
                  refine ⟨3674439265084785859290419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2449626176723190572860279 3674439265084785859290419)
                  ·
                    refine ⟨5511658897627178788935629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3674439265084785859290419 5511658897627178788935629)
                    ·
                      refine ⟨2066872086610192045850861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5511658897627178788935629 2066872086610192045850861)
                      ·
                        rfl

theorem cell23_4025219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 6, 1, 1, 3].length) (baseStart_4025219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4025219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4025219 prefixEnd_4025219 := by exact prefixLift 4025219
  have htrace : WordTrace (prefixWord ++ tailWord_4025219) baseStart_4025219 baseEnd_4025219 := by
    simpa [prefixWord, tailWord_4025219, baseEnd_4025219] using wordTrace_append hprefix tailTrace_4025219
  have hstable : (prefixWord ++ tailWord_4025219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4025219).length < 2 ^ (prefixWord ++ tailWord_4025219).sum := by decide
  have hdescent : baseEnd_4025219 < baseStart_4025219 := by decide
  rcases family_descends (prefixWord ++ tailWord_4025219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4025245 : List Nat := [1, 4, 2, 1, 2, 1, 1, 2, 3, 1, 5]
def baseStart_4025245 : Nat := 118140960795 + 4025245 * 2 ^ 59
def prefixEnd_4025245 : Nat := 4983230072969 + 3 ^ 40 * 4025245 * 2
def baseEnd_4025245 : Nat := 2066885437107208944125741

theorem tailTrace_4025245 : CollatzResearch.WordTrace tailWord_4025245 prefixEnd_4025245 2066885437107208944125741 := by
  unfold tailWord_4025245
  simp only [CollatzResearch.WordTrace]
  refine ⟨146812746302232296959853189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97875164201488197973235459 146812746302232296959853189)
  ·
    refine ⟨27527389931668555679972473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146812746302232296959853189 27527389931668555679972473)
    ·
      refine ⟨20645542448751416759979355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27527389931668555679972473 20645542448751416759979355)
      ·
        refine ⟨30968313673127125139969033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20645542448751416759979355 30968313673127125139969033)
        ·
          refine ⟨23226235254845343854976775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30968313673127125139969033 23226235254845343854976775)
          ·
            refine ⟨34839352882268015782465163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23226235254845343854976775 34839352882268015782465163)
            ·
              refine ⟨52259029323402023673697745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34839352882268015782465163 52259029323402023673697745)
              ·
                refine ⟨39194271992551517755273309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52259029323402023673697745 39194271992551517755273309)
                ·
                  refine ⟨14697851997206819158227491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39194271992551517755273309 14697851997206819158227491)
                  ·
                    refine ⟨22046777995810228737341237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14697851997206819158227491 22046777995810228737341237)
                    ·
                      refine ⟨2066885437107208944125741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22046777995810228737341237 2066885437107208944125741)
                      ·
                        rfl

theorem cell23_4025245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 2, 3, 1, 5].length) (baseStart_4025245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4025245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4025245 prefixEnd_4025245 := by exact prefixLift 4025245
  have htrace : WordTrace (prefixWord ++ tailWord_4025245) baseStart_4025245 baseEnd_4025245 := by
    simpa [prefixWord, tailWord_4025245, baseEnd_4025245] using wordTrace_append hprefix tailTrace_4025245
  have hstable : (prefixWord ++ tailWord_4025245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4025245).length < 2 ^ (prefixWord ++ tailWord_4025245).sum := by decide
  have hdescent : baseEnd_4025245 < baseStart_4025245 := by decide
  rcases family_descends (prefixWord ++ tailWord_4025245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4025292 : List Nat := [2, 2, 1, 4, 1, 1, 2, 3, 1, 3, 3]
def baseStart_4025292 : Nat := 118140960795 + 4025292 * 2 ^ 59
def prefixEnd_4025292 : Nat := 4983230072969 + 3 ^ 40 * 4025292 * 2
def baseEnd_4025292 : Nat := 2066909570697970260238025

theorem tailTrace_4025292 : CollatzResearch.WordTrace tailWord_4025292 prefixEnd_4025292 2066909570697970260238025 := by
  unfold tailWord_4025292
  simp only [CollatzResearch.WordTrace]
  refine ⟨73407230266531011993407065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97876307022041349324542753 73407230266531011993407065)
  ·
    refine ⟨55055422699898258995055299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73407230266531011993407065 55055422699898258995055299)
    ·
      refine ⟨82583134049847388492582949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55055422699898258995055299 82583134049847388492582949)
      ·
        refine ⟨15484337634346385342359303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82583134049847388492582949 15484337634346385342359303)
        ·
          refine ⟨23226506451519578013538955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15484337634346385342359303 23226506451519578013538955)
          ·
            refine ⟨34839759677279367020308433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23226506451519578013538955 34839759677279367020308433)
            ·
              refine ⟨26129819757959525265231325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34839759677279367020308433 26129819757959525265231325)
              ·
                refine ⟨9798682409234821974461747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26129819757959525265231325 9798682409234821974461747)
                ·
                  refine ⟨14698023613852232961692621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9798682409234821974461747 14698023613852232961692621)
                  ·
                    refine ⟨5511758855194587360634733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14698023613852232961692621 5511758855194587360634733)
                    ·
                      refine ⟨2066909570697970260238025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5511758855194587360634733 2066909570697970260238025)
                      ·
                        rfl

theorem cell23_4025292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 3, 1, 3, 3].length) (baseStart_4025292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4025292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4025292 prefixEnd_4025292 := by exact prefixLift 4025292
  have htrace : WordTrace (prefixWord ++ tailWord_4025292) baseStart_4025292 baseEnd_4025292 := by
    simpa [prefixWord, tailWord_4025292, baseEnd_4025292] using wordTrace_append hprefix tailTrace_4025292
  have hstable : (prefixWord ++ tailWord_4025292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4025292).length < 2 ^ (prefixWord ++ tailWord_4025292).sum := by decide
  have hdescent : baseEnd_4025292 < baseStart_4025292 := by decide
  rcases family_descends (prefixWord ++ tailWord_4025292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4025293 : List Nat := [1, 6, 3, 1, 1, 1, 1, 1, 3, 1, 4]
def baseStart_4025293 : Nat := 118140960795 + 4025293 * 2 ^ 59
def prefixEnd_4025293 : Nat := 4983230072969 + 3 ^ 40 * 4025293 * 2
def baseEnd_4025293 : Nat := 2066910084178624756325521

theorem tailTrace_4025293 : CollatzResearch.WordTrace tailWord_4025293 prefixEnd_4025293 2066910084178624756325521 := by
  unfold tailWord_4025293
  simp only [CollatzResearch.WordTrace]
  refine ⟨146814497006058401157600533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97876331337372267438400355 146814497006058401157600533)
  ·
    refine ⟨6881929547158987554262525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 146814497006058401157600533 6881929547158987554262525)
    ·
      refine ⟨2580723580184620332848447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6881929547158987554262525 2580723580184620332848447)
      ·
        refine ⟨3871085370276930499272671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2580723580184620332848447 3871085370276930499272671)
        ·
          refine ⟨5806628055415395748909007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3871085370276930499272671 5806628055415395748909007)
          ·
            refine ⟨8709942083123093623363511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5806628055415395748909007 8709942083123093623363511)
            ·
              refine ⟨13064913124684640435045267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8709942083123093623363511 13064913124684640435045267)
              ·
                refine ⟨19597369687026960652567901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13064913124684640435045267 19597369687026960652567901)
                ·
                  refine ⟨7349013632635110244712963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19597369687026960652567901 7349013632635110244712963)
                  ·
                    refine ⟨11023520448952665367069445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7349013632635110244712963 11023520448952665367069445)
                    ·
                      refine ⟨2066910084178624756325521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11023520448952665367069445 2066910084178624756325521)
                      ·
                        rfl

theorem cell23_4025293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_4025293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4025293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4025293 prefixEnd_4025293 := by exact prefixLift 4025293
  have htrace : WordTrace (prefixWord ++ tailWord_4025293) baseStart_4025293 baseEnd_4025293 := by
    simpa [prefixWord, tailWord_4025293, baseEnd_4025293] using wordTrace_append hprefix tailTrace_4025293
  have hstable : (prefixWord ++ tailWord_4025293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4025293).length < 2 ^ (prefixWord ++ tailWord_4025293).sum := by decide
  have hdescent : baseEnd_4025293 < baseStart_4025293 := by decide
  rcases family_descends (prefixWord ++ tailWord_4025293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4025309 : List Nat := [1, 4, 3, 1, 2, 2, 1, 2, 1, 3, 3]
def baseStart_4025309 : Nat := 118140960795 + 4025309 * 2 ^ 59
def prefixEnd_4025309 : Nat := 4983230072969 + 3 ^ 40 * 4025309 * 2
def baseEnd_4025309 : Nat := 2066918299869096693725447

theorem tailTrace_4025309 : CollatzResearch.WordTrace tailWord_4025309 prefixEnd_4025309 2066918299869096693725447 := by
  unfold tailWord_4025309
  simp only [CollatzResearch.WordTrace]
  refine ⟨146815080574000435890182981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97876720382666957260121987 146815080574000435890182981)
  ·
    refine ⟨27527827607625081729409309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146815080574000435890182981 27527827607625081729409309)
    ·
      refine ⟨10322935352859405648528491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27527827607625081729409309 10322935352859405648528491)
      ·
        refine ⟨15484403029289108472792737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10322935352859405648528491 15484403029289108472792737)
        ·
          refine ⟨11613302271966831354594553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15484403029289108472792737 11613302271966831354594553)
          ·
            refine ⟨8709976703975123515945915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11613302271966831354594553 8709976703975123515945915)
            ·
              refine ⟨13064965055962685273918873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8709976703975123515945915 13064965055962685273918873)
              ·
                refine ⟨9798723791972013955439155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13064965055962685273918873 9798723791972013955439155)
                ·
                  refine ⟨14698085687958020933158733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9798723791972013955439155 14698085687958020933158733)
                  ·
                    refine ⟨5511782132984257849934525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14698085687958020933158733 5511782132984257849934525)
                    ·
                      refine ⟨2066918299869096693725447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5511782132984257849934525 2066918299869096693725447)
                      ·
                        rfl

theorem cell23_4025309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 2, 1, 3, 3].length) (baseStart_4025309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4025309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4025309 prefixEnd_4025309 := by exact prefixLift 4025309
  have htrace : WordTrace (prefixWord ++ tailWord_4025309) baseStart_4025309 baseEnd_4025309 := by
    simpa [prefixWord, tailWord_4025309, baseEnd_4025309] using wordTrace_append hprefix tailTrace_4025309
  have hstable : (prefixWord ++ tailWord_4025309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4025309).length < 2 ^ (prefixWord ++ tailWord_4025309).sum := by decide
  have hdescent : baseEnd_4025309 < baseStart_4025309 := by decide
  rcases family_descends (prefixWord ++ tailWord_4025309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4025349 : List Nat := [1, 3, 1, 1, 2, 3, 4, 1, 1, 4, 2]
def baseStart_4025349 : Nat := 118140960795 + 4025349 * 2 ^ 59
def prefixEnd_4025349 : Nat := 4983230072969 + 3 ^ 40 * 4025349 * 2
def baseEnd_4025349 : Nat := 2066938839095276537225263

theorem tailTrace_4025349 : CollatzResearch.WordTrace tailWord_4025349 prefixEnd_4025349 2066938839095276537225263 := by
  unfold tailWord_4025349
  simp only [CollatzResearch.WordTrace]
  refine ⟨146816539493855522721639101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97877692995903681814426067 146816539493855522721639101)
  ·
    refine ⟨55056202310195821020614663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146816539493855522721639101 55056202310195821020614663)
    ·
      refine ⟨82584303465293731530921995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55056202310195821020614663 82584303465293731530921995)
      ·
        refine ⟨123876455197940597296382993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82584303465293731530921995 123876455197940597296382993)
        ·
          refine ⟨92907341398455447972287245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123876455197940597296382993 92907341398455447972287245)
          ·
            refine ⟨34840253024420792989607717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92907341398455447972287245 34840253024420792989607717)
            ·
              refine ⟨6532547442078898685551447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34840253024420792989607717 6532547442078898685551447)
              ·
                refine ⟨9798821163118348028327171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6532547442078898685551447 9798821163118348028327171)
                ·
                  refine ⟨14698231744677522042490757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9798821163118348028327171 14698231744677522042490757)
                  ·
                    refine ⟨2755918452127035382967017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14698231744677522042490757 2755918452127035382967017)
                    ·
                      refine ⟨2066938839095276537225263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2755918452127035382967017 2066938839095276537225263)
                      ·
                        rfl

theorem cell23_4025349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 4, 1, 1, 4, 2].length) (baseStart_4025349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4025349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4025349 prefixEnd_4025349 := by exact prefixLift 4025349
  have htrace : WordTrace (prefixWord ++ tailWord_4025349) baseStart_4025349 baseEnd_4025349 := by
    simpa [prefixWord, tailWord_4025349, baseEnd_4025349] using wordTrace_append hprefix tailTrace_4025349
  have hstable : (prefixWord ++ tailWord_4025349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4025349).length < 2 ^ (prefixWord ++ tailWord_4025349).sum := by decide
  have hdescent : baseEnd_4025349 < baseStart_4025349 := by decide
  rcases family_descends (prefixWord ++ tailWord_4025349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4025355 : List Nat := [1, 1, 1, 1, 6, 2, 1, 1, 9]
def baseStart_4025355 : Nat := 118140960795 + 4025355 * 2 ^ 59
def prefixEnd_4025355 : Nat := 4983230072969 + 3 ^ 40 * 4025355 * 2
def baseEnd_4025355 : Nat := 229660213331022612638915

theorem tailTrace_4025355 : CollatzResearch.WordTrace tailWord_4025355 prefixEnd_4025355 229660213331022612638915 := by
  unfold tailWord_4025355
  simp only [CollatzResearch.WordTrace]
  refine ⟨146816758331833785746357519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97877838887889190497571679 146816758331833785746357519)
  ·
    refine ⟨220225137497750678619536279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146816758331833785746357519 220225137497750678619536279)
    ·
      refine ⟨330337706246626017929304419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220225137497750678619536279 330337706246626017929304419)
      ·
        refine ⟨495506559369939026893956629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330337706246626017929304419 495506559369939026893956629)
        ·
          refine ⟨23226869970465891885654217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 495506559369939026893956629 23226869970465891885654217)
          ·
            refine ⟨17420152477849418914240663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23226869970465891885654217 17420152477849418914240663)
            ·
              refine ⟨26130228716774128371360995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17420152477849418914240663 26130228716774128371360995)
              ·
                refine ⟨39195343075161192557041493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26130228716774128371360995 39195343075161192557041493)
                ·
                  refine ⟨229660213331022612638915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 39195343075161192557041493 229660213331022612638915)
                  ·
                    rfl

theorem cell23_4025355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 1, 9].length) (baseStart_4025355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4025355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4025355 prefixEnd_4025355 := by exact prefixLift 4025355
  have htrace : WordTrace (prefixWord ++ tailWord_4025355) baseStart_4025355 baseEnd_4025355 := by
    simpa [prefixWord, tailWord_4025355, baseEnd_4025355] using wordTrace_append hprefix tailTrace_4025355
  have hstable : (prefixWord ++ tailWord_4025355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4025355).length < 2 ^ (prefixWord ++ tailWord_4025355).sum := by decide
  have hdescent : baseEnd_4025355 < baseStart_4025355 := by decide
  rcases family_descends (prefixWord ++ tailWord_4025355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4025383 : List Nat := [1, 1, 7, 1, 1, 2, 1, 1, 4, 2, 2]
def baseStart_4025383 : Nat := 118140960795 + 4025383 * 2 ^ 59
def prefixEnd_4025383 : Nat := 4983230072969 + 3 ^ 40 * 4025383 * 2
def baseEnd_4025383 : Nat := 2066956297437529404200107

theorem tailTrace_4025383 : CollatzResearch.WordTrace tailWord_4025383 prefixEnd_4025383 2066956297437529404200107 := by
  unfold tailWord_4025383
  simp only [CollatzResearch.WordTrace]
  refine ⟨146817779575732346528376803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97878519717154897685584535 146817779575732346528376803)
  ·
    refine ⟨220226669363598519792565205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146817779575732346528376803 220226669363598519792565205)
    ·
      refine ⟨5161562563209340307638247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 220226669363598519792565205 5161562563209340307638247)
      ·
        refine ⟨7742343844814010461457371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5161562563209340307638247 7742343844814010461457371)
        ·
          refine ⟨11613515767221015692186057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7742343844814010461457371 11613515767221015692186057)
          ·
            refine ⟨8710136825415761769139543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11613515767221015692186057 8710136825415761769139543)
            ·
              refine ⟨13065205238123642653709315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8710136825415761769139543 13065205238123642653709315)
              ·
                refine ⟨19597807857185463980563973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13065205238123642653709315 19597807857185463980563973)
                ·
                  refine ⟨3674588973222274496355745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19597807857185463980563973 3674588973222274496355745)
                  ·
                    refine ⟨2755941729916705872266809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3674588973222274496355745 2755941729916705872266809)
                    ·
                      refine ⟨2066956297437529404200107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2755941729916705872266809 2066956297437529404200107)
                      ·
                        rfl

theorem cell23_4025383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 1, 4, 2, 2].length) (baseStart_4025383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4025383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4025383 prefixEnd_4025383 := by exact prefixLift 4025383
  have htrace : WordTrace (prefixWord ++ tailWord_4025383) baseStart_4025383 baseEnd_4025383 := by
    simpa [prefixWord, tailWord_4025383, baseEnd_4025383] using wordTrace_append hprefix tailTrace_4025383
  have hstable : (prefixWord ++ tailWord_4025383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4025383).length < 2 ^ (prefixWord ++ tailWord_4025383).sum := by decide
  have hdescent : baseEnd_4025383 < baseStart_4025383 := by decide
  rcases family_descends (prefixWord ++ tailWord_4025383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4025395 : List Nat := [1, 1, 1, 2, 4, 1, 1, 3, 1, 1, 7]
def baseStart_4025395 : Nat := 118140960795 + 4025395 * 2 ^ 59
def prefixEnd_4025395 : Nat := 4983230072969 + 3 ^ 40 * 4025395 * 2
def baseEnd_4025395 : Nat := 2066962459205383357250051

theorem tailTrace_4025395 : CollatzResearch.WordTrace tailWord_4025395 prefixEnd_4025395 2066962459205383357250051 := by
  unfold tailWord_4025395
  simp only [CollatzResearch.WordTrace]
  refine ⟨146818217251688872577813639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97878811501125915051875759 146818217251688872577813639)
  ·
    refine ⟨220227325877533308866720459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146818217251688872577813639 220227325877533308866720459)
    ·
      refine ⟨330340988816299963300080689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220227325877533308866720459 330340988816299963300080689)
      ·
        refine ⟨247755741612224972475060517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 330340988816299963300080689 247755741612224972475060517)
        ·
          refine ⟨46454201552292182339073847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 247755741612224972475060517 46454201552292182339073847)
          ·
            refine ⟨69681302328438273508610771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46454201552292182339073847 69681302328438273508610771)
            ·
              refine ⟨104521953492657410262916157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69681302328438273508610771 104521953492657410262916157)
              ·
                refine ⟨39195732559746528848593559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104521953492657410262916157 39195732559746528848593559)
                ·
                  refine ⟨58793598839619793272890339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39195732559746528848593559 58793598839619793272890339)
                  ·
                    refine ⟨88190398259429689909335509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58793598839619793272890339 88190398259429689909335509)
                    ·
                      refine ⟨2066962459205383357250051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 88190398259429689909335509 2066962459205383357250051)
                      ·
                        rfl

theorem cell23_4025395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 3, 1, 1, 7].length) (baseStart_4025395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4025395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4025395 prefixEnd_4025395 := by exact prefixLift 4025395
  have htrace : WordTrace (prefixWord ++ tailWord_4025395) baseStart_4025395 baseEnd_4025395 := by
    simpa [prefixWord, tailWord_4025395, baseEnd_4025395] using wordTrace_append hprefix tailTrace_4025395
  have hstable : (prefixWord ++ tailWord_4025395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4025395).length < 2 ^ (prefixWord ++ tailWord_4025395).sum := by decide
  have hdescent : baseEnd_4025395 < baseStart_4025395 := by decide
  rcases family_descends (prefixWord ++ tailWord_4025395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4025422 : List Nat := [4, 1, 1, 1, 1, 3, 1, 3, 1, 3, 4]
def baseStart_4025422 : Nat := 118140960795 + 4025422 * 2 ^ 59
def prefixEnd_4025422 : Nat := 4983230072969 + 3 ^ 40 * 4025422 * 2
def baseEnd_4025422 : Nat := 2066976323183054751612427

theorem tailTrace_4025422 : CollatzResearch.WordTrace tailWord_4025422 prefixEnd_4025422 2066976323183054751612427 := by
  unfold tailWord_4025422
  simp only [CollatzResearch.WordTrace]
  refine ⟨18352400252823882023630815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97879468015060704126031013 18352400252823882023630815)
  ·
    refine ⟨27528600379235823035446223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18352400252823882023630815 27528600379235823035446223)
    ·
      refine ⟨41292900568853734553169335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27528600379235823035446223 41292900568853734553169335)
      ·
        refine ⟨61939350853280601829754003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41292900568853734553169335 61939350853280601829754003)
        ·
          refine ⟨92909026279920902744631005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61939350853280601829754003 92909026279920902744631005)
          ·
            refine ⟨34840884854970338529236627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92909026279920902744631005 34840884854970338529236627)
            ·
              refine ⟨52261327282455507793854941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34840884854970338529236627 52261327282455507793854941)
              ·
                refine ⟨19597997730920815422695603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52261327282455507793854941 19597997730920815422695603)
                ·
                  refine ⟨29396996596381223134043405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19597997730920815422695603 29396996596381223134043405)
                  ·
                    refine ⟨11023873723642958675266277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29396996596381223134043405 11023873723642958675266277)
                    ·
                      refine ⟨2066976323183054751612427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11023873723642958675266277 2066976323183054751612427)
                      ·
                        rfl

theorem cell23_4025422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 3, 1, 3, 4].length) (baseStart_4025422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4025422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4025422 prefixEnd_4025422 := by exact prefixLift 4025422
  have htrace : WordTrace (prefixWord ++ tailWord_4025422) baseStart_4025422 baseEnd_4025422 := by
    simpa [prefixWord, tailWord_4025422, baseEnd_4025422] using wordTrace_append hprefix tailTrace_4025422
  have hstable : (prefixWord ++ tailWord_4025422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4025422).length < 2 ^ (prefixWord ++ tailWord_4025422).sum := by decide
  have hdescent : baseEnd_4025422 < baseStart_4025422 := by decide
  rcases family_descends (prefixWord ++ tailWord_4025422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4025449 : List Nat := [1, 2, 1, 1, 1, 6, 3, 1, 3, 4]
def baseStart_4025449 : Nat := 118140960795 + 4025449 * 2 ^ 59
def prefixEnd_4025449 : Nat := 4983230072969 + 3 ^ 40 * 4025449 * 2
def baseEnd_4025449 : Nat := 688996729053575381991601

theorem tailTrace_4025449 : CollatzResearch.WordTrace tailWord_4025449 prefixEnd_4025449 688996729053575381991601 := by
  unfold tailWord_4025449
  simp only [CollatzResearch.WordTrace]
  refine ⟨146820186793493239800279401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97880124528995493200186267 146820186793493239800279401)
  ·
    refine ⟨110115140095119929850209551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146820186793493239800279401 110115140095119929850209551)
    ·
      refine ⟨165172710142679894775314327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110115140095119929850209551 165172710142679894775314327)
      ·
        refine ⟨247759065214019842162971491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165172710142679894775314327 247759065214019842162971491)
        ·
          refine ⟨371638597821029763244457237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247759065214019842162971491 371638597821029763244457237)
          ·
            refine ⟨17420559272860770152083933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 371638597821029763244457237 17420559272860770152083933)
            ·
              refine ⟨6532709727322788807031475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17420559272860770152083933 6532709727322788807031475)
              ·
                refine ⟨9799064590984183210547213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6532709727322788807031475 9799064590984183210547213)
                ·
                  refine ⟨3674649221619068703955205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9799064590984183210547213 3674649221619068703955205)
                  ·
                    refine ⟨688996729053575381991601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3674649221619068703955205 688996729053575381991601)
                    ·
                      rfl

theorem cell23_4025449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 3, 1, 3, 4].length) (baseStart_4025449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4025449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4025449 prefixEnd_4025449 := by exact prefixLift 4025449
  have htrace : WordTrace (prefixWord ++ tailWord_4025449) baseStart_4025449 baseEnd_4025449 := by
    simpa [prefixWord, tailWord_4025449, baseEnd_4025449] using wordTrace_append hprefix tailTrace_4025449
  have hstable : (prefixWord ++ tailWord_4025449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4025449).length < 2 ^ (prefixWord ++ tailWord_4025449).sum := by decide
  have hdescent : baseEnd_4025449 < baseStart_4025449 := by decide
  rcases family_descends (prefixWord ++ tailWord_4025449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4025470 : List Nat := [4, 2, 4, 1, 1, 1, 2, 1, 2, 5]
def baseStart_4025470 : Nat := 118140960795 + 4025470 * 2 ^ 59
def prefixEnd_4025470 : Nat := 4983230072969 + 3 ^ 40 * 4025470 * 2
def baseEnd_4025470 : Nat := 689000323418156854604069

theorem tailTrace_4025470 : CollatzResearch.WordTrace tailWord_4025470 prefixEnd_4025470 689000323418156854604069 := by
  unfold tailWord_4025470
  simp only [CollatzResearch.WordTrace]
  refine ⟨18352619090802145048349233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97880635150944773591195909 18352619090802145048349233)
  ·
    refine ⟨13764464318101608786261925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18352619090802145048349233 13764464318101608786261925)
    ·
      refine ⟨2580837059644051647424111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13764464318101608786261925 2580837059644051647424111)
      ·
        refine ⟨3871255589466077471136167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2580837059644051647424111 3871255589466077471136167)
        ·
          refine ⟨5806883384199116206704251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3871255589466077471136167 5806883384199116206704251)
          ·
            refine ⟨8710325076298674310056377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5806883384199116206704251 8710325076298674310056377)
            ·
              refine ⟨6532743807224005732542283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8710325076298674310056377 6532743807224005732542283)
              ·
                refine ⟨9799115710836008598813425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6532743807224005732542283 9799115710836008598813425)
                ·
                  refine ⟨7349336783127006449110069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9799115710836008598813425 7349336783127006449110069)
                  ·
                    refine ⟨689000323418156854604069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7349336783127006449110069 689000323418156854604069)
                    ·
                      rfl

theorem cell23_4025470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_4025470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4025470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4025470 prefixEnd_4025470 := by exact prefixLift 4025470
  have htrace : WordTrace (prefixWord ++ tailWord_4025470) baseStart_4025470 baseEnd_4025470 := by
    simpa [prefixWord, tailWord_4025470, baseEnd_4025470] using wordTrace_append hprefix tailTrace_4025470
  have hstable : (prefixWord ++ tailWord_4025470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4025470).length < 2 ^ (prefixWord ++ tailWord_4025470).sum := by decide
  have hdescent : baseEnd_4025470 < baseStart_4025470 := by decide
  rcases family_descends (prefixWord ++ tailWord_4025470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4025472 : List Nat := [2, 1, 1, 2, 1, 3, 2, 1, 2, 5, 3]
def baseStart_4025472 : Nat := 118140960795 + 4025472 * 2 ^ 59
def prefixEnd_4025472 : Nat := 4983230072969 + 3 ^ 40 * 4025472 * 2
def baseEnd_4025472 : Nat := 2067001997215779555987197

theorem tailTrace_4025472 : CollatzResearch.WordTrace tailWord_4025472 prefixEnd_4025472 2067001997215779555987197 := by
  unfold tailWord_4025472
  simp only [CollatzResearch.WordTrace]
  refine ⟨73410512836204957364183335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97880683781606609818911113 73410512836204957364183335)
  ·
    refine ⟨110115769254307436046275003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73410512836204957364183335 110115769254307436046275003)
    ·
      refine ⟨165173653881461154069412505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110115769254307436046275003 165173653881461154069412505)
      ·
        refine ⟨123880240411095865552059379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165173653881461154069412505 123880240411095865552059379)
        ·
          refine ⟨185820360616643798328089069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123880240411095865552059379 185820360616643798328089069)
          ·
            refine ⟨69682635231241424373033401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 185820360616643798328089069 69682635231241424373033401)
            ·
              refine ⟨52261976423431068279775051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69682635231241424373033401 52261976423431068279775051)
              ·
                refine ⟨78392964635146602419662577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52261976423431068279775051 78392964635146602419662577)
                ·
                  refine ⟨58794723476359951814746933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78392964635146602419662577 58794723476359951814746933)
                  ·
                    refine ⟨5512005325908745482632525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58794723476359951814746933 5512005325908745482632525)
                    ·
                      refine ⟨2067001997215779555987197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5512005325908745482632525 2067001997215779555987197)
                      ·
                        rfl

theorem cell23_4025472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 2, 5, 3].length) (baseStart_4025472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4025472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4025472 prefixEnd_4025472 := by exact prefixLift 4025472
  have htrace : WordTrace (prefixWord ++ tailWord_4025472) baseStart_4025472 baseEnd_4025472 := by
    simpa [prefixWord, tailWord_4025472, baseEnd_4025472] using wordTrace_append hprefix tailTrace_4025472
  have hstable : (prefixWord ++ tailWord_4025472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4025472).length < 2 ^ (prefixWord ++ tailWord_4025472).sum := by decide
  have hdescent : baseEnd_4025472 < baseStart_4025472 := by decide
  rcases family_descends (prefixWord ++ tailWord_4025472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4025476 : List Nat := [2, 3, 2, 1, 2, 3, 2, 1, 2, 2, 3]
def baseStart_4025476 : Nat := 118140960795 + 4025476 * 2 ^ 59
def prefixEnd_4025476 : Nat := 4983230072969 + 3 ^ 40 * 4025476 * 2
def baseEnd_4025476 : Nat := 2067004051138397540337179

theorem tailTrace_4025476 : CollatzResearch.WordTrace tailWord_4025476 prefixEnd_4025476 2067004051138397540337179 := by
  unfold tailWord_4025476
  simp only [CollatzResearch.WordTrace]
  refine ⟨73410585782197711705756141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97880781042930282274341521 73410585782197711705756141)
  ·
    refine ⟨27528969668324141889658553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73410585782197711705756141 27528969668324141889658553)
    ·
      refine ⟨20646727251243106417243915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27528969668324141889658553 20646727251243106417243915)
      ·
        refine ⟨30970090876864659625865873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20646727251243106417243915 30970090876864659625865873)
        ·
          refine ⟨23227568157648494719399405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30970090876864659625865873 23227568157648494719399405)
          ·
            refine ⟨8710338059118185519774777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23227568157648494719399405 8710338059118185519774777)
            ·
              refine ⟨6532753544338639139831083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8710338059118185519774777 6532753544338639139831083)
              ·
                refine ⟨9799130316507958709746625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6532753544338639139831083 9799130316507958709746625)
                ·
                  refine ⟨7349347737380969032309969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9799130316507958709746625 7349347737380969032309969)
                  ·
                    refine ⟨5512010803035726774232477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7349347737380969032309969 5512010803035726774232477)
                    ·
                      refine ⟨2067004051138397540337179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5512010803035726774232477 2067004051138397540337179)
                      ·
                        rfl

theorem cell23_4025476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 2, 3].length) (baseStart_4025476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4025476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4025476 prefixEnd_4025476 := by exact prefixLift 4025476
  have htrace : WordTrace (prefixWord ++ tailWord_4025476) baseStart_4025476 baseEnd_4025476 := by
    simpa [prefixWord, tailWord_4025476, baseEnd_4025476] using wordTrace_append hprefix tailTrace_4025476
  have hstable : (prefixWord ++ tailWord_4025476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4025476).length < 2 ^ (prefixWord ++ tailWord_4025476).sum := by decide
  have hdescent : baseEnd_4025476 < baseStart_4025476 := by decide
  rcases family_descends (prefixWord ++ tailWord_4025476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4025500 : List Nat := [2, 2, 3, 2, 1, 4, 2, 2, 1, 4]
def baseStart_4025500 : Nat := 118140960795 + 4025500 * 2 ^ 59
def prefixEnd_4025500 : Nat := 4983230072969 + 3 ^ 40 * 4025500 * 2
def baseEnd_4025500 : Nat := 689005458224701815479023

theorem tailTrace_4025500 : CollatzResearch.WordTrace tailWord_4025500 prefixEnd_4025500 689005458224701815479023 := by
  unfold tailWord_4025500
  simp only [CollatzResearch.WordTrace]
  refine ⟨73411023458154237755192977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97881364610872317006923969 73411023458154237755192977)
  ·
    refine ⟨55058267593615678316394733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73411023458154237755192977 55058267593615678316394733)
    ·
      refine ⟨20646850347605879368648025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55058267593615678316394733 20646850347605879368648025)
      ·
        refine ⟨15485137760704409526486019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20646850347605879368648025 15485137760704409526486019)
        ·
          refine ⟨23227706641056614289729029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15485137760704409526486019 23227706641056614289729029)
          ·
            refine ⟨4355194995198115179324193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23227706641056614289729029 4355194995198115179324193)
            ·
              refine ⟨3266396246398586384493145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4355194995198115179324193 3266396246398586384493145)
              ·
                refine ⟨2449797184798939788369859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3266396246398586384493145 2449797184798939788369859)
                ·
                  refine ⟨3674695777198409682554789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2449797184798939788369859 3674695777198409682554789)
                  ·
                    refine ⟨689005458224701815479023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3674695777198409682554789 689005458224701815479023)
                    ·
                      rfl

theorem cell23_4025500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 2, 2, 1, 4].length) (baseStart_4025500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4025500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4025500 prefixEnd_4025500 := by exact prefixLift 4025500
  have htrace : WordTrace (prefixWord ++ tailWord_4025500) baseStart_4025500 baseEnd_4025500 := by
    simpa [prefixWord, tailWord_4025500, baseEnd_4025500] using wordTrace_append hprefix tailTrace_4025500
  have hstable : (prefixWord ++ tailWord_4025500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4025500).length < 2 ^ (prefixWord ++ tailWord_4025500).sum := by decide
  have hdescent : baseEnd_4025500 < baseStart_4025500 := by decide
  rcases family_descends (prefixWord ++ tailWord_4025500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4025529 : List Nat := [1, 2, 1, 4, 1, 3, 2, 1, 3, 1, 4]
def baseStart_4025529 : Nat := 118140960795 + 4025529 * 2 ^ 59
def prefixEnd_4025529 : Nat := 4983230072969 + 3 ^ 40 * 4025529 * 2
def baseEnd_4025529 : Nat := 2067031265613085832974435

theorem tailTrace_4025529 : CollatzResearch.WordTrace tailWord_4025529 prefixEnd_4025529 2067031265613085832974435 := by
  unfold tailWord_4025529
  simp only [CollatzResearch.WordTrace]
  refine ⟨146823104633203413463191641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97882069755468942308794427 146823104633203413463191641)
  ·
    refine ⟨110117328474902560097393731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146823104633203413463191641 110117328474902560097393731)
    ·
      refine ⟨165175992712353840146090597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110117328474902560097393731 165175992712353840146090597)
      ·
        refine ⟨30970498633566345027391987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 165175992712353840146090597 30970498633566345027391987)
        ·
          refine ⟨46455747950349517541087981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30970498633566345027391987 46455747950349517541087981)
          ·
            refine ⟨17420905481381069077907993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46455747950349517541087981 17420905481381069077907993)
            ·
              refine ⟨13065679111035801808430995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17420905481381069077907993 13065679111035801808430995)
              ·
                refine ⟨19598518666553702712646493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13065679111035801808430995 19598518666553702712646493)
                ·
                  refine ⟨7349444499957638517242435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19598518666553702712646493 7349444499957638517242435)
                  ·
                    refine ⟨11024166749936457775863653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7349444499957638517242435 11024166749936457775863653)
                    ·
                      refine ⟨2067031265613085832974435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11024166749936457775863653 2067031265613085832974435)
                      ·
                        rfl

theorem cell23_4025529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 1, 3, 1, 4].length) (baseStart_4025529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4025529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4025529 prefixEnd_4025529 := by exact prefixLift 4025529
  have htrace : WordTrace (prefixWord ++ tailWord_4025529) baseStart_4025529 baseEnd_4025529 := by
    simpa [prefixWord, tailWord_4025529, baseEnd_4025529] using wordTrace_append hprefix tailTrace_4025529
  have hstable : (prefixWord ++ tailWord_4025529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4025529).length < 2 ^ (prefixWord ++ tailWord_4025529).sum := by decide
  have hdescent : baseEnd_4025529 < baseStart_4025529 := by decide
  rcases family_descends (prefixWord ++ tailWord_4025529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4025546 : List Nat := [3, 1, 2, 1, 3, 3, 1, 3, 1, 1, 4]
def baseStart_4025546 : Nat := 118140960795 + 4025546 * 2 ^ 59
def prefixEnd_4025546 : Nat := 4983230072969 + 3 ^ 40 * 4025546 * 2
def baseEnd_4025546 : Nat := 2067039994784212266461857

theorem tailTrace_4025546 : CollatzResearch.WordTrace tailWord_4025546 prefixEnd_4025546 2067039994784212266461857 := by
  unfold tailWord_4025546
  simp only [CollatzResearch.WordTrace]
  refine ⟨36705931168535456341640123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97882483116094550244373661 36705931168535456341640123)
  ·
    refine ⟨55058896752803184512460185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36705931168535456341640123 55058896752803184512460185)
    ·
      refine ⟨41294172564602388384345139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55058896752803184512460185 41294172564602388384345139)
      ·
        refine ⟨61941258846903582576517709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41294172564602388384345139 61941258846903582576517709)
        ·
          refine ⟨23227972067588843466194141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61941258846903582576517709 23227972067588843466194141)
          ·
            refine ⟨8710489525345816299822803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23227972067588843466194141 8710489525345816299822803)
            ·
              refine ⟨13065734288018724449734205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8710489525345816299822803 13065734288018724449734205)
              ·
                refine ⟨4899650358007021668650327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13065734288018724449734205 4899650358007021668650327)
                ·
                  refine ⟨7349475537010532502975491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4899650358007021668650327 7349475537010532502975491)
                  ·
                    refine ⟨11024213305515798754463237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7349475537010532502975491 11024213305515798754463237)
                    ·
                      refine ⟨2067039994784212266461857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11024213305515798754463237 2067039994784212266461857)
                      ·
                        rfl

theorem cell23_4025546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 3, 1, 1, 4].length) (baseStart_4025546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4025546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4025546 prefixEnd_4025546 := by exact prefixLift 4025546
  have htrace : WordTrace (prefixWord ++ tailWord_4025546) baseStart_4025546 baseEnd_4025546 := by
    simpa [prefixWord, tailWord_4025546, baseEnd_4025546] using wordTrace_append hprefix tailTrace_4025546
  have hstable : (prefixWord ++ tailWord_4025546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4025546).length < 2 ^ (prefixWord ++ tailWord_4025546).sum := by decide
  have hdescent : baseEnd_4025546 < baseStart_4025546 := by decide
  rcases family_descends (prefixWord ++ tailWord_4025546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4025562 : List Nat := [3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 7]
def baseStart_4025562 : Nat := 118140960795 + 4025562 * 2 ^ 59
def prefixEnd_4025562 : Nat := 4983230072969 + 3 ^ 40 * 4025562 * 2
def baseEnd_4025562 : Nat := 2067048210474684203861783

theorem tailTrace_4025562 : CollatzResearch.WordTrace tailWord_4025562 prefixEnd_4025562 2067048210474684203861783 := by
  unfold tailWord_4025562
  simp only [CollatzResearch.WordTrace]
  refine ⟨36706077060520965024785735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97882872161389240066095293 36706077060520965024785735)
  ·
    refine ⟨55059115590781447537178603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36706077060520965024785735 55059115590781447537178603)
    ·
      refine ⟨82588673386172171305767905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55059115590781447537178603 82588673386172171305767905)
      ·
        refine ⟨61941505039629128479325929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82588673386172171305767905 61941505039629128479325929)
        ·
          refine ⟨46456128779721846359494447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61941505039629128479325929 46456128779721846359494447)
          ·
            refine ⟨69684193169582769539241671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46456128779721846359494447 69684193169582769539241671)
            ·
              refine ⟨104526289754374154308862507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69684193169582769539241671 104526289754374154308862507)
              ·
                refine ⟨156789434631561231463293761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104526289754374154308862507 156789434631561231463293761)
                ·
                  refine ⟨117592075973670923597470321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 156789434631561231463293761 117592075973670923597470321)
                  ·
                    refine ⟨88194056980253192698102741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 117592075973670923597470321 88194056980253192698102741)
                    ·
                      refine ⟨2067048210474684203861783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 88194056980253192698102741 2067048210474684203861783)
                      ·
                        rfl

theorem cell23_4025562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 7].length) (baseStart_4025562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4025562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4025562 prefixEnd_4025562 := by exact prefixLift 4025562
  have htrace : WordTrace (prefixWord ++ tailWord_4025562) baseStart_4025562 baseEnd_4025562 := by
    simpa [prefixWord, tailWord_4025562, baseEnd_4025562] using wordTrace_append hprefix tailTrace_4025562
  have hstable : (prefixWord ++ tailWord_4025562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4025562).length < 2 ^ (prefixWord ++ tailWord_4025562).sum := by decide
  have hdescent : baseEnd_4025562 < baseStart_4025562 := by decide
  rcases family_descends (prefixWord ++ tailWord_4025562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4025573 : List Nat := [1, 3, 1, 4, 4, 1, 1, 1, 1, 6]
def baseStart_4025573 : Nat := 118140960795 + 4025573 * 2 ^ 59
def prefixEnd_4025573 : Nat := 4983230072969 + 3 ^ 40 * 4025573 * 2
def baseEnd_4025573 : Nat := 689017952920627886941411

theorem tailTrace_4025573 : CollatzResearch.WordTrace tailWord_4025573 prefixEnd_4025573 689017952920627886941411 := by
  unfold tailWord_4025573
  simp only [CollatzResearch.WordTrace]
  refine ⟨146824709445044008977793373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97883139630029339318528915 146824709445044008977793373)
  ·
    refine ⟨55059266041891503366672515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146824709445044008977793373 55059266041891503366672515)
    ·
      refine ⟨82588899062837255050008773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55059266041891503366672515 82588899062837255050008773)
      ·
        refine ⟨15485418574281985321876645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82588899062837255050008773 15485418574281985321876645)
        ·
          refine ⟨2903515982677872247851871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15485418574281985321876645 2903515982677872247851871)
          ·
            refine ⟨4355273974016808371777807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2903515982677872247851871 4355273974016808371777807)
            ·
              refine ⟨6532910961025212557666711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4355273974016808371777807 6532910961025212557666711)
              ·
                refine ⟨9799366441537818836500067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6532910961025212557666711 9799366441537818836500067)
                ·
                  refine ⟨14699049662306728254750101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9799366441537818836500067 14699049662306728254750101)
                  ·
                    refine ⟨689017952920627886941411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14699049662306728254750101 689017952920627886941411)
                    ·
                      rfl

theorem cell23_4025573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 1, 1, 1, 6].length) (baseStart_4025573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4025573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4025573 prefixEnd_4025573 := by exact prefixLift 4025573
  have htrace : WordTrace (prefixWord ++ tailWord_4025573) baseStart_4025573 baseEnd_4025573 := by
    simpa [prefixWord, tailWord_4025573, baseEnd_4025573] using wordTrace_append hprefix tailTrace_4025573
  have hstable : (prefixWord ++ tailWord_4025573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4025573).length < 2 ^ (prefixWord ++ tailWord_4025573).sum := by decide
  have hdescent : baseEnd_4025573 < baseStart_4025573 := by decide
  rcases family_descends (prefixWord ++ tailWord_4025573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4025583 : List Nat := [1, 1, 2, 1, 7, 1, 2, 2, 1, 2, 3]
def baseStart_4025583 : Nat := 118140960795 + 4025583 * 2 ^ 59
def prefixEnd_4025583 : Nat := 4983230072969 + 3 ^ 40 * 4025583 * 2
def baseEnd_4025583 : Nat := 2067058993568428621699187

theorem tailTrace_4025583 : CollatzResearch.WordTrace tailWord_4025583 prefixEnd_4025583 2067058993568428621699187 := by
  unfold tailWord_4025583
  simp only [CollatzResearch.WordTrace]
  refine ⟨146825074175007780685657403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97883382783338520457104935 146825074175007780685657403)
  ·
    refine ⟨220237611262511671028486105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146825074175007780685657403 220237611262511671028486105)
    ·
      refine ⟨165178208446883753271364579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220237611262511671028486105 165178208446883753271364579)
      ·
        refine ⟨247767312670325629907046869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165178208446883753271364579 247767312670325629907046869)
        ·
          refine ⟨5807046390710756950946411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 247767312670325629907046869 5807046390710756950946411)
          ·
            refine ⟨8710569586066135426419617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5807046390710756950946411 8710569586066135426419617)
            ·
              refine ⟨6532927189549601569814713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8710569586066135426419617 6532927189549601569814713)
              ·
                refine ⟨4899695392162201177361035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6532927189549601569814713 4899695392162201177361035)
                ·
                  refine ⟨7349543088243301766041553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4899695392162201177361035 7349543088243301766041553)
                  ·
                    refine ⟨5512157316182476324531165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7349543088243301766041553 5512157316182476324531165)
                    ·
                      refine ⟨2067058993568428621699187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5512157316182476324531165 2067058993568428621699187)
                      ·
                        rfl

theorem cell23_4025583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 2, 2, 1, 2, 3].length) (baseStart_4025583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4025583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4025583 prefixEnd_4025583 := by exact prefixLift 4025583
  have htrace : WordTrace (prefixWord ++ tailWord_4025583) baseStart_4025583 baseEnd_4025583 := by
    simpa [prefixWord, tailWord_4025583, baseEnd_4025583] using wordTrace_append hprefix tailTrace_4025583
  have hstable : (prefixWord ++ tailWord_4025583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4025583).length < 2 ^ (prefixWord ++ tailWord_4025583).sum := by decide
  have hdescent : baseEnd_4025583 < baseStart_4025583 := by decide
  rcases family_descends (prefixWord ++ tailWord_4025583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4025640 : List Nat := [2, 1, 5, 1, 2, 1, 3, 2, 1, 3, 2]
def baseStart_4025640 : Nat := 118140960795 + 4025640 * 2 ^ 59
def prefixEnd_4025640 : Nat := 4983230072969 + 3 ^ 40 * 4025640 * 2
def baseEnd_4025640 : Nat := 2067088261965734898686425

theorem tailTrace_4025640 : CollatzResearch.WordTrace tailWord_4025640 prefixEnd_4025640 2067088261965734898686425 := by
  unfold tailWord_4025640
  simp only [CollatzResearch.WordTrace]
  refine ⟨73413576567900639710241187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97884768757200852946988249 73413576567900639710241187)
  ·
    refine ⟨110120364851850959565361781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73413576567900639710241187 110120364851850959565361781)
    ·
      refine ⟨10323784204861027459252667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 110120364851850959565361781 10323784204861027459252667)
      ·
        refine ⟨15485676307291541188879001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10323784204861027459252667 15485676307291541188879001)
        ·
          refine ⟨11614257230468655891659251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15485676307291541188879001 11614257230468655891659251)
          ·
            refine ⟨17421385845702983837488877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11614257230468655891659251 17421385845702983837488877)
            ·
              refine ⟨6533019692138618939058329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17421385845702983837488877 6533019692138618939058329)
              ·
                refine ⟨4899764769103964204293747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6533019692138618939058329 4899764769103964204293747)
                ·
                  refine ⟨7349647153655946306440621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4899764769103964204293747 7349647153655946306440621)
                  ·
                    refine ⟨2756117682620979864915233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7349647153655946306440621 2756117682620979864915233)
                    ·
                      refine ⟨2067088261965734898686425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2756117682620979864915233 2067088261965734898686425)
                      ·
                        rfl

theorem cell23_4025640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 3, 2, 1, 3, 2].length) (baseStart_4025640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4025640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4025640 prefixEnd_4025640 := by exact prefixLift 4025640
  have htrace : WordTrace (prefixWord ++ tailWord_4025640) baseStart_4025640 baseEnd_4025640 := by
    simpa [prefixWord, tailWord_4025640, baseEnd_4025640] using wordTrace_append hprefix tailTrace_4025640
  have hstable : (prefixWord ++ tailWord_4025640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4025640).length < 2 ^ (prefixWord ++ tailWord_4025640).sum := by decide
  have hdescent : baseEnd_4025640 < baseStart_4025640 := by decide
  rcases family_descends (prefixWord ++ tailWord_4025640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4025653 : List Nat := [1, 3, 3, 1, 2, 3, 1, 2, 1, 4, 2]
def baseStart_4025653 : Nat := 118140960795 + 4025653 * 2 ^ 59
def prefixEnd_4025653 : Nat := 4983230072969 + 3 ^ 40 * 4025653 * 2
def baseEnd_4025653 : Nat := 2067094937214243347823865

theorem tailTrace_4025653 : CollatzResearch.WordTrace tailWord_4025653 prefixEnd_4025653 2067094937214243347823865 := by
  unfold tailWord_4025653
  simp only [CollatzResearch.WordTrace]
  refine ⟨146827627284754182640705613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97885084856502788427137075 146827627284754182640705613)
  ·
    refine ⟨55060360231782818490264605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146827627284754182640705613 55060360231782818490264605)
    ·
      refine ⟨20647635086918556933849227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55060360231782818490264605 20647635086918556933849227)
      ·
        refine ⟨30971452630377835400773841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20647635086918556933849227 30971452630377835400773841)
        ·
          refine ⟨23228589472783376550580381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30971452630377835400773841 23228589472783376550580381)
          ·
            refine ⟨8710721052293766206467643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23228589472783376550580381 8710721052293766206467643)
            ·
              refine ⟨13066081578440649309701465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8710721052293766206467643 13066081578440649309701465)
              ·
                refine ⟨9799561183830486982276099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13066081578440649309701465 9799561183830486982276099)
                ·
                  refine ⟨14699341775745730473414149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9799561183830486982276099 14699341775745730473414149)
                  ·
                    refine ⟨2756126582952324463765153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14699341775745730473414149 2756126582952324463765153)
                    ·
                      refine ⟨2067094937214243347823865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2756126582952324463765153 2067094937214243347823865)
                      ·
                        rfl

theorem cell23_4025653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 2, 1, 4, 2].length) (baseStart_4025653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4025653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4025653 prefixEnd_4025653 := by exact prefixLift 4025653
  have htrace : WordTrace (prefixWord ++ tailWord_4025653) baseStart_4025653 baseEnd_4025653 := by
    simpa [prefixWord, tailWord_4025653, baseEnd_4025653] using wordTrace_append hprefix tailTrace_4025653
  have hstable : (prefixWord ++ tailWord_4025653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4025653).length < 2 ^ (prefixWord ++ tailWord_4025653).sum := by decide
  have hdescent : baseEnd_4025653 < baseStart_4025653 := by decide
  rcases family_descends (prefixWord ++ tailWord_4025653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4025657 : List Nat := [1, 2, 1, 6, 2, 1, 3, 1, 1, 3, 2]
def baseStart_4025657 : Nat := 118140960795 + 4025657 * 2 ^ 59
def prefixEnd_4025657 : Nat := 4983230072969 + 3 ^ 40 * 4025657 * 2
def baseEnd_4025657 : Nat := 2067096991136861332173847

theorem tailTrace_4025657 : CollatzResearch.WordTrace tailWord_4025657 prefixEnd_4025657 2067096991136861332173847 := by
  unfold tailWord_4025657
  simp only [CollatzResearch.WordTrace]
  refine ⟨146827773176739691323851225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97885182117826460882567483 146827773176739691323851225)
  ·
    refine ⟨110120829882554768492888419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146827773176739691323851225 110120829882554768492888419)
    ·
      refine ⟨165181244823832152739332629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110120829882554768492888419 165181244823832152739332629)
      ·
        refine ⟨7742870851117132159656217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 165181244823832152739332629 7742870851117132159656217)
        ·
          refine ⟨5807153138337849119742163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7742870851117132159656217 5807153138337849119742163)
          ·
            refine ⟨8710729707506773679613245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5807153138337849119742163 8710729707506773679613245)
            ·
              refine ⟨3266523640315040129854967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8710729707506773679613245 3266523640315040129854967)
              ·
                refine ⟨4899785460472560194782451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3266523640315040129854967 4899785460472560194782451)
                ·
                  refine ⟨7349678190708840292173677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4899785460472560194782451 7349678190708840292173677)
                  ·
                    refine ⟨2756129321515815109565129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7349678190708840292173677 2756129321515815109565129)
                    ·
                      refine ⟨2067096991136861332173847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2756129321515815109565129 2067096991136861332173847)
                      ·
                        rfl

theorem cell23_4025657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 3, 1, 1, 3, 2].length) (baseStart_4025657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4025657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4025657 prefixEnd_4025657 := by exact prefixLift 4025657
  have htrace : WordTrace (prefixWord ++ tailWord_4025657) baseStart_4025657 baseEnd_4025657 := by
    simpa [prefixWord, tailWord_4025657, baseEnd_4025657] using wordTrace_append hprefix tailTrace_4025657
  have hstable : (prefixWord ++ tailWord_4025657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4025657).length < 2 ^ (prefixWord ++ tailWord_4025657).sum := by decide
  have hdescent : baseEnd_4025657 < baseStart_4025657 := by decide
  rcases family_descends (prefixWord ++ tailWord_4025657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4025669 : List Nat := [1, 3, 1, 1, 1, 2, 1, 2, 3, 5, 3]
def baseStart_4025669 : Nat := 118140960795 + 4025669 * 2 ^ 59
def prefixEnd_4025669 : Nat := 4983230072969 + 3 ^ 40 * 4025669 * 2
def baseEnd_4025669 : Nat := 2067103152904715285223791

theorem tailTrace_4025669 : CollatzResearch.WordTrace tailWord_4025669 prefixEnd_4025669 2067103152904715285223791 := by
  unfold tailWord_4025669
  simp only [CollatzResearch.WordTrace]
  refine ⟨146828210852696217373288061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97885473901797478248858707 146828210852696217373288061)
  ·
    refine ⟨55060579069761081514983023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146828210852696217373288061 55060579069761081514983023)
    ·
      refine ⟨82590868604641622272474535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55060579069761081514983023 82590868604641622272474535)
      ·
        refine ⟨123886302906962433408711803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82590868604641622272474535 123886302906962433408711803)
        ·
          refine ⟨185829454360443650113067705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123886302906962433408711803 185829454360443650113067705)
          ·
            refine ⟨139372090770332737584800779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185829454360443650113067705 139372090770332737584800779)
            ·
              refine ⟨209058136155499106377201169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139372090770332737584800779 209058136155499106377201169)
              ·
                refine ⟨156793602116624329782900877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 209058136155499106377201169 156793602116624329782900877)
                ·
                  refine ⟨58797600793734123668587829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 156793602116624329782900877 58797600793734123668587829)
                  ·
                    refine ⟨5512275074412574093930109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58797600793734123668587829 5512275074412574093930109)
                    ·
                      refine ⟨2067103152904715285223791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5512275074412574093930109 2067103152904715285223791)
                      ·
                        rfl

theorem cell23_4025669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 3, 5, 3].length) (baseStart_4025669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4025669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4025669 prefixEnd_4025669 := by exact prefixLift 4025669
  have htrace : WordTrace (prefixWord ++ tailWord_4025669) baseStart_4025669 baseEnd_4025669 := by
    simpa [prefixWord, tailWord_4025669, baseEnd_4025669] using wordTrace_append hprefix tailTrace_4025669
  have hstable : (prefixWord ++ tailWord_4025669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4025669).length < 2 ^ (prefixWord ++ tailWord_4025669).sum := by decide
  have hdescent : baseEnd_4025669 < baseStart_4025669 := by decide
  rcases family_descends (prefixWord ++ tailWord_4025669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4025689 : List Nat := [1, 2, 1, 2, 2, 2, 2, 2, 4, 5]
def baseStart_4025689 : Nat := 118140960795 + 4025689 * 2 ^ 59
def prefixEnd_4025689 : Nat := 4983230072969 + 3 ^ 40 * 4025689 * 2
def baseEnd_4025689 : Nat := 689037807505935068991233

theorem tailTrace_4025689 : CollatzResearch.WordTrace tailWord_4025689 prefixEnd_4025689 689037807505935068991233 := by
  unfold tailWord_4025689
  simp only [CollatzResearch.WordTrace]
  refine ⟨146828940312623760789016121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97885960208415840526010747 146828940312623760789016121)
  ·
    refine ⟨110121705234467820591762091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146828940312623760789016121 110121705234467820591762091)
    ·
      refine ⟨165182557851701730887643137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110121705234467820591762091 165182557851701730887643137)
      ·
        refine ⟨123886918388776298165732353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165182557851701730887643137 123886918388776298165732353)
        ·
          refine ⟨92915188791582223624299265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123886918388776298165732353 92915188791582223624299265)
          ·
            refine ⟨69686391593686667718224449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92915188791582223624299265 69686391593686667718224449)
            ·
              refine ⟨52264793695265000788668337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69686391593686667718224449 52264793695265000788668337)
              ·
                refine ⟨39198595271448750591501253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52264793695265000788668337 39198595271448750591501253)
                ·
                  refine ⟨7349736613396640735906485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39198595271448750591501253 7349736613396640735906485)
                  ·
                    refine ⟨689037807505935068991233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7349736613396640735906485 689037807505935068991233)
                    ·
                      rfl

theorem cell23_4025689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 2, 4, 5].length) (baseStart_4025689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4025689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4025689 prefixEnd_4025689 := by exact prefixLift 4025689
  have htrace : WordTrace (prefixWord ++ tailWord_4025689) baseStart_4025689 baseEnd_4025689 := by
    simpa [prefixWord, tailWord_4025689, baseEnd_4025689] using wordTrace_append hprefix tailTrace_4025689
  have hstable : (prefixWord ++ tailWord_4025689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4025689).length < 2 ^ (prefixWord ++ tailWord_4025689).sum := by decide
  have hdescent : baseEnd_4025689 < baseStart_4025689 := by decide
  rcases family_descends (prefixWord ++ tailWord_4025689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4025739 : List Nat := [1, 1, 1, 1, 4, 3, 1, 2, 2, 1, 6]
def baseStart_4025739 : Nat := 118140960795 + 4025739 * 2 ^ 59
def prefixEnd_4025739 : Nat := 4983230072969 + 3 ^ 40 * 4025739 * 2
def baseEnd_4025739 : Nat := 2067139096550530011348469

theorem tailTrace_4025739 : CollatzResearch.WordTrace tailWord_4025739 prefixEnd_4025739 2067139096550530011348469 := by
  unfold tailWord_4025739
  simp only [CollatzResearch.WordTrace]
  refine ⟨146830763962442619328336271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97887175974961746218890847 146830763962442619328336271)
  ·
    refine ⟨220246145943663928992504407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146830763962442619328336271 220246145943663928992504407)
    ·
      refine ⟨330369218915495893488756611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220246145943663928992504407 330369218915495893488756611)
      ·
        refine ⟨495553828373243840233134917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330369218915495893488756611 495553828373243840233134917)
        ·
          refine ⟨92916342819983220043712797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 495553828373243840233134917 92916342819983220043712797)
          ·
            refine ⟨34843628557493707516392299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92916342819983220043712797 34843628557493707516392299)
            ·
              refine ⟨52265442836240561274588449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34843628557493707516392299 52265442836240561274588449)
              ·
                refine ⟨39199082127180420955941337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52265442836240561274588449 39199082127180420955941337)
                ·
                  refine ⟨29399311595385315716956003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39199082127180420955941337 29399311595385315716956003)
                  ·
                    refine ⟨44098967393077973575434005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29399311595385315716956003 44098967393077973575434005)
                    ·
                      refine ⟨2067139096550530011348469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44098967393077973575434005 2067139096550530011348469)
                      ·
                        rfl

theorem cell23_4025739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 2, 2, 1, 6].length) (baseStart_4025739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4025739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4025739 prefixEnd_4025739 := by exact prefixLift 4025739
  have htrace : WordTrace (prefixWord ++ tailWord_4025739) baseStart_4025739 baseEnd_4025739 := by
    simpa [prefixWord, tailWord_4025739, baseEnd_4025739] using wordTrace_append hprefix tailTrace_4025739
  have hstable : (prefixWord ++ tailWord_4025739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4025739).length < 2 ^ (prefixWord ++ tailWord_4025739).sum := by decide
  have hdescent : baseEnd_4025739 < baseStart_4025739 := by decide
  rcases family_descends (prefixWord ++ tailWord_4025739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4025836 : List Nat := [2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 5]
def baseStart_4025836 : Nat := 118140960795 + 4025836 * 2 ^ 59
def prefixEnd_4025836 : Nat := 4983230072969 + 3 ^ 40 * 4025836 * 2
def baseEnd_4025836 : Nat := 2067188904174016131835523

theorem tailTrace_4025836 : CollatzResearch.WordTrace tailWord_4025836 prefixEnd_4025836 2067188904174016131835523 := by
  unfold tailWord_4025836
  simp only [CollatzResearch.WordTrace]
  refine ⟨73417150921545602447308681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97889534562060803263078241 73417150921545602447308681)
  ·
    refine ⟨55062863191159201835481511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73417150921545602447308681 55062863191159201835481511)
    ·
      refine ⟨82594294786738802753222267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55062863191159201835481511 82594294786738802753222267)
      ·
        refine ⟨123891442180108204129833401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82594294786738802753222267 123891442180108204129833401)
        ·
          refine ⟨92918581635081153097375051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123891442180108204129833401 92918581635081153097375051)
          ·
            refine ⟨139377872452621729646062577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92918581635081153097375051 139377872452621729646062577)
            ·
              refine ⟨104533404339466297234546933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139377872452621729646062577 104533404339466297234546933)
              ·
                refine ⟨9800006656824965365738775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 104533404339466297234546933 9800006656824965365738775)
                ·
                  refine ⟨14700009985237448048608163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9800006656824965365738775 14700009985237448048608163)
                  ·
                    refine ⟨22050014977856172072912245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14700009985237448048608163 22050014977856172072912245)
                    ·
                      refine ⟨2067188904174016131835523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22050014977856172072912245 2067188904174016131835523)
                      ·
                        rfl

theorem cell23_4025836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 5].length) (baseStart_4025836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4025836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4025836 prefixEnd_4025836 := by exact prefixLift 4025836
  have htrace : WordTrace (prefixWord ++ tailWord_4025836) baseStart_4025836 baseEnd_4025836 := by
    simpa [prefixWord, tailWord_4025836, baseEnd_4025836] using wordTrace_append hprefix tailTrace_4025836
  have hstable : (prefixWord ++ tailWord_4025836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4025836).length < 2 ^ (prefixWord ++ tailWord_4025836).sum := by decide
  have hdescent : baseEnd_4025836 < baseStart_4025836 := by decide
  rcases family_descends (prefixWord ++ tailWord_4025836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4025850 : List Nat := [3, 1, 1, 1, 1, 2, 4, 3, 3, 2, 2]
def baseStart_4025850 : Nat := 118140960795 + 4025850 * 2 ^ 59
def prefixEnd_4025850 : Nat := 4983230072969 + 3 ^ 40 * 4025850 * 2
def baseEnd_4025850 : Nat := 2067196092903179077060459

theorem tailTrace_4025850 : CollatzResearch.WordTrace tailWord_4025850 prefixEnd_4025850 2067196092903179077060459 := by
  unfold tailWord_4025850
  simp only [CollatzResearch.WordTrace]
  refine ⟨36708703116260121321406751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97889874976693656857084669 36708703116260121321406751)
  ·
    refine ⟨55063054674390181982110127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36708703116260121321406751 55063054674390181982110127)
    ·
      refine ⟨82594582011585272973165191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55063054674390181982110127 82594582011585272973165191)
      ·
        refine ⟨123891873017377909459747787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82594582011585272973165191 123891873017377909459747787)
        ·
          refine ⟨185837809526066864189621681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123891873017377909459747787 185837809526066864189621681)
          ·
            refine ⟨139378357144550148142216261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185837809526066864189621681 139378357144550148142216261)
            ·
              refine ⟨26133441964603152776665549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 139378357144550148142216261 26133441964603152776665549)
              ·
                refine ⟨9800040736726182291249581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26133441964603152776665549 9800040736726182291249581)
                ·
                  refine ⟨3675015276272318359218593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9800040736726182291249581 3675015276272318359218593)
                  ·
                    refine ⟨2756261457204238769413945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3675015276272318359218593 2756261457204238769413945)
                    ·
                      refine ⟨2067196092903179077060459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2756261457204238769413945 2067196092903179077060459)
                      ·
                        rfl

theorem cell23_4025850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 3, 3, 2, 2].length) (baseStart_4025850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4025850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4025850 prefixEnd_4025850 := by exact prefixLift 4025850
  have htrace : WordTrace (prefixWord ++ tailWord_4025850) baseStart_4025850 baseEnd_4025850 := by
    simpa [prefixWord, tailWord_4025850, baseEnd_4025850] using wordTrace_append hprefix tailTrace_4025850
  have hstable : (prefixWord ++ tailWord_4025850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4025850).length < 2 ^ (prefixWord ++ tailWord_4025850).sum := by decide
  have hdescent : baseEnd_4025850 < baseStart_4025850 := by decide
  rcases family_descends (prefixWord ++ tailWord_4025850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4025853 : List Nat := [1, 4, 1, 1, 1, 4, 1, 2, 3, 2, 3]
def baseStart_4025853 : Nat := 118140960795 + 4025853 * 2 ^ 59
def prefixEnd_4025853 : Nat := 4983230072969 + 3 ^ 40 * 4025853 * 2
def baseEnd_4025853 : Nat := 2067197633345142565322945

theorem tailTrace_4025853 : CollatzResearch.WordTrace tailWord_4025853 prefixEnd_4025853 2067197633345142565322945 := by
  unfold tailWord_4025853
  simp only [CollatzResearch.WordTrace]
  refine ⟨146834921884029616797986213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97889947922686411198657475 146834921884029616797986213)
  ·
    refine ⟨27531547853255553149622415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146834921884029616797986213 27531547853255553149622415)
    ·
      refine ⟨41297321779883329724433623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27531547853255553149622415 41297321779883329724433623)
      ·
        refine ⟨61945982669824994586650435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41297321779883329724433623 61945982669824994586650435)
        ·
          refine ⟨92918974004737491879975653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61945982669824994586650435 92918974004737491879975653)
          ·
            refine ⟨17422307625888279727495435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92918974004737491879975653 17422307625888279727495435)
            ·
              refine ⟨26133461438832419591243153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17422307625888279727495435 26133461438832419591243153)
              ·
                refine ⟨19600096079124314693432365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26133461438832419591243153 19600096079124314693432365)
                ·
                  refine ⟨7350036029671618010037137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19600096079124314693432365 7350036029671618010037137)
                  ·
                    refine ⟨5512527022253713507527853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7350036029671618010037137 5512527022253713507527853)
                    ·
                      refine ⟨2067197633345142565322945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5512527022253713507527853 2067197633345142565322945)
                      ·
                        rfl

theorem cell23_4025853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 2, 3, 2, 3].length) (baseStart_4025853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4025853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4025853 prefixEnd_4025853 := by exact prefixLift 4025853
  have htrace : WordTrace (prefixWord ++ tailWord_4025853) baseStart_4025853 baseEnd_4025853 := by
    simpa [prefixWord, tailWord_4025853, baseEnd_4025853] using wordTrace_append hprefix tailTrace_4025853
  have hstable : (prefixWord ++ tailWord_4025853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4025853).length < 2 ^ (prefixWord ++ tailWord_4025853).sum := by decide
  have hdescent : baseEnd_4025853 < baseStart_4025853 := by decide
  rcases family_descends (prefixWord ++ tailWord_4025853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4025860 : List Nat := [2, 3, 2, 3, 2, 1, 2, 1, 1, 6]
def baseStart_4025860 : Nat := 118140960795 + 4025860 * 2 ^ 59
def prefixEnd_4025860 : Nat := 4983230072969 + 3 ^ 40 * 4025860 * 2
def baseEnd_4025860 : Nat := 689067075903241345978471

theorem tailTrace_4025860 : CollatzResearch.WordTrace tailWord_4025860 prefixEnd_4025860 689067075903241345978471 := by
  unfold tailWord_4025860
  simp only [CollatzResearch.WordTrace]
  refine ⟨73417588597502128496745517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97890118130002837995660689 73417588597502128496745517)
  ·
    refine ⟨27531595724063298186279569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73417588597502128496745517 27531595724063298186279569)
    ·
      refine ⟨20648696793047473639709677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27531595724063298186279569 20648696793047473639709677)
      ·
        refine ⟨7743261297392802614891129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20648696793047473639709677 7743261297392802614891129)
        ·
          refine ⟨5807445973044601961168347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7743261297392802614891129 5807445973044601961168347)
          ·
            refine ⟨8711168959566902941752521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5807445973044601961168347 8711168959566902941752521)
            ·
              refine ⟨6533376719675177206314391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8711168959566902941752521 6533376719675177206314391)
              ·
                refine ⟨9800065079512765809471587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6533376719675177206314391 9800065079512765809471587)
                ·
                  refine ⟨14700097619269148714207381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9800065079512765809471587 14700097619269148714207381)
                  ·
                    refine ⟨689067075903241345978471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14700097619269148714207381 689067075903241345978471)
                    ·
                      rfl

theorem cell23_4025860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 2, 1, 1, 6].length) (baseStart_4025860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4025860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4025860 prefixEnd_4025860 := by exact prefixLift 4025860
  have htrace : WordTrace (prefixWord ++ tailWord_4025860) baseStart_4025860 baseEnd_4025860 := by
    simpa [prefixWord, tailWord_4025860, baseEnd_4025860] using wordTrace_append hprefix tailTrace_4025860
  have hstable : (prefixWord ++ tailWord_4025860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4025860).length < 2 ^ (prefixWord ++ tailWord_4025860).sum := by decide
  have hdescent : baseEnd_4025860 < baseStart_4025860 := by decide
  rcases family_descends (prefixWord ++ tailWord_4025860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4025863 : List Nat := [1, 1, 4, 3, 2, 1, 1, 3, 1, 2, 4]
def baseStart_4025863 : Nat := 118140960795 + 4025863 * 2 ^ 59
def prefixEnd_4025863 : Nat := 4983230072969 + 3 ^ 40 * 4025863 * 2
def baseEnd_4025863 : Nat := 2067202768151687526197899

theorem tailTrace_4025863 : CollatzResearch.WordTrace tailWord_4025863 prefixEnd_4025863 2067202768151687526197899 := by
  unfold tailWord_4025863
  simp only [CollatzResearch.WordTrace]
  refine ⟨146835286613993388505850243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97890191075995592337233495 146835286613993388505850243)
  ·
    refine ⟨220252929920990082758775365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146835286613993388505850243 220252929920990082758775365)
    ·
      refine ⟨41297424360185640517270381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 220252929920990082758775365 41297424360185640517270381)
      ·
        refine ⟨15486534135069615193976393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41297424360185640517270381 15486534135069615193976393)
        ·
          refine ⟨11614900601302211395482295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15486534135069615193976393 11614900601302211395482295)
          ·
            refine ⟨17422350901953317093223443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11614900601302211395482295 17422350901953317093223443)
            ·
              refine ⟨26133526352929975639835165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17422350901953317093223443 26133526352929975639835165)
              ·
                refine ⟨9800072382348740864938187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26133526352929975639835165 9800072382348740864938187)
                ·
                  refine ⟨14700108573523111297407281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9800072382348740864938187 14700108573523111297407281)
                  ·
                    refine ⟨11025081430142333473055461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14700108573523111297407281 11025081430142333473055461)
                    ·
                      refine ⟨2067202768151687526197899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11025081430142333473055461 2067202768151687526197899)
                      ·
                        rfl

theorem cell23_4025863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_4025863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4025863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4025863 prefixEnd_4025863 := by exact prefixLift 4025863
  have htrace : WordTrace (prefixWord ++ tailWord_4025863) baseStart_4025863 baseEnd_4025863 := by
    simpa [prefixWord, tailWord_4025863, baseEnd_4025863] using wordTrace_append hprefix tailTrace_4025863
  have hstable : (prefixWord ++ tailWord_4025863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4025863).length < 2 ^ (prefixWord ++ tailWord_4025863).sum := by decide
  have hdescent : baseEnd_4025863 < baseStart_4025863 := by decide
  rcases family_descends (prefixWord ++ tailWord_4025863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4025867 : List Nat := [1, 1, 1, 1, 8, 1, 1, 2, 3, 2, 2]
def baseStart_4025867 : Nat := 118140960795 + 4025867 * 2 ^ 59
def prefixEnd_4025867 : Nat := 4983230072969 + 3 ^ 40 * 4025867 * 2
def baseEnd_4025867 : Nat := 2067204822074305510547881

theorem tailTrace_4025867 : CollatzResearch.WordTrace tailWord_4025867 prefixEnd_4025867 2067204822074305510547881 := by
  unfold tailWord_4025867
  simp only [CollatzResearch.WordTrace]
  refine ⟨146835432505978897188995855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97890288337319264792663903 146835432505978897188995855)
  ·
    refine ⟨220253148758968345783493783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146835432505978897188995855 220253148758968345783493783)
    ·
      refine ⟨330379723138452518675240675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220253148758968345783493783 330379723138452518675240675)
      ·
        refine ⟨495569584707678778012861013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330379723138452518675240675 495569584707678778012861013)
        ·
          refine ⟨5807456070793110679838215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 495569584707678778012861013 5807456070793110679838215)
          ·
            refine ⟨8711184106189666019757323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5807456070793110679838215 8711184106189666019757323)
            ·
              refine ⟨13066776159284499029635985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8711184106189666019757323 13066776159284499029635985)
              ·
                refine ⟨9800082119463374272226989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13066776159284499029635985 9800082119463374272226989)
                ·
                  refine ⟨3675030794798765352085121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9800082119463374272226989 3675030794798765352085121)
                  ·
                    refine ⟨2756273096099074014063841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3675030794798765352085121 2756273096099074014063841)
                    ·
                      refine ⟨2067204822074305510547881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2756273096099074014063841 2067204822074305510547881)
                      ·
                        rfl

theorem cell23_4025867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 2, 3, 2, 2].length) (baseStart_4025867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4025867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4025867 prefixEnd_4025867 := by exact prefixLift 4025867
  have htrace : WordTrace (prefixWord ++ tailWord_4025867) baseStart_4025867 baseEnd_4025867 := by
    simpa [prefixWord, tailWord_4025867, baseEnd_4025867] using wordTrace_append hprefix tailTrace_4025867
  have hstable : (prefixWord ++ tailWord_4025867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4025867).length < 2 ^ (prefixWord ++ tailWord_4025867).sum := by decide
  have hdescent : baseEnd_4025867 < baseStart_4025867 := by decide
  rcases family_descends (prefixWord ++ tailWord_4025867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4025884 : List Nat := [2, 2, 3, 1, 2, 1, 4, 3, 1, 2, 2]
def baseStart_4025884 : Nat := 118140960795 + 4025884 * 2 ^ 59
def prefixEnd_4025884 : Nat := 4983230072969 + 3 ^ 40 * 4025884 * 2
def baseEnd_4025884 : Nat := 2067213551245431944035303

theorem tailTrace_4025884 : CollatzResearch.WordTrace tailWord_4025884 prefixEnd_4025884 2067213551245431944035303 := by
  unfold tailWord_4025884
  simp only [CollatzResearch.WordTrace]
  refine ⟨73418026273458654546182353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97890701697944872728243137 73418026273458654546182353)
  ·
    refine ⟨55063519705093990909636765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73418026273458654546182353 55063519705093990909636765)
    ·
      refine ⟨20648819889410246591113787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55063519705093990909636765 20648819889410246591113787)
      ·
        refine ⟨30973229834115369886670681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20648819889410246591113787 30973229834115369886670681)
        ·
          refine ⟨23229922375586527415003011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30973229834115369886670681 23229922375586527415003011)
          ·
            refine ⟨34844883563379791122504517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23229922375586527415003011 34844883563379791122504517)
            ·
              refine ⟨6533415668133710835469597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34844883563379791122504517 6533415668133710835469597)
              ·
                refine ⟨2450030875550141563301099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6533415668133710835469597 2450030875550141563301099)
                ·
                  refine ⟨3675046313325212344951649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2450030875550141563301099 3675046313325212344951649)
                  ·
                    refine ⟨2756284734993909258713737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3675046313325212344951649 2756284734993909258713737)
                    ·
                      refine ⟨2067213551245431944035303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2756284734993909258713737 2067213551245431944035303)
                      ·
                        rfl

theorem cell23_4025884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 4, 3, 1, 2, 2].length) (baseStart_4025884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4025884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4025884 prefixEnd_4025884 := by exact prefixLift 4025884
  have htrace : WordTrace (prefixWord ++ tailWord_4025884) baseStart_4025884 baseEnd_4025884 := by
    simpa [prefixWord, tailWord_4025884, baseEnd_4025884] using wordTrace_append hprefix tailTrace_4025884
  have hstable : (prefixWord ++ tailWord_4025884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4025884).length < 2 ^ (prefixWord ++ tailWord_4025884).sum := by decide
  have hdescent : baseEnd_4025884 < baseStart_4025884 := by decide
  rcases family_descends (prefixWord ++ tailWord_4025884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4025917 : List Nat := [1, 4, 1, 3, 3, 2, 1, 1, 1, 3, 3]
def baseStart_4025917 : Nat := 118140960795 + 4025917 * 2 ^ 59
def prefixEnd_4025917 : Nat := 4983230072969 + 3 ^ 40 * 4025917 * 2
def baseEnd_4025917 : Nat := 2067230496107030314922651

theorem tailTrace_4025917 : CollatzResearch.WordTrace tailWord_4025917 prefixEnd_4025917 2067230496107030314922651 := by
  unfold tailWord_4025917
  simp only [CollatzResearch.WordTrace]
  refine ⟨146837256155797755728316005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97891504103865170485544003 146837256155797755728316005)
  ·
    refine ⟨27531985529212079199059251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146837256155797755728316005 27531985529212079199059251)
    ·
      refine ⟨41297978293818118798588877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27531985529212079199059251 41297978293818118798588877)
      ·
        refine ⟨15486741860181794549470829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41297978293818118798588877 15486741860181794549470829)
        ·
          refine ⟨5807528197568172956051561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15486741860181794549470829 5807528197568172956051561)
          ·
            refine ⟨4355646148176129717038671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5807528197568172956051561 4355646148176129717038671)
            ·
              refine ⟨6533469222264194575558007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4355646148176129717038671 6533469222264194575558007)
              ·
                refine ⟨9800203833396291863337011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6533469222264194575558007 9800203833396291863337011)
                ·
                  refine ⟨14700305750094437795005517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9800203833396291863337011 14700305750094437795005517)
                  ·
                    refine ⟨5512614656285414173127069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14700305750094437795005517 5512614656285414173127069)
                    ·
                      refine ⟨2067230496107030314922651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5512614656285414173127069 2067230496107030314922651)
                      ·
                        rfl

theorem cell23_4025917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 1, 1, 1, 3, 3].length) (baseStart_4025917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4025917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4025917 prefixEnd_4025917 := by exact prefixLift 4025917
  have htrace : WordTrace (prefixWord ++ tailWord_4025917) baseStart_4025917 baseEnd_4025917 := by
    simpa [prefixWord, tailWord_4025917, baseEnd_4025917] using wordTrace_append hprefix tailTrace_4025917
  have hstable : (prefixWord ++ tailWord_4025917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4025917).length < 2 ^ (prefixWord ++ tailWord_4025917).sum := by decide
  have hdescent : baseEnd_4025917 < baseStart_4025917 := by decide
  rcases family_descends (prefixWord ++ tailWord_4025917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4025940 : List Nat := [2, 4, 1, 1, 1, 2, 2, 1, 3, 4, 2]
def baseStart_4025940 : Nat := 118140960795 + 4025940 * 2 ^ 59
def prefixEnd_4025940 : Nat := 4983230072969 + 3 ^ 40 * 4025940 * 2
def baseEnd_4025940 : Nat := 2067242306162083724935045

theorem tailTrace_4025940 : CollatzResearch.WordTrace tailWord_4025940 prefixEnd_4025940 2067242306162083724935045 := by
  unfold tailWord_4025940
  simp only [CollatzResearch.WordTrace]
  refine ⟨73419047517357215328201637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97892063356476287104268849 73419047517357215328201637)
  ·
    refine ⟨13766071409504477874037807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73419047517357215328201637 13766071409504477874037807)
    ·
      refine ⟨20649107114256716811056711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13766071409504477874037807 20649107114256716811056711)
      ·
        refine ⟨30973660671385075216585067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20649107114256716811056711 30973660671385075216585067)
        ·
          refine ⟨46460491007077612824877601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30973660671385075216585067 46460491007077612824877601)
          ·
            refine ⟨34845368255308209618658201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46460491007077612824877601 34845368255308209618658201)
            ·
              refine ⟨26134026191481157213993651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34845368255308209618658201 26134026191481157213993651)
              ·
                refine ⟨39201039287221735820990477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26134026191481157213993651 39201039287221735820990477)
                ·
                  refine ⟨14700389732708150932871429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39201039287221735820990477 14700389732708150932871429)
                  ·
                    refine ⟨2756323074882778299913393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14700389732708150932871429 2756323074882778299913393)
                    ·
                      refine ⟨2067242306162083724935045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2756323074882778299913393 2067242306162083724935045)
                      ·
                        rfl

theorem cell23_4025940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 1, 3, 4, 2].length) (baseStart_4025940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4025940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4025940 prefixEnd_4025940 := by exact prefixLift 4025940
  have htrace : WordTrace (prefixWord ++ tailWord_4025940) baseStart_4025940 baseEnd_4025940 := by
    simpa [prefixWord, tailWord_4025940, baseEnd_4025940] using wordTrace_append hprefix tailTrace_4025940
  have hstable : (prefixWord ++ tailWord_4025940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4025940).length < 2 ^ (prefixWord ++ tailWord_4025940).sum := by decide
  have hdescent : baseEnd_4025940 < baseStart_4025940 := by decide
  rcases family_descends (prefixWord ++ tailWord_4025940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4025943 : List Nat := [1, 1, 3, 2, 2, 4, 1, 1, 2, 1, 5]
def baseStart_4025943 : Nat := 118140960795 + 4025943 * 2 ^ 59
def prefixEnd_4025943 : Nat := 4983230072969 + 3 ^ 40 * 4025943 * 2
def baseEnd_4025943 : Nat := 2067243846604047213197531

theorem tailTrace_4025943 : CollatzResearch.WordTrace tailWord_4025943 prefixEnd_4025943 2067243846604047213197531 := by
  unfold tailWord_4025943
  simp only [CollatzResearch.WordTrace]
  refine ⟨146838204453703562168762483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97892136302469041445841655 146838204453703562168762483)
  ·
    refine ⟨220257306680555343253143725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146838204453703562168762483 220257306680555343253143725)
    ·
      refine ⟨82596490005208253719928897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220257306680555343253143725 82596490005208253719928897)
      ·
        refine ⟨61947367503906190289946673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82596490005208253719928897 61947367503906190289946673)
        ·
          refine ⟨46460525627929642717460005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61947367503906190289946673 46460525627929642717460005)
          ·
            refine ⟨8711348555236808009523751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46460525627929642717460005 8711348555236808009523751)
            ·
              refine ⟨13067022832855212014285627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8711348555236808009523751 13067022832855212014285627)
              ·
                refine ⟨19600534249282818021428441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13067022832855212014285627 19600534249282818021428441)
                ·
                  refine ⟨14700400686962113516071331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19600534249282818021428441 14700400686962113516071331)
                  ·
                    refine ⟨22050601030443170274106997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14700400686962113516071331 22050601030443170274106997)
                    ·
                      refine ⟨2067243846604047213197531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22050601030443170274106997 2067243846604047213197531)
                      ·
                        rfl

theorem cell23_4025943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 1, 2, 1, 5].length) (baseStart_4025943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4025943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4025943 prefixEnd_4025943 := by exact prefixLift 4025943
  have htrace : WordTrace (prefixWord ++ tailWord_4025943) baseStart_4025943 baseEnd_4025943 := by
    simpa [prefixWord, tailWord_4025943, baseEnd_4025943] using wordTrace_append hprefix tailTrace_4025943
  have hstable : (prefixWord ++ tailWord_4025943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4025943).length < 2 ^ (prefixWord ++ tailWord_4025943).sum := by decide
  have hdescent : baseEnd_4025943 < baseStart_4025943 := by decide
  rcases family_descends (prefixWord ++ tailWord_4025943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4025946 : List Nat := [3, 1, 1, 2, 1, 1, 1, 4, 9]
def baseStart_4025946 : Nat := 118140960795 + 4025946 * 2 ^ 59
def prefixEnd_4025946 : Nat := 4983230072969 + 3 ^ 40 * 4025946 * 2
def baseEnd_4025946 : Nat := 229693931894001189051113

theorem tailTrace_4025946 : CollatzResearch.WordTrace tailWord_4025946 prefixEnd_4025946 229693931894001189051113 := by
  unfold tailWord_4025946
  simp only [CollatzResearch.WordTrace]
  refine ⟨36709578468173173420280423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97892209248461795787414461 36709578468173173420280423)
  ·
    refine ⟨55064367702259760130420635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36709578468173173420280423 55064367702259760130420635)
    ·
      refine ⟨82596551553389640195630953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55064367702259760130420635 82596551553389640195630953)
      ·
        refine ⟨61947413665042230146723215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82596551553389640195630953 61947413665042230146723215)
        ·
          refine ⟨92921120497563345220084823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61947413665042230146723215 92921120497563345220084823)
          ·
            refine ⟨139381680746345017830127235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92921120497563345220084823 139381680746345017830127235)
            ·
              refine ⟨209072521119517526745190853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139381680746345017830127235 209072521119517526745190853)
              ·
                refine ⟨39201097709909536264723285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 209072521119517526745190853 39201097709909536264723285)
                ·
                  refine ⟨229693931894001189051113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 39201097709909536264723285 229693931894001189051113)
                  ·
                    rfl

theorem cell23_4025946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 4, 9].length) (baseStart_4025946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4025946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4025946 prefixEnd_4025946 := by exact prefixLift 4025946
  have htrace : WordTrace (prefixWord ++ tailWord_4025946) baseStart_4025946 baseEnd_4025946 := by
    simpa [prefixWord, tailWord_4025946, baseEnd_4025946] using wordTrace_append hprefix tailTrace_4025946
  have hstable : (prefixWord ++ tailWord_4025946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4025946).length < 2 ^ (prefixWord ++ tailWord_4025946).sum := by decide
  have hdescent : baseEnd_4025946 < baseStart_4025946 := by decide
  rcases family_descends (prefixWord ++ tailWord_4025946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4025957 : List Nat := [1, 3, 1, 3, 3, 1, 2, 1, 4, 2, 2]
def baseStart_4025957 : Nat := 118140960795 + 4025957 * 2 ^ 59
def prefixEnd_4025957 : Nat := 4983230072969 + 3 ^ 40 * 4025957 * 2
def baseEnd_4025957 : Nat := 2067251035333210158422467

theorem tailTrace_4025957 : CollatzResearch.WordTrace tailWord_4025957 prefixEnd_4025957 2067251035333210158422467 := by
  unfold tailWord_4025957
  simp only [CollatzResearch.WordTrace]
  refine ⟨146838715075652842559772125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97892476717101895039848083 146838715075652842559772125)
  ·
    refine ⟨55064518153369815959914547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146838715075652842559772125 55064518153369815959914547)
    ·
      refine ⟨82596777230054723939871821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55064518153369815959914547 82596777230054723939871821)
      ·
        refine ⟨30973791461270521477451933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82596777230054723939871821 30973791461270521477451933)
        ·
          refine ⟨11615171797976445554044475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30973791461270521477451933 11615171797976445554044475)
          ·
            refine ⟨17422757696964668331066713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11615171797976445554044475 17422757696964668331066713)
            ·
              refine ⟨13067068272723501248300035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17422757696964668331066713 13067068272723501248300035)
              ·
                refine ⟨19600602409085251872450053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13067068272723501248300035 19600602409085251872450053)
                ·
                  refine ⟨3675112951703484726084385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19600602409085251872450053 3675112951703484726084385)
                  ·
                    refine ⟨2756334713777613544563289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3675112951703484726084385 2756334713777613544563289)
                    ·
                      refine ⟨2067251035333210158422467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2756334713777613544563289 2067251035333210158422467)
                      ·
                        rfl

theorem cell23_4025957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 1, 4, 2, 2].length) (baseStart_4025957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4025957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4025957 prefixEnd_4025957 := by exact prefixLift 4025957
  have htrace : WordTrace (prefixWord ++ tailWord_4025957) baseStart_4025957 baseEnd_4025957 := by
    simpa [prefixWord, tailWord_4025957, baseEnd_4025957] using wordTrace_append hprefix tailTrace_4025957
  have hstable : (prefixWord ++ tailWord_4025957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4025957).length < 2 ^ (prefixWord ++ tailWord_4025957).sum := by decide
  have hdescent : baseEnd_4025957 < baseStart_4025957 := by decide
  rcases family_descends (prefixWord ++ tailWord_4025957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4025993 : List Nat := [1, 2, 1, 1, 4, 1, 3, 3, 2, 5]
def baseStart_4025993 : Nat := 118140960795 + 4025993 * 2 ^ 59
def prefixEnd_4025993 : Nat := 4983230072969 + 3 ^ 40 * 4025993 * 2
def baseEnd_4025993 : Nat := 689089840212257339190767

theorem tailTrace_4025993 : CollatzResearch.WordTrace tailWord_4025993 prefixEnd_4025993 689089840212257339190767 := by
  unfold tailWord_4025993
  simp only [CollatzResearch.WordTrace]
  refine ⟨146840028103522420708082633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97893352069014947138721755 146840028103522420708082633)
  ·
    refine ⟨110130021077641815531061975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146840028103522420708082633 110130021077641815531061975)
    ·
      refine ⟨165195031616462723296592963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110130021077641815531061975 165195031616462723296592963)
      ·
        refine ⟨247792547424694084944889445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165195031616462723296592963 247792547424694084944889445)
        ·
          refine ⟨46461102642130140927166771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 247792547424694084944889445 46461102642130140927166771)
          ·
            refine ⟨69691653963195211390750157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46461102642130140927166771 69691653963195211390750157)
            ·
              refine ⟨26134370236198204271531309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69691653963195211390750157 26134370236198204271531309)
              ·
                refine ⟨9800388838574326601824241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26134370236198204271531309 9800388838574326601824241)
                ·
                  refine ⟨7350291628930744951368181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9800388838574326601824241 7350291628930744951368181)
                  ·
                    refine ⟨689089840212257339190767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7350291628930744951368181 689089840212257339190767)
                    ·
                      rfl

theorem cell23_4025993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 3, 2, 5].length) (baseStart_4025993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4025993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4025993 prefixEnd_4025993 := by exact prefixLift 4025993
  have htrace : WordTrace (prefixWord ++ tailWord_4025993) baseStart_4025993 baseEnd_4025993 := by
    simpa [prefixWord, tailWord_4025993, baseEnd_4025993] using wordTrace_append hprefix tailTrace_4025993
  have hstable : (prefixWord ++ tailWord_4025993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4025993).length < 2 ^ (prefixWord ++ tailWord_4025993).sum := by decide
  have hdescent : baseEnd_4025993 < baseStart_4025993 := by decide
  rcases family_descends (prefixWord ++ tailWord_4025993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4026013 : List Nat := [1, 4, 2, 1, 1, 1, 1, 2, 3, 3, 4]
def baseStart_4026013 : Nat := 118140960795 + 4026013 * 2 ^ 59
def prefixEnd_4026013 : Nat := 4983230072969 + 3 ^ 40 * 4026013 * 2
def baseEnd_4026013 : Nat := 2067279790249861939322209

theorem tailTrace_4026013 : CollatzResearch.WordTrace tailWord_4026013 prefixEnd_4026013 2067279790249861939322209 := by
  unfold tailWord_4026013
  simp only [CollatzResearch.WordTrace]
  refine ⟨146840757563449964123810693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97893838375633309415873795 146840757563449964123810693)
  ·
    refine ⟨27532642043146868273214505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146840757563449964123810693 27532642043146868273214505)
    ·
      refine ⟨20649481532360151204910879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27532642043146868273214505 20649481532360151204910879)
      ·
        refine ⟨30974222298540226807366319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20649481532360151204910879 30974222298540226807366319)
        ·
          refine ⟨46461333447810340211049479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30974222298540226807366319 46461333447810340211049479)
          ·
            refine ⟨69692000171715510316574219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46461333447810340211049479 69692000171715510316574219)
            ·
              refine ⟨104538000257573265474861329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69692000171715510316574219 104538000257573265474861329)
              ·
                refine ⟨78403500193179949106145997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104538000257573265474861329 78403500193179949106145997)
                ·
                  refine ⟨29401312572442480914804749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78403500193179949106145997 29401312572442480914804749)
                  ·
                    refine ⟨11025492214665930343051781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29401312572442480914804749 11025492214665930343051781)
                    ·
                      refine ⟨2067279790249861939322209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11025492214665930343051781 2067279790249861939322209)
                      ·
                        rfl

theorem cell23_4026013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 3, 3, 4].length) (baseStart_4026013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4026013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4026013 prefixEnd_4026013 := by exact prefixLift 4026013
  have htrace : WordTrace (prefixWord ++ tailWord_4026013) baseStart_4026013 baseEnd_4026013 := by
    simpa [prefixWord, tailWord_4026013, baseEnd_4026013] using wordTrace_append hprefix tailTrace_4026013
  have hstable : (prefixWord ++ tailWord_4026013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4026013).length < 2 ^ (prefixWord ++ tailWord_4026013).sum := by decide
  have hdescent : baseEnd_4026013 < baseStart_4026013 := by decide
  rcases family_descends (prefixWord ++ tailWord_4026013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4026014 : List Nat := [4, 3, 1, 1, 1, 2, 4, 2, 5]
def baseStart_4026014 : Nat := 118140960795 + 4026014 * 2 ^ 59
def prefixEnd_4026014 : Nat := 4983230072969 + 3 ^ 40 * 4026014 * 2
def baseEnd_4026014 : Nat := 229697811525612937267745

theorem tailTrace_4026014 : CollatzResearch.WordTrace tailWord_4026014 prefixEnd_4026014 229697811525612937267745 := by
  unfold tailWord_4026014
  simp only [CollatzResearch.WordTrace]
  refine ⟨18355099254555792661824637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97893862690964227529731397 18355099254555792661824637)
  ·
    refine ⟨6883162220458422248184239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18355099254555792661824637 6883162220458422248184239)
    ·
      refine ⟨10324743330687633372276359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6883162220458422248184239 10324743330687633372276359)
      ·
        refine ⟨15487114996031450058414539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10324743330687633372276359 15487114996031450058414539)
        ·
          refine ⟨23230672494047175087621809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15487114996031450058414539 23230672494047175087621809)
          ·
            refine ⟨17423004370535381315716357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23230672494047175087621809 17423004370535381315716357)
            ·
              refine ⟨3266813319475383996696817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17423004370535381315716357 3266813319475383996696817)
              ·
                refine ⟨2450109989606537997522613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3266813319475383996696817 2450109989606537997522613)
                ·
                  refine ⟨229697811525612937267745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2450109989606537997522613 229697811525612937267745)
                  ·
                    rfl

theorem cell23_4026014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 4, 2, 5].length) (baseStart_4026014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4026014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4026014 prefixEnd_4026014 := by exact prefixLift 4026014
  have htrace : WordTrace (prefixWord ++ tailWord_4026014) baseStart_4026014 baseEnd_4026014 := by
    simpa [prefixWord, tailWord_4026014, baseEnd_4026014] using wordTrace_append hprefix tailTrace_4026014
  have hstable : (prefixWord ++ tailWord_4026014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4026014).length < 2 ^ (prefixWord ++ tailWord_4026014).sum := by decide
  have hdescent : baseEnd_4026014 < baseStart_4026014 := by decide
  rcases family_descends (prefixWord ++ tailWord_4026014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4026063 : List Nat := [1, 1, 2, 1, 1, 3, 1, 2, 1, 7, 3]
def baseStart_4026063 : Nat := 118140960795 + 4026063 * 2 ^ 59
def prefixEnd_4026063 : Nat := 4983230072969 + 3 ^ 40 * 4026063 * 2
def baseEnd_4026063 : Nat := 2067305464282586743696979

theorem tailTrace_4026063 : CollatzResearch.WordTrace tailWord_4026063 prefixEnd_4026063 2067305464282586743696979 := by
  unfold tailWord_4026063
  simp only [CollatzResearch.WordTrace]
  refine ⟨146842581213268822663130843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97895054142179215108753895 146842581213268822663130843)
  ·
    refine ⟨220263871819903233994696265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146842581213268822663130843 220263871819903233994696265)
    ·
      refine ⟨165197903864927425496022199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220263871819903233994696265 165197903864927425496022199)
      ·
        refine ⟨247796855797391138244033299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165197903864927425496022199 247796855797391138244033299)
        ·
          refine ⟨371695283696086707366049949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247796855797391138244033299 371695283696086707366049949)
          ·
            refine ⟨139385731386032515262268731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 371695283696086707366049949 139385731386032515262268731)
            ·
              refine ⟨209078597079048772893403097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139385731386032515262268731 209078597079048772893403097)
              ·
                refine ⟨156808947809286579670052323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 209078597079048772893403097 156808947809286579670052323)
                ·
                  refine ⟨235213421713929869505078485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 156808947809286579670052323 235213421713929869505078485)
                  ·
                    refine ⟨5512814571420231316525277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 235213421713929869505078485 5512814571420231316525277)
                    ·
                      refine ⟨2067305464282586743696979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5512814571420231316525277 2067305464282586743696979)
                      ·
                        rfl

theorem cell23_4026063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 7, 3].length) (baseStart_4026063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4026063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4026063 prefixEnd_4026063 := by exact prefixLift 4026063
  have htrace : WordTrace (prefixWord ++ tailWord_4026063) baseStart_4026063 baseEnd_4026063 := by
    simpa [prefixWord, tailWord_4026063, baseEnd_4026063] using wordTrace_append hprefix tailTrace_4026063
  have hstable : (prefixWord ++ tailWord_4026063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4026063).length < 2 ^ (prefixWord ++ tailWord_4026063).sum := by decide
  have hdescent : baseEnd_4026063 < baseStart_4026063 := by decide
  rcases family_descends (prefixWord ++ tailWord_4026063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4026073 : List Nat := [1, 2, 1, 2, 3, 3, 1, 1, 1, 2, 6]
def baseStart_4026073 : Nat := 118140960795 + 4026073 * 2 ^ 59
def prefixEnd_4026073 : Nat := 4983230072969 + 3 ^ 40 * 4026073 * 2
def baseEnd_4026073 : Nat := 2067310599089131704571933

theorem tailTrace_4026073 : CollatzResearch.WordTrace tailWord_4026073 prefixEnd_4026073 2067310599089131704571933 := by
  unfold tailWord_4026073
  simp only [CollatzResearch.WordTrace]
  refine ⟨146842945943232594370994873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97895297295488396247329915 146842945943232594370994873)
  ·
    refine ⟨110132209457424445778246155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146842945943232594370994873 110132209457424445778246155)
    ·
      refine ⟨165198314186136668667369233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110132209457424445778246155 165198314186136668667369233)
      ·
        refine ⟨123898735639602501500526925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165198314186136668667369233 123898735639602501500526925)
        ·
          refine ⟨46462025864850938062697597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123898735639602501500526925 46462025864850938062697597)
          ·
            refine ⟨17423259699319101773511599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46462025864850938062697597 17423259699319101773511599)
            ·
              refine ⟨26134889548978652660267399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17423259699319101773511599 26134889548978652660267399)
              ·
                refine ⟨39202334323467978990401099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26134889548978652660267399 39202334323467978990401099)
                ·
                  refine ⟨58803501485201968485601649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39202334323467978990401099 58803501485201968485601649)
                  ·
                    refine ⟨44102626113901476364201237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58803501485201968485601649 44102626113901476364201237)
                    ·
                      refine ⟨2067310599089131704571933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44102626113901476364201237 2067310599089131704571933)
                      ·
                        rfl

theorem cell23_4026073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 1, 1, 2, 6].length) (baseStart_4026073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4026073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4026073 prefixEnd_4026073 := by exact prefixLift 4026073
  have htrace : WordTrace (prefixWord ++ tailWord_4026073) baseStart_4026073 baseEnd_4026073 := by
    simpa [prefixWord, tailWord_4026073, baseEnd_4026073] using wordTrace_append hprefix tailTrace_4026073
  have hstable : (prefixWord ++ tailWord_4026073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4026073).length < 2 ^ (prefixWord ++ tailWord_4026073).sum := by decide
  have hdescent : baseEnd_4026073 < baseStart_4026073 := by decide
  rcases family_descends (prefixWord ++ tailWord_4026073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4026097 : List Nat := [1, 2, 2, 2, 2, 3, 2, 2, 3, 1, 3]
def baseStart_4026097 : Nat := 118140960795 + 4026097 * 2 ^ 59
def prefixEnd_4026097 : Nat := 4983230072969 + 3 ^ 40 * 4026097 * 2
def baseEnd_4026097 : Nat := 2067322922624839610671823

theorem tailTrace_4026097 : CollatzResearch.WordTrace tailWord_4026097 prefixEnd_4026097 2067322922624839610671823 := by
  unfold tailWord_4026097
  simp only [CollatzResearch.WordTrace]
  refine ⟨146843821295145646469868545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97895880863430430979912363 146843821295145646469868545)
  ·
    refine ⟨110132865971359234852401409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146843821295145646469868545 110132865971359234852401409)
    ·
      refine ⟨82599649478519426139301057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110132865971359234852401409 82599649478519426139301057)
      ·
        refine ⟨61949737108889569604475793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82599649478519426139301057 61949737108889569604475793)
        ·
          refine ⟨46462302831667177203356845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61949737108889569604475793 46462302831667177203356845)
          ·
            refine ⟨17423363561875191451258817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46462302831667177203356845 17423363561875191451258817)
            ·
              refine ⟨13067522671406393588444113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17423363561875191451258817 13067522671406393588444113)
              ·
                refine ⟨9800642003554795191333085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13067522671406393588444113 9800642003554795191333085)
                ·
                  refine ⟨3675240751333048196749907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9800642003554795191333085 3675240751333048196749907)
                  ·
                    refine ⟨5512861126999572295124861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3675240751333048196749907 5512861126999572295124861)
                    ·
                      refine ⟨2067322922624839610671823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5512861126999572295124861 2067322922624839610671823)
                      ·
                        rfl

theorem cell23_4026097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 2, 3, 1, 3].length) (baseStart_4026097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4026097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4026097 prefixEnd_4026097 := by exact prefixLift 4026097
  have htrace : WordTrace (prefixWord ++ tailWord_4026097) baseStart_4026097 baseEnd_4026097 := by
    simpa [prefixWord, tailWord_4026097, baseEnd_4026097] using wordTrace_append hprefix tailTrace_4026097
  have hstable : (prefixWord ++ tailWord_4026097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4026097).length < 2 ^ (prefixWord ++ tailWord_4026097).sum := by decide
  have hdescent : baseEnd_4026097 < baseStart_4026097 := by decide
  rcases family_descends (prefixWord ++ tailWord_4026097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4026125 : List Nat := [1, 7, 2, 1, 1, 2, 1, 1, 3, 4]
def baseStart_4026125 : Nat := 118140960795 + 4026125 * 2 ^ 59
def prefixEnd_4026125 : Nat := 4983230072969 + 3 ^ 40 * 4026125 * 2
def baseEnd_4026125 : Nat := 689112433361055167040565

theorem tailTrace_4026125 : CollatzResearch.WordTrace tailWord_4026125 prefixEnd_4026125 689112433361055167040565 := by
  unfold tailWord_4026125
  simp only [CollatzResearch.WordTrace]
  refine ⟨146844842539044207251887829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97896561692696138167925219 146844842539044207251887829)
  ·
    refine ⟨3441675997008848607466121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 146844842539044207251887829 3441675997008848607466121)
    ·
      refine ⟨2581256997756636455599591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3441675997008848607466121 2581256997756636455599591)
      ·
        refine ⟨3871885496634954683399387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2581256997756636455599591 3871885496634954683399387)
        ·
          refine ⟨5807828244952432025099081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3871885496634954683399387 5807828244952432025099081)
          ·
            refine ⟨4355871183714324018824311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5807828244952432025099081 4355871183714324018824311)
            ·
              refine ⟨6533806775571486028236467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4355871183714324018824311 6533806775571486028236467)
              ·
                refine ⟨9800710163357229042354701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6533806775571486028236467 9800710163357229042354701)
                ·
                  refine ⟨3675266311258960890883013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9800710163357229042354701 3675266311258960890883013)
                  ·
                    refine ⟨689112433361055167040565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3675266311258960890883013 689112433361055167040565)
                    ·
                      rfl

theorem cell23_4026125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_4026125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4026125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4026125 prefixEnd_4026125 := by exact prefixLift 4026125
  have htrace : WordTrace (prefixWord ++ tailWord_4026125) baseStart_4026125 baseEnd_4026125 := by
    simpa [prefixWord, tailWord_4026125, baseEnd_4026125] using wordTrace_append hprefix tailTrace_4026125
  have hstable : (prefixWord ++ tailWord_4026125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4026125).length < 2 ^ (prefixWord ++ tailWord_4026125).sum := by decide
  have hdescent : baseEnd_4026125 < baseStart_4026125 := by decide
  rcases family_descends (prefixWord ++ tailWord_4026125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4026140 : List Nat := [2, 2, 3, 1, 1, 2, 1, 4, 1, 1, 5]
def baseStart_4026140 : Nat := 118140960795 + 4026140 * 2 ^ 59
def prefixEnd_4026140 : Nat := 4983230072969 + 3 ^ 40 * 4026140 * 2
def baseEnd_4026140 : Nat := 2067345002292982942434125

theorem tailTrace_4026140 : CollatzResearch.WordTrace tailWord_4026140 prefixEnd_4026140 2067345002292982942434125 := by
  unfold tailWord_4026140
  simp only [CollatzResearch.WordTrace]
  refine ⟨73422694816994932406841937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97896926422659909875789249 73422694816994932406841937)
  ·
    refine ⟨55067021112746199305131453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73422694816994932406841937 55067021112746199305131453)
    ·
      refine ⟨20650132917279824739424295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55067021112746199305131453 20650132917279824739424295)
      ·
        refine ⟨30975199375919737109136443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20650132917279824739424295 30975199375919737109136443)
        ·
          refine ⟨46462799063879605663704665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30975199375919737109136443 46462799063879605663704665)
          ·
            refine ⟨34847099297909704247778499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46462799063879605663704665 34847099297909704247778499)
            ·
              refine ⟨52270648946864556371667749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34847099297909704247778499 52270648946864556371667749)
              ·
                refine ⟨9800746677537104319687703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52270648946864556371667749 9800746677537104319687703)
                ·
                  refine ⟨14701120016305656479531555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9800746677537104319687703 14701120016305656479531555)
                  ·
                    refine ⟨22051680024458484719297333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14701120016305656479531555 22051680024458484719297333)
                    ·
                      refine ⟨2067345002292982942434125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22051680024458484719297333 2067345002292982942434125)
                      ·
                        rfl

theorem cell23_4026140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 4, 1, 1, 5].length) (baseStart_4026140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4026140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4026140 prefixEnd_4026140 := by exact prefixLift 4026140
  have htrace : WordTrace (prefixWord ++ tailWord_4026140) baseStart_4026140 baseEnd_4026140 := by
    simpa [prefixWord, tailWord_4026140, baseEnd_4026140] using wordTrace_append hprefix tailTrace_4026140
  have hstable : (prefixWord ++ tailWord_4026140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4026140).length < 2 ^ (prefixWord ++ tailWord_4026140).sum := by decide
  have hdescent : baseEnd_4026140 < baseStart_4026140 := by decide
  rcases family_descends (prefixWord ++ tailWord_4026140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4026174 : List Nat := [4, 2, 1, 2, 2, 3, 1, 1, 1, 1, 5]
def baseStart_4026174 : Nat := 118140960795 + 4026174 * 2 ^ 59
def prefixEnd_4026174 : Nat := 4983230072969 + 3 ^ 40 * 4026174 * 2
def baseEnd_4026174 : Nat := 2067362460635235809408969

theorem tailTrace_4026174 : CollatzResearch.WordTrace tailWord_4026174 prefixEnd_4026174 2067362460635235809408969 := by
  unfold tailWord_4026174
  simp only [CollatzResearch.WordTrace]
  refine ⟨18355828714483336077552697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97897753143911125746947717 18355828714483336077552697)
  ·
    refine ⟨13766871535862502058164523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18355828714483336077552697 13766871535862502058164523)
    ·
      refine ⟨20650307303793753087246785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13766871535862502058164523 20650307303793753087246785)
      ·
        refine ⟨15487730477845314815435089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20650307303793753087246785 15487730477845314815435089)
        ·
          refine ⟨11615797858383986111576317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15487730477845314815435089 11615797858383986111576317)
          ·
            refine ⟨4355924196893994791841119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11615797858383986111576317 4355924196893994791841119)
            ·
              refine ⟨6533886295340992187761679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4355924196893994791841119 6533886295340992187761679)
              ·
                refine ⟨9800829443011488281642519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6533886295340992187761679 9800829443011488281642519)
                ·
                  refine ⟨14701244164517232422463779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9800829443011488281642519 14701244164517232422463779)
                  ·
                    refine ⟨22051866246775848633695669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14701244164517232422463779 22051866246775848633695669)
                    ·
                      refine ⟨2067362460635235809408969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22051866246775848633695669 2067362460635235809408969)
                      ·
                        rfl

theorem cell23_4026174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 1, 1, 1, 1, 5].length) (baseStart_4026174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4026174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4026174 prefixEnd_4026174 := by exact prefixLift 4026174
  have htrace : WordTrace (prefixWord ++ tailWord_4026174) baseStart_4026174 baseEnd_4026174 := by
    simpa [prefixWord, tailWord_4026174, baseEnd_4026174] using wordTrace_append hprefix tailTrace_4026174
  have hstable : (prefixWord ++ tailWord_4026174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4026174).length < 2 ^ (prefixWord ++ tailWord_4026174).sum := by decide
  have hdescent : baseEnd_4026174 < baseStart_4026174 := by decide
  rcases family_descends (prefixWord ++ tailWord_4026174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4026182 : List Nat := [6, 1, 1, 2, 1, 3, 2, 2, 1, 1, 3]
def baseStart_4026182 : Nat := 118140960795 + 4026182 * 2 ^ 59
def prefixEnd_4026182 : Nat := 4983230072969 + 3 ^ 40 * 4026182 * 2
def baseEnd_4026182 : Nat := 2067366568480471778108933

theorem tailTrace_4026182 : CollatzResearch.WordTrace tailWord_4026182 prefixEnd_4026182 2067366568480471778108933 := by
  unfold tailWord_4026182
  simp only [CollatzResearch.WordTrace]
  refine ⟨4588966296869928312084775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 97897947666558470657808533 4588966296869928312084775)
  ·
    refine ⟨6883449445304892468127163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4588966296869928312084775 6883449445304892468127163)
    ·
      refine ⟨10325174167957338702190745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6883449445304892468127163 10325174167957338702190745)
      ·
        refine ⟨7743880625968004026643059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10325174167957338702190745 7743880625968004026643059)
        ·
          refine ⟨11615820938952006039964589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7743880625968004026643059 11615820938952006039964589)
          ·
            refine ⟨4355932852107002264986721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11615820938952006039964589 4355932852107002264986721)
            ·
              refine ⟨3266949639080251698740041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4355932852107002264986721 3266949639080251698740041)
              ·
                refine ⟨2450212229310188774055031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3266949639080251698740041 2450212229310188774055031)
                ·
                  refine ⟨3675318343965283161082547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2450212229310188774055031 3675318343965283161082547)
                  ·
                    refine ⟨5512977515947924741623821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3675318343965283161082547 5512977515947924741623821)
                    ·
                      refine ⟨2067366568480471778108933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5512977515947924741623821 2067366568480471778108933)
                      ·
                        rfl

theorem cell23_4026182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 2, 2, 1, 1, 3].length) (baseStart_4026182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4026182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4026182 prefixEnd_4026182 := by exact prefixLift 4026182
  have htrace : WordTrace (prefixWord ++ tailWord_4026182) baseStart_4026182 baseEnd_4026182 := by
    simpa [prefixWord, tailWord_4026182, baseEnd_4026182] using wordTrace_append hprefix tailTrace_4026182
  have hstable : (prefixWord ++ tailWord_4026182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4026182).length < 2 ^ (prefixWord ++ tailWord_4026182).sum := by decide
  have hdescent : baseEnd_4026182 < baseStart_4026182 := by decide
  rcases family_descends (prefixWord ++ tailWord_4026182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4026188 : List Nat := [2, 2, 1, 3, 4, 1, 1, 4, 1, 2, 2]
def baseStart_4026188 : Nat := 118140960795 + 4026188 * 2 ^ 59
def prefixEnd_4026188 : Nat := 4983230072969 + 3 ^ 40 * 4026188 * 2
def baseEnd_4026188 : Nat := 2067369649364398754633905

theorem tailTrace_4026188 : CollatzResearch.WordTrace tailWord_4026188 prefixEnd_4026188 2067369649364398754633905 := by
  unfold tailWord_4026188
  simp only [CollatzResearch.WordTrace]
  refine ⟨73423570168907984505715609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97898093558543979340954145 73423570168907984505715609)
  ·
    refine ⟨55067677626680988379286707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73423570168907984505715609 55067677626680988379286707)
    ·
      refine ⟨82601516440021482568930061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55067677626680988379286707 82601516440021482568930061)
      ·
        refine ⟨30975568665008055963348773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82601516440021482568930061 30975568665008055963348773)
        ·
          refine ⟨5807919124689010493127895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30975568665008055963348773 5807919124689010493127895)
          ·
            refine ⟨8711878687033515739691843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5807919124689010493127895 8711878687033515739691843)
            ·
              refine ⟨13067818030550273609537765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8711878687033515739691843 13067818030550273609537765)
              ·
                refine ⟨2450215880728176301788331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13067818030550273609537765 2450215880728176301788331)
                ·
                  refine ⟨3675323821092264452682497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2450215880728176301788331 3675323821092264452682497)
                  ·
                    refine ⟨2756492865819198339511873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3675323821092264452682497 2756492865819198339511873)
                    ·
                      refine ⟨2067369649364398754633905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2756492865819198339511873 2067369649364398754633905)
                      ·
                        rfl

theorem cell23_4026188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 4, 1, 2, 2].length) (baseStart_4026188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4026188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4026188 prefixEnd_4026188 := by exact prefixLift 4026188
  have htrace : WordTrace (prefixWord ++ tailWord_4026188) baseStart_4026188 baseEnd_4026188 := by
    simpa [prefixWord, tailWord_4026188, baseEnd_4026188] using wordTrace_append hprefix tailTrace_4026188
  have hstable : (prefixWord ++ tailWord_4026188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4026188).length < 2 ^ (prefixWord ++ tailWord_4026188).sum := by decide
  have hdescent : baseEnd_4026188 < baseStart_4026188 := by decide
  rcases family_descends (prefixWord ++ tailWord_4026188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4026238 : List Nat := [4, 2, 3, 1, 1, 1, 3, 2, 2, 1, 3]
def baseStart_4026238 : Nat := 118140960795 + 4026238 * 2 ^ 59
def prefixEnd_4026238 : Nat := 4983230072969 + 3 ^ 40 * 4026238 * 2
def baseEnd_4026238 : Nat := 2067395323397123559008675

theorem tailTrace_4026238 : CollatzResearch.WordTrace tailWord_4026238 prefixEnd_4026238 2067395323397123559008675 := by
  unfold tailWord_4026238
  simp only [CollatzResearch.WordTrace]
  refine ⟨18356120498454353443843921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97899309325089885033834245 18356120498454353443843921)
  ·
    refine ⟨13767090373840765082882941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18356120498454353443843921 13767090373840765082882941)
    ·
      refine ⟨5162658890190286906081103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13767090373840765082882941 5162658890190286906081103)
      ·
        refine ⟨7743988335285430359121655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5162658890190286906081103 7743988335285430359121655)
        ·
          refine ⟨11615982502928145538682483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7743988335285430359121655 11615982502928145538682483)
          ·
            refine ⟨17423973754392218308023725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11615982502928145538682483 17423973754392218308023725)
            ·
              refine ⟨6533990157897081865508897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17423973754392218308023725 6533990157897081865508897)
              ·
                refine ⟨4900492618422811399131673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6533990157897081865508897 4900492618422811399131673)
                ·
                  refine ⟨3675369463817108549348755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4900492618422811399131673 3675369463817108549348755)
                  ·
                    refine ⟨5513054195725662824023133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3675369463817108549348755 5513054195725662824023133)
                    ·
                      refine ⟨2067395323397123559008675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5513054195725662824023133 2067395323397123559008675)
                      ·
                        rfl

theorem cell23_4026238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_4026238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4026238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4026238 prefixEnd_4026238 := by exact prefixLift 4026238
  have htrace : WordTrace (prefixWord ++ tailWord_4026238) baseStart_4026238 baseEnd_4026238 := by
    simpa [prefixWord, tailWord_4026238, baseEnd_4026238] using wordTrace_append hprefix tailTrace_4026238
  have hstable : (prefixWord ++ tailWord_4026238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4026238).length < 2 ^ (prefixWord ++ tailWord_4026238).sum := by decide
  have hdescent : baseEnd_4026238 < baseStart_4026238 := by decide
  rcases family_descends (prefixWord ++ tailWord_4026238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4026240 : List Nat := [2, 1, 1, 2, 1, 2, 3, 1, 4, 2, 4]
def baseStart_4026240 : Nat := 118140960795 + 4026240 * 2 ^ 59
def prefixEnd_4026240 : Nat := 4983230072969 + 3 ^ 40 * 4026240 * 2
def baseEnd_4026240 : Nat := 2067396350358432551183665

theorem tailTrace_4026240 : CollatzResearch.WordTrace tailWord_4026240 prefixEnd_4026240 2067396350358432551183665 := by
  unfold tailWord_4026240
  simp only [CollatzResearch.WordTrace]
  refine ⟨73424518466813790946162087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97899357955751721261549449 73424518466813790946162087)
  ·
    refine ⟨110136777700220686419243131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73424518466813790946162087 110136777700220686419243131)
    ·
      refine ⟨165205166550331029628864697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110136777700220686419243131 165205166550331029628864697)
      ·
        refine ⟨123903874912748272221648523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165205166550331029628864697 123903874912748272221648523)
        ·
          refine ⟨185855812369122408332472785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123903874912748272221648523 185855812369122408332472785)
          ·
            refine ⟨139391859276841806249354589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185855812369122408332472785 139391859276841806249354589)
            ·
              refine ⟨52271947228815677343507971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139391859276841806249354589 52271947228815677343507971)
              ·
                refine ⟨78407920843223516015261957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52271947228815677343507971 78407920843223516015261957)
                ·
                  refine ⟨14701485158104409252861617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78407920843223516015261957 14701485158104409252861617)
                  ·
                    refine ⟨11026113868578306939646213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14701485158104409252861617 11026113868578306939646213)
                    ·
                      refine ⟨2067396350358432551183665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11026113868578306939646213 2067396350358432551183665)
                      ·
                        rfl

theorem cell23_4026240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 4, 2, 4].length) (baseStart_4026240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4026240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4026240 prefixEnd_4026240 := by exact prefixLift 4026240
  have htrace : WordTrace (prefixWord ++ tailWord_4026240) baseStart_4026240 baseEnd_4026240 := by
    simpa [prefixWord, tailWord_4026240, baseEnd_4026240] using wordTrace_append hprefix tailTrace_4026240
  have hstable : (prefixWord ++ tailWord_4026240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4026240).length < 2 ^ (prefixWord ++ tailWord_4026240).sum := by decide
  have hdescent : baseEnd_4026240 < baseStart_4026240 := by decide
  rcases family_descends (prefixWord ++ tailWord_4026240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4026290 : List Nat := [3, 2, 1, 1, 1, 1, 1, 2, 3, 1, 7]
def baseStart_4026290 : Nat := 118140960795 + 4026290 * 2 ^ 59
def prefixEnd_4026290 : Nat := 4983230072969 + 3 ^ 40 * 4026290 * 2
def baseEnd_4026290 : Nat := 2067422024391157355558435

theorem tailTrace_4026290 : CollatzResearch.WordTrace tailWord_4026290 prefixEnd_4026290 2067422024391157355558435 := by
  unfold tailWord_4026290
  simp only [CollatzResearch.WordTrace]
  refine ⟨36712715145861610107911081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97900573722297626954429549 36712715145861610107911081)
  ·
    refine ⟨27534536359396207580933311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36712715145861610107911081 27534536359396207580933311)
    ·
      refine ⟨41301804539094311371399967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27534536359396207580933311 41301804539094311371399967)
      ·
        refine ⟨61952706808641467057099951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41301804539094311371399967 61952706808641467057099951)
        ·
          refine ⟨92929060212962200585649927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61952706808641467057099951 92929060212962200585649927)
          ·
            refine ⟨139393590319443300878474891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92929060212962200585649927 139393590319443300878474891)
            ·
              refine ⟨209090385479164951317712337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139393590319443300878474891 209090385479164951317712337)
              ·
                refine ⟨156817789109373713488284253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 209090385479164951317712337 156817789109373713488284253)
                ·
                  refine ⟨58806670916015142558106595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 156817789109373713488284253 58806670916015142558106595)
                  ·
                    refine ⟨88210006374022713837159893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58806670916015142558106595 88210006374022713837159893)
                    ·
                      refine ⟨2067422024391157355558435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 88210006374022713837159893 2067422024391157355558435)
                      ·
                        rfl

theorem cell23_4026290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 3, 1, 7].length) (baseStart_4026290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4026290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4026290 prefixEnd_4026290 := by exact prefixLift 4026290
  have htrace : WordTrace (prefixWord ++ tailWord_4026290) baseStart_4026290 baseEnd_4026290 := by
    simpa [prefixWord, tailWord_4026290, baseEnd_4026290] using wordTrace_append hprefix tailTrace_4026290
  have hstable : (prefixWord ++ tailWord_4026290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4026290).length < 2 ^ (prefixWord ++ tailWord_4026290).sum := by decide
  have hdescent : baseEnd_4026290 < baseStart_4026290 := by decide
  rcases family_descends (prefixWord ++ tailWord_4026290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4026297 : List Nat := [1, 2, 1, 4, 2, 1, 3, 2, 2, 5]
def baseStart_4026297 : Nat := 118140960795 + 4026297 * 2 ^ 59
def prefixEnd_4026297 : Nat := 4983230072969 + 3 ^ 40 * 4026297 * 2
def baseEnd_4026297 : Nat := 689141872918579609390301

theorem tailTrace_4026297 : CollatzResearch.WordTrace tailWord_4026297 prefixEnd_4026297 689141872918579609390301 := by
  unfold tailWord_4026297
  simp only [CollatzResearch.WordTrace]
  refine ⟨146851115894421080627149145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97900743929614053751432763 146851115894421080627149145)
  ·
    refine ⟨110138336920815810470361859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146851115894421080627149145 110138336920815810470361859)
    ·
      refine ⟨165207505381223715705542789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110138336920815810470361859 165207505381223715705542789)
      ·
        refine ⟨30976407258979446694789273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 165207505381223715705542789 30976407258979446694789273)
        ·
          refine ⟨23232305444234585021091955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30976407258979446694789273 23232305444234585021091955)
          ·
            refine ⟨34848458166351877531637933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23232305444234585021091955 34848458166351877531637933)
            ·
              refine ⟨13068171812381954074364225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34848458166351877531637933 13068171812381954074364225)
              ·
                refine ⟨9801128859286465555773169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13068171812381954074364225 9801128859286465555773169)
                ·
                  refine ⟨7350846644464849166829877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9801128859286465555773169 7350846644464849166829877)
                  ·
                    refine ⟨689141872918579609390301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7350846644464849166829877 689141872918579609390301)
                    ·
                      rfl

theorem cell23_4026297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 2, 2, 5].length) (baseStart_4026297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4026297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4026297 prefixEnd_4026297 := by exact prefixLift 4026297
  have htrace : WordTrace (prefixWord ++ tailWord_4026297) baseStart_4026297 baseEnd_4026297 := by
    simpa [prefixWord, tailWord_4026297, baseEnd_4026297] using wordTrace_append hprefix tailTrace_4026297
  have hstable : (prefixWord ++ tailWord_4026297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4026297).length < 2 ^ (prefixWord ++ tailWord_4026297).sum := by decide
  have hdescent : baseEnd_4026297 < baseStart_4026297 := by decide
  rcases family_descends (prefixWord ++ tailWord_4026297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4026301 : List Nat := [1, 4, 1, 2, 3, 2, 3, 2, 5]
def baseStart_4026301 : Nat := 118140960795 + 4026301 * 2 ^ 59
def prefixEnd_4026301 : Nat := 4983230072969 + 3 ^ 40 * 4026301 * 2
def baseEnd_4026301 : Nat := 229714185853150756946765

theorem tailTrace_4026301 : CollatzResearch.WordTrace tailWord_4026301 prefixEnd_4026301 229714185853150756946765 := by
  unfold tailWord_4026301
  simp only [CollatzResearch.WordTrace]
  refine ⟨146851261786406589310294757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97900841190937726206863171 146851261786406589310294757)
  ·
    refine ⟨27534611584951235495680267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146851261786406589310294757 27534611584951235495680267)
    ·
      refine ⟨41301917377426853243520401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27534611584951235495680267 41301917377426853243520401)
      ·
        refine ⟨30976438033070139932640301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41301917377426853243520401 30976438033070139932640301)
        ·
          refine ⟨11616164262401302474740113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30976438033070139932640301 11616164262401302474740113)
          ·
            refine ⟨8712123196800976856055085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11616164262401302474740113 8712123196800976856055085)
            ·
              refine ⟨3267046198800366321020657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8712123196800976856055085 3267046198800366321020657)
              ·
                refine ⟨2450284649100274740765493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3267046198800366321020657 2450284649100274740765493)
                ·
                  refine ⟨229714185853150756946765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2450284649100274740765493 229714185853150756946765)
                  ·
                    rfl

theorem cell23_4026301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 3, 2, 5].length) (baseStart_4026301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4026301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4026301 prefixEnd_4026301 := by exact prefixLift 4026301
  have htrace : WordTrace (prefixWord ++ tailWord_4026301) baseStart_4026301 baseEnd_4026301 := by
    simpa [prefixWord, tailWord_4026301, baseEnd_4026301] using wordTrace_append hprefix tailTrace_4026301
  have hstable : (prefixWord ++ tailWord_4026301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4026301).length < 2 ^ (prefixWord ++ tailWord_4026301).sum := by decide
  have hdescent : baseEnd_4026301 < baseStart_4026301 := by decide
  rcases family_descends (prefixWord ++ tailWord_4026301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4026327 : List Nat := [1, 1, 3, 2, 1, 1, 4, 1, 5, 4]
def baseStart_4026327 : Nat := 118140960795 + 4026327 * 2 ^ 59
def prefixEnd_4026327 : Nat := 4983230072969 + 3 ^ 40 * 4026327 * 2
def baseEnd_4026327 : Nat := 689147007725124570265255

theorem tailTrace_4026327 : CollatzResearch.WordTrace tailWord_4026327 prefixEnd_4026327 689147007725124570265255 := by
  unfold tailWord_4026327
  simp only [CollatzResearch.WordTrace]
  refine ⟨146852210084312395750741235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97901473389541597167160823 146852210084312395750741235)
  ·
    refine ⟨220278315126468593626111853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146852210084312395750741235 220278315126468593626111853)
    ·
      refine ⟨82604368172425722609791945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220278315126468593626111853 82604368172425722609791945)
      ·
        refine ⟨61953276129319291957343959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82604368172425722609791945 61953276129319291957343959)
        ·
          refine ⟨92929914193978937936015939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61953276129319291957343959 92929914193978937936015939)
          ·
            refine ⟨139394871290968406904023909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92929914193978937936015939 139394871290968406904023909)
            ·
              refine ⟨26136538367056576294504483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 139394871290968406904023909 26136538367056576294504483)
              ·
                refine ⟨39204807550584864441756725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26136538367056576294504483 39204807550584864441756725)
                ·
                  refine ⟨3675450707867331041414693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39204807550584864441756725 3675450707867331041414693)
                  ·
                    refine ⟨689147007725124570265255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3675450707867331041414693 689147007725124570265255)
                    ·
                      rfl

theorem cell23_4026327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 1, 5, 4].length) (baseStart_4026327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4026327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4026327 prefixEnd_4026327 := by exact prefixLift 4026327
  have htrace : WordTrace (prefixWord ++ tailWord_4026327) baseStart_4026327 baseEnd_4026327 := by
    simpa [prefixWord, tailWord_4026327, baseEnd_4026327] using wordTrace_append hprefix tailTrace_4026327
  have hstable : (prefixWord ++ tailWord_4026327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4026327).length < 2 ^ (prefixWord ++ tailWord_4026327).sum := by decide
  have hdescent : baseEnd_4026327 < baseStart_4026327 := by decide
  rcases family_descends (prefixWord ++ tailWord_4026327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4026337 : List Nat := [1, 2, 3, 1, 2, 1, 2, 3, 1, 4, 3]
def baseStart_4026337 : Nat := 118140960795 + 4026337 * 2 ^ 59
def prefixEnd_4026337 : Nat := 4983230072969 + 3 ^ 40 * 4026337 * 2
def baseEnd_4026337 : Nat := 2067446157981918671670719

theorem tailTrace_4026337 : CollatzResearch.WordTrace tailWord_4026337 prefixEnd_4026337 2067446157981918671670719 := by
  unfold tailWord_4026337
  simp only [CollatzResearch.WordTrace]
  refine ⟨146852574814276167458605265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97901716542850778305736843 146852574814276167458605265)
  ·
    refine ⟨110139431110707125593953949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146852574814276167458605265 110139431110707125593953949)
    ·
      refine ⟨41302286666515172097732731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110139431110707125593953949 41302286666515172097732731)
      ·
        refine ⟨61953429999772758146599097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41302286666515172097732731 61953429999772758146599097)
        ·
          refine ⟨46465072499829568609949323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61953429999772758146599097 46465072499829568609949323)
          ·
            refine ⟨69697608749744352914923985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46465072499829568609949323 69697608749744352914923985)
            ·
              refine ⟨52273206562308264686192989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69697608749744352914923985 52273206562308264686192989)
              ·
                refine ⟨19602452460865599257322371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52273206562308264686192989 19602452460865599257322371)
                ·
                  refine ⟨29403678691298398885983557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19602452460865599257322371 29403678691298398885983557)
                  ·
                    refine ⟨5513189754618449791121917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29403678691298398885983557 5513189754618449791121917)
                    ·
                      refine ⟨2067446157981918671670719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5513189754618449791121917 2067446157981918671670719)
                      ·
                        rfl

theorem cell23_4026337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 3, 1, 4, 3].length) (baseStart_4026337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4026337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4026337 prefixEnd_4026337 := by exact prefixLift 4026337
  have htrace : WordTrace (prefixWord ++ tailWord_4026337) baseStart_4026337 baseEnd_4026337 := by
    simpa [prefixWord, tailWord_4026337, baseEnd_4026337] using wordTrace_append hprefix tailTrace_4026337
  have hstable : (prefixWord ++ tailWord_4026337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4026337).length < 2 ^ (prefixWord ++ tailWord_4026337).sum := by decide
  have hdescent : baseEnd_4026337 < baseStart_4026337 := by decide
  rcases family_descends (prefixWord ++ tailWord_4026337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4026361 : List Nat := [1, 2, 1, 3, 1, 5, 1, 4, 1, 4]
def baseStart_4026361 : Nat := 118140960795 + 4026361 * 2 ^ 59
def prefixEnd_4026361 : Nat := 4983230072969 + 3 ^ 40 * 4026361 * 2
def baseEnd_4026361 : Nat := 689152827172542192590203

theorem tailTrace_4026361 : CollatzResearch.WordTrace tailWord_4026361 prefixEnd_4026361 689152827172542192590203 := by
  unfold tailWord_4026361
  simp only [CollatzResearch.WordTrace]
  refine ⟨146853450166189219557478937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97902300110792813038319291 146853450166189219557478937)
  ·
    refine ⟨110140087624641914668109203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146853450166189219557478937 110140087624641914668109203)
    ·
      refine ⟨165210131436962872002163805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110140087624641914668109203 165210131436962872002163805)
      ·
        refine ⟨61953799288861077000811427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165210131436962872002163805 61953799288861077000811427)
        ·
          refine ⟨92930698933291615501217141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61953799288861077000811427 92930698933291615501217141)
          ·
            refine ⟨8712253024996088953239107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 92930698933291615501217141 8712253024996088953239107)
            ·
              refine ⟨13068379537494133429858661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8712253024996088953239107 13068379537494133429858661)
              ·
                refine ⟨2450321163280150018098499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13068379537494133429858661 2450321163280150018098499)
                ·
                  refine ⟨3675481744920225027147749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2450321163280150018098499 3675481744920225027147749)
                  ·
                    refine ⟨689152827172542192590203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3675481744920225027147749 689152827172542192590203)
                    ·
                      rfl

theorem cell23_4026361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 4, 1, 4].length) (baseStart_4026361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4026361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4026361 prefixEnd_4026361 := by exact prefixLift 4026361
  have htrace : WordTrace (prefixWord ++ tailWord_4026361) baseStart_4026361 baseEnd_4026361 := by
    simpa [prefixWord, tailWord_4026361, baseEnd_4026361] using wordTrace_append hprefix tailTrace_4026361
  have hstable : (prefixWord ++ tailWord_4026361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4026361).length < 2 ^ (prefixWord ++ tailWord_4026361).sum := by decide
  have hdescent : baseEnd_4026361 < baseStart_4026361 := by decide
  rcases family_descends (prefixWord ++ tailWord_4026361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4026384 : List Nat := [2, 1, 1, 1, 1, 1, 1, 8, 3, 1, 3]
def baseStart_4026384 : Nat := 118140960795 + 4026384 * 2 ^ 59
def prefixEnd_4026384 : Nat := 4983230072969 + 3 ^ 40 * 4026384 * 2
def baseEnd_4026384 : Nat := 2067470291572679987783003

theorem tailTrace_4026384 : CollatzResearch.WordTrace tailWord_4026384 prefixEnd_4026384 2067470291572679987783003 := by
  unfold tailWord_4026384
  simp only [CollatzResearch.WordTrace]
  refine ⟨73427144522552947242783103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97902859363403929657044137 73427144522552947242783103)
  ·
    refine ⟨110140716783829420864174655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73427144522552947242783103 110140716783829420864174655)
    ·
      refine ⟨165211075175744131296261983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110140716783829420864174655 165211075175744131296261983)
      ·
        refine ⟨247816612763616196944392975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165211075175744131296261983 247816612763616196944392975)
        ·
          refine ⟨371724919145424295416589463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247816612763616196944392975 371724919145424295416589463)
          ·
            refine ⟨557587378718136443124884195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 371724919145424295416589463 557587378718136443124884195)
            ·
              refine ⟨836381068077204664687326293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 557587378718136443124884195 836381068077204664687326293)
              ·
                refine ⟨9801340641529742164304605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 836381068077204664687326293 9801340641529742164304605)
                ·
                  refine ⟨3675502740573653311614227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9801340641529742164304605 3675502740573653311614227)
                  ·
                    refine ⟨5513254110860479967421341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3675502740573653311614227 5513254110860479967421341)
                    ·
                      refine ⟨2067470291572679987783003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5513254110860479967421341 2067470291572679987783003)
                      ·
                        rfl

theorem cell23_4026384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 8, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 8, 3, 1, 3].length) (baseStart_4026384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4026384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4026384 prefixEnd_4026384 := by exact prefixLift 4026384
  have htrace : WordTrace (prefixWord ++ tailWord_4026384) baseStart_4026384 baseEnd_4026384 := by
    simpa [prefixWord, tailWord_4026384, baseEnd_4026384] using wordTrace_append hprefix tailTrace_4026384
  have hstable : (prefixWord ++ tailWord_4026384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4026384).length < 2 ^ (prefixWord ++ tailWord_4026384).sum := by decide
  have hdescent : baseEnd_4026384 < baseStart_4026384 := by decide
  rcases family_descends (prefixWord ++ tailWord_4026384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4026387 : List Nat := [1, 1, 1, 2, 1, 4, 4, 1, 3, 5]
def baseStart_4026387 : Nat := 118140960795 + 4026387 * 2 ^ 59
def prefixEnd_4026387 : Nat := 4983230072969 + 3 ^ 40 * 4026387 * 2
def baseEnd_4026387 : Nat := 689157277338214492015163

theorem tailTrace_4026387 : CollatzResearch.WordTrace tailWord_4026387 prefixEnd_4026387 689157277338214492015163 := by
  unfold tailWord_4026387
  simp only [CollatzResearch.WordTrace]
  refine ⟨146854398464095025997925415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97902932309396683998616943 146854398464095025997925415)
  ·
    refine ⟨220281597696142538996888123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146854398464095025997925415 220281597696142538996888123)
    ·
      refine ⟨330422396544213808495332185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220281597696142538996888123 330422396544213808495332185)
      ·
        refine ⟨247816797408160356371499139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 330422396544213808495332185 247816797408160356371499139)
        ·
          refine ⟨371725196112240534557248709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247816797408160356371499139 371725196112240534557248709)
          ·
            refine ⟨69698474271045100229484133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 371725196112240534557248709 69698474271045100229484133)
            ·
              refine ⟨13068463925820956293028275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69698474271045100229484133 13068463925820956293028275)
              ·
                refine ⟨19602695888731434439542413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13068463925820956293028275 19602695888731434439542413)
                ·
                  refine ⟨7351010958274287914828405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19602695888731434439542413 7351010958274287914828405)
                  ·
                    refine ⟨689157277338214492015163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7351010958274287914828405 689157277338214492015163)
                    ·
                      rfl

theorem cell23_4026387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 1, 3, 5].length) (baseStart_4026387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4026387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4026387 prefixEnd_4026387 := by exact prefixLift 4026387
  have htrace : WordTrace (prefixWord ++ tailWord_4026387) baseStart_4026387 baseEnd_4026387 := by
    simpa [prefixWord, tailWord_4026387, baseEnd_4026387] using wordTrace_append hprefix tailTrace_4026387
  have hstable : (prefixWord ++ tailWord_4026387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4026387).length < 2 ^ (prefixWord ++ tailWord_4026387).sum := by decide
  have hdescent : baseEnd_4026387 < baseStart_4026387 := by decide
  rcases family_descends (prefixWord ++ tailWord_4026387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4026388 : List Nat := [2, 4, 3, 2, 1, 1, 1, 1, 1, 4, 3]
def baseStart_4026388 : Nat := 118140960795 + 4026388 * 2 ^ 59
def prefixEnd_4026388 : Nat := 4983230072969 + 3 ^ 40 * 4026388 * 2
def baseEnd_4026388 : Nat := 2067472345495297972132985

theorem tailTrace_4026388 : CollatzResearch.WordTrace tailWord_4026388 prefixEnd_4026388 2067472345495297972132985 := by
  unfold tailWord_4026388
  simp only [CollatzResearch.WordTrace]
  refine ⟨73427217468545701584355909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97902956624727602112474545 73427217468545701584355909)
  ·
    refine ⟨13767603275352319047066733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73427217468545701584355909 13767603275352319047066733)
    ·
      refine ⟨5162851228257119642650025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13767603275352319047066733 5162851228257119642650025)
      ·
        refine ⟨3872138421192839731987519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5162851228257119642650025 3872138421192839731987519)
        ·
          refine ⟨5808207631789259597981279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3872138421192839731987519 5808207631789259597981279)
          ·
            refine ⟨8712311447683889396971919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5808207631789259597981279 8712311447683889396971919)
            ·
              refine ⟨13068467171525834095457879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8712311447683889396971919 13068467171525834095457879)
              ·
                refine ⟨19602700757288751143186819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13068467171525834095457879 19602700757288751143186819)
                ·
                  refine ⟨29404051135933126714780229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19602700757288751143186819 29404051135933126714780229)
                  ·
                    refine ⟨5513259587987461259021293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29404051135933126714780229 5513259587987461259021293)
                    ·
                      refine ⟨2067472345495297972132985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5513259587987461259021293 2067472345495297972132985)
                      ·
                        rfl

theorem cell23_4026388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_4026388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4026388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4026388 prefixEnd_4026388 := by exact prefixLift 4026388
  have htrace : WordTrace (prefixWord ++ tailWord_4026388) baseStart_4026388 baseEnd_4026388 := by
    simpa [prefixWord, tailWord_4026388, baseEnd_4026388] using wordTrace_append hprefix tailTrace_4026388
  have hstable : (prefixWord ++ tailWord_4026388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4026388).length < 2 ^ (prefixWord ++ tailWord_4026388).sum := by decide
  have hdescent : baseEnd_4026388 < baseStart_4026388 := by decide
  rcases family_descends (prefixWord ++ tailWord_4026388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4026408 : List Nat := [2, 1, 5, 3, 1, 2, 1, 2, 6]
def baseStart_4026408 : Nat := 118140960795 + 4026408 * 2 ^ 59
def prefixEnd_4026408 : Nat := 4983230072969 + 3 ^ 40 * 4026408 * 2
def baseEnd_4026408 : Nat := 229720290567598654875877

theorem tailTrace_4026408 : CollatzResearch.WordTrace tailWord_4026408 prefixEnd_4026408 229720290567598654875877 := by
  unfold tailWord_4026408
  simp only [CollatzResearch.WordTrace]
  refine ⟨73427582198509473292219939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97903442931345964389626585 73427582198509473292219939)
  ·
    refine ⟨110141373297764209938329909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73427582198509473292219939 110141373297764209938329909)
    ·
      refine ⟨10325753746665394681718429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 110141373297764209938329909 10325753746665394681718429)
      ·
        refine ⟨3872157654999523005644411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10325753746665394681718429 3872157654999523005644411)
        ·
          refine ⟨5808236482499284508466617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3872157654999523005644411 5808236482499284508466617)
          ·
            refine ⟨4356177361874463381349963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5808236482499284508466617 4356177361874463381349963)
            ·
              refine ⟨6534266042811695072024945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4356177361874463381349963 6534266042811695072024945)
              ·
                refine ⟨4900699532108771304018709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6534266042811695072024945 4900699532108771304018709)
                ·
                  refine ⟨229720290567598654875877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4900699532108771304018709 229720290567598654875877)
                  ·
                    rfl

theorem cell23_4026408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 1, 2, 6].length) (baseStart_4026408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4026408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4026408 prefixEnd_4026408 := by exact prefixLift 4026408
  have htrace : WordTrace (prefixWord ++ tailWord_4026408) baseStart_4026408 baseEnd_4026408 := by
    simpa [prefixWord, tailWord_4026408, baseEnd_4026408] using wordTrace_append hprefix tailTrace_4026408
  have hstable : (prefixWord ++ tailWord_4026408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4026408).length < 2 ^ (prefixWord ++ tailWord_4026408).sum := by decide
  have hdescent : baseEnd_4026408 < baseStart_4026408 := by decide
  rcases family_descends (prefixWord ++ tailWord_4026408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4026418 : List Nat := [3, 2, 1, 1, 2, 3, 2, 4, 1, 1, 3]
def baseStart_4026418 : Nat := 118140960795 + 4026418 * 2 ^ 59
def prefixEnd_4026418 : Nat := 4983230072969 + 3 ^ 40 * 4026418 * 2
def baseEnd_4026418 : Nat := 2067487749914932854757847

theorem tailTrace_4026418 : CollatzResearch.WordTrace tailWord_4026418 prefixEnd_4026418 2067487749914932854757847 := by
  unfold tailWord_4026418
  simp only [CollatzResearch.WordTrace]
  refine ⟨36713882281745679573075977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97903686084655145528202605 36713882281745679573075977)
  ·
    refine ⟨27535411711309259679806983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36713882281745679573075977 27535411711309259679806983)
    ·
      refine ⟨41303117566963889519710475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27535411711309259679806983 41303117566963889519710475)
      ·
        refine ⟨61954676350445834279565713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41303117566963889519710475 61954676350445834279565713)
        ·
          refine ⟨46466007262834375709674285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61954676350445834279565713 46466007262834375709674285)
          ·
            refine ⟨17424752723562890891127857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46466007262834375709674285 17424752723562890891127857)
            ·
              refine ⟨13068564542672168168345893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17424752723562890891127857 13068564542672168168345893)
              ·
                refine ⟨2450355851751031531564855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13068564542672168168345893 2450355851751031531564855)
                ·
                  refine ⟨3675533777626547297347283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2450355851751031531564855 3675533777626547297347283)
                  ·
                    refine ⟨5513300666439820946020925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3675533777626547297347283 5513300666439820946020925)
                    ·
                      refine ⟨2067487749914932854757847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5513300666439820946020925 2067487749914932854757847)
                      ·
                        rfl

theorem cell23_4026418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 4, 1, 1, 3].length) (baseStart_4026418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4026418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4026418 prefixEnd_4026418 := by exact prefixLift 4026418
  have htrace : WordTrace (prefixWord ++ tailWord_4026418) baseStart_4026418 baseEnd_4026418 := by
    simpa [prefixWord, tailWord_4026418, baseEnd_4026418] using wordTrace_append hprefix tailTrace_4026418
  have hstable : (prefixWord ++ tailWord_4026418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4026418).length < 2 ^ (prefixWord ++ tailWord_4026418).sum := by decide
  have hdescent : baseEnd_4026418 < baseStart_4026418 := by decide
  rcases family_descends (prefixWord ++ tailWord_4026418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4026427 : List Nat := [1, 1, 1, 1, 1, 2, 1, 8, 1, 1, 5]
def baseStart_4026427 : Nat := 118140960795 + 4026427 * 2 ^ 59
def prefixEnd_4026427 : Nat := 4983230072969 + 3 ^ 40 * 4026427 * 2
def baseEnd_4026427 : Nat := 2067492371240823319545305

theorem tailTrace_4026427 : CollatzResearch.WordTrace tailWord_4026427 prefixEnd_4026427 2067492371240823319545305 := by
  unfold tailWord_4026427
  simp only [CollatzResearch.WordTrace]
  refine ⟨146855857383950112829381535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97903904922633408552921023 146855857383950112829381535)
  ·
    refine ⟨220283786075925169244072303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146855857383950112829381535 220283786075925169244072303)
    ·
      refine ⟨330425679113887753866108455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220283786075925169244072303 330425679113887753866108455)
      ·
        refine ⟨495638518670831630799162683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330425679113887753866108455 495638518670831630799162683)
        ·
          refine ⟨743457778006247446198744025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 495638518670831630799162683 743457778006247446198744025)
          ·
            refine ⟨557593333504685584649058019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 743457778006247446198744025 557593333504685584649058019)
            ·
              refine ⟨836390000257028376973587029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 557593333504685584649058019 836390000257028376973587029)
              ·
                refine ⟨9801445315512051292659223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 836390000257028376973587029 9801445315512051292659223)
                ·
                  refine ⟨14702167973268076938988835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9801445315512051292659223 14702167973268076938988835)
                  ·
                    refine ⟨22053251959902115408483253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14702167973268076938988835 22053251959902115408483253)
                    ·
                      refine ⟨2067492371240823319545305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22053251959902115408483253 2067492371240823319545305)
                      ·
                        rfl

theorem cell23_4026427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 8, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 8, 1, 1, 5].length) (baseStart_4026427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4026427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4026427 prefixEnd_4026427 := by exact prefixLift 4026427
  have htrace : WordTrace (prefixWord ++ tailWord_4026427) baseStart_4026427 baseEnd_4026427 := by
    simpa [prefixWord, tailWord_4026427, baseEnd_4026427] using wordTrace_append hprefix tailTrace_4026427
  have hstable : (prefixWord ++ tailWord_4026427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4026427).length < 2 ^ (prefixWord ++ tailWord_4026427).sum := by decide
  have hdescent : baseEnd_4026427 < baseStart_4026427 := by decide
  rcases family_descends (prefixWord ++ tailWord_4026427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4026438 : List Nat := [6, 1, 1, 1, 1, 1, 4, 2, 1, 5]
def baseStart_4026438 : Nat := 118140960795 + 4026438 * 2 ^ 59
def prefixEnd_4026438 : Nat := 4983230072969 + 3 ^ 40 * 4026438 * 2
def baseEnd_4026438 : Nat := 689166006509340925502585

theorem tailTrace_4026438 : CollatzResearch.WordTrace tailWord_4026438 prefixEnd_4026438 689166006509340925502585 := by
  unfold tailWord_4026438
  simp only [CollatzResearch.WordTrace]
  refine ⟨4589258080840945678375999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 97904172391273507805354645 4589258080840945678375999)
  ·
    refine ⟨6883887121261418517563999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4589258080840945678375999 6883887121261418517563999)
    ·
      refine ⟨10325830681892127776345999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6883887121261418517563999 10325830681892127776345999)
      ·
        refine ⟨15488746022838191664518999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10325830681892127776345999 15488746022838191664518999)
        ·
          refine ⟨23233119034257287496778499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15488746022838191664518999 23233119034257287496778499)
          ·
            refine ⟨34849678551385931245167749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23233119034257287496778499 34849678551385931245167749)
            ·
              refine ⟨6534314728384862108468953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34849678551385931245167749 6534314728384862108468953)
              ·
                refine ⟨4900736046288646581351715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6534314728384862108468953 4900736046288646581351715)
                ·
                  refine ⟨7351104069432969872027573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4900736046288646581351715 7351104069432969872027573)
                  ·
                    refine ⟨689166006509340925502585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7351104069432969872027573 689166006509340925502585)
                    ·
                      rfl

theorem cell23_4026438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 4, 2, 1, 5].length) (baseStart_4026438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4026438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4026438 prefixEnd_4026438 := by exact prefixLift 4026438
  have htrace : WordTrace (prefixWord ++ tailWord_4026438) baseStart_4026438 baseEnd_4026438 := by
    simpa [prefixWord, tailWord_4026438, baseEnd_4026438] using wordTrace_append hprefix tailTrace_4026438
  have hstable : (prefixWord ++ tailWord_4026438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4026438).length < 2 ^ (prefixWord ++ tailWord_4026438).sum := by decide
  have hdescent : baseEnd_4026438 < baseStart_4026438 := by decide
  rcases family_descends (prefixWord ++ tailWord_4026438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4026441 : List Nat := [1, 2, 1, 1, 2, 2, 3, 4, 3, 2, 2]
def baseStart_4026441 : Nat := 118140960795 + 4026441 * 2 ^ 59
def prefixEnd_4026441 : Nat := 4983230072969 + 3 ^ 40 * 4026441 * 2
def baseEnd_4026441 : Nat := 2067499559969986264770241

theorem tailTrace_4026441 : CollatzResearch.WordTrace tailWord_4026441 prefixEnd_4026441 2067499559969986264770241 := by
  unfold tailWord_4026441
  simp only [CollatzResearch.WordTrace]
  refine ⟨146856368005899393220391177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97904245337266262146927451 146856368005899393220391177)
  ·
    refine ⟨110142276004424544915293383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146856368005899393220391177 110142276004424544915293383)
    ·
      refine ⟨165213414006636817372940075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110142276004424544915293383 165213414006636817372940075)
      ·
        refine ⟨247820121009955226059410113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165213414006636817372940075 247820121009955226059410113)
        ·
          refine ⟨185865090757466419544557585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 247820121009955226059410113 185865090757466419544557585)
          ·
            refine ⟨139398818068099814658418189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185865090757466419544557585 139398818068099814658418189)
            ·
              refine ⟨52274556775537430496906821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139398818068099814658418189 52274556775537430496906821)
              ·
                refine ⟨9801479395413268218170029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52274556775537430496906821 9801479395413268218170029)
                ·
                  refine ⟨3675554773279975581813761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9801479395413268218170029 3675554773279975581813761)
                  ·
                    refine ⟨2756666079959981686360321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3675554773279975581813761 2756666079959981686360321)
                    ·
                      refine ⟨2067499559969986264770241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2756666079959981686360321 2067499559969986264770241)
                      ·
                        rfl

theorem cell23_4026441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 4, 3, 2, 2].length) (baseStart_4026441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4026441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4026441 prefixEnd_4026441 := by exact prefixLift 4026441
  have htrace : WordTrace (prefixWord ++ tailWord_4026441) baseStart_4026441 baseEnd_4026441 := by
    simpa [prefixWord, tailWord_4026441, baseEnd_4026441] using wordTrace_append hprefix tailTrace_4026441
  have hstable : (prefixWord ++ tailWord_4026441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4026441).length < 2 ^ (prefixWord ++ tailWord_4026441).sum := by decide
  have hdescent : baseEnd_4026441 < baseStart_4026441 := by decide
  rcases family_descends (prefixWord ++ tailWord_4026441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4026444 : List Nat := [2, 2, 1, 3, 1, 1, 2, 3, 3, 2, 3]
def baseStart_4026444 : Nat := 118140960795 + 4026444 * 2 ^ 59
def prefixEnd_4026444 : Nat := 4983230072969 + 3 ^ 40 * 4026444 * 2
def baseEnd_4026444 : Nat := 2067501100411949753032727

theorem tailTrace_4026444 : CollatzResearch.WordTrace tailWord_4026444 prefixEnd_4026444 2067501100411949753032727 := by
  unfold tailWord_4026444
  simp only [CollatzResearch.WordTrace]
  refine ⟨73428238712444262366375193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97904318283259016488500257 73428238712444262366375193)
  ·
    refine ⟨55071179034333196774781395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73428238712444262366375193 55071179034333196774781395)
    ·
      refine ⟨82606768551499795162172093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55071179034333196774781395 82606768551499795162172093)
      ·
        refine ⟨30977538206812423185814535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82606768551499795162172093 30977538206812423185814535)
        ·
          refine ⟨46466307310218634778721803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30977538206812423185814535 46466307310218634778721803)
          ·
            refine ⟨69699460965327952168082705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46466307310218634778721803 69699460965327952168082705)
            ·
              refine ⟨52274595723995964126062029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69699460965327952168082705 52274595723995964126062029)
              ·
                refine ⟨19602973396498486547273261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52274595723995964126062029 19602973396498486547273261)
                ·
                  refine ⟨7351115023686932455227473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19602973396498486547273261 7351115023686932455227473)
                  ·
                    refine ⟨5513336267765199341420605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7351115023686932455227473 5513336267765199341420605)
                    ·
                      refine ⟨2067501100411949753032727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5513336267765199341420605 2067501100411949753032727)
                      ·
                        rfl

theorem cell23_4026444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 3, 3, 2, 3].length) (baseStart_4026444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4026444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4026444 prefixEnd_4026444 := by exact prefixLift 4026444
  have htrace : WordTrace (prefixWord ++ tailWord_4026444) baseStart_4026444 baseEnd_4026444 := by
    simpa [prefixWord, tailWord_4026444, baseEnd_4026444] using wordTrace_append hprefix tailTrace_4026444
  have hstable : (prefixWord ++ tailWord_4026444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4026444).length < 2 ^ (prefixWord ++ tailWord_4026444).sum := by decide
  have hdescent : baseEnd_4026444 < baseStart_4026444 := by decide
  rcases family_descends (prefixWord ++ tailWord_4026444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4026461 : List Nat := [1, 4, 4, 1, 1, 1, 1, 3, 1, 1, 5]
def baseStart_4026461 : Nat := 118140960795 + 4026461 * 2 ^ 59
def prefixEnd_4026461 : Nat := 4983230072969 + 3 ^ 40 * 4026461 * 2
def baseEnd_4026461 : Nat := 2067509829583076186520149

theorem tailTrace_4026461 : CollatzResearch.WordTrace tailWord_4026461 prefixEnd_4026461 2067509829583076186520149 := by
  unfold tailWord_4026461
  simp only [CollatzResearch.WordTrace]
  refine ⟨146857097465826936636119237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97904731643884624424079491 146857097465826936636119237)
  ·
    refine ⟨27535705774842550619272357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146857097465826936636119237 27535705774842550619272357)
    ·
      refine ⟨5162944832782978241113567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27535705774842550619272357 5162944832782978241113567)
      ·
        refine ⟨7744417249174467361670351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5162944832782978241113567 7744417249174467361670351)
        ·
          refine ⟨11616625873761701042505527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7744417249174467361670351 11616625873761701042505527)
          ·
            refine ⟨17424938810642551563758291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11616625873761701042505527 17424938810642551563758291)
            ·
              refine ⟨26137408215963827345637437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17424938810642551563758291 26137408215963827345637437)
              ·
                refine ⟨9801528080986435254614039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26137408215963827345637437 9801528080986435254614039)
                ·
                  refine ⟨14702292121479652881921059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9801528080986435254614039 14702292121479652881921059)
                  ·
                    refine ⟨22053438182219479322881589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14702292121479652881921059 22053438182219479322881589)
                    ·
                      refine ⟨2067509829583076186520149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22053438182219479322881589 2067509829583076186520149)
                      ·
                        rfl

theorem cell23_4026461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_4026461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4026461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4026461 prefixEnd_4026461 := by exact prefixLift 4026461
  have htrace : WordTrace (prefixWord ++ tailWord_4026461) baseStart_4026461 baseEnd_4026461 := by
    simpa [prefixWord, tailWord_4026461, baseEnd_4026461] using wordTrace_append hprefix tailTrace_4026461
  have hstable : (prefixWord ++ tailWord_4026461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4026461).length < 2 ^ (prefixWord ++ tailWord_4026461).sum := by decide
  have hdescent : baseEnd_4026461 < baseStart_4026461 := by decide
  rcases family_descends (prefixWord ++ tailWord_4026461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4026462 : List Nat := [4, 4, 1, 1, 2, 1, 1, 2, 2, 3, 2]
def baseStart_4026462 : Nat := 118140960795 + 4026462 * 2 ^ 59
def prefixEnd_4026462 : Nat := 4983230072969 + 3 ^ 40 * 4026462 * 2
def baseEnd_4026462 : Nat := 2067510343063730682607645

theorem tailTrace_4026462 : CollatzResearch.WordTrace tailWord_4026462 prefixEnd_4026462 2067510343063730682607645 := by
  unfold tailWord_4026462
  simp only [CollatzResearch.WordTrace]
  refine ⟨18357141742352914225863205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97904755959215542537937093 18357141742352914225863205)
  ·
    refine ⟨3441964076691171417349351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18357141742352914225863205 3441964076691171417349351)
    ·
      refine ⟨5162946115036757126024027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3441964076691171417349351 5162946115036757126024027)
      ·
        refine ⟨7744419172555135689036041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5162946115036757126024027 7744419172555135689036041)
        ·
          refine ⟨5808314379416351766777031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7744419172555135689036041 5808314379416351766777031)
          ·
            refine ⟨8712471569124527650165547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5808314379416351766777031 8712471569124527650165547)
            ·
              refine ⟨13068707353686791475248321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8712471569124527650165547 13068707353686791475248321)
              ·
                refine ⟨9801530515265093606436241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13068707353686791475248321 9801530515265093606436241)
                ·
                  refine ⟨7351147886448820204827181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9801530515265093606436241 7351147886448820204827181)
                  ·
                    refine ⟨2756680457418307576810193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7351147886448820204827181 2756680457418307576810193)
                    ·
                      refine ⟨2067510343063730682607645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2756680457418307576810193 2067510343063730682607645)
                      ·
                        rfl

theorem cell23_4026462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 2, 2, 3, 2].length) (baseStart_4026462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4026462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4026462 prefixEnd_4026462 := by exact prefixLift 4026462
  have htrace : WordTrace (prefixWord ++ tailWord_4026462) baseStart_4026462 baseEnd_4026462 := by
    simpa [prefixWord, tailWord_4026462, baseEnd_4026462] using wordTrace_append hprefix tailTrace_4026462
  have hstable : (prefixWord ++ tailWord_4026462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4026462).length < 2 ^ (prefixWord ++ tailWord_4026462).sum := by decide
  have hdescent : baseEnd_4026462 < baseStart_4026462 := by decide
  rcases family_descends (prefixWord ++ tailWord_4026462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4026507 : List Nat := [1, 1, 1, 1, 4, 1, 1, 1, 6, 6]
def baseStart_4026507 : Nat := 118140960795 + 4026507 * 2 ^ 59
def prefixEnd_4026507 : Nat := 4983230072969 + 3 ^ 40 * 4026507 * 2
def baseEnd_4026507 : Nat := 689177816564394335514979

theorem tailTrace_4026507 : CollatzResearch.WordTrace tailWord_4026507 prefixEnd_4026507 689177816564394335514979 := by
  unfold tailWord_4026507
  simp only [CollatzResearch.WordTrace]
  refine ⟨146858775223660286492293775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97905850149106857661529183 146858775223660286492293775)
  ·
    refine ⟨220288162835490429738440663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146858775223660286492293775 220288162835490429738440663)
    ·
      refine ⟨330432244253235644607660995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220288162835490429738440663 330432244253235644607660995)
      ·
        refine ⟨495648366379853466911491493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330432244253235644607660995 495648366379853466911491493)
        ·
          refine ⟨92934068696222525045904655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 495648366379853466911491493 92934068696222525045904655)
          ·
            refine ⟨139401103044333787568856983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92934068696222525045904655 139401103044333787568856983)
            ·
              refine ⟨209101654566500681353285475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139401103044333787568856983 209101654566500681353285475)
              ·
                refine ⟨313652481849751022029928213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 209101654566500681353285475 313652481849751022029928213)
                ·
                  refine ⟨14702460086707079157652885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 313652481849751022029928213 14702460086707079157652885)
                  ·
                    refine ⟨689177816564394335514979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14702460086707079157652885 689177816564394335514979)
                    ·
                      rfl

theorem cell23_4026507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 6, 6].length) (baseStart_4026507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4026507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4026507 prefixEnd_4026507 := by exact prefixLift 4026507
  have htrace : WordTrace (prefixWord ++ tailWord_4026507) baseStart_4026507 baseEnd_4026507 := by
    simpa [prefixWord, tailWord_4026507, baseEnd_4026507] using wordTrace_append hprefix tailTrace_4026507
  have hstable : (prefixWord ++ tailWord_4026507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4026507).length < 2 ^ (prefixWord ++ tailWord_4026507).sum := by decide
  have hdescent : baseEnd_4026507 < baseStart_4026507 := by decide
  rcases family_descends (prefixWord ++ tailWord_4026507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4026524 : List Nat := [2, 2, 3, 2, 1, 1, 2, 2, 2, 6]
def baseStart_4026524 : Nat := 118140960795 + 4026524 * 2 ^ 59
def prefixEnd_4026524 : Nat := 4983230072969 + 3 ^ 40 * 4026524 * 2
def baseEnd_4026524 : Nat := 689180726288103146677453

theorem tailTrace_4026524 : CollatzResearch.WordTrace tailWord_4026524 prefixEnd_4026524 689180726288103146677453 := by
  unfold tailWord_4026524
  simp only [CollatzResearch.WordTrace]
  refine ⟨73429697632299349197831313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97906263509732465597108417 73429697632299349197831313)
  ·
    refine ⟨55072273224224511898373485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73429697632299349197831313 55072273224224511898373485)
    ·
      refine ⟨20652102459084191961890057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55072273224224511898373485 20652102459084191961890057)
      ·
        refine ⟨15489076844313143971417543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20652102459084191961890057 15489076844313143971417543)
        ·
          refine ⟨23233615266469715957126315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15489076844313143971417543 23233615266469715957126315)
          ·
            refine ⟨34850422899704573935689473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23233615266469715957126315 34850422899704573935689473)
            ·
              refine ⟨26137817174778430451767105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34850422899704573935689473 26137817174778430451767105)
              ·
                refine ⟨19603362881083822838825329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26137817174778430451767105 19603362881083822838825329)
                ·
                  refine ⟨14702522160812867129118997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19603362881083822838825329 14702522160812867129118997)
                  ·
                    refine ⟨689180726288103146677453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14702522160812867129118997 689180726288103146677453)
                    ·
                      rfl

theorem cell23_4026524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 2, 2, 6].length) (baseStart_4026524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4026524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4026524 prefixEnd_4026524 := by exact prefixLift 4026524
  have htrace : WordTrace (prefixWord ++ tailWord_4026524) baseStart_4026524 baseEnd_4026524 := by
    simpa [prefixWord, tailWord_4026524, baseEnd_4026524] using wordTrace_append hprefix tailTrace_4026524
  have hstable : (prefixWord ++ tailWord_4026524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4026524).length < 2 ^ (prefixWord ++ tailWord_4026524).sum := by decide
  have hdescent : baseEnd_4026524 < baseStart_4026524 := by decide
  rcases family_descends (prefixWord ++ tailWord_4026524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4026526 : List Nat := [4, 3, 1, 1, 3, 2, 2, 2, 1, 2, 2]
def baseStart_4026526 : Nat := 118140960795 + 4026526 * 2 ^ 59
def prefixEnd_4026526 : Nat := 4983230072969 + 3 ^ 40 * 4026526 * 2
def baseEnd_4026526 : Nat := 2067543205825618432207351

theorem tailTrace_4026526 : CollatzResearch.WordTrace tailWord_4026526 prefixEnd_4026526 2067543205825618432207351 := by
  unfold tailWord_4026526
  simp only [CollatzResearch.WordTrace]
  refine ⟨18357433526323931592154429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97906312140394301824823621 18357433526323931592154429)
  ·
    refine ⟨6884037572371474347057911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18357433526323931592154429 6884037572371474347057911)
    ·
      refine ⟨10326056358557211520586867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6884037572371474347057911 10326056358557211520586867)
      ·
        refine ⟨15489084537835817280880301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10326056358557211520586867 15489084537835817280880301)
        ·
          refine ⟨5808406701688431480330113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15489084537835817280880301 5808406701688431480330113)
          ·
            refine ⟨4356305026266323610247585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5808406701688431480330113 4356305026266323610247585)
            ·
              refine ⟨3267228769699742707685689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4356305026266323610247585 3267228769699742707685689)
              ·
                refine ⟨2450421577274807030764267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3267228769699742707685689 2450421577274807030764267)
                ·
                  refine ⟨3675632365912210546146401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2450421577274807030764267 3675632365912210546146401)
                  ·
                    refine ⟨2756724274434157909609801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3675632365912210546146401 2756724274434157909609801)
                    ·
                      refine ⟨2067543205825618432207351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2756724274434157909609801 2067543205825618432207351)
                      ·
                        rfl

theorem cell23_4026526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 2, 2, 1, 2, 2].length) (baseStart_4026526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4026526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4026526 prefixEnd_4026526 := by exact prefixLift 4026526
  have htrace : WordTrace (prefixWord ++ tailWord_4026526) baseStart_4026526 baseEnd_4026526 := by
    simpa [prefixWord, tailWord_4026526, baseEnd_4026526] using wordTrace_append hprefix tailTrace_4026526
  have hstable : (prefixWord ++ tailWord_4026526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4026526).length < 2 ^ (prefixWord ++ tailWord_4026526).sum := by decide
  have hdescent : baseEnd_4026526 < baseStart_4026526 := by decide
  rcases family_descends (prefixWord ++ tailWord_4026526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4026541 : List Nat := [1, 5, 2, 1, 2, 2, 1, 1, 2, 6]
def baseStart_4026541 : Nat := 118140960795 + 4026541 * 2 ^ 59
def prefixEnd_4026541 : Nat := 4983230072969 + 3 ^ 40 * 4026541 * 2
def baseEnd_4026541 : Nat := 689183636011811957839927

theorem tailTrace_4026541 : CollatzResearch.WordTrace tailWord_4026541 prefixEnd_4026541 689183636011811957839927 := by
  unfold tailWord_4026541
  simp only [CollatzResearch.WordTrace]
  refine ⟨146860015305537110299031477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97906676870358073532687651 146860015305537110299031477)
  ·
    refine ⟨13768126434894104090534201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 146860015305537110299031477 13768126434894104090534201)
    ·
      refine ⟨10326094826170578067900651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13768126434894104090534201 10326094826170578067900651)
      ·
        refine ⟨15489142239255867101850977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10326094826170578067900651 15489142239255867101850977)
        ·
          refine ⟨11616856679441900326388233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15489142239255867101850977 11616856679441900326388233)
          ·
            refine ⟨8712642509581425244791175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11616856679441900326388233 8712642509581425244791175)
            ·
              refine ⟨13068963764372137867186763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8712642509581425244791175 13068963764372137867186763)
              ·
                refine ⟨19603445646558206800780145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13068963764372137867186763 19603445646558206800780145)
                ·
                  refine ⟨14702584234918655100585109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19603445646558206800780145 14702584234918655100585109)
                  ·
                    refine ⟨689183636011811957839927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14702584234918655100585109 689183636011811957839927)
                    ·
                      rfl

theorem cell23_4026541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 1, 2, 6].length) (baseStart_4026541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4026541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4026541 prefixEnd_4026541 := by exact prefixLift 4026541
  have htrace : WordTrace (prefixWord ++ tailWord_4026541) baseStart_4026541 baseEnd_4026541 := by
    simpa [prefixWord, tailWord_4026541, baseEnd_4026541] using wordTrace_append hprefix tailTrace_4026541
  have hstable : (prefixWord ++ tailWord_4026541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4026541).length < 2 ^ (prefixWord ++ tailWord_4026541).sum := by decide
  have hdescent : baseEnd_4026541 < baseStart_4026541 := by decide
  rcases family_descends (prefixWord ++ tailWord_4026541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4026571 : List Nat := [1, 1, 1, 1, 3, 2, 6, 3, 5]
def baseStart_4026571 : Nat := 118140960795 + 4026571 * 2 ^ 59
def prefixEnd_4026571 : Nat := 4983230072969 + 3 ^ 40 * 4026571 * 2
def baseEnd_4026571 : Nat := 229729590272785639571627

theorem tailTrace_4026571 : CollatzResearch.WordTrace tailWord_4026571 prefixEnd_4026571 229729590272785639571627 := by
  unfold tailWord_4026571
  simp only [CollatzResearch.WordTrace]
  refine ⟨146861109495428425422623567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97907406330285616948415711 146861109495428425422623567)
  ·
    refine ⟨220291664243142638133935351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146861109495428425422623567 220291664243142638133935351)
    ·
      refine ⟨330437496364713957200903027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220291664243142638133935351 330437496364713957200903027)
      ·
        refine ⟨495656244547070935801354541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330437496364713957200903027 495656244547070935801354541)
        ·
          refine ⟨185871091705151600925507953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 495656244547070935801354541 185871091705151600925507953)
          ·
            refine ⟨139403318778863700694130965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185871091705151600925507953 139403318778863700694130965)
            ·
              refine ⟨6534530567759235970037389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 139403318778863700694130965 6534530567759235970037389)
              ·
                refine ⟨2450448962909713488764021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6534530567759235970037389 2450448962909713488764021)
                ·
                  refine ⟨229729590272785639571627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2450448962909713488764021 229729590272785639571627)
                  ·
                    rfl

theorem cell23_4026571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 6, 3, 5].length) (baseStart_4026571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4026571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4026571 prefixEnd_4026571 := by exact prefixLift 4026571
  have htrace : WordTrace (prefixWord ++ tailWord_4026571) baseStart_4026571 baseEnd_4026571 := by
    simpa [prefixWord, tailWord_4026571, baseEnd_4026571] using wordTrace_append hprefix tailTrace_4026571
  have hstable : (prefixWord ++ tailWord_4026571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4026571).length < 2 ^ (prefixWord ++ tailWord_4026571).sum := by decide
  have hdescent : baseEnd_4026571 < baseStart_4026571 := by decide
  rcases family_descends (prefixWord ++ tailWord_4026571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4026582 : List Nat := [5, 2, 1, 2, 1, 2, 1, 1, 4, 2, 2]
def baseStart_4026582 : Nat := 118140960795 + 4026582 * 2 ^ 59
def prefixEnd_4026582 : Nat := 4983230072969 + 3 ^ 40 * 4026582 * 2
def baseEnd_4026582 : Nat := 2067571960742270213107093

theorem tailTrace_4026582 : CollatzResearch.WordTrace tailWord_4026582 prefixEnd_4026582 2067571960742270213107093 := by
  unfold tailWord_4026582
  simp only [CollatzResearch.WordTrace]
  refine ⟨9178844418649285893829625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 97907673798925716200849333 9178844418649285893829625)
  ·
    refine ⟨6884133313986964420372219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9178844418649285893829625 6884133313986964420372219)
    ·
      refine ⟨10326199970980446630558329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6884133313986964420372219 10326199970980446630558329)
      ·
        refine ⟨7744649978235334972918747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10326199970980446630558329 7744649978235334972918747)
        ·
          refine ⟨11616974967353002459378121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7744649978235334972918747 11616974967353002459378121)
          ·
            refine ⟨8712731225514751844533591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11616974967353002459378121 8712731225514751844533591)
            ·
              refine ⟨13069096838272127766800387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8712731225514751844533591 13069096838272127766800387)
              ·
                refine ⟨19603645257408191650200581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13069096838272127766800387 19603645257408191650200581)
                ·
                  refine ⟨3675683485764035934412609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19603645257408191650200581 3675683485764035934412609)
                  ·
                    refine ⟨2756762614323026950809457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3675683485764035934412609 2756762614323026950809457)
                    ·
                      refine ⟨2067571960742270213107093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2756762614323026950809457 2067571960742270213107093)
                      ·
                        rfl

theorem cell23_4026582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 1, 4, 2, 2].length) (baseStart_4026582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4026582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4026582 prefixEnd_4026582 := by exact prefixLift 4026582
  have htrace : WordTrace (prefixWord ++ tailWord_4026582) baseStart_4026582 baseEnd_4026582 := by
    simpa [prefixWord, tailWord_4026582, baseEnd_4026582] using wordTrace_append hprefix tailTrace_4026582
  have hstable : (prefixWord ++ tailWord_4026582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4026582).length < 2 ^ (prefixWord ++ tailWord_4026582).sum := by decide
  have hdescent : baseEnd_4026582 < baseStart_4026582 := by decide
  rcases family_descends (prefixWord ++ tailWord_4026582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4026604 : List Nat := [2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 4]
def baseStart_4026604 : Nat := 118140960795 + 4026604 * 2 ^ 59
def prefixEnd_4026604 : Nat := 4983230072969 + 3 ^ 40 * 4026604 * 2
def baseEnd_4026604 : Nat := 2067583257316669127031991

theorem tailTrace_4026604 : CollatzResearch.WordTrace tailWord_4026604 prefixEnd_4026604 2067583257316669127031991 := by
  unfold tailWord_4026604
  simp only [CollatzResearch.WordTrace]
  refine ⟨73431156552154436029287433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97908208736205914705716577 73431156552154436029287433)
  ·
    refine ⟨55073367414115827021965575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73431156552154436029287433 55073367414115827021965575)
    ·
      refine ⟨82610051121173740532948363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55073367414115827021965575 82610051121173740532948363)
      ·
        refine ⟨123915076681760610799422545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82610051121173740532948363 123915076681760610799422545)
        ·
          refine ⟨92936307511320458099566909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123915076681760610799422545 92936307511320458099566909)
          ·
            refine ⟨34851115316745171787337591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92936307511320458099566909 34851115316745171787337591)
            ·
              refine ⟨52276672975117757681006387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34851115316745171787337591 52276672975117757681006387)
              ·
                refine ⟨78415009462676636521509581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52276672975117757681006387 78415009462676636521509581)
                ·
                  refine ⟨29405628548503738695566093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78415009462676636521509581 29405628548503738695566093)
                  ·
                    refine ⟨11027110705688902010837285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29405628548503738695566093 11027110705688902010837285)
                    ·
                      refine ⟨2067583257316669127031991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11027110705688902010837285 2067583257316669127031991)
                      ·
                        rfl

theorem cell23_4026604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 4].length) (baseStart_4026604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4026604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4026604 prefixEnd_4026604 := by exact prefixLift 4026604
  have htrace : WordTrace (prefixWord ++ tailWord_4026604) baseStart_4026604 baseEnd_4026604 := by
    simpa [prefixWord, tailWord_4026604, baseEnd_4026604] using wordTrace_append hprefix tailTrace_4026604
  have hstable : (prefixWord ++ tailWord_4026604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4026604).length < 2 ^ (prefixWord ++ tailWord_4026604).sum := by decide
  have hdescent : baseEnd_4026604 < baseStart_4026604 := by decide
  rcases family_descends (prefixWord ++ tailWord_4026604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4026621 : List Nat := [1, 4, 1, 1, 1, 1, 1, 4, 1, 6, 2]
def baseStart_4026621 : Nat := 118140960795 + 4026621 * 2 ^ 59
def prefixEnd_4026621 : Nat := 4983230072969 + 3 ^ 40 * 4026621 * 2
def baseEnd_4026621 : Nat := 2067591986487795560519413

theorem tailTrace_4026621 : CollatzResearch.WordTrace tailWord_4026621 prefixEnd_4026621 2067591986487795560519413 := by
  unfold tailWord_4026621
  simp only [CollatzResearch.WordTrace]
  refine ⟨146862933145247283961943717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97908622096831522641295811 146862933145247283961943717)
  ·
    refine ⟨27536799964733865742864447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146862933145247283961943717 27536799964733865742864447)
    ·
      refine ⟨41305199947100798614296671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27536799964733865742864447 41305199947100798614296671)
      ·
        refine ⟨61957799920651197921445007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41305199947100798614296671 61957799920651197921445007)
        ·
          refine ⟨92936699880976796882167511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61957799920651197921445007 92936699880976796882167511)
          ·
            refine ⟨139405049821465195323251267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92936699880976796882167511 139405049821465195323251267)
            ·
              refine ⟨209107574732197792984876901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139405049821465195323251267 209107574732197792984876901)
              ·
                refine ⟨39207670262287086184664419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 209107574732197792984876901 39207670262287086184664419)
                ·
                  refine ⟨58811505393430629276996629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39207670262287086184664419 58811505393430629276996629)
                  ·
                    refine ⟨2756789315317060747359217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 58811505393430629276996629 2756789315317060747359217)
                    ·
                      refine ⟨2067591986487795560519413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2756789315317060747359217 2067591986487795560519413)
                      ·
                        rfl

theorem cell23_4026621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 4, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 4, 1, 6, 2].length) (baseStart_4026621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4026621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4026621 prefixEnd_4026621 := by exact prefixLift 4026621
  have htrace : WordTrace (prefixWord ++ tailWord_4026621) baseStart_4026621 baseEnd_4026621 := by
    simpa [prefixWord, tailWord_4026621, baseEnd_4026621] using wordTrace_append hprefix tailTrace_4026621
  have hstable : (prefixWord ++ tailWord_4026621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4026621).length < 2 ^ (prefixWord ++ tailWord_4026621).sum := by decide
  have hdescent : baseEnd_4026621 < baseStart_4026621 := by decide
  rcases family_descends (prefixWord ++ tailWord_4026621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4026634 : List Nat := [3, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6]
def baseStart_4026634 : Nat := 118140960795 + 4026634 * 2 ^ 59
def prefixEnd_4026634 : Nat := 4983230072969 + 3 ^ 40 * 4026634 * 2
def baseEnd_4026634 : Nat := 2067598661736304009656853

theorem tailTrace_4026634 : CollatzResearch.WordTrace tailWord_4026634 prefixEnd_4026634 2067598661736304009656853 := by
  unfold tailWord_4026634
  simp only [CollatzResearch.WordTrace]
  refine ⟨36715851823550046795541739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97908938196133458121444637 36715851823550046795541739)
  ·
    refine ⟨55073777735325070193312609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36715851823550046795541739 55073777735325070193312609)
    ·
      refine ⟨41305333301493802644984457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55073777735325070193312609 41305333301493802644984457)
      ·
        refine ⟨30978999976120351983738343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41305333301493802644984457 30978999976120351983738343)
        ·
          refine ⟨46468499964180527975607515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30978999976120351983738343 46468499964180527975607515)
          ·
            refine ⟨69702749946270791963411273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46468499964180527975607515 69702749946270791963411273)
            ·
              refine ⟨52277062459703093972558455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69702749946270791963411273 52277062459703093972558455)
              ·
                refine ⟨78415593689554640958837683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52277062459703093972558455 78415593689554640958837683)
                ·
                  refine ⟨117623390534331961438256525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78415593689554640958837683 117623390534331961438256525)
                  ·
                    refine ⟨44108771450374485539346197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 117623390534331961438256525 44108771450374485539346197)
                    ·
                      refine ⟨2067598661736304009656853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44108771450374485539346197 2067598661736304009656853)
                      ·
                        rfl

theorem cell23_4026634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6].length) (baseStart_4026634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4026634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4026634 prefixEnd_4026634 := by exact prefixLift 4026634
  have htrace : WordTrace (prefixWord ++ tailWord_4026634) baseStart_4026634 baseEnd_4026634 := by
    simpa [prefixWord, tailWord_4026634, baseEnd_4026634] using wordTrace_append hprefix tailTrace_4026634
  have hstable : (prefixWord ++ tailWord_4026634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4026634).length < 2 ^ (prefixWord ++ tailWord_4026634).sum := by decide
  have hdescent : baseEnd_4026634 < baseStart_4026634 := by decide
  rcases family_descends (prefixWord ++ tailWord_4026634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4026641 : List Nat := [1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 3]
def baseStart_4026641 : Nat := 118140960795 + 4026641 * 2 ^ 59
def prefixEnd_4026641 : Nat := 4983230072969 + 3 ^ 40 * 4026641 * 2
def baseEnd_4026641 : Nat := 2067602256100885482269321

theorem tailTrace_4026641 : CollatzResearch.WordTrace tailWord_4026641 prefixEnd_4026641 2067602256100885482269321 := by
  unfold tailWord_4026641
  simp only [CollatzResearch.WordTrace]
  refine ⟨146863662605174827377671777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97909108403449884918447851 146863662605174827377671777)
  ·
    refine ⟨110147746953881120533253833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146863662605174827377671777 110147746953881120533253833)
    ·
      refine ⟨82610810215410840399940375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110147746953881120533253833 82610810215410840399940375)
      ·
        refine ⟨123916215323116260599910563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82610810215410840399940375 123916215323116260599910563)
        ·
          refine ⟨185874322984674390899865845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123916215323116260599910563 185874322984674390899865845)
          ·
            refine ⟨17425717779813224146862423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 185874322984674390899865845 17425717779813224146862423)
            ·
              refine ⟨26138576669719836220293635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17425717779813224146862423 26138576669719836220293635)
              ·
                refine ⟨39207865004579754330440453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26138576669719836220293635 39207865004579754330440453)
                ·
                  refine ⟨7351474688358703936957585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39207865004579754330440453 7351474688358703936957585)
                  ·
                    refine ⟨5513606016269027952718189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7351474688358703936957585 5513606016269027952718189)
                    ·
                      refine ⟨2067602256100885482269321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5513606016269027952718189 2067602256100885482269321)
                      ·
                        rfl

theorem cell23_4026641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 3].length) (baseStart_4026641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4026641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4026641 prefixEnd_4026641 := by exact prefixLift 4026641
  have htrace : WordTrace (prefixWord ++ tailWord_4026641) baseStart_4026641 baseEnd_4026641 := by
    simpa [prefixWord, tailWord_4026641, baseEnd_4026641] using wordTrace_append hprefix tailTrace_4026641
  have hstable : (prefixWord ++ tailWord_4026641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4026641).length < 2 ^ (prefixWord ++ tailWord_4026641).sum := by decide
  have hdescent : baseEnd_4026641 < baseStart_4026641 := by decide
  rcases family_descends (prefixWord ++ tailWord_4026641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4026691 : List Nat := [1, 1, 1, 3, 1, 3, 2, 5, 1, 5]
def baseStart_4026691 : Nat := 118140960795 + 4026691 * 2 ^ 59
def prefixEnd_4026691 : Nat := 4983230072969 + 3 ^ 40 * 4026691 * 2
def baseEnd_4026691 : Nat := 689209310044536762214697

theorem tailTrace_4026691 : CollatzResearch.WordTrace tailWord_4026691 prefixEnd_4026691 689209310044536762214697 := by
  unfold tailWord_4026691
  simp only [CollatzResearch.WordTrace]
  refine ⟨146865486254993685916991927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97910324169995790611327951 146865486254993685916991927)
  ·
    refine ⟨220298229382490528875487891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146865486254993685916991927 220298229382490528875487891)
    ·
      refine ⟨330447344073735793313231837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220298229382490528875487891 330447344073735793313231837)
      ·
        refine ⟨123917754027650922492461939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 330447344073735793313231837 123917754027650922492461939)
        ·
          refine ⟨185876631041476383738692909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123917754027650922492461939 185876631041476383738692909)
          ·
            refine ⟨69703736640553643902009841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 185876631041476383738692909 69703736640553643902009841)
            ·
              refine ⟨52277802480415232926507381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69703736640553643902009841 52277802480415232926507381)
              ·
                refine ⟨4901043982538928086860067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52277802480415232926507381 4901043982538928086860067)
                ·
                  refine ⟨7351565973808392130290101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4901043982538928086860067 7351565973808392130290101)
                  ·
                    refine ⟨689209310044536762214697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7351565973808392130290101 689209310044536762214697)
                    ·
                      rfl

theorem cell23_4026691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 5, 1, 5].length) (baseStart_4026691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4026691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4026691 prefixEnd_4026691 := by exact prefixLift 4026691
  have htrace : WordTrace (prefixWord ++ tailWord_4026691) baseStart_4026691 baseEnd_4026691 := by
    simpa [prefixWord, tailWord_4026691, baseEnd_4026691] using wordTrace_append hprefix tailTrace_4026691
  have hstable : (prefixWord ++ tailWord_4026691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4026691).length < 2 ^ (prefixWord ++ tailWord_4026691).sum := by decide
  have hdescent : baseEnd_4026691 < baseStart_4026691 := by decide
  rcases family_descends (prefixWord ++ tailWord_4026691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4026711 : List Nat := [1, 1, 3, 2, 3, 1, 1, 1, 5, 1, 4]
def baseStart_4026711 : Nat := 118140960795 + 4026711 * 2 ^ 59
def prefixEnd_4026711 : Nat := 4983230072969 + 3 ^ 40 * 4026711 * 2
def baseEnd_4026711 : Nat := 2067638199746700208393999

theorem tailTrace_4026711 : CollatzResearch.WordTrace tailWord_4026711 prefixEnd_4026711 2067638199746700208393999 := by
  unfold tailWord_4026711
  simp only [CollatzResearch.WordTrace]
  refine ⟨146866215714921229332719987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97910810476614152888479991 146866215714921229332719987)
  ·
    refine ⟨220299323572381843999079981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146866215714921229332719987 220299323572381843999079981)
    ·
      refine ⟨82612246339643191499654993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220299323572381843999079981 82612246339643191499654993)
      ·
        refine ⟨61959184754732393624741245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82612246339643191499654993 61959184754732393624741245)
        ·
          refine ⟨23234694283024647609277967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61959184754732393624741245 23234694283024647609277967)
          ·
            refine ⟨34852041424536971413916951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23234694283024647609277967 34852041424536971413916951)
            ·
              refine ⟨52278062136805457120875427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34852041424536971413916951 52278062136805457120875427)
              ·
                refine ⟨78417093205208185681313141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52278062136805457120875427 78417093205208185681313141)
                ·
                  refine ⟨7351602487988267407623107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78417093205208185681313141 7351602487988267407623107)
                  ·
                    refine ⟨11027403731982401111434661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7351602487988267407623107 11027403731982401111434661)
                    ·
                      refine ⟨2067638199746700208393999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11027403731982401111434661 2067638199746700208393999)
                      ·
                        rfl

theorem cell23_4026711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 5, 1, 4].length) (baseStart_4026711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4026711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4026711 prefixEnd_4026711 := by exact prefixLift 4026711
  have htrace : WordTrace (prefixWord ++ tailWord_4026711) baseStart_4026711 baseEnd_4026711 := by
    simpa [prefixWord, tailWord_4026711, baseEnd_4026711] using wordTrace_append hprefix tailTrace_4026711
  have hstable : (prefixWord ++ tailWord_4026711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4026711).length < 2 ^ (prefixWord ++ tailWord_4026711).sum := by decide
  have hdescent : baseEnd_4026711 < baseStart_4026711 := by decide
  rcases family_descends (prefixWord ++ tailWord_4026711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4026721 : List Nat := [1, 2, 3, 1, 1, 1, 1, 1, 8, 4]
def baseStart_4026721 : Nat := 118140960795 + 4026721 * 2 ^ 59
def prefixEnd_4026721 : Nat := 4983230072969 + 3 ^ 40 * 4026721 * 2
def baseEnd_4026721 : Nat := 689214444851081723089651

theorem tailTrace_4026721 : CollatzResearch.WordTrace tailWord_4026721 prefixEnd_4026721 689214444851081723089651 := by
  unfold tailWord_4026721
  simp only [CollatzResearch.WordTrace]
  refine ⟨146866580444885001040584017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97911053629923334027056011 146866580444885001040584017)
  ·
    refine ⟨110149935333663750780438013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146866580444885001040584017 110149935333663750780438013)
    ·
      refine ⟨41306225750123906542664255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110149935333663750780438013 41306225750123906542664255)
      ·
        refine ⟨61959338625185859813996383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41306225750123906542664255 61959338625185859813996383)
        ·
          refine ⟨92939007937778789720994575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61959338625185859813996383 92939007937778789720994575)
          ·
            refine ⟨139408511906668184581491863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92939007937778789720994575 139408511906668184581491863)
            ·
              refine ⟨209112767860002276872237795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139408511906668184581491863 209112767860002276872237795)
              ·
                refine ⟨313669151790003415308356693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 209112767860002276872237795 313669151790003415308356693)
                ·
                  refine ⟨3675810372539102523144805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 313669151790003415308356693 3675810372539102523144805)
                  ·
                    refine ⟨689214444851081723089651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3675810372539102523144805 689214444851081723089651)
                    ·
                      rfl

theorem cell23_4026721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 8, 4].length) (baseStart_4026721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4026721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4026721 prefixEnd_4026721 := by exact prefixLift 4026721
  have htrace : WordTrace (prefixWord ++ tailWord_4026721) baseStart_4026721 baseEnd_4026721 := by
    simpa [prefixWord, tailWord_4026721, baseEnd_4026721] using wordTrace_append hprefix tailTrace_4026721
  have hstable : (prefixWord ++ tailWord_4026721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4026721).length < 2 ^ (prefixWord ++ tailWord_4026721).sum := by decide
  have hdescent : baseEnd_4026721 < baseStart_4026721 := by decide
  rcases family_descends (prefixWord ++ tailWord_4026721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4026728 : List Nat := [2, 1, 4, 2, 2, 1, 2, 1, 3, 1, 4]
def baseStart_4026728 : Nat := 118140960795 + 4026728 * 2 ^ 59
def prefixEnd_4026728 : Nat := 4983230072969 + 3 ^ 40 * 4026728 * 2
def baseEnd_4026728 : Nat := 2067646928917826641881421

theorem tailTrace_4026728 : CollatzResearch.WordTrace tailWord_4026728 prefixEnd_4026728 2067646928917826641881421 := by
  unfold tailWord_4026728
  simp only [CollatzResearch.WordTrace]
  refine ⟨73433417877929820618044419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97911223837239760824059225 73433417877929820618044419)
  ·
    refine ⟨110150126816894730927066629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73433417877929820618044419 110150126816894730927066629)
    ·
      refine ⟨20653148778167762048824993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110150126816894730927066629 20653148778167762048824993)
      ·
        refine ⟨15489861583625821536618745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20653148778167762048824993 15489861583625821536618745)
        ·
          refine ⟨11617396187719366152464059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15489861583625821536618745 11617396187719366152464059)
          ·
            refine ⟨17426094281579049228696089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11617396187719366152464059 17426094281579049228696089)
            ·
              refine ⟨13069570711184286921522067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17426094281579049228696089 13069570711184286921522067)
              ·
                refine ⟨19604356066776430382283101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13069570711184286921522067 19604356066776430382283101)
                ·
                  refine ⟨7351633525041161393356163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19604356066776430382283101 7351633525041161393356163)
                  ·
                    refine ⟨11027450287561742090034245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7351633525041161393356163 11027450287561742090034245)
                    ·
                      refine ⟨2067646928917826641881421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11027450287561742090034245 2067646928917826641881421)
                      ·
                        rfl

theorem cell23_4026728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_4026728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4026728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4026728 prefixEnd_4026728 := by exact prefixLift 4026728
  have htrace : WordTrace (prefixWord ++ tailWord_4026728) baseStart_4026728 baseEnd_4026728 := by
    simpa [prefixWord, tailWord_4026728, baseEnd_4026728] using wordTrace_append hprefix tailTrace_4026728
  have hstable : (prefixWord ++ tailWord_4026728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4026728).length < 2 ^ (prefixWord ++ tailWord_4026728).sum := by decide
  have hdescent : baseEnd_4026728 < baseStart_4026728 := by decide
  rcases family_descends (prefixWord ++ tailWord_4026728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4026732 : List Nat := [2, 2, 1, 1, 6, 2, 1, 1, 2, 3, 2]
def baseStart_4026732 : Nat := 118140960795 + 4026732 * 2 ^ 59
def prefixEnd_4026732 : Nat := 4983230072969 + 3 ^ 40 * 4026732 * 2
def baseEnd_4026732 : Nat := 2067648982840444626231403

theorem tailTrace_4026732 : CollatzResearch.WordTrace tailWord_4026732 prefixEnd_4026732 2067648982840444626231403 := by
  unfold tailWord_4026732
  simp only [CollatzResearch.WordTrace]
  refine ⟨73433490823922574959617225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97911321098563433279489633 73433490823922574959617225)
  ·
    refine ⟨55075118117941931219712919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73433490823922574959617225 55075118117941931219712919)
    ·
      refine ⟨82612677176912896829569379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55075118117941931219712919 82612677176912896829569379)
      ·
        refine ⟨123919015765369345244354069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82612677176912896829569379 123919015765369345244354069)
        ·
          refine ⟨5808703864001688058329097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 123919015765369345244354069 5808703864001688058329097)
          ·
            refine ⟨4356527898001266043746823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5808703864001688058329097 4356527898001266043746823)
            ·
              refine ⟨6534791847001899065620235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4356527898001266043746823 6534791847001899065620235)
              ·
                refine ⟨9802187770502848598430353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6534791847001899065620235 9802187770502848598430353)
                ·
                  refine ⟨7351640827877136448822765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9802187770502848598430353 7351640827877136448822765)
                  ·
                    refine ⟨2756865310453926168308537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7351640827877136448822765 2756865310453926168308537)
                    ·
                      refine ⟨2067648982840444626231403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2756865310453926168308537 2067648982840444626231403)
                      ·
                        rfl

theorem cell23_4026732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 3, 2].length) (baseStart_4026732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4026732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4026732 prefixEnd_4026732 := by exact prefixLift 4026732
  have htrace : WordTrace (prefixWord ++ tailWord_4026732) baseStart_4026732 baseEnd_4026732 := by
    simpa [prefixWord, tailWord_4026732, baseEnd_4026732] using wordTrace_append hprefix tailTrace_4026732
  have hstable : (prefixWord ++ tailWord_4026732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4026732).length < 2 ^ (prefixWord ++ tailWord_4026732).sum := by decide
  have hdescent : baseEnd_4026732 < baseStart_4026732 := by decide
  rcases family_descends (prefixWord ++ tailWord_4026732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4026742 : List Nat := [5, 1, 1, 4, 1, 1, 1, 3, 1, 5]
def baseStart_4026742 : Nat := 118140960795 + 4026742 * 2 ^ 59
def prefixEnd_4026742 : Nat := 4983230072969 + 3 ^ 40 * 4026742 * 2
def baseEnd_4026742 : Nat := 689218039215663195702119

theorem tailTrace_4026742 : CollatzResearch.WordTrace tailWord_4026742 prefixEnd_4026742 689218039215663195702119 := by
  unfold tailWord_4026742
  simp only [CollatzResearch.WordTrace]
  refine ⟨9179209148613057601693655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 97911564251872614418065653 9179209148613057601693655)
  ·
    refine ⟨13768813722919586402540483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9179209148613057601693655 13768813722919586402540483)
    ·
      refine ⟨20653220584379379603810725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13768813722919586402540483 20653220584379379603810725)
      ·
        refine ⟨3872478859571133675714511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20653220584379379603810725 3872478859571133675714511)
        ·
          refine ⟨5808718289356700513571767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3872478859571133675714511 5808718289356700513571767)
          ·
            refine ⟨8713077434035050770357651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5808718289356700513571767 8713077434035050770357651)
            ·
              refine ⟨13069616151052576155536477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8713077434035050770357651 13069616151052576155536477)
              ·
                refine ⟨4901106056644716058326179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13069616151052576155536477 4901106056644716058326179)
                ·
                  refine ⟨7351659084967074087489269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4901106056644716058326179 7351659084967074087489269)
                  ·
                    refine ⟨689218039215663195702119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7351659084967074087489269 689218039215663195702119)
                    ·
                      rfl

theorem cell23_4026742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 3, 1, 5].length) (baseStart_4026742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4026742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4026742 prefixEnd_4026742 := by exact prefixLift 4026742
  have htrace : WordTrace (prefixWord ++ tailWord_4026742) baseStart_4026742 baseEnd_4026742 := by
    simpa [prefixWord, tailWord_4026742, baseEnd_4026742] using wordTrace_append hprefix tailTrace_4026742
  have hstable : (prefixWord ++ tailWord_4026742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4026742).length < 2 ^ (prefixWord ++ tailWord_4026742).sum := by decide
  have hdescent : baseEnd_4026742 < baseStart_4026742 := by decide
  rcases family_descends (prefixWord ++ tailWord_4026742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4026772 : List Nat := [2, 4, 2, 1, 4, 1, 1, 1, 1, 6]
def baseStart_4026772 : Nat := 118140960795 + 4026772 * 2 ^ 59
def prefixEnd_4026772 : Nat := 4983230072969 + 3 ^ 40 * 4026772 * 2
def baseEnd_4026772 : Nat := 689223174022208156577073

theorem tailTrace_4026772 : CollatzResearch.WordTrace tailWord_4026772 prefixEnd_4026772 689223174022208156577073 := by
  unfold tailWord_4026772
  simp only [CollatzResearch.WordTrace]
  refine ⟨73434220283850118375345285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97912293711800157833793713 73434220283850118375345285)
  ·
    refine ⟨13768916303221897195377241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73434220283850118375345285 13768916303221897195377241)
    ·
      refine ⟨10326687227416422896532931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13768916303221897195377241 10326687227416422896532931)
      ·
        refine ⟨15490030841124634344799397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10326687227416422896532931 15490030841124634344799397)
        ·
          refine ⟨2904380782710868939649887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15490030841124634344799397 2904380782710868939649887)
          ·
            refine ⟨4356571174066303409474831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2904380782710868939649887 4356571174066303409474831)
            ·
              refine ⟨6534856761099455114212247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4356571174066303409474831 6534856761099455114212247)
              ·
                refine ⟨9802285141649182671318371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6534856761099455114212247 9802285141649182671318371)
                ·
                  refine ⟨14703427712473774006977557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9802285141649182671318371 14703427712473774006977557)
                  ·
                    refine ⟨689223174022208156577073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14703427712473774006977557 689223174022208156577073)
                    ·
                      rfl

theorem cell23_4026772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 1, 1, 1, 6].length) (baseStart_4026772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4026772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4026772 prefixEnd_4026772 := by exact prefixLift 4026772
  have htrace : WordTrace (prefixWord ++ tailWord_4026772) baseStart_4026772 baseEnd_4026772 := by
    simpa [prefixWord, tailWord_4026772, baseEnd_4026772] using wordTrace_append hprefix tailTrace_4026772
  have hstable : (prefixWord ++ tailWord_4026772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4026772).length < 2 ^ (prefixWord ++ tailWord_4026772).sum := by decide
  have hdescent : baseEnd_4026772 < baseStart_4026772 := by decide
  rcases family_descends (prefixWord ++ tailWord_4026772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4026782 : List Nat := [4, 3, 1, 2, 1, 1, 1, 4, 1, 2, 3]
def baseStart_4026782 : Nat := 118140960795 + 4026782 * 2 ^ 59
def prefixEnd_4026782 : Nat := 4983230072969 + 3 ^ 40 * 4026782 * 2
def baseEnd_4026782 : Nat := 2067674656873169430606173

theorem tailTrace_4026782 : CollatzResearch.WordTrace tailWord_4026782 prefixEnd_4026782 2067674656873169430606173 := by
  unfold tailWord_4026782
  simp only [CollatzResearch.WordTrace]
  refine ⟨18358600662208001057319325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97912536865109338972369733 18358600662208001057319325)
  ·
    refine ⟨6884475248328000396494747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18358600662208001057319325 6884475248328000396494747)
    ·
      refine ⟨10326712872492000594742121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6884475248328000396494747 10326712872492000594742121)
      ·
        refine ⟨7745034654369000446056591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10326712872492000594742121 7745034654369000446056591)
        ·
          refine ⟨11617551981553500669084887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7745034654369000446056591 11617551981553500669084887)
          ·
            refine ⟨17426327972330251003627331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11617551981553500669084887 17426327972330251003627331)
            ·
              refine ⟨26139491958495376505440997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17426327972330251003627331 26139491958495376505440997)
              ·
                refine ⟨4901154742217883094770187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26139491958495376505440997 4901154742217883094770187)
                ·
                  refine ⟨7351732113326824642155281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4901154742217883094770187 7351732113326824642155281)
                  ·
                    refine ⟨5513799084995118481616461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7351732113326824642155281 5513799084995118481616461)
                    ·
                      refine ⟨2067674656873169430606173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5513799084995118481616461 2067674656873169430606173)
                      ·
                        rfl

theorem cell23_4026782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_4026782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4026782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4026782 prefixEnd_4026782 := by exact prefixLift 4026782
  have htrace : WordTrace (prefixWord ++ tailWord_4026782) baseStart_4026782 baseEnd_4026782 := by
    simpa [prefixWord, tailWord_4026782, baseEnd_4026782] using wordTrace_append hprefix tailTrace_4026782
  have hstable : (prefixWord ++ tailWord_4026782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4026782).length < 2 ^ (prefixWord ++ tailWord_4026782).sum := by decide
  have hdescent : baseEnd_4026782 < baseStart_4026782 := by decide
  rcases family_descends (prefixWord ++ tailWord_4026782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4026831 : List Nat := [1, 1, 2, 1, 1, 4, 1, 3, 1, 4, 4]
def baseStart_4026831 : Nat := 118140960795 + 4026831 * 2 ^ 59
def prefixEnd_4026831 : Nat := 4983230072969 + 3 ^ 40 * 4026831 * 2
def baseEnd_4026831 : Nat := 2067699817425239738893447

theorem tailTrace_4026831 : CollatzResearch.WordTrace tailWord_4026831 prefixEnd_4026831 2067699817425239738893447 := by
  unfold tailWord_4026831
  simp only [CollatzResearch.WordTrace]
  refine ⟨146870592474486489827088347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97913728316324326551392231 146870592474486489827088347)
  ·
    refine ⟨220305888711729734740632521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146870592474486489827088347 220305888711729734740632521)
    ·
      refine ⟨165229416533797301055474391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220305888711729734740632521 165229416533797301055474391)
      ·
        refine ⟨247844124800695951583211587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165229416533797301055474391 247844124800695951583211587)
        ·
          refine ⟨371766187201043927374817381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247844124800695951583211587 371766187201043927374817381)
          ·
            refine ⟨69706160100195736382778259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 371766187201043927374817381 69706160100195736382778259)
            ·
              refine ⟨104559240150293604574167389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69706160100195736382778259 104559240150293604574167389)
              ·
                refine ⟨39209715056360101715312771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104559240150293604574167389 39209715056360101715312771)
                ·
                  refine ⟨58814572584540152572969157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39209715056360101715312771 58814572584540152572969157)
                  ·
                    refine ⟨11027732359601278607431717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58814572584540152572969157 11027732359601278607431717)
                    ·
                      refine ⟨2067699817425239738893447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11027732359601278607431717 2067699817425239738893447)
                      ·
                        rfl

theorem cell23_4026831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 3, 1, 4, 4].length) (baseStart_4026831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4026831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4026831 prefixEnd_4026831 := by exact prefixLift 4026831
  have htrace : WordTrace (prefixWord ++ tailWord_4026831) baseStart_4026831 baseEnd_4026831 := by
    simpa [prefixWord, tailWord_4026831, baseEnd_4026831] using wordTrace_append hprefix tailTrace_4026831
  have hstable : (prefixWord ++ tailWord_4026831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4026831).length < 2 ^ (prefixWord ++ tailWord_4026831).sum := by decide
  have hdescent : baseEnd_4026831 < baseStart_4026831 := by decide
  rcases family_descends (prefixWord ++ tailWord_4026831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4026841 : List Nat := [1, 2, 1, 2, 4, 1, 2, 1, 9]
def baseStart_4026841 : Nat := 118140960795 + 4026841 * 2 ^ 59
def prefixEnd_4026841 : Nat := 4983230072969 + 3 ^ 40 * 4026841 * 2
def baseEnd_4026841 : Nat := 229744994692420522196489

theorem tailTrace_4026841 : CollatzResearch.WordTrace tailWord_4026841 prefixEnd_4026841 229744994692420522196489 := by
  unfold tailWord_4026841
  simp only [CollatzResearch.WordTrace]
  refine ⟨146870957204450261534952377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97913971469633507689968251 146870957204450261534952377)
  ·
    refine ⟨110153217903337696151214283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146870957204450261534952377 110153217903337696151214283)
    ·
      refine ⟨165229826855006544226821425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110153217903337696151214283 165229826855006544226821425)
      ·
        refine ⟨123922370141254908170116069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165229826855006544226821425 123922370141254908170116069)
        ·
          refine ⟨23235444401485295281896763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 123922370141254908170116069 23235444401485295281896763)
          ·
            refine ⟨34853166602227942922845145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23235444401485295281896763 34853166602227942922845145)
            ·
              refine ⟨26139874951670957192133859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34853166602227942922845145 26139874951670957192133859)
              ·
                refine ⟨39209812427506435788200789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26139874951670957192133859 39209812427506435788200789)
                ·
                  refine ⟨229744994692420522196489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 39209812427506435788200789 229744994692420522196489)
                  ·
                    rfl

theorem cell23_4026841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 1, 9].length) (baseStart_4026841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4026841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4026841 prefixEnd_4026841 := by exact prefixLift 4026841
  have htrace : WordTrace (prefixWord ++ tailWord_4026841) baseStart_4026841 baseEnd_4026841 := by
    simpa [prefixWord, tailWord_4026841, baseEnd_4026841] using wordTrace_append hprefix tailTrace_4026841
  have hstable : (prefixWord ++ tailWord_4026841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4026841).length < 2 ^ (prefixWord ++ tailWord_4026841).sum := by decide
  have hdescent : baseEnd_4026841 < baseStart_4026841 := by decide
  rcases family_descends (prefixWord ++ tailWord_4026841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4026882 : List Nat := [3, 4, 1, 2, 2, 1, 1, 1, 2, 2, 4]
def baseStart_4026882 : Nat := 118140960795 + 4026882 * 2 ^ 59
def prefixEnd_4026882 : Nat := 4983230072969 + 3 ^ 40 * 4026882 * 2
def baseEnd_4026882 : Nat := 2067726004938619039355713

theorem tailTrace_4026882 : CollatzResearch.WordTrace tailWord_4026882 prefixEnd_4026882 2067726004938619039355713 := by
  unfold tailWord_4026882
  simp only [CollatzResearch.WordTrace]
  refine ⟨36718113149325431384298725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97914968398201150358129933 36718113149325431384298725)
  ·
    refine ⟨6884646215498518384556011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36718113149325431384298725 6884646215498518384556011)
    ·
      refine ⟨10326969323247777576834017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6884646215498518384556011 10326969323247777576834017)
      ·
        refine ⟨7745226992435833182625513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10326969323247777576834017 7745226992435833182625513)
        ·
          refine ⟨5808920244326874886969135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7745226992435833182625513 5808920244326874886969135)
          ·
            refine ⟨8713380366490312330453703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5808920244326874886969135 8713380366490312330453703)
            ·
              refine ⟨13070070549735468495680555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8713380366490312330453703 13070070549735468495680555)
              ·
                refine ⟨19605105824603202743520833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13070070549735468495680555 19605105824603202743520833)
                ·
                  refine ⟨14703829368452402057640625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19605105824603202743520833 14703829368452402057640625)
                  ·
                    refine ⟨11027872026339301543230469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14703829368452402057640625 11027872026339301543230469)
                    ·
                      refine ⟨2067726004938619039355713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11027872026339301543230469 2067726004938619039355713)
                      ·
                        rfl

theorem cell23_4026882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_4026882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4026882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4026882 prefixEnd_4026882 := by exact prefixLift 4026882
  have htrace : WordTrace (prefixWord ++ tailWord_4026882) baseStart_4026882 baseEnd_4026882 := by
    simpa [prefixWord, tailWord_4026882, baseEnd_4026882] using wordTrace_append hprefix tailTrace_4026882
  have hstable : (prefixWord ++ tailWord_4026882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4026882).length < 2 ^ (prefixWord ++ tailWord_4026882).sum := by decide
  have hdescent : baseEnd_4026882 < baseStart_4026882 := by decide
  rcases family_descends (prefixWord ++ tailWord_4026882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4026886 : List Nat := [6, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2]
def baseStart_4026886 : Nat := 118140960795 + 4026886 * 2 ^ 59
def prefixEnd_4026886 : Nat := 4983230072969 + 3 ^ 40 * 4026886 * 2
def baseEnd_4026886 : Nat := 2067728058861237023705695

theorem tailTrace_4026886 : CollatzResearch.WordTrace tailWord_4026886 prefixEnd_4026886 2067728058861237023705695 := by
  unfold tailWord_4026886
  simp only [CollatzResearch.WordTrace]
  refine ⟨4589768702790226069385641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 97915065659524822813560341 4589768702790226069385641)
  ·
    refine ⟨3442326527092669552039231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4589768702790226069385641 3442326527092669552039231)
    ·
      refine ⟨5163489790639004328058847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3442326527092669552039231 5163489790639004328058847)
      ·
        refine ⟨7745234685958506492088271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5163489790639004328058847 7745234685958506492088271)
        ·
          refine ⟨11617852028937759738132407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7745234685958506492088271 11617852028937759738132407)
          ·
            refine ⟨17426778043406639607198611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11617852028937759738132407 17426778043406639607198611)
            ·
              refine ⟨26140167065109959410797917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17426778043406639607198611 26140167065109959410797917)
              ·
                refine ⟨9802562649416234779049219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26140167065109959410797917 9802562649416234779049219)
                ·
                  refine ⟨14703843974124352168573829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9802562649416234779049219 14703843974124352168573829)
                  ·
                    refine ⟨2756970745148316031607593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14703843974124352168573829 2756970745148316031607593)
                    ·
                      refine ⟨2067728058861237023705695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2756970745148316031607593 2067728058861237023705695)
                      ·
                        rfl

theorem cell23_4026886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2].length) (baseStart_4026886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4026886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4026886 prefixEnd_4026886 := by exact prefixLift 4026886
  have htrace : WordTrace (prefixWord ++ tailWord_4026886) baseStart_4026886 baseEnd_4026886 := by
    simpa [prefixWord, tailWord_4026886, baseEnd_4026886] using wordTrace_append hprefix tailTrace_4026886
  have hstable : (prefixWord ++ tailWord_4026886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4026886).length < 2 ^ (prefixWord ++ tailWord_4026886).sum := by decide
  have hdescent : baseEnd_4026886 < baseStart_4026886 := by decide
  rcases family_descends (prefixWord ++ tailWord_4026886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4026935 : List Nat := [1, 1, 3, 1, 2, 3, 4, 1, 3, 4]
def baseStart_4026935 : Nat := 118140960795 + 4026935 * 2 ^ 59
def prefixEnd_4026935 : Nat := 4983230072969 + 3 ^ 40 * 4026935 * 2
def baseEnd_4026935 : Nat := 689251073137769110664323

theorem tailTrace_4026935 : CollatzResearch.WordTrace tailWord_4026935 prefixEnd_4026935 689251073137769110664323 := by
  unfold tailWord_4026935
  simp only [CollatzResearch.WordTrace]
  refine ⟨146874385666109715588874259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97916257110739810392582839 146874385666109715588874259)
  ·
    refine ⟨220311578499164573383311389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146874385666109715588874259 220311578499164573383311389)
    ·
      refine ⟨82616841937186715018741771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220311578499164573383311389 82616841937186715018741771)
      ·
        refine ⟨123925262905780072528112657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82616841937186715018741771 123925262905780072528112657)
        ·
          refine ⟨92943947179335054396084493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123925262905780072528112657 92943947179335054396084493)
          ·
            refine ⟨34853980192250645398531685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92943947179335054396084493 34853980192250645398531685)
            ·
              refine ⟨6535121286046996012224691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34853980192250645398531685 6535121286046996012224691)
              ·
                refine ⟨9802681929070494018337037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6535121286046996012224691 9802681929070494018337037)
                ·
                  refine ⟨3676005723401435256876389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9802681929070494018337037 3676005723401435256876389)
                  ·
                    refine ⟨689251073137769110664323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3676005723401435256876389 689251073137769110664323)
                    ·
                      rfl

theorem cell23_4026935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 4, 1, 3, 4].length) (baseStart_4026935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4026935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4026935 prefixEnd_4026935 := by exact prefixLift 4026935
  have htrace : WordTrace (prefixWord ++ tailWord_4026935) baseStart_4026935 baseEnd_4026935 := by
    simpa [prefixWord, tailWord_4026935, baseEnd_4026935] using wordTrace_append hprefix tailTrace_4026935
  have hstable : (prefixWord ++ tailWord_4026935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4026935).length < 2 ^ (prefixWord ++ tailWord_4026935).sum := by decide
  have hdescent : baseEnd_4026935 < baseStart_4026935 := by decide
  rcases family_descends (prefixWord ++ tailWord_4026935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4026945 : List Nat := [1, 2, 5, 1, 1, 2, 1, 2, 1, 4, 3]
def baseStart_4026945 : Nat := 118140960795 + 4026945 * 2 ^ 59
def prefixEnd_4026945 : Nat := 4983230072969 + 3 ^ 40 * 4026945 * 2
def baseEnd_4026945 : Nat := 2067758354219852292867923

theorem tailTrace_4026945 : CollatzResearch.WordTrace tailWord_4026945 prefixEnd_4026945 2067758354219852292867923 := by
  unfold tailWord_4026945
  simp only [CollatzResearch.WordTrace]
  refine ⟨146874750396073487296738289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97916500264048991531158859 146874750396073487296738289)
  ·
    refine ⟨110156062797055115472553717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146874750396073487296738289 110156062797055115472553717)
    ·
      refine ⟨10327130887223917075551911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 110156062797055115472553717 10327130887223917075551911)
      ·
        refine ⟨15490696330835875613327867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10327130887223917075551911 15490696330835875613327867)
        ·
          refine ⟨23236044496253813419991801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15490696330835875613327867 23236044496253813419991801)
          ·
            refine ⟨17427033372190360064993851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23236044496253813419991801 17427033372190360064993851)
            ·
              refine ⟨26140550058285540097490777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17427033372190360064993851 26140550058285540097490777)
              ·
                refine ⟨19605412543714155073118083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26140550058285540097490777 19605412543714155073118083)
                ·
                  refine ⟨29408118815571232609677125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19605412543714155073118083 29408118815571232609677125)
                  ·
                    refine ⟨5514022277919606114314461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29408118815571232609677125 5514022277919606114314461)
                    ·
                      refine ⟨2067758354219852292867923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5514022277919606114314461 2067758354219852292867923)
                      ·
                        rfl

theorem cell23_4026945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 2, 1, 4, 3].length) (baseStart_4026945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4026945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4026945 prefixEnd_4026945 := by exact prefixLift 4026945
  have htrace : WordTrace (prefixWord ++ tailWord_4026945) baseStart_4026945 baseEnd_4026945 := by
    simpa [prefixWord, tailWord_4026945, baseEnd_4026945] using wordTrace_append hprefix tailTrace_4026945
  have hstable : (prefixWord ++ tailWord_4026945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4026945).length < 2 ^ (prefixWord ++ tailWord_4026945).sum := by decide
  have hdescent : baseEnd_4026945 < baseStart_4026945 := by decide
  rcases family_descends (prefixWord ++ tailWord_4026945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4026975 : List Nat := [1, 1, 2, 3, 1, 1, 1, 4, 5, 1, 3]
def baseStart_4026975 : Nat := 118140960795 + 4026975 * 2 ^ 59
def prefixEnd_4026975 : Nat := 4983230072969 + 3 ^ 40 * 4026975 * 2
def baseEnd_4026975 : Nat := 2067773758639487175492785

theorem tailTrace_4026975 : CollatzResearch.WordTrace tailWord_4026975 prefixEnd_4026975 2067773758639487175492785 := by
  unfold tailWord_4026975
  simp only [CollatzResearch.WordTrace]
  refine ⟨146875844585964802420330379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97917229723976534946886919 146875844585964802420330379)
  ·
    refine ⟨220313766878947203630495569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146875844585964802420330379 220313766878947203630495569)
    ·
      refine ⟨165235325159210402722871677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220313766878947203630495569 165235325159210402722871677)
      ·
        refine ⟨61963246934703901021076879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165235325159210402722871677 61963246934703901021076879)
        ·
          refine ⟨92944870402055851531615319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61963246934703901021076879 92944870402055851531615319)
          ·
            refine ⟨139417305603083777297422979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92944870402055851531615319 139417305603083777297422979)
            ·
              refine ⟨209125958404625665946134469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139417305603083777297422979 209125958404625665946134469)
              ·
                refine ⟨39211117200867312364900213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 209125958404625665946134469 39211117200867312364900213)
                ·
                  refine ⟨3676042237581310534209395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39211117200867312364900213 3676042237581310534209395)
                  ·
                    refine ⟨5514063356371965801314093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3676042237581310534209395 5514063356371965801314093)
                    ·
                      refine ⟨2067773758639487175492785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5514063356371965801314093 2067773758639487175492785)
                      ·
                        rfl

theorem cell23_4026975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 4, 5, 1, 3].length) (baseStart_4026975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4026975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4026975 prefixEnd_4026975 := by exact prefixLift 4026975
  have htrace : WordTrace (prefixWord ++ tailWord_4026975) baseStart_4026975 baseEnd_4026975 := by
    simpa [prefixWord, tailWord_4026975, baseEnd_4026975] using wordTrace_append hprefix tailTrace_4026975
  have hstable : (prefixWord ++ tailWord_4026975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4026975).length < 2 ^ (prefixWord ++ tailWord_4026975).sum := by decide
  have hdescent : baseEnd_4026975 < baseStart_4026975 := by decide
  rcases family_descends (prefixWord ++ tailWord_4026975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
