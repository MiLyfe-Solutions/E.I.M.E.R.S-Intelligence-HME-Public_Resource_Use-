import V185TrunkScan22Chunk288

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2577312 : List Nat := [2, 1, 1, 4, 1, 1, 2, 10]
def baseStart_2577312 : Nat := 118140960795 + 2577312 * 2 ^ 59
def prefixEnd_2577312 : Nat := 4983230072969 + 3 ^ 40 * 2577312 * 2
def baseEnd_2577312 : Nat := 98029618711164851010901

theorem tailTrace_2577312 : CollatzResearch.WordTrace tailWord_2577312 prefixEnd_2577312 98029618711164851010901 := by
  unfold tailWord_2577312
  simp only [CollatzResearch.WordTrace]
  refine ⟨47001145619423134345499095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62668194159230845793998793 47001145619423134345499095)
  ·
    refine ⟨70501718429134701518248643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47001145619423134345499095 70501718429134701518248643)
    ·
      refine ⟨105752577643702052277372965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70501718429134701518248643 105752577643702052277372965)
      ·
        refine ⟨19828608308194134802007431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 105752577643702052277372965 19828608308194134802007431)
        ·
          refine ⟨29742912462291202203011147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19828608308194134802007431 29742912462291202203011147)
          ·
            refine ⟨44614368693436803304516721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29742912462291202203011147 44614368693436803304516721)
            ·
              refine ⟨33460776520077602478387541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44614368693436803304516721 33460776520077602478387541)
              ·
                refine ⟨98029618711164851010901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 33460776520077602478387541 98029618711164851010901)
                ·
                  rfl

theorem cell22_2577312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 10].length) (baseStart_2577312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2577312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2577312 prefixEnd_2577312 := by exact prefixLift 2577312
  have htrace : WordTrace (prefixWord ++ tailWord_2577312) baseStart_2577312 baseEnd_2577312 := by
    simpa [prefixWord, tailWord_2577312, baseEnd_2577312] using wordTrace_append hprefix tailTrace_2577312
  have hstable : (prefixWord ++ tailWord_2577312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2577312).length < 2 ^ (prefixWord ++ tailWord_2577312).sum := by decide
  have hdescent : baseEnd_2577312 < baseStart_2577312 := by decide
  rcases family_descends (prefixWord ++ tailWord_2577312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2577329 : List Nat := [1, 2, 2, 4, 3, 1, 9]
def baseStart_2577329 : Nat := 118140960795 + 2577329 * 2 ^ 59
def prefixEnd_2577329 : Nat := 4983230072969 + 3 ^ 40 * 2577329 * 2
def baseEnd_2577329 : Nat := 32676755105477825237891

theorem tailTrace_2577329 : CollatzResearch.WordTrace tailWord_2577329 prefixEnd_2577329 32676755105477825237891 := by
  unfold tailWord_2577329
  simp only [CollatzResearch.WordTrace]
  refine ⟨94002911279784680594367041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62668607519856453729578027 94002911279784680594367041)
  ·
    refine ⟨70502183459838510445775281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94002911279784680594367041 70502183459838510445775281)
    ·
      refine ⟨52876637594878882834331461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70502183459838510445775281 52876637594878882834331461)
      ·
        refine ⟨9914369549039790531437149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52876637594878882834331461 9914369549039790531437149)
        ·
          refine ⟨3717888580889921449288931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9914369549039790531437149 3717888580889921449288931)
          ·
            refine ⟨5576832871334882173933397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3717888580889921449288931 5576832871334882173933397)
            ·
              refine ⟨32676755105477825237891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5576832871334882173933397 32676755105477825237891)
              ·
                rfl

theorem cell22_2577329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 9].length) (baseStart_2577329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2577329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2577329 prefixEnd_2577329 := by exact prefixLift 2577329
  have htrace : WordTrace (prefixWord ++ tailWord_2577329) baseStart_2577329 baseEnd_2577329 := by
    simpa [prefixWord, tailWord_2577329, baseEnd_2577329] using wordTrace_append hprefix tailTrace_2577329
  have hstable : (prefixWord ++ tailWord_2577329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2577329).length < 2 ^ (prefixWord ++ tailWord_2577329).sum := by decide
  have hdescent : baseEnd_2577329 < baseStart_2577329 := by decide
  rcases family_descends (prefixWord ++ tailWord_2577329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2577468 : List Nat := [2, 2, 2, 2, 2, 2, 2, 3, 2, 3]
def baseStart_2577468 : Nat := 118140960795 + 2577468 * 2 ^ 59
def prefixEnd_2577468 : Nat := 4983230072969 + 3 ^ 40 * 2577468 * 2
def baseEnd_2577468 : Nat := 882319970388551252197631

theorem tailTrace_2577468 : CollatzResearch.WordTrace tailWord_2577468 prefixEnd_2577468 882319970388551252197631 := by
  unfold tailWord_2577468
  simp only [CollatzResearch.WordTrace]
  refine ⟨47003990513140553666838529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62671987350854071555784705 47003990513140553666838529)
  ·
    refine ⟨35252992884855415250128897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47003990513140553666838529 35252992884855415250128897)
    ·
      refine ⟨26439744663641561437596673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35252992884855415250128897 26439744663641561437596673)
      ·
        refine ⟨19829808497731171078197505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26439744663641561437596673 19829808497731171078197505)
        ·
          refine ⟨14872356373298378308648129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19829808497731171078197505 14872356373298378308648129)
          ·
            refine ⟨11154267279973783731486097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14872356373298378308648129 11154267279973783731486097)
            ·
              refine ⟨8365700459980337798614573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11154267279973783731486097 8365700459980337798614573)
              ·
                refine ⟨3137137672492626674480465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8365700459980337798614573 3137137672492626674480465)
                ·
                  refine ⟨2352853254369470005860349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3137137672492626674480465 2352853254369470005860349)
                  ·
                    refine ⟨882319970388551252197631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2352853254369470005860349 882319970388551252197631)
                    ·
                      rfl

theorem cell22_2577468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 3, 2, 3].length) (baseStart_2577468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2577468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2577468 prefixEnd_2577468 := by exact prefixLift 2577468
  have htrace : WordTrace (prefixWord ++ tailWord_2577468) baseStart_2577468 baseEnd_2577468 := by
    simpa [prefixWord, tailWord_2577468, baseEnd_2577468] using wordTrace_append hprefix tailTrace_2577468
  have hstable : (prefixWord ++ tailWord_2577468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2577468).length < 2 ^ (prefixWord ++ tailWord_2577468).sum := by decide
  have hdescent : baseEnd_2577468 < baseStart_2577468 := by decide
  rcases family_descends (prefixWord ++ tailWord_2577468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2577496 : List Nat := [2, 1, 2, 2, 1, 3, 1, 2, 5, 3]
def baseStart_2577496 : Nat := 118140960795 + 2577496 * 2 ^ 59
def prefixEnd_2577496 : Nat := 4983230072969 + 3 ^ 40 * 2577496 * 2
def baseEnd_2577496 : Nat := 882329555360768512497545

theorem tailTrace_2577496 : CollatzResearch.WordTrace tailWord_2577496 prefixEnd_2577496 882329555360768512497545 := by
  unfold tailWord_2577496
  simp only [CollatzResearch.WordTrace]
  refine ⟨47004501135089834057848171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62672668180119778743797561 47004501135089834057848171)
  ·
    refine ⟨70506751702634751086772257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47004501135089834057848171 70506751702634751086772257)
    ·
      refine ⟨52880063776976063315079193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70506751702634751086772257 52880063776976063315079193)
      ·
        refine ⟨39660047832732047486309395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52880063776976063315079193 39660047832732047486309395)
        ·
          refine ⟨59490071749098071229464093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39660047832732047486309395 59490071749098071229464093)
          ·
            refine ⟨22308776905911776711049035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59490071749098071229464093 22308776905911776711049035)
            ·
              refine ⟨33463165358867665066573553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22308776905911776711049035 33463165358867665066573553)
              ·
                refine ⟨25097374019150748799930165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33463165358867665066573553 25097374019150748799930165)
                ·
                  refine ⟨2352878814295382699993453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25097374019150748799930165 2352878814295382699993453)
                  ·
                    refine ⟨882329555360768512497545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2352878814295382699993453 882329555360768512497545)
                    ·
                      rfl

theorem cell22_2577496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 2, 5, 3].length) (baseStart_2577496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2577496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2577496 prefixEnd_2577496 := by exact prefixLift 2577496
  have htrace : WordTrace (prefixWord ++ tailWord_2577496) baseStart_2577496 baseEnd_2577496 := by
    simpa [prefixWord, tailWord_2577496, baseEnd_2577496] using wordTrace_append hprefix tailTrace_2577496
  have hstable : (prefixWord ++ tailWord_2577496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2577496).length < 2 ^ (prefixWord ++ tailWord_2577496).sum := by decide
  have hdescent : baseEnd_2577496 < baseStart_2577496 := by decide
  rcases family_descends (prefixWord ++ tailWord_2577496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2577502 : List Nat := [4, 4, 1, 1, 1, 2, 1, 1, 4, 3]
def baseStart_2577502 : Nat := 118140960795 + 2577502 * 2 ^ 59
def prefixEnd_2577502 : Nat := 4983230072969 + 3 ^ 40 * 2577502 * 2
def baseEnd_2577502 : Nat := 882331609283386496847527

theorem tailTrace_2577502 : CollatzResearch.WordTrace tailWord_2577502 prefixEnd_2577502 882331609283386496847527 := by
  unfold tailWord_2577502
  simp only [CollatzResearch.WordTrace]
  refine ⟨11751152638519741392551845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62672814072105287426943173 11751152638519741392551845)
  ·
    refine ⟨2203341119722451511103471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11751152638519741392551845 2203341119722451511103471)
    ·
      refine ⟨3305011679583677266655207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2203341119722451511103471 3305011679583677266655207)
      ·
        refine ⟨4957517519375515899982811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3305011679583677266655207 4957517519375515899982811)
        ·
          refine ⟨7436276279063273849974217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4957517519375515899982811 7436276279063273849974217)
          ·
            refine ⟨5577207209297455387480663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7436276279063273849974217 5577207209297455387480663)
            ·
              refine ⟨8365810813946183081220995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5577207209297455387480663 8365810813946183081220995)
              ·
                refine ⟨12548716220919274621831493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8365810813946183081220995 12548716220919274621831493)
                ·
                  refine ⟨2352884291422363991593405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12548716220919274621831493 2352884291422363991593405)
                  ·
                    refine ⟨882331609283386496847527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2352884291422363991593405 882331609283386496847527)
                    ·
                      rfl

theorem cell22_2577502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_2577502 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2577502 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2577502 prefixEnd_2577502 := by exact prefixLift 2577502
  have htrace : WordTrace (prefixWord ++ tailWord_2577502) baseStart_2577502 baseEnd_2577502 := by
    simpa [prefixWord, tailWord_2577502, baseEnd_2577502] using wordTrace_append hprefix tailTrace_2577502
  have hstable : (prefixWord ++ tailWord_2577502).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2577502).length < 2 ^ (prefixWord ++ tailWord_2577502).sum := by decide
  have hdescent : baseEnd_2577502 < baseStart_2577502 := by decide
  rcases family_descends (prefixWord ++ tailWord_2577502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2577513 : List Nat := [1, 2, 1, 1, 1, 7, 2, 1, 3, 3]
def baseStart_2577513 : Nat := 118140960795 + 2577513 * 2 ^ 59
def prefixEnd_2577513 : Nat := 4983230072969 + 3 ^ 40 * 2577513 * 2
def baseEnd_2577513 : Nat := 882335374808186134822493

theorem tailTrace_2577513 : CollatzResearch.WordTrace tailWord_2577513 prefixEnd_2577513 882335374808186134822493 := by
  unfold tailWord_2577513
  simp only [CollatzResearch.WordTrace]
  refine ⟨94009622311118080019065193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62673081540745386679376795 94009622311118080019065193)
  ·
    refine ⟨70507216733338560014298895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94009622311118080019065193 70507216733338560014298895)
    ·
      refine ⟨105760825100007840021448343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70507216733338560014298895 105760825100007840021448343)
      ·
        refine ⟨158641237650011760032172515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105760825100007840021448343 158641237650011760032172515)
        ·
          refine ⟨237961856475017640048258773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158641237650011760032172515 237961856475017640048258773)
          ·
            refine ⟨5577231011133225938631065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 237961856475017640048258773 5577231011133225938631065)
            ·
              refine ⟨4182923258349919453973299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5577231011133225938631065 4182923258349919453973299)
              ·
                refine ⟨6274384887524879180959949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4182923258349919453973299 6274384887524879180959949)
                ·
                  refine ⟨2352894332821829692859981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6274384887524879180959949 2352894332821829692859981)
                  ·
                    refine ⟨882335374808186134822493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2352894332821829692859981 882335374808186134822493)
                    ·
                      rfl

theorem cell22_2577513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 2, 1, 3, 3].length) (baseStart_2577513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2577513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2577513 prefixEnd_2577513 := by exact prefixLift 2577513
  have htrace : WordTrace (prefixWord ++ tailWord_2577513) baseStart_2577513 baseEnd_2577513 := by
    simpa [prefixWord, tailWord_2577513, baseEnd_2577513] using wordTrace_append hprefix tailTrace_2577513
  have hstable : (prefixWord ++ tailWord_2577513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2577513).length < 2 ^ (prefixWord ++ tailWord_2577513).sum := by decide
  have hdescent : baseEnd_2577513 < baseStart_2577513 := by decide
  rcases family_descends (prefixWord ++ tailWord_2577513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2577618 : List Nat := [3, 2, 2, 2, 1, 1, 1, 4, 2, 4]
def baseStart_2577618 : Nat := 118140960795 + 2577618 * 2 ^ 59
def prefixEnd_2577618 : Nat := 4983230072969 + 3 ^ 40 * 2577618 * 2
def baseEnd_2577618 : Nat := 882371318454000860947171

theorem tailTrace_2577618 : CollatzResearch.WordTrace tailWord_2577618 prefixEnd_2577618 882371318454000860947171 := by
  unfold tailWord_2577618
  simp only [CollatzResearch.WordTrace]
  refine ⟨23503362993934420737909377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62675634650491788634425005 23503362993934420737909377)
  ·
    refine ⟨17627522245450815553432033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23503362993934420737909377 17627522245450815553432033)
    ·
      refine ⟨13220641684088111665074025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17627522245450815553432033 13220641684088111665074025)
      ·
        refine ⟨9915481263066083748805519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13220641684088111665074025 9915481263066083748805519)
        ·
          refine ⟨14873221894599125623208279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9915481263066083748805519 14873221894599125623208279)
          ·
            refine ⟨22309832841898688434812419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14873221894599125623208279 22309832841898688434812419)
            ·
              refine ⟨33464749262848032652218629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22309832841898688434812419 33464749262848032652218629)
              ·
                refine ⟨6274640486784006122290993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33464749262848032652218629 6274640486784006122290993)
                ·
                  refine ⟨4705980365088004591718245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6274640486784006122290993 4705980365088004591718245)
                  ·
                    refine ⟨882371318454000860947171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4705980365088004591718245 882371318454000860947171)
                    ·
                      rfl

theorem cell22_2577618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 4, 2, 4].length) (baseStart_2577618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2577618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2577618 prefixEnd_2577618 := by exact prefixLift 2577618
  have htrace : WordTrace (prefixWord ++ tailWord_2577618) baseStart_2577618 baseEnd_2577618 := by
    simpa [prefixWord, tailWord_2577618, baseEnd_2577618] using wordTrace_append hprefix tailTrace_2577618
  have hstable : (prefixWord ++ tailWord_2577618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2577618).length < 2 ^ (prefixWord ++ tailWord_2577618).sum := by decide
  have hdescent : baseEnd_2577618 < baseStart_2577618 := by decide
  rcases family_descends (prefixWord ++ tailWord_2577618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2577633 : List Nat := [1, 2, 3, 1, 3, 4, 1, 7]
def baseStart_2577633 : Nat := 118140960795 + 2577633 * 2 ^ 59
def prefixEnd_2577633 : Nat := 4983230072969 + 3 ^ 40 * 2577633 * 2
def baseEnd_2577633 : Nat := 98041828140060646869125

theorem tailTrace_2577633 : CollatzResearch.WordTrace tailWord_2577633 prefixEnd_2577633 98041828140060646869125 := by
  unfold tailWord_2577633
  simp only [CollatzResearch.WordTrace]
  refine ⟨94013999070683340513433553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62675999380455560342289035 94013999070683340513433553)
  ·
    refine ⟨70510499303012505385075165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94013999070683340513433553 70510499303012505385075165)
    ·
      refine ⟨26441437238629689519403187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70510499303012505385075165 26441437238629689519403187)
      ·
        refine ⟨39662155857944534279104781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26441437238629689519403187 39662155857944534279104781)
        ·
          refine ⟨14873308446729200354664293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39662155857944534279104781 14873308446729200354664293)
          ·
            refine ⟨2788745333761725066499555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14873308446729200354664293 2788745333761725066499555)
            ·
              refine ⟨4183118000642587599749333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2788745333761725066499555 4183118000642587599749333)
              ·
                refine ⟨98041828140060646869125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4183118000642587599749333 98041828140060646869125)
                ·
                  rfl

theorem cell22_2577633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 1, 7].length) (baseStart_2577633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2577633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2577633 prefixEnd_2577633 := by exact prefixLift 2577633
  have htrace : WordTrace (prefixWord ++ tailWord_2577633) baseStart_2577633 baseEnd_2577633 := by
    simpa [prefixWord, tailWord_2577633, baseEnd_2577633] using wordTrace_append hprefix tailTrace_2577633
  have hstable : (prefixWord ++ tailWord_2577633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2577633).length < 2 ^ (prefixWord ++ tailWord_2577633).sum := by decide
  have hdescent : baseEnd_2577633 < baseStart_2577633 := by decide
  rcases family_descends (prefixWord ++ tailWord_2577633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2577650 : List Nat := [3, 2, 1, 3, 3, 1, 3, 6]
def baseStart_2577650 : Nat := 118140960795 + 2577650 * 2 ^ 59
def prefixEnd_2577650 : Nat := 4983230072969 + 3 ^ 40 * 2577650 * 2
def baseEnd_2577650 : Nat := 98042474745329271571897

theorem tailTrace_2577650 : CollatzResearch.WordTrace tailWord_2577650 prefixEnd_2577650 98042474745329271571897 := by
  unfold tailWord_2577650
  simp only [CollatzResearch.WordTrace]
  refine ⟨23503654777905438104200601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62676412741081168277868269 23503654777905438104200601)
  ·
    refine ⟨17627741083429078578150451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23503654777905438104200601 17627741083429078578150451)
    ·
      refine ⟨26441611625143617867225677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17627741083429078578150451 26441611625143617867225677)
      ·
        refine ⟨9915604359428856700209629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26441611625143617867225677 9915604359428856700209629)
        ·
          refine ⟨3718351634785821262578611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9915604359428856700209629 3718351634785821262578611)
          ·
            refine ⟨5577527452178731893867917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3718351634785821262578611 5577527452178731893867917)
            ·
              refine ⟨2091572794567024460200469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5577527452178731893867917 2091572794567024460200469)
              ·
                refine ⟨98042474745329271571897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2091572794567024460200469 98042474745329271571897)
                ·
                  rfl

theorem cell22_2577650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 3, 6].length) (baseStart_2577650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2577650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2577650 prefixEnd_2577650 := by exact prefixLift 2577650
  have htrace : WordTrace (prefixWord ++ tailWord_2577650) baseStart_2577650 baseEnd_2577650 := by
    simpa [prefixWord, tailWord_2577650, baseEnd_2577650] using wordTrace_append hprefix tailTrace_2577650
  have hstable : (prefixWord ++ tailWord_2577650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2577650).length < 2 ^ (prefixWord ++ tailWord_2577650).sum := by decide
  have hdescent : baseEnd_2577650 < baseStart_2577650 := by decide
  rcases family_descends (prefixWord ++ tailWord_2577650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2577678 : List Nat := [4, 1, 1, 2, 1, 4, 1, 1, 7]
def baseStart_2577678 : Nat := 118140960795 + 2577678 * 2 ^ 59
def prefixEnd_2577678 : Nat := 4983230072969 + 3 ^ 40 * 2577678 * 2
def baseEnd_2577678 : Nat := 294130619226726901482329

theorem tailTrace_2577678 : CollatzResearch.WordTrace tailWord_2577678 prefixEnd_2577678 294130619226726901482329 := by
  unfold tailWord_2577678
  simp only [CollatzResearch.WordTrace]
  refine ⟨11751955044440039149852711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62677093570346875465881125 11751955044440039149852711)
  ·
    refine ⟨17627932566660058724779067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11751955044440039149852711 17627932566660058724779067)
    ·
      refine ⟨26441898849990088087168601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17627932566660058724779067 26441898849990088087168601)
      ·
        refine ⟨19831424137492566065376451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26441898849990088087168601 19831424137492566065376451)
        ·
          refine ⟨29747136206238849098064677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19831424137492566065376451 29747136206238849098064677)
          ·
            refine ⟨5577588038669784205887127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29747136206238849098064677 5577588038669784205887127)
            ·
              refine ⟨8366382058004676308830691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5577588038669784205887127 8366382058004676308830691)
              ·
                refine ⟨12549573087007014463246037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8366382058004676308830691 12549573087007014463246037)
                ·
                  refine ⟨294130619226726901482329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12549573087007014463246037 294130619226726901482329)
                  ·
                    rfl

theorem cell22_2577678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 1, 7].length) (baseStart_2577678 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2577678 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2577678 prefixEnd_2577678 := by exact prefixLift 2577678
  have htrace : WordTrace (prefixWord ++ tailWord_2577678) baseStart_2577678 baseEnd_2577678 := by
    simpa [prefixWord, tailWord_2577678, baseEnd_2577678] using wordTrace_append hprefix tailTrace_2577678
  have hstable : (prefixWord ++ tailWord_2577678).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2577678).length < 2 ^ (prefixWord ++ tailWord_2577678).sum := by decide
  have hdescent : baseEnd_2577678 < baseStart_2577678 := by decide
  rcases family_descends (prefixWord ++ tailWord_2577678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2577740 : List Nat := [2, 2, 1, 3, 2, 4, 1, 1, 6]
def baseStart_2577740 : Nat := 118140960795 + 2577740 * 2 ^ 59
def prefixEnd_2577740 : Nat := 4983230072969 + 3 ^ 40 * 2577740 * 2
def baseEnd_2577740 : Nat := 294137693849077736465599

theorem tailTrace_2577740 : CollatzResearch.WordTrace tailWord_2577740 prefixEnd_2577740 294137693849077736465599 := by
  unfold tailWord_2577740
  simp only [CollatzResearch.WordTrace]
  refine ⟨47008950840647848893789337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62678601120863798525052449 47008950840647848893789337)
  ·
    refine ⟨35256713130485886670342003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47008950840647848893789337 35256713130485886670342003)
    ·
      refine ⟨52885069695728830005513005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35256713130485886670342003 52885069695728830005513005)
      ·
        refine ⟨19831901135898311252067377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52885069695728830005513005 19831901135898311252067377)
        ·
          refine ⟨14873925851923733439050533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19831901135898311252067377 14873925851923733439050533)
          ·
            refine ⟨2788861097235700019821975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14873925851923733439050533 2788861097235700019821975)
            ·
              refine ⟨4183291645853550029732963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2788861097235700019821975 4183291645853550029732963)
              ·
                refine ⟨6274937468780325044599445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4183291645853550029732963 6274937468780325044599445)
                ·
                  refine ⟨294137693849077736465599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6274937468780325044599445 294137693849077736465599)
                  ·
                    rfl

theorem cell22_2577740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 1, 1, 6].length) (baseStart_2577740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2577740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2577740 prefixEnd_2577740 := by exact prefixLift 2577740
  have htrace : WordTrace (prefixWord ++ tailWord_2577740) baseStart_2577740 baseEnd_2577740 := by
    simpa [prefixWord, tailWord_2577740, baseEnd_2577740] using wordTrace_append hprefix tailTrace_2577740
  have hstable : (prefixWord ++ tailWord_2577740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2577740).length < 2 ^ (prefixWord ++ tailWord_2577740).sum := by decide
  have hdescent : baseEnd_2577740 < baseStart_2577740 := by decide
  rcases family_descends (prefixWord ++ tailWord_2577740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2577828 : List Nat := [2, 3, 1, 2, 1, 1, 1, 1, 3, 7]
def baseStart_2577828 : Nat := 118140960795 + 2577828 * 2 ^ 59
def prefixEnd_2577828 : Nat := 4983230072969 + 3 ^ 40 * 2577828 * 2
def baseEnd_2577828 : Nat := 882443205745630313196527

theorem tailTrace_2577828 : CollatzResearch.WordTrace tailWord_2577828 prefixEnd_2577828 882443205745630313196527 := by
  unfold tailWord_2577828
  simp only [CollatzResearch.WordTrace]
  refine ⟨47010555652488444408391069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62680740869984592544521425 47010555652488444408391069)
  ·
    refine ⟨17628958369683166653146651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47010555652488444408391069 17628958369683166653146651)
    ·
      refine ⟨26443437554524749979719977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17628958369683166653146651 26443437554524749979719977)
      ·
        refine ⟨19832578165893562484789983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26443437554524749979719977 19832578165893562484789983)
        ·
          refine ⟨29748867248840343727184975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19832578165893562484789983 29748867248840343727184975)
          ·
            refine ⟨44623300873260515590777463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29748867248840343727184975 44623300873260515590777463)
            ·
              refine ⟨66934951309890773386166195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44623300873260515590777463 66934951309890773386166195)
              ·
                refine ⟨100402426964836160079249293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66934951309890773386166195 100402426964836160079249293)
                ·
                  refine ⟨37650910111813560029718485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 100402426964836160079249293 37650910111813560029718485)
                  ·
                    refine ⟨882443205745630313196527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37650910111813560029718485 882443205745630313196527)
                    ·
                      rfl

theorem cell22_2577828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 3, 7].length) (baseStart_2577828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2577828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2577828 prefixEnd_2577828 := by exact prefixLift 2577828
  have htrace : WordTrace (prefixWord ++ tailWord_2577828) baseStart_2577828 baseEnd_2577828 := by
    simpa [prefixWord, tailWord_2577828, baseEnd_2577828] using wordTrace_append hprefix tailTrace_2577828
  have hstable : (prefixWord ++ tailWord_2577828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2577828).length < 2 ^ (prefixWord ++ tailWord_2577828).sum := by decide
  have hdescent : baseEnd_2577828 < baseStart_2577828 := by decide
  rcases family_descends (prefixWord ++ tailWord_2577828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2577845 : List Nat := [1, 3, 3, 2, 2, 1, 1, 2, 2, 5]
def baseStart_2577845 : Nat := 118140960795 + 2577845 * 2 ^ 59
def prefixEnd_2577845 : Nat := 4983230072969 + 3 ^ 40 * 2577845 * 2
def baseEnd_2577845 : Nat := 882449025193047935521475

theorem tailTrace_2577845 : CollatzResearch.WordTrace tailWord_2577845 prefixEnd_2577845 882449025193047935521475 := by
  unfold tailWord_2577845
  simp only [CollatzResearch.WordTrace]
  refine ⟨94021731345915300720150989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62681154230610200480100659 94021731345915300720150989)
  ·
    refine ⟨35258149254718237770056621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94021731345915300720150989 35258149254718237770056621)
    ·
      refine ⟨13221805970519339163771233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35258149254718237770056621 13221805970519339163771233)
      ·
        refine ⟨9916354477889504372828425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13221805970519339163771233 9916354477889504372828425)
        ·
          refine ⟨7437265858417128279621319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9916354477889504372828425 7437265858417128279621319)
          ·
            refine ⟨11155898787625692419431979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7437265858417128279621319 11155898787625692419431979)
            ·
              refine ⟨16733848181438538629147969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11155898787625692419431979 16733848181438538629147969)
              ·
                refine ⟨12550386136078903971860977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16733848181438538629147969 12550386136078903971860977)
                ·
                  refine ⟨9412789602059177978895733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12550386136078903971860977 9412789602059177978895733)
                  ·
                    refine ⟨882449025193047935521475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9412789602059177978895733 882449025193047935521475)
                    ·
                      rfl

theorem cell22_2577845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 2, 2, 5].length) (baseStart_2577845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2577845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2577845 prefixEnd_2577845 := by exact prefixLift 2577845
  have htrace : WordTrace (prefixWord ++ tailWord_2577845) baseStart_2577845 baseEnd_2577845 := by
    simpa [prefixWord, tailWord_2577845, baseEnd_2577845] using wordTrace_append hprefix tailTrace_2577845
  have hstable : (prefixWord ++ tailWord_2577845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2577845).length < 2 ^ (prefixWord ++ tailWord_2577845).sum := by decide
  have hdescent : baseEnd_2577845 < baseStart_2577845 := by decide
  rcases family_descends (prefixWord ++ tailWord_2577845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2577877 : List Nat := [1, 3, 2, 3, 1, 1, 4, 2, 1, 4]
def baseStart_2577877 : Nat := 118140960795 + 2577877 * 2 ^ 59
def prefixEnd_2577877 : Nat := 4983230072969 + 3 ^ 40 * 2577877 * 2
def baseEnd_2577877 : Nat := 882459979447010518721377

theorem tailTrace_2577877 : CollatzResearch.WordTrace tailWord_2577877 prefixEnd_2577877 882459979447010518721377 := by
  unfold tailWord_2577877
  simp only [CollatzResearch.WordTrace]
  refine ⟨94022898481799370185315885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62681932321199580123543923 94022898481799370185315885)
  ·
    refine ⟨35258586930674763819493457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94022898481799370185315885 35258586930674763819493457)
    ·
      refine ⟨26443940198006072864620093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35258586930674763819493457 26443940198006072864620093)
      ·
        refine ⟨9916477574252277324232535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26443940198006072864620093 9916477574252277324232535)
        ·
          refine ⟨14874716361378415986348803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9916477574252277324232535 14874716361378415986348803)
          ·
            refine ⟨22312074542067623979523205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14874716361378415986348803 22312074542067623979523205)
            ·
              refine ⟨4183513976637679496160601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22312074542067623979523205 4183513976637679496160601)
              ·
                refine ⟨3137635482478259622120451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4183513976637679496160601 3137635482478259622120451)
                ·
                  refine ⟨4706453223717389433180677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3137635482478259622120451 4706453223717389433180677)
                  ·
                    refine ⟨882459979447010518721377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4706453223717389433180677 882459979447010518721377)
                    ·
                      rfl

theorem cell22_2577877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 4, 2, 1, 4].length) (baseStart_2577877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2577877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2577877 prefixEnd_2577877 := by exact prefixLift 2577877
  have htrace : WordTrace (prefixWord ++ tailWord_2577877) baseStart_2577877 baseEnd_2577877 := by
    simpa [prefixWord, tailWord_2577877, baseEnd_2577877] using wordTrace_append hprefix tailTrace_2577877
  have hstable : (prefixWord ++ tailWord_2577877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2577877).length < 2 ^ (prefixWord ++ tailWord_2577877).sum := by decide
  have hdescent : baseEnd_2577877 < baseStart_2577877 := by decide
  rcases family_descends (prefixWord ++ tailWord_2577877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2577903 : List Nat := [1, 1, 2, 1, 4, 1, 12]
def baseStart_2577903 : Nat := 118140960795 + 2577903 * 2 ^ 59
def prefixEnd_2577903 : Nat := 4983230072969 + 3 ^ 40 * 2577903 * 2
def baseEnd_2577903 : Nat := 32684032584383522873011

theorem tailTrace_2577903 : CollatzResearch.WordTrace tailWord_2577903 prefixEnd_2577903 32684032584383522873011 := by
  unfold tailWord_2577903
  simp only [CollatzResearch.WordTrace]
  refine ⟨94023846779705176625762363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62682564519803451083841575 94023846779705176625762363)
  ·
    refine ⟨141035770169557764938643545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94023846779705176625762363 141035770169557764938643545)
    ·
      refine ⟨105776827627168323703982659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141035770169557764938643545 105776827627168323703982659)
      ·
        refine ⟨158665241440752485555973989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105776827627168323703982659 158665241440752485555973989)
        ·
          refine ⟨29749732770141091041745123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 158665241440752485555973989 29749732770141091041745123)
          ·
            refine ⟨44624599155211636562617685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29749732770141091041745123 44624599155211636562617685)
            ·
              refine ⟨32684032584383522873011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 44624599155211636562617685 32684032584383522873011)
              ·
                rfl

theorem cell22_2577903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 12].length) (baseStart_2577903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2577903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2577903 prefixEnd_2577903 := by exact prefixLift 2577903
  have htrace : WordTrace (prefixWord ++ tailWord_2577903) baseStart_2577903 baseEnd_2577903 := by
    simpa [prefixWord, tailWord_2577903, baseEnd_2577903] using wordTrace_append hprefix tailTrace_2577903
  have hstable : (prefixWord ++ tailWord_2577903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2577903).length < 2 ^ (prefixWord ++ tailWord_2577903).sum := by decide
  have hdescent : baseEnd_2577903 < baseStart_2577903 := by decide
  rcases family_descends (prefixWord ++ tailWord_2577903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2577905 : List Nat := [1, 2, 2, 2, 3, 2, 1, 1, 4, 4]
def baseStart_2577905 : Nat := 118140960795 + 2577905 * 2 ^ 59
def prefixEnd_2577905 : Nat := 4983230072969 + 3 ^ 40 * 2577905 * 2
def baseEnd_2577905 : Nat := 882469564419227779021291

theorem tailTrace_2577905 : CollatzResearch.WordTrace tailWord_2577905 prefixEnd_2577905 882469564419227779021291 := by
  unfold tailWord_2577905
  simp only [CollatzResearch.WordTrace]
  refine ⟨94023919725697930967335169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62682613150465287311556779 94023919725697930967335169)
  ·
    refine ⟨70517939794273448225501377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94023919725697930967335169 70517939794273448225501377)
    ·
      refine ⟨52888454845705086169126033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70517939794273448225501377 52888454845705086169126033)
      ·
        refine ⟨39666341134278814626844525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52888454845705086169126033 39666341134278814626844525)
        ·
          refine ⟨14874877925354555485066697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39666341134278814626844525 14874877925354555485066697)
          ·
            refine ⟨11156158444015916613800023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14874877925354555485066697 11156158444015916613800023)
            ·
              refine ⟨16734237666023874920700035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11156158444015916613800023 16734237666023874920700035)
              ·
                refine ⟨25101356499035812381050053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16734237666023874920700035 25101356499035812381050053)
                ·
                  refine ⟨4706504343569214821446885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25101356499035812381050053 4706504343569214821446885)
                  ·
                    refine ⟨882469564419227779021291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4706504343569214821446885 882469564419227779021291)
                    ·
                      rfl

theorem cell22_2577905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 1, 4, 4].length) (baseStart_2577905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2577905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2577905 prefixEnd_2577905 := by exact prefixLift 2577905
  have htrace : WordTrace (prefixWord ++ tailWord_2577905) baseStart_2577905 baseEnd_2577905 := by
    simpa [prefixWord, tailWord_2577905, baseEnd_2577905] using wordTrace_append hprefix tailTrace_2577905
  have hstable : (prefixWord ++ tailWord_2577905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2577905).length < 2 ^ (prefixWord ++ tailWord_2577905).sum := by decide
  have hdescent : baseEnd_2577905 < baseStart_2577905 := by decide
  rcases family_descends (prefixWord ++ tailWord_2577905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2577909 : List Nat := [1, 3, 5, 1, 1, 3, 1, 1, 6]
def baseStart_2577909 : Nat := 118140960795 + 2577909 * 2 ^ 59
def prefixEnd_2577909 : Nat := 4983230072969 + 3 ^ 40 * 2577909 * 2
def baseEnd_2577909 : Nat := 294156977900324367307093

theorem tailTrace_2577909 : CollatzResearch.WordTrace tailWord_2577909 prefixEnd_2577909 294156977900324367307093 := by
  unfold tailWord_2577909
  simp only [CollatzResearch.WordTrace]
  refine ⟨94024065617683439650480781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62682710411788959766987187 94024065617683439650480781)
  ·
    refine ⟨35259024606631289868930293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94024065617683439650480781 35259024606631289868930293)
    ·
      refine ⟨3305533556871683425212215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 35259024606631289868930293 3305533556871683425212215)
      ·
        refine ⟨4958300335307525137818323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3305533556871683425212215 4958300335307525137818323)
        ·
          refine ⟨7437450502961287706727485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4958300335307525137818323 7437450502961287706727485)
          ·
            refine ⟨2789043938610482890022807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7437450502961287706727485 2789043938610482890022807)
            ·
              refine ⟨4183565907915724335034211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2789043938610482890022807 4183565907915724335034211)
              ·
                refine ⟨6275348861873586502551317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4183565907915724335034211 6275348861873586502551317)
                ·
                  refine ⟨294156977900324367307093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6275348861873586502551317 294156977900324367307093)
                  ·
                    rfl

theorem cell22_2577909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 1, 1, 6].length) (baseStart_2577909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2577909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2577909 prefixEnd_2577909 := by exact prefixLift 2577909
  have htrace : WordTrace (prefixWord ++ tailWord_2577909) baseStart_2577909 baseEnd_2577909 := by
    simpa [prefixWord, tailWord_2577909, baseEnd_2577909] using wordTrace_append hprefix tailTrace_2577909
  have hstable : (prefixWord ++ tailWord_2577909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2577909).length < 2 ^ (prefixWord ++ tailWord_2577909).sum := by decide
  have hdescent : baseEnd_2577909 < baseStart_2577909 := by decide
  rcases family_descends (prefixWord ++ tailWord_2577909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2578025 : List Nat := [1, 2, 1, 1, 1, 4, 2, 2, 3, 5]
def baseStart_2578025 : Nat := 118140960795 + 2578025 * 2 ^ 59
def prefixEnd_2578025 : Nat := 4983230072969 + 3 ^ 40 * 2578025 * 2
def baseEnd_2578025 : Nat := 882510642871587466020923

theorem tailTrace_2578025 : CollatzResearch.WordTrace tailWord_2578025 prefixEnd_2578025 882510642871587466020923 := by
  unfold tailWord_2578025
  simp only [CollatzResearch.WordTrace]
  refine ⟨94028296485263191461703529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62685530990175460974469019 94028296485263191461703529)
  ·
    refine ⟨70521222363947393596277647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94028296485263191461703529 70521222363947393596277647)
    ·
      refine ⟨105781833545921090394416471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70521222363947393596277647 105781833545921090394416471)
      ·
        refine ⟨158672750318881635591624707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105781833545921090394416471 158672750318881635591624707)
        ·
          refine ⟨238009125478322453387437061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158672750318881635591624707 238009125478322453387437061)
          ·
            refine ⟨44626711027185460010144449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 238009125478322453387437061 44626711027185460010144449)
            ·
              refine ⟨33470033270389095007608337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44626711027185460010144449 33470033270389095007608337)
              ·
                refine ⟨25102524952791821255706253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33470033270389095007608337 25102524952791821255706253)
                ·
                  refine ⟨9413446857296932970889845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25102524952791821255706253 9413446857296932970889845)
                  ·
                    refine ⟨882510642871587466020923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9413446857296932970889845 882510642871587466020923)
                    ·
                      rfl

theorem cell22_2578025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 2, 3, 5].length) (baseStart_2578025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2578025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2578025 prefixEnd_2578025 := by exact prefixLift 2578025
  have htrace : WordTrace (prefixWord ++ tailWord_2578025) baseStart_2578025 baseEnd_2578025 := by
    simpa [prefixWord, tailWord_2578025, baseEnd_2578025] using wordTrace_append hprefix tailTrace_2578025
  have hstable : (prefixWord ++ tailWord_2578025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2578025).length < 2 ^ (prefixWord ++ tailWord_2578025).sum := by decide
  have hdescent : baseEnd_2578025 < baseStart_2578025 := by decide
  rcases family_descends (prefixWord ++ tailWord_2578025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2578072 : List Nat := [2, 1, 2, 4, 1, 4, 8]
def baseStart_2578072 : Nat := 118140960795 + 2578072 * 2 ^ 59
def prefixEnd_2578072 : Nat := 4983230072969 + 3 ^ 40 * 2578072 * 2
def baseEnd_2578072 : Nat := 32686175256744259633177

theorem tailTrace_2578072 : CollatzResearch.WordTrace tailWord_2578072 prefixEnd_2578072 32686175256744259633177 := by
  unfold tailWord_2578072
  simp only [CollatzResearch.WordTrace]
  refine ⟨47015005358046459244332235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62686673810728612325776313 47015005358046459244332235)
  ·
    refine ⟨70522508037069688866498353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47015005358046459244332235 70522508037069688866498353)
    ·
      refine ⟨52891881027802266649873765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70522508037069688866498353 52891881027802266649873765)
      ·
        refine ⟨9917227692712924996851331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52891881027802266649873765 9917227692712924996851331)
        ·
          refine ⟨14875841539069387495276997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9917227692712924996851331 14875841539069387495276997)
          ·
            refine ⟨2789220288575510155364437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14875841539069387495276997 2789220288575510155364437)
            ·
              refine ⟨32686175256744259633177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2789220288575510155364437 32686175256744259633177)
              ·
                rfl

theorem cell22_2578072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 8].length) (baseStart_2578072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2578072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2578072 prefixEnd_2578072 := by exact prefixLift 2578072
  have htrace : WordTrace (prefixWord ++ tailWord_2578072) baseStart_2578072 baseEnd_2578072 := by
    simpa [prefixWord, tailWord_2578072, baseEnd_2578072] using wordTrace_append hprefix tailTrace_2578072
  have hstable : (prefixWord ++ tailWord_2578072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2578072).length < 2 ^ (prefixWord ++ tailWord_2578072).sum := by decide
  have hdescent : baseEnd_2578072 < baseStart_2578072 := by decide
  rcases family_descends (prefixWord ++ tailWord_2578072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2578078 : List Nat := [4, 3, 1, 1, 1, 3, 3, 2, 4]
def baseStart_2578078 : Nat := 118140960795 + 2578078 * 2 ^ 59
def prefixEnd_2578078 : Nat := 4983230072969 + 3 ^ 40 * 2578078 * 2
def baseEnd_2578078 : Nat := 294176261951570998148587

theorem tailTrace_2578078 : CollatzResearch.WordTrace tailWord_2578078 prefixEnd_2578078 294176261951570998148587 := by
  unfold tailWord_2578078
  simp only [CollatzResearch.WordTrace]
  refine ⟨11753778694258897689172861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62686819702714121008921925 11753778694258897689172861)
  ·
    refine ⟨4407667010347086633439823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11753778694258897689172861 4407667010347086633439823)
    ·
      refine ⟨6611500515520629950159735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4407667010347086633439823 6611500515520629950159735)
      ·
        refine ⟨9917250773280944925239603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6611500515520629950159735 9917250773280944925239603)
        ·
          refine ⟨14875876159921417387859405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9917250773280944925239603 14875876159921417387859405)
          ·
            refine ⟨5578453559970531520447277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14875876159921417387859405 5578453559970531520447277)
            ·
              refine ⟨2091920084988949320167729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5578453559970531520447277 2091920084988949320167729)
              ·
                refine ⟨1568940063741711990125797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2091920084988949320167729 1568940063741711990125797)
                ·
                  refine ⟨294176261951570998148587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1568940063741711990125797 294176261951570998148587)
                  ·
                    rfl

theorem cell22_2578078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 3, 2, 4].length) (baseStart_2578078 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2578078 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2578078 prefixEnd_2578078 := by exact prefixLift 2578078
  have htrace : WordTrace (prefixWord ++ tailWord_2578078) baseStart_2578078 baseEnd_2578078 := by
    simpa [prefixWord, tailWord_2578078, baseEnd_2578078] using wordTrace_append hprefix tailTrace_2578078
  have hstable : (prefixWord ++ tailWord_2578078).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2578078).length < 2 ^ (prefixWord ++ tailWord_2578078).sum := by decide
  have hdescent : baseEnd_2578078 < baseStart_2578078 := by decide
  rcases family_descends (prefixWord ++ tailWord_2578078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2578138 : List Nat := [3, 1, 1, 2, 2, 3, 4, 2, 1, 3]
def baseStart_2578138 : Nat := 118140960795 + 2578138 * 2 ^ 59
def prefixEnd_2578138 : Nat := 4983230072969 + 3 ^ 40 * 2578138 * 2
def baseEnd_2578138 : Nat := 882549325080892837945577

theorem tailTrace_2578138 : CollatzResearch.WordTrace tailWord_2578138 prefixEnd_2578138 882549325080892837945577 := by
  unfold tailWord_2578138
  simp only [CollatzResearch.WordTrace]
  refine ⟨23508104483463452940141767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62688278622569207840378045 23508104483463452940141767)
  ·
    refine ⟨35262156725195179410212651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23508104483463452940141767 35262156725195179410212651)
    ·
      refine ⟨52893235087792769115318977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35262156725195179410212651 52893235087792769115318977)
      ·
        refine ⟨39669926315844576836489233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52893235087792769115318977 39669926315844576836489233)
        ·
          refine ⟨29752444736883432627366925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39669926315844576836489233 29752444736883432627366925)
          ·
            refine ⟨11157166776331287235262597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29752444736883432627366925 11157166776331287235262597)
            ·
              refine ⟨2091968770562116356611737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11157166776331287235262597 2091968770562116356611737)
              ·
                refine ⟨1568976577921587267458803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2091968770562116356611737 1568976577921587267458803)
                ·
                  refine ⟨2353464866882380901188205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1568976577921587267458803 2353464866882380901188205)
                  ·
                    refine ⟨882549325080892837945577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2353464866882380901188205 882549325080892837945577)
                    ·
                      rfl

theorem cell22_2578138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 4, 2, 1, 3].length) (baseStart_2578138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2578138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2578138 prefixEnd_2578138 := by exact prefixLift 2578138
  have htrace : WordTrace (prefixWord ++ tailWord_2578138) baseStart_2578138 baseEnd_2578138 := by
    simpa [prefixWord, tailWord_2578138, baseEnd_2578138] using wordTrace_append hprefix tailTrace_2578138
  have hstable : (prefixWord ++ tailWord_2578138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2578138).length < 2 ^ (prefixWord ++ tailWord_2578138).sum := by decide
  have hdescent : baseEnd_2578138 < baseStart_2578138 := by decide
  rcases family_descends (prefixWord ++ tailWord_2578138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2578179 : List Nat := [1, 1, 1, 3, 2, 2, 3, 5, 4]
def baseStart_2578179 : Nat := 118140960795 + 2578179 * 2 ^ 59
def prefixEnd_2578179 : Nat := 4983230072969 + 3 ^ 40 * 2578179 * 2
def baseEnd_2578179 : Nat := 294187786739594132556817

theorem tailTrace_2578179 : CollatzResearch.WordTrace tailWord_2578179 prefixEnd_2578179 294187786739594132556817 := by
  unfold tailWord_2578179
  simp only [CollatzResearch.WordTrace]
  refine ⟨94033913326705275762809591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62689275551136850508539727 94033913326705275762809591)
  ·
    refine ⟨141050869990057913644214387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94033913326705275762809591 141050869990057913644214387)
    ·
      refine ⟨211576304985086870466321581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141050869990057913644214387 211576304985086870466321581)
      ·
        refine ⟨79341114369407576424870593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 211576304985086870466321581 79341114369407576424870593)
        ·
          refine ⟨59505835777055682318652945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79341114369407576424870593 59505835777055682318652945)
          ·
            refine ⟨44629376832791761738989709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59505835777055682318652945 44629376832791761738989709)
            ·
              refine ⟨16736016312296910652121141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44629376832791761738989709 16736016312296910652121141)
              ·
                refine ⟨1569001529277835373636357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16736016312296910652121141 1569001529277835373636357)
                ·
                  refine ⟨294187786739594132556817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1569001529277835373636357 294187786739594132556817)
                  ·
                    rfl

theorem cell22_2578179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 5, 4].length) (baseStart_2578179 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2578179 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2578179 prefixEnd_2578179 := by exact prefixLift 2578179
  have htrace : WordTrace (prefixWord ++ tailWord_2578179) baseStart_2578179 baseEnd_2578179 := by
    simpa [prefixWord, tailWord_2578179, baseEnd_2578179] using wordTrace_append hprefix tailTrace_2578179
  have hstable : (prefixWord ++ tailWord_2578179).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2578179).length < 2 ^ (prefixWord ++ tailWord_2578179).sum := by decide
  have hdescent : baseEnd_2578179 < baseStart_2578179 := by decide
  rcases family_descends (prefixWord ++ tailWord_2578179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2578207 : List Nat := [1, 1, 2, 4, 2, 1, 2, 9]
def baseStart_2578207 : Nat := 118140960795 + 2578207 * 2 ^ 59
def prefixEnd_2578207 : Nat := 4983230072969 + 3 ^ 40 * 2578207 * 2
def baseEnd_2578207 : Nat := 98063660576777739774485

theorem tailTrace_2578207 : CollatzResearch.WordTrace tailWord_2578207 prefixEnd_2578207 98063660576777739774485 := by
  unfold tailWord_2578207
  simp only [CollatzResearch.WordTrace]
  refine ⟨94034934570603836544828875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62689956380402557696552583 94034934570603836544828875)
  ·
    refine ⟨141052401855905754817243313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94034934570603836544828875 141052401855905754817243313)
    ·
      refine ⟨105789301391929316112932485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141052401855905754817243313 105789301391929316112932485)
      ·
        refine ⟨19835494010986746771174841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 105789301391929316112932485 19835494010986746771174841)
        ·
          refine ⟨14876620508240060078381131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19835494010986746771174841 14876620508240060078381131)
          ·
            refine ⟨22314930762360090117571697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14876620508240060078381131 22314930762360090117571697)
            ·
              refine ⟨16736198071770067588178773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22314930762360090117571697 16736198071770067588178773)
              ·
                refine ⟨98063660576777739774485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16736198071770067588178773 98063660576777739774485)
                ·
                  rfl

theorem cell22_2578207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 9].length) (baseStart_2578207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2578207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2578207 prefixEnd_2578207 := by exact prefixLift 2578207
  have htrace : WordTrace (prefixWord ++ tailWord_2578207) baseStart_2578207 baseEnd_2578207 := by
    simpa [prefixWord, tailWord_2578207, baseEnd_2578207] using wordTrace_append hprefix tailTrace_2578207
  have hstable : (prefixWord ++ tailWord_2578207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2578207).length < 2 ^ (prefixWord ++ tailWord_2578207).sum := by decide
  have hdescent : baseEnd_2578207 < baseStart_2578207 := by decide
  rcases family_descends (prefixWord ++ tailWord_2578207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2578230 : List Nat := [5, 1, 2, 2, 1, 3, 1, 3, 4]
def baseStart_2578230 : Nat := 118140960795 + 2578230 * 2 ^ 59
def prefixEnd_2578230 : Nat := 4983230072969 + 3 ^ 40 * 2578230 * 2
def baseEnd_2578230 : Nat := 294193606187011754881765

theorem tailTrace_2578230 : CollatzResearch.WordTrace tailWord_2578230 prefixEnd_2578230 294193606187011754881765 := by
  unfold tailWord_2578230
  simp only [CollatzResearch.WordTrace]
  refine ⟨5877235840595031967057259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 62690515633013674315277429 5877235840595031967057259)
  ·
    refine ⟨8815853760892547950585889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5877235840595031967057259 8815853760892547950585889)
    ·
      refine ⟨6611890320669410962939417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8815853760892547950585889 6611890320669410962939417)
      ·
        refine ⟨4958917740502058222204563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6611890320669410962939417 4958917740502058222204563)
        ·
          refine ⟨7438376610753087333306845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4958917740502058222204563 7438376610753087333306845)
          ·
            refine ⟨2789391229032407749990067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7438376610753087333306845 2789391229032407749990067)
            ·
              refine ⟨4184086843548611624985101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2789391229032407749990067 4184086843548611624985101)
              ·
                refine ⟨1569032566330729359369413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4184086843548611624985101 1569032566330729359369413)
                ·
                  refine ⟨294193606187011754881765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1569032566330729359369413 294193606187011754881765)
                  ·
                    rfl

theorem cell22_2578230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 1, 3, 4].length) (baseStart_2578230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2578230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2578230 prefixEnd_2578230 := by exact prefixLift 2578230
  have htrace : WordTrace (prefixWord ++ tailWord_2578230) baseStart_2578230 baseEnd_2578230 := by
    simpa [prefixWord, tailWord_2578230, baseEnd_2578230] using wordTrace_append hprefix tailTrace_2578230
  have hstable : (prefixWord ++ tailWord_2578230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2578230).length < 2 ^ (prefixWord ++ tailWord_2578230).sum := by decide
  have hdescent : baseEnd_2578230 < baseStart_2578230 := by decide
  rcases family_descends (prefixWord ++ tailWord_2578230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2578318 : List Nat := [4, 1, 1, 5, 1, 1, 1, 1, 2, 5]
def baseStart_2578318 : Nat := 118140960795 + 2578318 * 2 ^ 59
def prefixEnd_2578318 : Nat := 4983230072969 + 3 ^ 40 * 2578318 * 2
def baseEnd_2578318 : Nat := 882610942759432368445025

theorem tailTrace_2578318 : CollatzResearch.WordTrace tailWord_2578318 prefixEnd_2578318 882610942759432368445025 := by
  unfold tailWord_2578318
  simp only [CollatzResearch.WordTrace]
  refine ⟨11754872884150212812764951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62692655382134468334746405 11754872884150212812764951)
  ·
    refine ⟨17632309326225319219147427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11754872884150212812764951 17632309326225319219147427)
    ·
      refine ⟨26448463989337978828721141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17632309326225319219147427 26448463989337978828721141)
      ·
        refine ⟨2479543499000435515192607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26448463989337978828721141 2479543499000435515192607)
        ·
          refine ⟨3719315248500653272788911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2479543499000435515192607 3719315248500653272788911)
          ·
            refine ⟨5578972872750979909183367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3719315248500653272788911 5578972872750979909183367)
            ·
              refine ⟨8368459309126469863775051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5578972872750979909183367 8368459309126469863775051)
              ·
                refine ⟨12552688963689704795662577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8368459309126469863775051 12552688963689704795662577)
                ·
                  refine ⟨9414516722767278596746933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12552688963689704795662577 9414516722767278596746933)
                  ·
                    refine ⟨882610942759432368445025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9414516722767278596746933 882610942759432368445025)
                    ·
                      rfl

theorem cell22_2578318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 1, 2, 5].length) (baseStart_2578318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2578318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2578318 prefixEnd_2578318 := by exact prefixLift 2578318
  have htrace : WordTrace (prefixWord ++ tailWord_2578318) baseStart_2578318 baseEnd_2578318 := by
    simpa [prefixWord, tailWord_2578318, baseEnd_2578318] using wordTrace_append hprefix tailTrace_2578318
  have hstable : (prefixWord ++ tailWord_2578318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2578318).length < 2 ^ (prefixWord ++ tailWord_2578318).sum := by decide
  have hdescent : baseEnd_2578318 < baseStart_2578318 := by decide
  rcases family_descends (prefixWord ++ tailWord_2578318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2578329 : List Nat := [1, 2, 1, 2, 1, 3, 3, 3, 1, 5]
def baseStart_2578329 : Nat := 118140960795 + 2578329 * 2 ^ 59
def prefixEnd_2578329 : Nat := 4983230072969 + 3 ^ 40 * 2578329 * 2
def baseEnd_2578329 : Nat := 882614708284232006419991

theorem tailTrace_2578329 : CollatzResearch.WordTrace tailWord_2578329 prefixEnd_2578329 882614708284232006419991 := by
  unfold tailWord_2578329
  simp only [CollatzResearch.WordTrace]
  refine ⟨94039384276161851380770041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62692922850774567587180027 94039384276161851380770041)
  ·
    refine ⟨70529538207121388535577531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94039384276161851380770041 70529538207121388535577531)
    ·
      refine ⟨105794307310682082803366297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70529538207121388535577531 105794307310682082803366297)
      ·
        refine ⟨79345730483011562102524723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105794307310682082803366297 79345730483011562102524723)
        ·
          refine ⟨119018595724517343153787085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79345730483011562102524723 119018595724517343153787085)
          ·
            refine ⟨44631973396694003682670157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 119018595724517343153787085 44631973396694003682670157)
            ·
              refine ⟨16736990023760251381001309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44631973396694003682670157 16736990023760251381001309)
              ·
                refine ⟨6276371258910094267875491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16736990023760251381001309 6276371258910094267875491)
                ·
                  refine ⟨9414556888365141401813237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6276371258910094267875491 9414556888365141401813237)
                  ·
                    refine ⟨882614708284232006419991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9414556888365141401813237 882614708284232006419991)
                    ·
                      rfl

theorem cell22_2578329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 3, 1, 5].length) (baseStart_2578329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2578329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2578329 prefixEnd_2578329 := by exact prefixLift 2578329
  have htrace : WordTrace (prefixWord ++ tailWord_2578329) baseStart_2578329 baseEnd_2578329 := by
    simpa [prefixWord, tailWord_2578329, baseEnd_2578329] using wordTrace_append hprefix tailTrace_2578329
  have hstable : (prefixWord ++ tailWord_2578329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2578329).length < 2 ^ (prefixWord ++ tailWord_2578329).sum := by decide
  have hdescent : baseEnd_2578329 < baseStart_2578329 := by decide
  rcases family_descends (prefixWord ++ tailWord_2578329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2578380 : List Nat := [2, 2, 1, 4, 1, 3, 3, 1, 2, 3]
def baseStart_2578380 : Nat := 118140960795 + 2578380 * 2 ^ 59
def prefixEnd_2578380 : Nat := 4983230072969 + 3 ^ 40 * 2578380 * 2
def baseEnd_2578380 : Nat := 882632166626484873394835

theorem tailTrace_2578380 : CollatzResearch.WordTrace tailWord_2578380 prefixEnd_2578380 882632166626484873394835 := by
  unfold tailWord_2578380
  simp only [CollatzResearch.WordTrace]
  refine ⟨47020622199488543545438297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62694162932651391393917729 47020622199488543545438297)
  ·
    refine ⟨35265466649616407659078723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47020622199488543545438297 35265466649616407659078723)
    ·
      refine ⟨52898199974424611488618085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35265466649616407659078723 52898199974424611488618085)
      ·
        refine ⟨9918412495204614654115891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52898199974424611488618085 9918412495204614654115891)
        ·
          refine ⟨14877618742806921981173837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9918412495204614654115891 14877618742806921981173837)
          ·
            refine ⟨5579107028552595742940189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14877618742806921981173837 5579107028552595742940189)
            ·
              refine ⟨2092165135707223403602571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5579107028552595742940189 2092165135707223403602571)
              ·
                refine ⟨3138247703560835105403857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2092165135707223403602571 3138247703560835105403857)
                ·
                  refine ⟨2353685777670626329052893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3138247703560835105403857 2353685777670626329052893)
                  ·
                    refine ⟨882632166626484873394835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2353685777670626329052893 882632166626484873394835)
                    ·
                      rfl

theorem cell22_2578380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 3, 1, 2, 3].length) (baseStart_2578380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2578380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2578380 prefixEnd_2578380 := by exact prefixLift 2578380
  have htrace : WordTrace (prefixWord ++ tailWord_2578380) baseStart_2578380 baseEnd_2578380 := by
    simpa [prefixWord, tailWord_2578380, baseEnd_2578380] using wordTrace_append hprefix tailTrace_2578380
  have hstable : (prefixWord ++ tailWord_2578380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2578380).length < 2 ^ (prefixWord ++ tailWord_2578380).sum := by decide
  have hdescent : baseEnd_2578380 < baseStart_2578380 := by decide
  rcases family_descends (prefixWord ++ tailWord_2578380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2578391 : List Nat := [1, 1, 3, 2, 1, 1, 3, 4, 3, 3]
def baseStart_2578391 : Nat := 118140960795 + 2578391 * 2 ^ 59
def prefixEnd_2578391 : Nat := 4983230072969 + 3 ^ 40 * 2578391 * 2
def baseEnd_2578391 : Nat := 882635932151284511369801

theorem tailTrace_2578391 : CollatzResearch.WordTrace tailWord_2578391 prefixEnd_2578391 882635932151284511369801 := by
  unfold tailWord_2578391
  simp only [CollatzResearch.WordTrace]
  refine ⟨94041645601937235969527027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62694430401291490646351351 94041645601937235969527027)
  ·
    refine ⟨141062468402905853954290541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94041645601937235969527027 141062468402905853954290541)
    ·
      refine ⟨52898425651089695232858953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141062468402905853954290541 52898425651089695232858953)
      ·
        refine ⟨39673819238317271424644215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52898425651089695232858953 39673819238317271424644215)
        ·
          refine ⟨59510728857475907136966323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39673819238317271424644215 59510728857475907136966323)
          ·
            refine ⟨89266093286213860705449485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59510728857475907136966323 89266093286213860705449485)
            ·
              refine ⟨33474784982330197764543557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89266093286213860705449485 33474784982330197764543557)
              ·
                refine ⟨6276522184186912080851917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33474784982330197764543557 6276522184186912080851917)
                ·
                  refine ⟨2353695819070092030319469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6276522184186912080851917 2353695819070092030319469)
                  ·
                    refine ⟨882635932151284511369801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2353695819070092030319469 882635932151284511369801)
                    ·
                      rfl

theorem cell22_2578391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 4, 3, 3].length) (baseStart_2578391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2578391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2578391 prefixEnd_2578391 := by exact prefixLift 2578391
  have htrace : WordTrace (prefixWord ++ tailWord_2578391) baseStart_2578391 baseEnd_2578391 := by
    simpa [prefixWord, tailWord_2578391, baseEnd_2578391] using wordTrace_append hprefix tailTrace_2578391
  have hstable : (prefixWord ++ tailWord_2578391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2578391).length < 2 ^ (prefixWord ++ tailWord_2578391).sum := by decide
  have hdescent : baseEnd_2578391 < baseStart_2578391 := by decide
  rcases family_descends (prefixWord ++ tailWord_2578391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2578393 : List Nat := [1, 2, 1, 2, 6, 2, 2, 6]
def baseStart_2578393 : Nat := 118140960795 + 2578393 * 2 ^ 59
def prefixEnd_2578393 : Nat := 4983230072969 + 3 ^ 40 * 2578393 * 2
def baseEnd_2578393 : Nat := 98070735199128574757755

theorem tailTrace_2578393 : CollatzResearch.WordTrace tailWord_2578393 prefixEnd_2578393 98070735199128574757755 := by
  unfold tailWord_2578393
  simp only [CollatzResearch.WordTrace]
  refine ⟨94041718547929990311099833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62694479031953326874066555 94041718547929990311099833)
  ·
    refine ⟨70531288910947492733324875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94041718547929990311099833 70531288910947492733324875)
    ·
      refine ⟨105796933366421239099987313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70531288910947492733324875 105796933366421239099987313)
      ·
        refine ⟨79347700024815929324990485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105796933366421239099987313 79347700024815929324990485)
        ·
          refine ⟨3719423438663246687108929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 79347700024815929324990485 3719423438663246687108929)
          ·
            refine ⟨2789567578997435015331697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3719423438663246687108929 2789567578997435015331697)
            ·
              refine ⟨2092175684248076261498773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2789567578997435015331697 2092175684248076261498773)
              ·
                refine ⟨98070735199128574757755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2092175684248076261498773 98070735199128574757755)
                ·
                  rfl

theorem cell22_2578393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 2, 6].length) (baseStart_2578393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2578393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2578393 prefixEnd_2578393 := by exact prefixLift 2578393
  have htrace : WordTrace (prefixWord ++ tailWord_2578393) baseStart_2578393 baseEnd_2578393 := by
    simpa [prefixWord, tailWord_2578393, baseEnd_2578393] using wordTrace_append hprefix tailTrace_2578393
  have hstable : (prefixWord ++ tailWord_2578393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2578393).length < 2 ^ (prefixWord ++ tailWord_2578393).sum := by decide
  have hdescent : baseEnd_2578393 < baseStart_2578393 := by decide
  rcases family_descends (prefixWord ++ tailWord_2578393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2578404 : List Nat := [2, 3, 1, 1, 1, 1, 3, 1, 9]
def baseStart_2578404 : Nat := 118140960795 + 2578404 * 2 ^ 59
def prefixEnd_2578404 : Nat := 4983230072969 + 3 ^ 40 * 2578404 * 2
def baseEnd_2578404 : Nat := 294213460772318936931587

theorem tailTrace_2578404 : CollatzResearch.WordTrace tailWord_2578404 prefixEnd_2578404 294213460772318936931587 := by
  unfold tailWord_2578404
  simp only [CollatzResearch.WordTrace]
  refine ⟨47021059875445069594875133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62694746500593426126500177 47021059875445069594875133)
  ·
    refine ⟨17632897453291901098078175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47021059875445069594875133 17632897453291901098078175)
    ·
      refine ⟨26449346179937851647117263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17632897453291901098078175 26449346179937851647117263)
      ·
        refine ⟨39674019269906777470675895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26449346179937851647117263 39674019269906777470675895)
        ·
          refine ⟨59511028904860166206013843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39674019269906777470675895 59511028904860166206013843)
          ·
            refine ⟨89266543357290249309020765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59511028904860166206013843 89266543357290249309020765)
            ·
              refine ⟨33474953758983843490882787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89266543357290249309020765 33474953758983843490882787)
              ·
                refine ⟨50212430638475765236324181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33474953758983843490882787 50212430638475765236324181)
                ·
                  refine ⟨294213460772318936931587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 50212430638475765236324181 294213460772318936931587)
                  ·
                    rfl

theorem cell22_2578404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 9].length) (baseStart_2578404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2578404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2578404 prefixEnd_2578404 := by exact prefixLift 2578404
  have htrace : WordTrace (prefixWord ++ tailWord_2578404) baseStart_2578404 baseEnd_2578404 := by
    simpa [prefixWord, tailWord_2578404, baseEnd_2578404] using wordTrace_append hprefix tailTrace_2578404
  have hstable : (prefixWord ++ tailWord_2578404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2578404).length < 2 ^ (prefixWord ++ tailWord_2578404).sum := by decide
  have hdescent : baseEnd_2578404 < baseStart_2578404 := by decide
  rcases family_descends (prefixWord ++ tailWord_2578404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2578419 : List Nat := [1, 1, 1, 2, 2, 2, 1, 3, 4, 5]
def baseStart_2578419 : Nat := 118140960795 + 2578419 * 2 ^ 59
def prefixEnd_2578419 : Nat := 4983230072969 + 3 ^ 40 * 2578419 * 2
def baseEnd_2578419 : Nat := 882645517123501771669715

theorem tailTrace_2578419 : CollatzResearch.WordTrace tailWord_2578419 prefixEnd_2578419 882645517123501771669715 := by
  unfold tailWord_2578419
  simp only [CollatzResearch.WordTrace]
  refine ⟨94042666845835796751546311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62695111230557197834364207 94042666845835796751546311)
  ·
    refine ⟨141064000268753695127319467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94042666845835796751546311 141064000268753695127319467)
    ·
      refine ⟨211596000403130542690979201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141064000268753695127319467 211596000403130542690979201)
      ·
        refine ⟨158697000302347907018234401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 211596000403130542690979201 158697000302347907018234401)
        ·
          refine ⟨119022750226760930263675801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 158697000302347907018234401 119022750226760930263675801)
          ·
            refine ⟨89267062670070697697756851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119022750226760930263675801 89267062670070697697756851)
            ·
              refine ⟨133900594005106046546635277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89267062670070697697756851 133900594005106046546635277)
              ·
                refine ⟨50212722751914767454988229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 133900594005106046546635277 50212722751914767454988229)
                ·
                  refine ⟨9414885515984018897810293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50212722751914767454988229 9414885515984018897810293)
                  ·
                    refine ⟨882645517123501771669715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9414885515984018897810293 882645517123501771669715)
                    ·
                      rfl

theorem cell22_2578419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 4, 5].length) (baseStart_2578419 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2578419 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2578419 prefixEnd_2578419 := by exact prefixLift 2578419
  have htrace : WordTrace (prefixWord ++ tailWord_2578419) baseStart_2578419 baseEnd_2578419 := by
    simpa [prefixWord, tailWord_2578419, baseEnd_2578419] using wordTrace_append hprefix tailTrace_2578419
  have hstable : (prefixWord ++ tailWord_2578419).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2578419).length < 2 ^ (prefixWord ++ tailWord_2578419).sum := by decide
  have hdescent : baseEnd_2578419 < baseStart_2578419 := by decide
  rcases family_descends (prefixWord ++ tailWord_2578419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2578543 : List Nat := [1, 1, 2, 1, 3, 4, 1, 3, 3, 3]
def baseStart_2578543 : Nat := 118140960795 + 2578543 * 2 ^ 59
def prefixEnd_2578543 : Nat := 4983230072969 + 3 ^ 40 * 2578543 * 2
def baseEnd_2578543 : Nat := 882687964857606781569335

theorem tailTrace_2578543 : CollatzResearch.WordTrace tailWord_2578543 prefixEnd_2578543 882687964857606781569335 := by
  unfold tailWord_2578543
  simp only [CollatzResearch.WordTrace]
  refine ⟨94047189497386565929060283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62698126331591043952706855 94047189497386565929060283)
  ·
    refine ⟨141070784246079848893590425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94047189497386565929060283 141070784246079848893590425)
    ·
      refine ⟨105803088184559886670192819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141070784246079848893590425 105803088184559886670192819)
      ·
        refine ⟨158704632276839830005289229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105803088184559886670192819 158704632276839830005289229)
        ·
          refine ⟨59514237103814936251983461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 158704632276839830005289229 59514237103814936251983461)
          ·
            refine ⟨11158919456965300547246899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59514237103814936251983461 11158919456965300547246899)
            ·
              refine ⟨16738379185447950820870349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11158919456965300547246899 16738379185447950820870349)
              ·
                refine ⟨6276892194542981557826381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16738379185447950820870349 6276892194542981557826381)
                ·
                  refine ⟨2353834572953618084184893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6276892194542981557826381 2353834572953618084184893)
                  ·
                    refine ⟨882687964857606781569335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2353834572953618084184893 882687964857606781569335)
                    ·
                      rfl

theorem cell22_2578543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 3, 3, 3].length) (baseStart_2578543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2578543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2578543 prefixEnd_2578543 := by exact prefixLift 2578543
  have htrace : WordTrace (prefixWord ++ tailWord_2578543) baseStart_2578543 baseEnd_2578543 := by
    simpa [prefixWord, tailWord_2578543, baseEnd_2578543] using wordTrace_append hprefix tailTrace_2578543
  have hstable : (prefixWord ++ tailWord_2578543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2578543).length < 2 ^ (prefixWord ++ tailWord_2578543).sum := by decide
  have hdescent : baseEnd_2578543 < baseStart_2578543 := by decide
  rcases family_descends (prefixWord ++ tailWord_2578543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2578620 : List Nat := [2, 2, 2, 3, 3, 1, 1, 1, 3, 4]
def baseStart_2578620 : Nat := 118140960795 + 2578620 * 2 ^ 59
def prefixEnd_2578620 : Nat := 4983230072969 + 3 ^ 40 * 2578620 * 2
def baseEnd_2578620 : Nat := 882714323531204247394099

theorem tailTrace_2578620 : CollatzResearch.WordTrace tailWord_2578620 prefixEnd_2578620 882714323531204247394099 := by
  unfold tailWord_2578620
  simp only [CollatzResearch.WordTrace]
  refine ⟨47024998959053804039806657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62699998612071738719742209 47024998959053804039806657)
  ·
    refine ⟨35268749219290353029854993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47024998959053804039806657 35268749219290353029854993)
    ·
      refine ⟨26451561914467764772391245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35268749219290353029854993 26451561914467764772391245)
      ·
        refine ⟨9919335717925411789646717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26451561914467764772391245 9919335717925411789646717)
        ·
          refine ⟨3719750894222029421117519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9919335717925411789646717 3719750894222029421117519)
          ·
            refine ⟨5579626341333044131676279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3719750894222029421117519 5579626341333044131676279)
            ·
              refine ⟨8369439511999566197514419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5579626341333044131676279 8369439511999566197514419)
              ·
                refine ⟨12554159267999349296271629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8369439511999566197514419 12554159267999349296271629)
                ·
                  refine ⟨4707809725499755986101861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12554159267999349296271629 4707809725499755986101861)
                  ·
                    refine ⟨882714323531204247394099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4707809725499755986101861 882714323531204247394099)
                    ·
                      rfl

theorem cell22_2578620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 1, 3, 4].length) (baseStart_2578620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2578620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2578620 prefixEnd_2578620 := by exact prefixLift 2578620
  have htrace : WordTrace (prefixWord ++ tailWord_2578620) baseStart_2578620 baseEnd_2578620 := by
    simpa [prefixWord, tailWord_2578620, baseEnd_2578620] using wordTrace_append hprefix tailTrace_2578620
  have hstable : (prefixWord ++ tailWord_2578620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2578620).length < 2 ^ (prefixWord ++ tailWord_2578620).sum := by decide
  have hdescent : baseEnd_2578620 < baseStart_2578620 := by decide
  rcases family_descends (prefixWord ++ tailWord_2578620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2578633 : List Nat := [1, 2, 1, 1, 2, 1, 1, 6, 4, 3]
def baseStart_2578633 : Nat := 118140960795 + 2578633 * 2 ^ 59
def prefixEnd_2578633 : Nat := 4983230072969 + 3 ^ 40 * 2578633 * 2
def baseEnd_2578633 : Nat := 882718773696876546819059

theorem tailTrace_2578633 : CollatzResearch.WordTrace tailWord_2578633 prefixEnd_2578633 882718773696876546819059 := by
  unfold tailWord_2578633
  simp only [CollatzResearch.WordTrace]
  refine ⟨94050472067060511299836553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62700314711373674199891035 94050472067060511299836553)
  ·
    refine ⟨70537854050295383474877415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94050472067060511299836553 70537854050295383474877415)
    ·
      refine ⟨105806781075443075212316123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70537854050295383474877415 105806781075443075212316123)
      ·
        refine ⟨158710171613164612818474185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105806781075443075212316123 158710171613164612818474185)
        ·
          refine ⟨119032628709873459613855639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 158710171613164612818474185 119032628709873459613855639)
          ·
            refine ⟨178548943064810189420783459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119032628709873459613855639 178548943064810189420783459)
            ·
              refine ⟨267823414597215284131175189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 178548943064810189420783459 267823414597215284131175189)
              ·
                refine ⟨12554222559244466443648837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 267823414597215284131175189 12554222559244466443648837)
                ·
                  refine ⟨2353916729858337458184157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12554222559244466443648837 2353916729858337458184157)
                  ·
                    refine ⟨882718773696876546819059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2353916729858337458184157 882718773696876546819059)
                    ·
                      rfl

theorem cell22_2578633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 6, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 6, 4, 3].length) (baseStart_2578633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2578633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2578633 prefixEnd_2578633 := by exact prefixLift 2578633
  have htrace : WordTrace (prefixWord ++ tailWord_2578633) baseStart_2578633 baseEnd_2578633 := by
    simpa [prefixWord, tailWord_2578633, baseEnd_2578633] using wordTrace_append hprefix tailTrace_2578633
  have hstable : (prefixWord ++ tailWord_2578633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2578633).length < 2 ^ (prefixWord ++ tailWord_2578633).sum := by decide
  have hdescent : baseEnd_2578633 < baseStart_2578633 := by decide
  rcases family_descends (prefixWord ++ tailWord_2578633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2578650 : List Nat := [3, 1, 1, 2, 2, 1, 3, 4, 2, 3]
def baseStart_2578650 : Nat := 118140960795 + 2578650 * 2 ^ 59
def prefixEnd_2578650 : Nat := 4983230072969 + 3 ^ 40 * 2578650 * 2
def baseEnd_2578650 : Nat := 882724593144294169144007

theorem tailTrace_2578650 : CollatzResearch.WordTrace tailWord_2578650 prefixEnd_2578650 882724593144294169144007 := by
  unfold tailWord_2578650
  simp only [CollatzResearch.WordTrace]
  refine ⟨23512773026999730800801351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62700728071999282135470269 23512773026999730800801351)
  ·
    refine ⟨35269159540499596201202027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23512773026999730800801351 35269159540499596201202027)
    ·
      refine ⟨52903739310749394301803041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35269159540499596201202027 52903739310749394301803041)
      ·
        refine ⟨39677804483062045726352281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52903739310749394301803041 39677804483062045726352281)
        ·
          refine ⟨29758353362296534294764211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39677804483062045726352281 29758353362296534294764211)
          ·
            refine ⟨44637530043444801442146317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29758353362296534294764211 44637530043444801442146317)
            ·
              refine ⟨16739073766291800540804869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44637530043444801442146317 16739073766291800540804869)
              ·
                refine ⟨3138576331179712601400913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16739073766291800540804869 3138576331179712601400913)
                ·
                  refine ⟨2353932248384784451050685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3138576331179712601400913 2353932248384784451050685)
                  ·
                    refine ⟨882724593144294169144007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2353932248384784451050685 882724593144294169144007)
                    ·
                      rfl

theorem cell22_2578650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 4, 2, 3].length) (baseStart_2578650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2578650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2578650 prefixEnd_2578650 := by exact prefixLift 2578650
  have htrace : WordTrace (prefixWord ++ tailWord_2578650) baseStart_2578650 baseEnd_2578650 := by
    simpa [prefixWord, tailWord_2578650, baseEnd_2578650] using wordTrace_append hprefix tailTrace_2578650
  have hstable : (prefixWord ++ tailWord_2578650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2578650).length < 2 ^ (prefixWord ++ tailWord_2578650).sum := by decide
  have hdescent : baseEnd_2578650 < baseStart_2578650 := by decide
  rcases family_descends (prefixWord ++ tailWord_2578650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2578712 : List Nat := [2, 1, 2, 3, 1, 2, 1, 6, 1, 3]
def baseStart_2578712 : Nat := 118140960795 + 2578712 * 2 ^ 59
def prefixEnd_2578712 : Nat := 4983230072969 + 3 ^ 40 * 2578712 * 2
def baseEnd_2578712 : Nat := 882745817011346674093817

theorem tailTrace_2578712 : CollatzResearch.WordTrace tailWord_2578712 prefixEnd_2578712 882745817011346674093817 := by
  unfold tailWord_2578712
  simp only [CollatzResearch.WordTrace]
  refine ⟨47026676716887153895981195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62702235622516205194641593 47026676716887153895981195)
  ·
    refine ⟨70540015075330730843971793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47026676716887153895981195 70540015075330730843971793)
    ·
      refine ⟨52905011306498048132978845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70540015075330730843971793 52905011306498048132978845)
      ·
        refine ⟨19839379239936768049867067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52905011306498048132978845 19839379239936768049867067)
        ·
          refine ⟨29759068859905152074800601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19839379239936768049867067 29759068859905152074800601)
          ·
            refine ⟨22319301644928864056100451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29759068859905152074800601 22319301644928864056100451)
            ·
              refine ⟨33478952467393296084150677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22319301644928864056100451 33478952467393296084150677)
              ·
                refine ⟨1569325896909060753944563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 33478952467393296084150677 1569325896909060753944563)
                ·
                  refine ⟨2353988845363591130916845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1569325896909060753944563 2353988845363591130916845)
                  ·
                    refine ⟨882745817011346674093817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2353988845363591130916845 882745817011346674093817)
                    ·
                      rfl

theorem cell22_2578712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 6, 1, 3].length) (baseStart_2578712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2578712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2578712 prefixEnd_2578712 := by exact prefixLift 2578712
  have htrace : WordTrace (prefixWord ++ tailWord_2578712) baseStart_2578712 baseEnd_2578712 := by
    simpa [prefixWord, tailWord_2578712, baseEnd_2578712] using wordTrace_append hprefix tailTrace_2578712
  have hstable : (prefixWord ++ tailWord_2578712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2578712).length < 2 ^ (prefixWord ++ tailWord_2578712).sum := by decide
  have hdescent : baseEnd_2578712 < baseStart_2578712 := by decide
  rcases family_descends (prefixWord ++ tailWord_2578712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2578723 : List Nat := [1, 1, 1, 4, 2, 2, 1, 3, 2, 5]
def baseStart_2578723 : Nat := 118140960795 + 2578723 * 2 ^ 59
def prefixEnd_2578723 : Nat := 4983230072969 + 3 ^ 40 * 2578723 * 2
def baseEnd_2578723 : Nat := 882749582536146312068783

theorem tailTrace_2578723 : CollatzResearch.WordTrace tailWord_2578723 prefixEnd_2578723 882749582536146312068783 := by
  unfold tailWord_2578723
  simp only [CollatzResearch.WordTrace]
  refine ⟨94053754636734456670612823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62702503091156304447075215 94053754636734456670612823)
  ·
    refine ⟨141080631955101685005919235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94053754636734456670612823 141080631955101685005919235)
    ·
      refine ⟨211620947932652527508878853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141080631955101685005919235 211620947932652527508878853)
      ·
        refine ⟨39678927737372348907914785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 211620947932652527508878853 39678927737372348907914785)
        ·
          refine ⟨29759195803029261680936089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39678927737372348907914785 29759195803029261680936089)
          ·
            refine ⟨22319396852271946260702067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29759195803029261680936089 22319396852271946260702067)
            ·
              refine ⟨33479095278407919391053101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22319396852271946260702067 33479095278407919391053101)
              ·
                refine ⟨12554660729402969771644913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33479095278407919391053101 12554660729402969771644913)
                ·
                  refine ⟨9415995547052227328733685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12554660729402969771644913 9415995547052227328733685)
                  ·
                    refine ⟨882749582536146312068783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9415995547052227328733685 882749582536146312068783)
                    ·
                      rfl

theorem cell22_2578723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 3, 2, 5].length) (baseStart_2578723 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2578723 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2578723 prefixEnd_2578723 := by exact prefixLift 2578723
  have htrace : WordTrace (prefixWord ++ tailWord_2578723) baseStart_2578723 baseEnd_2578723 := by
    simpa [prefixWord, tailWord_2578723, baseEnd_2578723] using wordTrace_append hprefix tailTrace_2578723
  have hstable : (prefixWord ++ tailWord_2578723).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2578723).length < 2 ^ (prefixWord ++ tailWord_2578723).sum := by decide
  have hdescent : baseEnd_2578723 < baseStart_2578723 := by decide
  rcases family_descends (prefixWord ++ tailWord_2578723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2578755 : List Nat := [1, 1, 1, 3, 1, 3, 4, 3, 1, 4]
def baseStart_2578755 : Nat := 118140960795 + 2578755 * 2 ^ 59
def prefixEnd_2578755 : Nat := 4983230072969 + 3 ^ 40 * 2578755 * 2
def baseEnd_2578755 : Nat := 882760536790108895268685

theorem tailTrace_2578755 : CollatzResearch.WordTrace tailWord_2578755 prefixEnd_2578755 882760536790108895268685 := by
  unfold tailWord_2578755
  simp only [CollatzResearch.WordTrace]
  refine ⟨94054921772618526135777719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62703281181745684090518479 94054921772618526135777719)
  ·
    refine ⟨141082382658927789203666579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94054921772618526135777719 141082382658927789203666579)
    ·
      refine ⟨211623573988391683805499869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141082382658927789203666579 211623573988391683805499869)
      ·
        refine ⟨79358840245646881427062451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 211623573988391683805499869 79358840245646881427062451)
        ·
          refine ⟨119038260368470322140593677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79358840245646881427062451 119038260368470322140593677)
          ·
            refine ⟨44639347638176370802722629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 119038260368470322140593677 44639347638176370802722629)
            ·
              refine ⟨8369877682158069525510493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44639347638176370802722629 8369877682158069525510493)
              ·
                refine ⟨3138704130809276072066435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8369877682158069525510493 3138704130809276072066435)
                ·
                  refine ⟨4708056196213914108099653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3138704130809276072066435 4708056196213914108099653)
                  ·
                    refine ⟨882760536790108895268685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4708056196213914108099653 882760536790108895268685)
                    ·
                      rfl

theorem cell22_2578755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 3, 1, 4].length) (baseStart_2578755 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2578755 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2578755 prefixEnd_2578755 := by exact prefixLift 2578755
  have htrace : WordTrace (prefixWord ++ tailWord_2578755) baseStart_2578755 baseEnd_2578755 := by
    simpa [prefixWord, tailWord_2578755, baseEnd_2578755] using wordTrace_append hprefix tailTrace_2578755
  have hstable : (prefixWord ++ tailWord_2578755).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2578755).length < 2 ^ (prefixWord ++ tailWord_2578755).sum := by decide
  have hdescent : baseEnd_2578755 < baseStart_2578755 := by decide
  rcases family_descends (prefixWord ++ tailWord_2578755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2578770 : List Nat := [3, 2, 2, 1, 1, 1, 5, 1, 6]
def baseStart_2578770 : Nat := 118140960795 + 2578770 * 2 ^ 59
def prefixEnd_2578770 : Nat := 4983230072969 + 3 ^ 40 * 2578770 * 2
def baseEnd_2578770 : Nat := 294255223865551285381213

theorem tailTrace_2578770 : CollatzResearch.WordTrace tailWord_2578770 prefixEnd_2578770 294255223865551285381213 := by
  unfold tailWord_2578770
  simp only [CollatzResearch.WordTrace]
  refine ⟨23513867216891045924393441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62703645911709455798382509 23513867216891045924393441)
  ·
    refine ⟨17635400412668284443295081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23513867216891045924393441 17635400412668284443295081)
    ·
      refine ⟨13226550309501213332471311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17635400412668284443295081 13226550309501213332471311)
      ·
        refine ⟨19839825464251819998706967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13226550309501213332471311 19839825464251819998706967)
        ·
          refine ⟨29759738196377729998060451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19839825464251819998706967 29759738196377729998060451)
          ·
            refine ⟨44639607294566594997090677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29759738196377729998060451 44639607294566594997090677)
            ·
              refine ⟨4184963183865618280977251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44639607294566594997090677 4184963183865618280977251)
              ·
                refine ⟨6277444775798427421465877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4184963183865618280977251 6277444775798427421465877)
                ·
                  refine ⟨294255223865551285381213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6277444775798427421465877 294255223865551285381213)
                  ·
                    rfl

theorem cell22_2578770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 5, 1, 6].length) (baseStart_2578770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2578770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2578770 prefixEnd_2578770 := by exact prefixLift 2578770
  have htrace : WordTrace (prefixWord ++ tailWord_2578770) baseStart_2578770 baseEnd_2578770 := by
    simpa [prefixWord, tailWord_2578770, baseEnd_2578770] using wordTrace_append hprefix tailTrace_2578770
  have hstable : (prefixWord ++ tailWord_2578770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2578770).length < 2 ^ (prefixWord ++ tailWord_2578770).sum := by decide
  have hdescent : baseEnd_2578770 < baseStart_2578770 := by decide
  rcases family_descends (prefixWord ++ tailWord_2578770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2578783 : List Nat := [1, 1, 2, 3, 1, 2, 2, 1, 3, 6]
def baseStart_2578783 : Nat := 118140960795 + 2578783 * 2 ^ 59
def prefixEnd_2578783 : Nat := 4983230072969 + 3 ^ 40 * 2578783 * 2
def baseEnd_2578783 : Nat := 882770121762326155568599

theorem tailTrace_2578783 : CollatzResearch.WordTrace tailWord_2578783 prefixEnd_2578783 882770121762326155568599 := by
  unfold tailWord_2578783
  simp only [CollatzResearch.WordTrace]
  refine ⟨94055943016517086917797003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62703962011011391278531335 94055943016517086917797003)
  ·
    refine ⟨141083914524775630376695505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94055943016517086917797003 141083914524775630376695505)
    ·
      refine ⟨105812935893581722782521629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141083914524775630376695505 105812935893581722782521629)
      ·
        refine ⟨39679850960093146043445611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105812935893581722782521629 39679850960093146043445611)
        ·
          refine ⟨59519776440139719065168417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39679850960093146043445611 59519776440139719065168417)
          ·
            refine ⟨44639832330104789298876313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59519776440139719065168417 44639832330104789298876313)
            ·
              refine ⟨33479874247578591974157235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44639832330104789298876313 33479874247578591974157235)
              ·
                refine ⟨50219811371367887961235853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33479874247578591974157235 50219811371367887961235853)
                ·
                  refine ⟨18832429264262957985463445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50219811371367887961235853 18832429264262957985463445)
                  ·
                    refine ⟨882770121762326155568599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18832429264262957985463445 882770121762326155568599)
                    ·
                      rfl

theorem cell22_2578783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 3, 6].length) (baseStart_2578783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2578783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2578783 prefixEnd_2578783 := by exact prefixLift 2578783
  have htrace : WordTrace (prefixWord ++ tailWord_2578783) baseStart_2578783 baseEnd_2578783 := by
    simpa [prefixWord, tailWord_2578783, baseEnd_2578783] using wordTrace_append hprefix tailTrace_2578783
  have hstable : (prefixWord ++ tailWord_2578783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2578783).length < 2 ^ (prefixWord ++ tailWord_2578783).sum := by decide
  have hdescent : baseEnd_2578783 < baseStart_2578783 := by decide
  rcases family_descends (prefixWord ++ tailWord_2578783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2578800 : List Nat := [2, 1, 1, 1, 4, 3, 1, 3, 2, 4]
def baseStart_2578800 : Nat := 118140960795 + 2578800 * 2 ^ 59
def prefixEnd_2578800 : Nat := 4983230072969 + 3 ^ 40 * 2578800 * 2
def baseEnd_2578800 : Nat := 882775941209743777893547

theorem tailTrace_2578800 : CollatzResearch.WordTrace tailWord_2578800 prefixEnd_2578800 882775941209743777893547 := by
  unfold tailWord_2578800
  simp only [CollatzResearch.WordTrace]
  refine ⟨47028281528727749410582927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62704375371636999214110569 47028281528727749410582927)
  ·
    refine ⟨70542422293091624115874391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47028281528727749410582927 70542422293091624115874391)
    ·
      refine ⟨105813633439637436173811587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70542422293091624115874391 105813633439637436173811587)
      ·
        refine ⟨158720450159456154260717381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105813633439637436173811587 158720450159456154260717381)
        ·
          refine ⟨29760084404898028923884509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 158720450159456154260717381 29760084404898028923884509)
          ·
            refine ⟨11160031651836760846456691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29760084404898028923884509 11160031651836760846456691)
            ·
              refine ⟨16740047477755141269685037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11160031651836760846456691 16740047477755141269685037)
              ·
                refine ⟨6277517804158177976131889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16740047477755141269685037 6277517804158177976131889)
                ·
                  refine ⟨4708138353118633482098917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6277517804158177976131889 4708138353118633482098917)
                  ·
                    refine ⟨882775941209743777893547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4708138353118633482098917 882775941209743777893547)
                    ·
                      rfl

theorem cell22_2578800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 3, 2, 4].length) (baseStart_2578800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2578800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2578800 prefixEnd_2578800 := by exact prefixLift 2578800
  have htrace : WordTrace (prefixWord ++ tailWord_2578800) baseStart_2578800 baseEnd_2578800 := by
    simpa [prefixWord, tailWord_2578800, baseEnd_2578800] using wordTrace_append hprefix tailTrace_2578800
  have hstable : (prefixWord ++ tailWord_2578800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2578800).length < 2 ^ (prefixWord ++ tailWord_2578800).sum := by decide
  have hdescent : baseEnd_2578800 < baseStart_2578800 := by decide
  rcases family_descends (prefixWord ++ tailWord_2578800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2578817 : List Nat := [1, 2, 4, 3, 1, 1, 2, 2, 2, 4]
def baseStart_2578817 : Nat := 118140960795 + 2578817 * 2 ^ 59
def prefixEnd_2578817 : Nat := 4983230072969 + 3 ^ 40 * 2578817 * 2
def baseEnd_2578817 : Nat := 882781760657161400218495

theorem tailTrace_2578817 : CollatzResearch.WordTrace tailWord_2578817 prefixEnd_2578817 882781760657161400218495 := by
  unfold tailWord_2578817
  simp only [CollatzResearch.WordTrace]
  refine ⟨94057183098393910724534705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62704788732262607149689803 94057183098393910724534705)
  ·
    refine ⟨70542887323795433043401029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94057183098393910724534705 70542887323795433043401029)
    ·
      refine ⟨13226791373211643695637693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70542887323795433043401029 13226791373211643695637693)
      ·
        refine ⟨4960046764954366385864135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13226791373211643695637693 4960046764954366385864135)
        ·
          refine ⟨7440070147431549578796203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4960046764954366385864135 7440070147431549578796203)
          ·
            refine ⟨11160105221147324368194305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7440070147431549578796203 11160105221147324368194305)
            ·
              refine ⟨8370078915860493276145729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11160105221147324368194305 8370078915860493276145729)
              ·
                refine ⟨6277559186895369957109297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8370078915860493276145729 6277559186895369957109297)
                ·
                  refine ⟨4708169390171527467831973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6277559186895369957109297 4708169390171527467831973)
                  ·
                    refine ⟨882781760657161400218495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4708169390171527467831973 882781760657161400218495)
                    ·
                      rfl

theorem cell22_2578817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 2, 2, 4].length) (baseStart_2578817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2578817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2578817 prefixEnd_2578817 := by exact prefixLift 2578817
  have htrace : WordTrace (prefixWord ++ tailWord_2578817) baseStart_2578817 baseEnd_2578817 := by
    simpa [prefixWord, tailWord_2578817, baseEnd_2578817] using wordTrace_append hprefix tailTrace_2578817
  have hstable : (prefixWord ++ tailWord_2578817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2578817).length < 2 ^ (prefixWord ++ tailWord_2578817).sum := by decide
  have hdescent : baseEnd_2578817 < baseStart_2578817 := by decide
  rcases family_descends (prefixWord ++ tailWord_2578817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2578819 : List Nat := [1, 1, 1, 3, 6, 1, 2, 2, 2, 3]
def baseStart_2578819 : Nat := 118140960795 + 2578819 * 2 ^ 59
def prefixEnd_2578819 : Nat := 4983230072969 + 3 ^ 40 * 2578819 * 2
def baseEnd_2578819 : Nat := 882782445298034061668489

theorem tailTrace_2578819 : CollatzResearch.WordTrace tailWord_2578819 prefixEnd_2578819 882782445298034061668489 := by
  unfold tailWord_2578819
  simp only [CollatzResearch.WordTrace]
  refine ⟨94057256044386665066107511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62704837362924443377405007 94057256044386665066107511)
  ·
    refine ⟨141085884066579997599161267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94057256044386665066107511 141085884066579997599161267)
    ·
      refine ⟨211628826099869996398741901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141085884066579997599161267 211628826099869996398741901)
      ·
        refine ⟨79360809787451248649528213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 211628826099869996398741901 79360809787451248649528213)
        ·
          refine ⟨3720037958786777280446635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 79360809787451248649528213 3720037958786777280446635)
          ·
            refine ⟨5580056938180165920669953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3720037958786777280446635 5580056938180165920669953)
            ·
              refine ⟨4185042703635124440502465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5580056938180165920669953 4185042703635124440502465)
              ·
                refine ⟨3138782027726343330376849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4185042703635124440502465 3138782027726343330376849)
                ·
                  refine ⟨2354086520794757497782637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3138782027726343330376849 2354086520794757497782637)
                  ·
                    refine ⟨882782445298034061668489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2354086520794757497782637 882782445298034061668489)
                    ·
                      rfl

theorem cell22_2578819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 2, 2, 2, 3].length) (baseStart_2578819 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2578819 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2578819 prefixEnd_2578819 := by exact prefixLift 2578819
  have htrace : WordTrace (prefixWord ++ tailWord_2578819) baseStart_2578819 baseEnd_2578819 := by
    simpa [prefixWord, tailWord_2578819, baseEnd_2578819] using wordTrace_append hprefix tailTrace_2578819
  have hstable : (prefixWord ++ tailWord_2578819).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2578819).length < 2 ^ (prefixWord ++ tailWord_2578819).sum := by decide
  have hdescent : baseEnd_2578819 < baseStart_2578819 := by decide
  rcases family_descends (prefixWord ++ tailWord_2578819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2578847 : List Nat := [1, 1, 2, 5, 1, 1, 3, 2, 3, 3]
def baseStart_2578847 : Nat := 118140960795 + 2578847 * 2 ^ 59
def prefixEnd_2578847 : Nat := 4983230072969 + 3 ^ 40 * 2578847 * 2
def baseEnd_2578847 : Nat := 882792030270251321968403

theorem tailTrace_2578847 : CollatzResearch.WordTrace tailWord_2578847 prefixEnd_2578847 882792030270251321968403 := by
  unfold tailWord_2578847
  simp only [CollatzResearch.WordTrace]
  refine ⟨94058277288285225848126795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62705518192190150565417863 94058277288285225848126795)
  ·
    refine ⟨141087415932427838772190193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94058277288285225848126795 141087415932427838772190193)
    ·
      refine ⟨105815561949320879079142645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141087415932427838772190193 105815561949320879079142645)
      ·
        refine ⟨9920208932748832413669623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 105815561949320879079142645 9920208932748832413669623)
        ·
          refine ⟨14880313399123248620504435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9920208932748832413669623 14880313399123248620504435)
          ·
            refine ⟨22320470098684872930756653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14880313399123248620504435 22320470098684872930756653)
            ·
              refine ⟨8370176287006827349033745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22320470098684872930756653 8370176287006827349033745)
              ·
                refine ⟨6277632215255120511775309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8370176287006827349033745 6277632215255120511775309)
                ·
                  refine ⟨2354112080720670191915741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6277632215255120511775309 2354112080720670191915741)
                  ·
                    refine ⟨882792030270251321968403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2354112080720670191915741 882792030270251321968403)
                    ·
                      rfl

theorem cell22_2578847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 2, 3, 3].length) (baseStart_2578847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2578847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2578847 prefixEnd_2578847 := by exact prefixLift 2578847
  have htrace : WordTrace (prefixWord ++ tailWord_2578847) baseStart_2578847 baseEnd_2578847 := by
    simpa [prefixWord, tailWord_2578847, baseEnd_2578847] using wordTrace_append hprefix tailTrace_2578847
  have hstable : (prefixWord ++ tailWord_2578847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2578847).length < 2 ^ (prefixWord ++ tailWord_2578847).sum := by decide
  have hdescent : baseEnd_2578847 < baseStart_2578847 := by decide
  rcases family_descends (prefixWord ++ tailWord_2578847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2578849 : List Nat := [1, 2, 3, 5, 1, 1, 3, 6]
def baseStart_2578849 : Nat := 118140960795 + 2578849 * 2 ^ 59
def prefixEnd_2578849 : Nat := 4983230072969 + 3 ^ 40 * 2578849 * 2
def baseEnd_2578849 : Nat := 98088079434569331490933

theorem tailTrace_2578849 : CollatzResearch.WordTrace tailWord_2578849 prefixEnd_2578849 98088079434569331490933 := by
  unfold tailWord_2578849
  simp only [CollatzResearch.WordTrace]
  refine ⟨94058350234277980189699601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62705566822851986793133067 94058350234277980189699601)
  ·
    refine ⟨70543762675708485142274701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94058350234277980189699601 70543762675708485142274701)
    ·
      refine ⟨26453911003390681928353013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70543762675708485142274701 26453911003390681928353013)
      ·
        refine ⟨2480054156567876430783095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26453911003390681928353013 2480054156567876430783095)
        ·
          refine ⟨3720081234851814646174643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2480054156567876430783095 3720081234851814646174643)
          ·
            refine ⟨5580121852277721969261965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3720081234851814646174643 5580121852277721969261965)
            ·
              refine ⟨2092545694604145738473237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5580121852277721969261965 2092545694604145738473237)
              ·
                refine ⟨98088079434569331490933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2092545694604145738473237 98088079434569331490933)
                ·
                  rfl

theorem cell22_2578849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 3, 6].length) (baseStart_2578849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2578849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2578849 prefixEnd_2578849 := by exact prefixLift 2578849
  have htrace : WordTrace (prefixWord ++ tailWord_2578849) baseStart_2578849 baseEnd_2578849 := by
    simpa [prefixWord, tailWord_2578849, baseEnd_2578849] using wordTrace_append hprefix tailTrace_2578849
  have hstable : (prefixWord ++ tailWord_2578849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2578849).length < 2 ^ (prefixWord ++ tailWord_2578849).sum := by decide
  have hdescent : baseEnd_2578849 < baseStart_2578849 := by decide
  rcases family_descends (prefixWord ++ tailWord_2578849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2578877 : List Nat := [1, 4, 1, 2, 2, 2, 3, 2, 5]
def baseStart_2578877 : Nat := 118140960795 + 2578877 * 2 ^ 59
def prefixEnd_2578877 : Nat := 4983230072969 + 3 ^ 40 * 2578877 * 2
def baseEnd_2578877 : Nat := 294267433294447081239437

theorem tailTrace_2578877 : CollatzResearch.WordTrace tailWord_2578877 prefixEnd_2578877 294267433294447081239437 := by
  unfold tailWord_2578877
  simp only [CollatzResearch.WordTrace]
  refine ⟨94059371478176540971718885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62706247652117693981145923 94059371478176540971718885)
  ·
    refine ⟨17636132152158101432197291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94059371478176540971718885 17636132152158101432197291)
    ·
      refine ⟨26454198228237152148295937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17636132152158101432197291 26454198228237152148295937)
      ·
        refine ⟨19840648671177864111221953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26454198228237152148295937 19840648671177864111221953)
        ·
          refine ⟨14880486503383398083416465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19840648671177864111221953 14880486503383398083416465)
          ·
            refine ⟨11160364877537548562562349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14880486503383398083416465 11160364877537548562562349)
            ·
              refine ⟨4185136829076580710960881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11160364877537548562562349 4185136829076580710960881)
              ·
                refine ⟨3138852621807435533220661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4185136829076580710960881 3138852621807435533220661)
                ·
                  refine ⟨294267433294447081239437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3138852621807435533220661 294267433294447081239437)
                  ·
                    rfl

theorem cell22_2578877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 3, 2, 5].length) (baseStart_2578877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2578877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2578877 prefixEnd_2578877 := by exact prefixLift 2578877
  have htrace : WordTrace (prefixWord ++ tailWord_2578877) baseStart_2578877 baseEnd_2578877 := by
    simpa [prefixWord, tailWord_2578877, baseEnd_2578877] using wordTrace_append hprefix tailTrace_2578877
  have hstable : (prefixWord ++ tailWord_2578877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2578877).length < 2 ^ (prefixWord ++ tailWord_2578877).sum := by decide
  have hdescent : baseEnd_2578877 < baseStart_2578877 := by decide
  rcases family_descends (prefixWord ++ tailWord_2578877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2578905 : List Nat := [1, 2, 1, 2, 4, 1, 1, 4, 6]
def baseStart_2578905 : Nat := 118140960795 + 2578905 * 2 ^ 59
def prefixEnd_2578905 : Nat := 4983230072969 + 3 ^ 40 * 2578905 * 2
def baseEnd_2578905 : Nat := 294270628285186168006075

theorem tailTrace_2578905 : CollatzResearch.WordTrace tailWord_2578905 prefixEnd_2578905 294270628285186168006075 := by
  unfold tailWord_2578905
  simp only [CollatzResearch.WordTrace]
  refine ⟨94060392722075101753738169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62706928481383401169158779 94060392722075101753738169)
  ·
    refine ⟨70545294541556326315303627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94060392722075101753738169 70545294541556326315303627)
    ·
      refine ⟨105817941812334489472955441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70545294541556326315303627 105817941812334489472955441)
      ·
        refine ⟨79363456359250867104716581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105817941812334489472955441 79363456359250867104716581)
        ·
          refine ⟨14880648067359537582134359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 79363456359250867104716581 14880648067359537582134359)
          ·
            refine ⟨22320972101039306373201539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14880648067359537582134359 22320972101039306373201539)
            ·
              refine ⟨33481458151558959559802309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22320972101039306373201539 33481458151558959559802309)
              ·
                refine ⟨6277773403417304917462933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33481458151558959559802309 6277773403417304917462933)
                ·
                  refine ⟨294270628285186168006075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6277773403417304917462933 294270628285186168006075)
                  ·
                    rfl

theorem cell22_2578905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 4, 6].length) (baseStart_2578905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2578905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2578905 prefixEnd_2578905 := by exact prefixLift 2578905
  have htrace : WordTrace (prefixWord ++ tailWord_2578905) baseStart_2578905 baseEnd_2578905 := by
    simpa [prefixWord, tailWord_2578905, baseEnd_2578905] using wordTrace_append hprefix tailTrace_2578905
  have hstable : (prefixWord ++ tailWord_2578905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2578905).length < 2 ^ (prefixWord ++ tailWord_2578905).sum := by decide
  have hdescent : baseEnd_2578905 < baseStart_2578905 := by decide
  rcases family_descends (prefixWord ++ tailWord_2578905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2578937 : List Nat := [1, 2, 1, 3, 1, 2, 4, 1, 4, 3]
def baseStart_2578937 : Nat := 118140960795 + 2578937 * 2 ^ 59
def prefixEnd_2578937 : Nat := 4983230072969 + 3 ^ 40 * 2578937 * 2
def baseEnd_2578937 : Nat := 882822839109521087218127

theorem tailTrace_2578937 : CollatzResearch.WordTrace tailWord_2578937 prefixEnd_2578937 882822839109521087218127 := by
  unfold tailWord_2578937
  simp only [CollatzResearch.WordTrace]
  refine ⟨94061559857959171218903065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62707706571972780812602043 94061559857959171218903065)
  ·
    refine ⟨70546169893469378414177299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94061559857959171218903065 70546169893469378414177299)
    ·
      refine ⟨105819254840204067621265949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70546169893469378414177299 105819254840204067621265949)
      ·
        refine ⟨39682220565076525357974731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105819254840204067621265949 39682220565076525357974731)
        ·
          refine ⟨59523330847614788036962097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39682220565076525357974731 59523330847614788036962097)
          ·
            refine ⟨44642498135711091027721573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59523330847614788036962097 44642498135711091027721573)
            ·
              refine ⟨8370468400445829567697795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44642498135711091027721573 8370468400445829567697795)
              ·
                refine ⟨12555702600668744351546693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8370468400445829567697795 12555702600668744351546693)
                ·
                  refine ⟨2354194237625389565915005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12555702600668744351546693 2354194237625389565915005)
                  ·
                    refine ⟨882822839109521087218127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2354194237625389565915005 882822839109521087218127)
                    ·
                      rfl

theorem cell22_2578937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 1, 4, 3].length) (baseStart_2578937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2578937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2578937 prefixEnd_2578937 := by exact prefixLift 2578937
  have htrace : WordTrace (prefixWord ++ tailWord_2578937) baseStart_2578937 baseEnd_2578937 := by
    simpa [prefixWord, tailWord_2578937, baseEnd_2578937] using wordTrace_append hprefix tailTrace_2578937
  have hstable : (prefixWord ++ tailWord_2578937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2578937).length < 2 ^ (prefixWord ++ tailWord_2578937).sum := by decide
  have hdescent : baseEnd_2578937 < baseStart_2578937 := by decide
  rcases family_descends (prefixWord ++ tailWord_2578937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2578954 : List Nat := [3, 1, 2, 2, 2, 1, 3, 3, 2, 3]
def baseStart_2578954 : Nat := 118140960795 + 2578954 * 2 ^ 59
def prefixEnd_2578954 : Nat := 4983230072969 + 3 ^ 40 * 2578954 * 2
def baseEnd_2578954 : Nat := 882828658556938709543075

theorem tailTrace_2578954 : CollatzResearch.WordTrace tailWord_2578954 prefixEnd_2578954 882828658556938709543075 := by
  unfold tailWord_2578954
  simp only [CollatzResearch.WordTrace]
  refine ⟨23515544974724395780567979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62708119932598388748181277 23515544974724395780567979)
  ·
    refine ⟨35273317462086593670851969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23515544974724395780567979 35273317462086593670851969)
    ·
      refine ⟨26454988096564945253138977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35273317462086593670851969 26454988096564945253138977)
      ·
        refine ⟨19841241072423708939854233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26454988096564945253138977 19841241072423708939854233)
        ·
          refine ⟨14880930804317781704890675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19841241072423708939854233 14880930804317781704890675)
          ·
            refine ⟨22321396206476672557336013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14880930804317781704890675 22321396206476672557336013)
            ·
              refine ⟨8370523577428752209001005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22321396206476672557336013 8370523577428752209001005)
              ·
                refine ⟨3138946341535782078375377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8370523577428752209001005 3138946341535782078375377)
                ·
                  refine ⟨2354209756151836558781533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3138946341535782078375377 2354209756151836558781533)
                  ·
                    refine ⟨882828658556938709543075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2354209756151836558781533 882828658556938709543075)
                    ·
                      rfl

theorem cell22_2578954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 3, 2, 3].length) (baseStart_2578954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2578954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2578954 prefixEnd_2578954 := by exact prefixLift 2578954
  have htrace : WordTrace (prefixWord ++ tailWord_2578954) baseStart_2578954 baseEnd_2578954 := by
    simpa [prefixWord, tailWord_2578954, baseEnd_2578954] using wordTrace_append hprefix tailTrace_2578954
  have hstable : (prefixWord ++ tailWord_2578954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2578954).length < 2 ^ (prefixWord ++ tailWord_2578954).sum := by decide
  have hdescent : baseEnd_2578954 < baseStart_2578954 := by decide
  rcases family_descends (prefixWord ++ tailWord_2578954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2578990 : List Nat := [4, 1, 3, 1, 4, 1, 2, 2, 4]
def baseStart_2578990 : Nat := 118140960795 + 2578990 * 2 ^ 59
def prefixEnd_2578990 : Nat := 4983230072969 + 3 ^ 40 * 2578990 * 2
def baseEnd_2578990 : Nat := 294280327364215538547655

theorem tailTrace_2578990 : CollatzResearch.WordTrace tailWord_2578990 prefixEnd_2578990 294280327364215538547655 := by
  unfold tailWord_2578990
  simp only [CollatzResearch.WordTrace]
  refine ⟨11757936615845895158822803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62708995284511440847054949 11757936615845895158822803)
  ·
    refine ⟨17636904923768842738234205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11757936615845895158822803 17636904923768842738234205)
    ·
      refine ⟨6613839346413316026837827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17636904923768842738234205 6613839346413316026837827)
      ·
        refine ⟨9920759019619974040256741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6613839346413316026837827 9920759019619974040256741)
        ·
          refine ⟨1860142316178745132548139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9920759019619974040256741 1860142316178745132548139)
          ·
            refine ⟨2790213474268117698822209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1860142316178745132548139 2790213474268117698822209)
            ·
              refine ⟨2092660105701088274116657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2790213474268117698822209 2092660105701088274116657)
              ·
                refine ⟨1569495079275816205587493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2092660105701088274116657 1569495079275816205587493)
                ·
                  refine ⟨294280327364215538547655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1569495079275816205587493 294280327364215538547655)
                  ·
                    rfl

theorem cell22_2578990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 2, 2, 4].length) (baseStart_2578990 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2578990 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2578990 prefixEnd_2578990 := by exact prefixLift 2578990
  have htrace : WordTrace (prefixWord ++ tailWord_2578990) baseStart_2578990 baseEnd_2578990 := by
    simpa [prefixWord, tailWord_2578990, baseEnd_2578990] using wordTrace_append hprefix tailTrace_2578990
  have hstable : (prefixWord ++ tailWord_2578990).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2578990).length < 2 ^ (prefixWord ++ tailWord_2578990).sum := by decide
  have hdescent : baseEnd_2578990 < baseStart_2578990 := by decide
  rcases family_descends (prefixWord ++ tailWord_2578990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2579076 : List Nat := [2, 3, 2, 1, 3, 2, 2, 2, 1, 4]
def baseStart_2579076 : Nat := 118140960795 + 2579076 * 2 ^ 59
def prefixEnd_2579076 : Nat := 4983230072969 + 3 ^ 40 * 2579076 * 2
def baseEnd_2579076 : Nat := 882870421650171057992701

theorem tailTrace_2579076 : CollatzResearch.WordTrace tailWord_2579076 prefixEnd_2579076 882870421650171057992701 := by
  unfold tailWord_2579076
  simp only [CollatzResearch.WordTrace]
  refine ⟨47033314802227798979106541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62711086402970398638808721 47033314802227798979106541)
  ·
    refine ⟨17637493050835424617164953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47033314802227798979106541 17637493050835424617164953)
    ·
      refine ⟨13228119788126568462873715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17637493050835424617164953 13228119788126568462873715)
      ·
        refine ⟨19842179682189852694310573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13228119788126568462873715 19842179682189852694310573)
        ·
          refine ⟨7440817380821194760366465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19842179682189852694310573 7440817380821194760366465)
          ·
            refine ⟨5580613035615896070274849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7440817380821194760366465 5580613035615896070274849)
            ·
              refine ⟨4185459776711922052706137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5580613035615896070274849 4185459776711922052706137)
              ·
                refine ⟨3139094832533941539529603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4185459776711922052706137 3139094832533941539529603)
                ·
                  refine ⟨4708642248800912309294405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3139094832533941539529603 4708642248800912309294405)
                  ·
                    refine ⟨882870421650171057992701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4708642248800912309294405 882870421650171057992701)
                    ·
                      rfl

theorem cell22_2579076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 2, 2, 1, 4].length) (baseStart_2579076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2579076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2579076 prefixEnd_2579076 := by exact prefixLift 2579076
  have htrace : WordTrace (prefixWord ++ tailWord_2579076) baseStart_2579076 baseEnd_2579076 := by
    simpa [prefixWord, tailWord_2579076, baseEnd_2579076] using wordTrace_append hprefix tailTrace_2579076
  have hstable : (prefixWord ++ tailWord_2579076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2579076).length < 2 ^ (prefixWord ++ tailWord_2579076).sum := by decide
  have hdescent : baseEnd_2579076 < baseStart_2579076 := by decide
  rcases family_descends (prefixWord ++ tailWord_2579076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2579123 : List Nat := [1, 1, 1, 2, 3, 6, 2, 1, 2, 3]
def baseStart_2579123 : Nat := 118140960795 + 2579123 * 2 ^ 59
def prefixEnd_2579123 : Nat := 4983230072969 + 3 ^ 40 * 2579123 * 2
def baseEnd_2579123 : Nat := 882886510710678602067557

theorem tailTrace_2579123 : CollatzResearch.WordTrace tailWord_2579123 prefixEnd_2579123 882886510710678602067557 := by
  unfold tailWord_2579123
  simp only [CollatzResearch.WordTrace]
  refine ⟨94068343835285324985174023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62712229223523549990116015 94068343835285324985174023)
  ·
    refine ⟨141102515752927987477761035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94068343835285324985174023 141102515752927987477761035)
    ·
      refine ⟨211653773629391981216641553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141102515752927987477761035 211653773629391981216641553)
      ·
        refine ⟨158740330222043985912481165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 211653773629391981216641553 158740330222043985912481165)
        ·
          refine ⟨59527623833266494717180437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 158740330222043985912481165 59527623833266494717180437)
          ·
            refine ⟨2790357367184366939867833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 59527623833266494717180437 2790357367184366939867833)
            ·
              refine ⟨2092768025388275204900875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2790357367184366939867833 2092768025388275204900875)
              ·
                refine ⟨3139152038082412807351313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2092768025388275204900875 3139152038082412807351313)
                ·
                  refine ⟨2354364028561809605513485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3139152038082412807351313 2354364028561809605513485)
                  ·
                    refine ⟨882886510710678602067557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2354364028561809605513485 882886510710678602067557)
                    ·
                      rfl

theorem cell22_2579123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 2, 1, 2, 3].length) (baseStart_2579123 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2579123 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2579123 prefixEnd_2579123 := by exact prefixLift 2579123
  have htrace : WordTrace (prefixWord ++ tailWord_2579123) baseStart_2579123 baseEnd_2579123 := by
    simpa [prefixWord, tailWord_2579123, baseEnd_2579123] using wordTrace_append hprefix tailTrace_2579123
  have hstable : (prefixWord ++ tailWord_2579123).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2579123).length < 2 ^ (prefixWord ++ tailWord_2579123).sum := by decide
  have hdescent : baseEnd_2579123 < baseStart_2579123 := by decide
  rcases family_descends (prefixWord ++ tailWord_2579123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2579194 : List Nat := [3, 1, 1, 1, 1, 3, 4, 1, 3, 4]
def baseStart_2579194 : Nat := 118140960795 + 2579194 * 2 ^ 59
def prefixEnd_2579194 : Nat := 4983230072969 + 3 ^ 40 * 2579194 * 2
def baseEnd_2579194 : Nat := 882910815461658083542339

theorem tailTrace_2579194 : CollatzResearch.WordTrace tailWord_2579194 prefixEnd_2579194 882910815461658083542339 := by
  unfold tailWord_2579194
  simp only [CollatzResearch.WordTrace]
  refine ⟨23517733354507026027752159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62713955612018736074005757 23517733354507026027752159)
  ·
    refine ⟨35276600031760539041628239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23517733354507026027752159 35276600031760539041628239)
    ·
      refine ⟨52914900047640808562442359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35276600031760539041628239 52914900047640808562442359)
      ·
        refine ⟨79372350071461212843663539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52914900047640808562442359 79372350071461212843663539)
        ·
          refine ⟨119058525107191819265495309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79372350071461212843663539 119058525107191819265495309)
          ·
            refine ⟨44646946915196932224560741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 119058525107191819265495309 44646946915196932224560741)
            ·
              refine ⟨8371302546599424792105139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44646946915196932224560741 8371302546599424792105139)
              ·
                refine ⟨12556953819899137188157709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8371302546599424792105139 12556953819899137188157709)
                ·
                  refine ⟨4708857682462176445559141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12556953819899137188157709 4708857682462176445559141)
                  ·
                    refine ⟨882910815461658083542339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4708857682462176445559141 882910815461658083542339)
                    ·
                      rfl

theorem cell22_2579194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 1, 3, 4].length) (baseStart_2579194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2579194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2579194 prefixEnd_2579194 := by exact prefixLift 2579194
  have htrace : WordTrace (prefixWord ++ tailWord_2579194) baseStart_2579194 baseEnd_2579194 := by
    simpa [prefixWord, tailWord_2579194, baseEnd_2579194] using wordTrace_append hprefix tailTrace_2579194
  have hstable : (prefixWord ++ tailWord_2579194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2579194).length < 2 ^ (prefixWord ++ tailWord_2579194).sum := by decide
  have hdescent : baseEnd_2579194 < baseStart_2579194 := by decide
  rcases family_descends (prefixWord ++ tailWord_2579194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2579226 : List Nat := [3, 1, 1, 3, 2, 1, 1, 6, 4]
def baseStart_2579226 : Nat := 118140960795 + 2579226 * 2 ^ 59
def prefixEnd_2579226 : Nat := 4983230072969 + 3 ^ 40 * 2579226 * 2
def baseEnd_2579226 : Nat := 294307256571873555580747

theorem tailTrace_2579226 : CollatzResearch.WordTrace tailWord_2579226 prefixEnd_2579226 294307256571873555580747 := by
  unfold tailWord_2579226
  simp only [CollatzResearch.WordTrace]
  refine ⟨23518025138478043394043383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62714733702608115717449021 23518025138478043394043383)
  ·
    refine ⟨35277037707717065091065075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23518025138478043394043383 35277037707717065091065075)
    ·
      refine ⟨52915556561575597636597613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35277037707717065091065075 52915556561575597636597613)
      ·
        refine ⟨19843333710590849113724105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52915556561575597636597613 19843333710590849113724105)
        ·
          refine ⟨14882500282943136835293079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19843333710590849113724105 14882500282943136835293079)
          ·
            refine ⟨22323750424414705252939619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14882500282943136835293079 22323750424414705252939619)
            ·
              refine ⟨33485625636622057879409429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22323750424414705252939619 33485625636622057879409429)
              ·
                refine ⟨1569638701716658963097317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 33485625636622057879409429 1569638701716658963097317)
                ·
                  refine ⟨294307256571873555580747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1569638701716658963097317 294307256571873555580747)
                  ·
                    rfl

theorem cell22_2579226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 6, 4].length) (baseStart_2579226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2579226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2579226 prefixEnd_2579226 := by exact prefixLift 2579226
  have htrace : WordTrace (prefixWord ++ tailWord_2579226) baseStart_2579226 baseEnd_2579226 := by
    simpa [prefixWord, tailWord_2579226, baseEnd_2579226] using wordTrace_append hprefix tailTrace_2579226
  have hstable : (prefixWord ++ tailWord_2579226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2579226).length < 2 ^ (prefixWord ++ tailWord_2579226).sum := by decide
  have hdescent : baseEnd_2579226 < baseStart_2579226 := by decide
  rcases family_descends (prefixWord ++ tailWord_2579226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2579277 : List Nat := [1, 6, 1, 2, 2, 1, 3, 2, 4]
def baseStart_2579277 : Nat := 118140960795 + 2579277 * 2 ^ 59
def prefixEnd_2579277 : Nat := 4983230072969 + 3 ^ 40 * 2579277 * 2
def baseEnd_2579277 : Nat := 294313076019291177905695

theorem tailTrace_2579277 : CollatzResearch.WordTrace tailWord_2579277 prefixEnd_2579277 294313076019291177905695 := by
  unfold tailWord_2579277
  simp only [CollatzResearch.WordTrace]
  refine ⟨94073960676727409286280085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62715973784484939524186723 94073960676727409286280085)
  ·
    refine ⟨4409716906721597310294379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 94073960676727409286280085 4409716906721597310294379)
    ·
      refine ⟨6614575360082395965441569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4409716906721597310294379 6614575360082395965441569)
      ·
        refine ⟨4960931520061796974081177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6614575360082395965441569 4960931520061796974081177)
        ·
          refine ⟨3720698640046347730560883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4960931520061796974081177 3720698640046347730560883)
          ·
            refine ⟨5581047960069521595841325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3720698640046347730560883 5581047960069521595841325)
            ·
              refine ⟨2092892985026070598440497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5581047960069521595841325 2092892985026070598440497)
              ·
                refine ⟨1569669738769552948830373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2092892985026070598440497 1569669738769552948830373)
                ·
                  refine ⟨294313076019291177905695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1569669738769552948830373 294313076019291177905695)
                  ·
                    rfl

theorem cell22_2579277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 3, 2, 4].length) (baseStart_2579277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2579277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2579277 prefixEnd_2579277 := by exact prefixLift 2579277
  have htrace : WordTrace (prefixWord ++ tailWord_2579277) baseStart_2579277 baseEnd_2579277 := by
    simpa [prefixWord, tailWord_2579277, baseEnd_2579277] using wordTrace_append hprefix tailTrace_2579277
  have hstable : (prefixWord ++ tailWord_2579277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2579277).length < 2 ^ (prefixWord ++ tailWord_2579277).sum := by decide
  have hdescent : baseEnd_2579277 < baseStart_2579277 := by decide
  rcases family_descends (prefixWord ++ tailWord_2579277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2579292 : List Nat := [2, 2, 4, 2, 1, 3, 2, 1, 2, 3]
def baseStart_2579292 : Nat := 118140960795 + 2579292 * 2 ^ 59
def prefixEnd_2579292 : Nat := 4983230072969 + 3 ^ 40 * 2579292 * 2
def baseEnd_2579292 : Nat := 882944362864418494592039

theorem tailTrace_2579292 : CollatzResearch.WordTrace tailWord_2579292 prefixEnd_2579292 882944362864418494592039 := by
  unfold tailWord_2579292
  simp only [CollatzResearch.WordTrace]
  refine ⟨47037253885836533424038065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62716338514448711232050753 47037253885836533424038065)
  ·
    refine ⟨35277940414377400068028549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47037253885836533424038065 35277940414377400068028549)
    ·
      refine ⟨6614613827695762512755353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35277940414377400068028549 6614613827695762512755353)
      ·
        refine ⟨4960960370771821884566515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6614613827695762512755353 4960960370771821884566515)
        ·
          refine ⟨7441440556157732826849773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4960960370771821884566515 7441440556157732826849773)
          ·
            refine ⟨2790540208559149810068665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7441440556157732826849773 2790540208559149810068665)
            ·
              refine ⟨2092905156419362357551499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2790540208559149810068665 2092905156419362357551499)
              ·
                refine ⟨3139357734629043536327249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2092905156419362357551499 3139357734629043536327249)
                ·
                  refine ⟨2354518300971782652245437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3139357734629043536327249 2354518300971782652245437)
                  ·
                    refine ⟨882944362864418494592039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2354518300971782652245437 882944362864418494592039)
                    ·
                      rfl

theorem cell22_2579292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 2, 1, 2, 3].length) (baseStart_2579292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2579292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2579292 prefixEnd_2579292 := by exact prefixLift 2579292
  have htrace : WordTrace (prefixWord ++ tailWord_2579292) baseStart_2579292 baseEnd_2579292 := by
    simpa [prefixWord, tailWord_2579292, baseEnd_2579292] using wordTrace_append hprefix tailTrace_2579292
  have hstable : (prefixWord ++ tailWord_2579292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2579292).length < 2 ^ (prefixWord ++ tailWord_2579292).sum := by decide
  have hdescent : baseEnd_2579292 < baseStart_2579292 := by decide
  rcases family_descends (prefixWord ++ tailWord_2579292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2579337 : List Nat := [1, 2, 1, 1, 5, 4, 2, 2, 1, 3]
def baseStart_2579337 : Nat := 118140960795 + 2579337 * 2 ^ 59
def prefixEnd_2579337 : Nat := 4983230072969 + 3 ^ 40 * 2579337 * 2
def baseEnd_2579337 : Nat := 882959767284053377216901

theorem tailTrace_2579337 : CollatzResearch.WordTrace tailWord_2579337 prefixEnd_2579337 882959767284053377216901 := by
  unfold tailWord_2579337
  simp only [CollatzResearch.WordTrace]
  refine ⟨94076149056510039533464265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62717432704340026355642843 94076149056510039533464265)
  ·
    refine ⟨70557111792382529650098199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94076149056510039533464265 70557111792382529650098199)
    ·
      refine ⟨105835667688573794475147299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70557111792382529650098199 105835667688573794475147299)
      ·
        refine ⟨158753501532860691712720949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105835667688573794475147299 158753501532860691712720949)
        ·
          refine ⟨14883140768705689848067589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 158753501532860691712720949 14883140768705689848067589)
          ·
            refine ⟨2790588894132316846512673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14883140768705689848067589 2790588894132316846512673)
            ·
              refine ⟨2092941670599237634884505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2790588894132316846512673 2092941670599237634884505)
              ·
                refine ⟨1569706252949428226163379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2092941670599237634884505 1569706252949428226163379)
                ·
                  refine ⟨2354559379424142339245069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1569706252949428226163379 2354559379424142339245069)
                  ·
                    refine ⟨882959767284053377216901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2354559379424142339245069 882959767284053377216901)
                    ·
                      rfl

theorem cell22_2579337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 2, 2, 1, 3].length) (baseStart_2579337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2579337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2579337 prefixEnd_2579337 := by exact prefixLift 2579337
  have htrace : WordTrace (prefixWord ++ tailWord_2579337) baseStart_2579337 baseEnd_2579337 := by
    simpa [prefixWord, tailWord_2579337, baseEnd_2579337] using wordTrace_append hprefix tailTrace_2579337
  have hstable : (prefixWord ++ tailWord_2579337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2579337).length < 2 ^ (prefixWord ++ tailWord_2579337).sum := by decide
  have hdescent : baseEnd_2579337 < baseStart_2579337 := by decide
  rcases family_descends (prefixWord ++ tailWord_2579337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2579361 : List Nat := [1, 2, 3, 4, 1, 1, 1, 1, 8]
def baseStart_2579361 : Nat := 118140960795 + 2579361 * 2 ^ 59
def prefixEnd_2579361 : Nat := 4983230072969 + 3 ^ 40 * 2579361 * 2
def baseEnd_2579361 : Nat := 294322660991508438205609

theorem tailTrace_2579361 : CollatzResearch.WordTrace tailWord_2579361 prefixEnd_2579361 294322660991508438205609 := by
  unfold tailWord_2579361
  simp only [CollatzResearch.WordTrace]
  refine ⟨94077024408423091632337937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62718016272282061088225291 94077024408423091632337937)
  ·
    refine ⟨70557768306317318724253453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94077024408423091632337937 70557768306317318724253453)
    ·
      refine ⟨26459163114868994521595045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70557768306317318724253453 26459163114868994521595045)
      ·
        refine ⟨4961093084037936472799071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26459163114868994521595045 4961093084037936472799071)
        ·
          refine ⟨7441639626056904709198607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4961093084037936472799071 7441639626056904709198607)
          ·
            refine ⟨11162459439085357063797911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7441639626056904709198607 11162459439085357063797911)
            ·
              refine ⟨16743689158628035595696867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11162459439085357063797911 16743689158628035595696867)
              ·
                refine ⟨25115533737942053393545301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16743689158628035595696867 25115533737942053393545301)
                ·
                  refine ⟨294322660991508438205609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25115533737942053393545301 294322660991508438205609)
                  ·
                    rfl

theorem cell22_2579361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 1, 8].length) (baseStart_2579361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2579361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2579361 prefixEnd_2579361 := by exact prefixLift 2579361
  have htrace : WordTrace (prefixWord ++ tailWord_2579361) baseStart_2579361 baseEnd_2579361 := by
    simpa [prefixWord, tailWord_2579361, baseEnd_2579361] using wordTrace_append hprefix tailTrace_2579361
  have hstable : (prefixWord ++ tailWord_2579361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2579361).length < 2 ^ (prefixWord ++ tailWord_2579361).sum := by decide
  have hdescent : baseEnd_2579361 < baseStart_2579361 := by decide
  rcases family_descends (prefixWord ++ tailWord_2579361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2579410 : List Nat := [3, 2, 2, 3, 1, 3, 1, 1, 1, 5]
def baseStart_2579410 : Nat := 118140960795 + 2579410 * 2 ^ 59
def prefixEnd_2579410 : Nat := 4983230072969 + 3 ^ 40 * 2579410 * 2
def baseEnd_2579410 : Nat := 882984756675905520141677

theorem tailTrace_2579410 : CollatzResearch.WordTrace tailWord_2579410 prefixEnd_2579410 882984756675905520141677 := by
  unfold tailWord_2579410
  simp only [CollatzResearch.WordTrace]
  refine ⟨23519702896311393250217921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62719207723497048667247789 23519702896311393250217921)
  ·
    refine ⟨17639777172233544937663441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23519702896311393250217921 17639777172233544937663441)
    ·
      refine ⟨13229832879175158703247581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17639777172233544937663441 13229832879175158703247581)
      ·
        refine ⟨4961187329690684513717843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13229832879175158703247581 4961187329690684513717843)
        ·
          refine ⟨7441780994536026770576765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4961187329690684513717843 7441780994536026770576765)
          ·
            refine ⟨2790667872951010038966287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7441780994536026770576765 2790667872951010038966287)
            ·
              refine ⟨4186001809426515058449431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2790667872951010038966287 4186001809426515058449431)
              ·
                refine ⟨6279002714139772587674147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4186001809426515058449431 6279002714139772587674147)
                ·
                  refine ⟨9418504071209658881511221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6279002714139772587674147 9418504071209658881511221)
                  ·
                    refine ⟨882984756675905520141677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9418504071209658881511221 882984756675905520141677)
                    ·
                      rfl

theorem cell22_2579410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 1, 1, 1, 5].length) (baseStart_2579410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2579410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2579410 prefixEnd_2579410 := by exact prefixLift 2579410
  have htrace : WordTrace (prefixWord ++ tailWord_2579410) baseStart_2579410 baseEnd_2579410 := by
    simpa [prefixWord, tailWord_2579410, baseEnd_2579410] using wordTrace_append hprefix tailTrace_2579410
  have hstable : (prefixWord ++ tailWord_2579410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2579410).length < 2 ^ (prefixWord ++ tailWord_2579410).sum := by decide
  have hdescent : baseEnd_2579410 < baseStart_2579410 := by decide
  rcases family_descends (prefixWord ++ tailWord_2579410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2579429 : List Nat := [1, 3, 1, 6, 2, 1, 1, 3, 4]
def baseStart_2579429 : Nat := 118140960795 + 2579429 * 2 ^ 59
def prefixEnd_2579429 : Nat := 4983230072969 + 3 ^ 40 * 2579429 * 2
def baseEnd_2579429 : Nat := 294330420254731934638873

theorem tailTrace_2579429 : CollatzResearch.WordTrace tailWord_2579429 prefixEnd_2579429 294330420254731934638873 := by
  unfold tailWord_2579429
  simp only [CollatzResearch.WordTrace]
  refine ⟨94079504572176739245813341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62719669714784492830542227 94079504572176739245813341)
  ·
    refine ⟨35279814214566277217180003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94079504572176739245813341 35279814214566277217180003)
    ·
      refine ⟨52919721321849415825770005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35279814214566277217180003 52919721321849415825770005)
      ·
        refine ⟨2480611936961691366832969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 52919721321849415825770005 2480611936961691366832969)
        ·
          refine ⟨1860458952721268525124727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2480611936961691366832969 1860458952721268525124727)
          ·
            refine ⟨2790688429081902787687091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1860458952721268525124727 2790688429081902787687091)
            ·
              refine ⟨4186032643622854181530637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2790688429081902787687091 4186032643622854181530637)
              ·
                refine ⟨1569762241358570318073989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4186032643622854181530637 1569762241358570318073989)
                ·
                  refine ⟨294330420254731934638873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1569762241358570318073989 294330420254731934638873)
                  ·
                    rfl

theorem cell22_2579429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 1, 3, 4].length) (baseStart_2579429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2579429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2579429 prefixEnd_2579429 := by exact prefixLift 2579429
  have htrace : WordTrace (prefixWord ++ tailWord_2579429) baseStart_2579429 baseEnd_2579429 := by
    simpa [prefixWord, tailWord_2579429, baseEnd_2579429] using wordTrace_append hprefix tailTrace_2579429
  have hstable : (prefixWord ++ tailWord_2579429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2579429).length < 2 ^ (prefixWord ++ tailWord_2579429).sum := by decide
  have hdescent : baseEnd_2579429 < baseStart_2579429 := by decide
  rcases family_descends (prefixWord ++ tailWord_2579429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2579451 : List Nat := [1, 1, 1, 1, 1, 3, 3, 6, 5]
def baseStart_2579451 : Nat := 118140960795 + 2579451 * 2 ^ 59
def prefixEnd_2579451 : Nat := 4983230072969 + 3 ^ 40 * 2579451 * 2
def baseEnd_2579451 : Nat := 294332930604598359955517

theorem tailTrace_2579451 : CollatzResearch.WordTrace tailWord_2579451 prefixEnd_2579451 294332930604598359955517 := by
  unfold tailWord_2579451
  simp only [CollatzResearch.WordTrace]
  refine ⟨94080306978097037003114207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62720204652064691335409471 94080306978097037003114207)
  ·
    refine ⟨141120460467145555504671311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94080306978097037003114207 141120460467145555504671311)
    ·
      refine ⟨211680690700718333257006967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141120460467145555504671311 211680690700718333257006967)
      ·
        refine ⟨317521036051077499885510451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211680690700718333257006967 317521036051077499885510451)
        ·
          refine ⟨476281554076616249828265677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 317521036051077499885510451 476281554076616249828265677)
          ·
            refine ⟨178605582778731093685599629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 476281554076616249828265677 178605582778731093685599629)
            ·
              refine ⟨66977093542024160132099861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 178605582778731093685599629 66977093542024160132099861)
              ·
                refine ⟨3139551259782382506192181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 66977093542024160132099861 3139551259782382506192181)
                ·
                  refine ⟨294332930604598359955517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3139551259782382506192181 294332930604598359955517)
                  ·
                    rfl

theorem cell22_2579451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 6, 5].length) (baseStart_2579451 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2579451 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2579451 prefixEnd_2579451 := by exact prefixLift 2579451
  have htrace : WordTrace (prefixWord ++ tailWord_2579451) baseStart_2579451 baseEnd_2579451 := by
    simpa [prefixWord, tailWord_2579451, baseEnd_2579451] using wordTrace_append hprefix tailTrace_2579451
  have hstable : (prefixWord ++ tailWord_2579451).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2579451).length < 2 ^ (prefixWord ++ tailWord_2579451).sum := by decide
  have hdescent : baseEnd_2579451 < baseStart_2579451 := by decide
  rcases family_descends (prefixWord ++ tailWord_2579451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2579468 : List Nat := [2, 2, 1, 2, 3, 3, 1, 3, 5]
def baseStart_2579468 : Nat := 118140960795 + 2579468 * 2 ^ 59
def prefixEnd_2579468 : Nat := 4983230072969 + 3 ^ 40 * 2579468 * 2
def baseEnd_2579468 : Nat := 294334870420404234063833

theorem tailTrace_2579468 : CollatzResearch.WordTrace tailWord_2579468 prefixEnd_2579468 294334870420404234063833 := by
  unfold tailWord_2579468
  simp only [CollatzResearch.WordTrace]
  refine ⟨47040463509517724453241529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62720618012690299270988705 47040463509517724453241529)
  ·
    refine ⟨35280347632138293339931147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47040463509517724453241529 35280347632138293339931147)
    ·
      refine ⟨52920521448207440009896721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35280347632138293339931147 52920521448207440009896721)
      ·
        refine ⟨39690391086155580007422541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52920521448207440009896721 39690391086155580007422541)
        ·
          refine ⟨14883896657308342502783453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39690391086155580007422541 14883896657308342502783453)
          ·
            refine ⟨5581461246490628438543795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14883896657308342502783453 5581461246490628438543795)
            ·
              refine ⟨8372191869735942657815693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5581461246490628438543795 8372191869735942657815693)
              ·
                refine ⟨3139571951150978496680885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8372191869735942657815693 3139571951150978496680885)
                ·
                  refine ⟨294334870420404234063833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3139571951150978496680885 294334870420404234063833)
                  ·
                    rfl

theorem cell22_2579468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 3, 5].length) (baseStart_2579468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2579468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2579468 prefixEnd_2579468 := by exact prefixLift 2579468
  have htrace : WordTrace (prefixWord ++ tailWord_2579468) baseStart_2579468 baseEnd_2579468 := by
    simpa [prefixWord, tailWord_2579468, baseEnd_2579468] using wordTrace_append hprefix tailTrace_2579468
  have hstable : (prefixWord ++ tailWord_2579468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2579468).length < 2 ^ (prefixWord ++ tailWord_2579468).sum := by decide
  have hdescent : baseEnd_2579468 < baseStart_2579468 := by decide
  rcases family_descends (prefixWord ++ tailWord_2579468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2579511 : List Nat := [1, 1, 3, 1, 2, 2, 1, 1, 5, 5]
def baseStart_2579511 : Nat := 118140960795 + 2579511 * 2 ^ 59
def prefixEnd_2579511 : Nat := 4983230072969 + 3 ^ 40 * 2579511 * 2
def baseEnd_2579511 : Nat := 883019331039974923366367

theorem tailTrace_2579511 : CollatzResearch.WordTrace tailWord_2579511 prefixEnd_2579511 883019331039974923366367 := by
  unfold tailWord_2579511
  simp only [CollatzResearch.WordTrace]
  refine ⟨94082495357879667250298387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62721663571919778166865591 94082495357879667250298387)
  ·
    refine ⟨141123743036819500875447581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94082495357879667250298387 141123743036819500875447581)
    ·
      refine ⟨52921403638807312828292843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141123743036819500875447581 52921403638807312828292843)
      ·
        refine ⟨79382105458210969242439265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52921403638807312828292843 79382105458210969242439265)
        ·
          refine ⟨59536579093658226931829449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79382105458210969242439265 59536579093658226931829449)
          ·
            refine ⟨44652434320243670198872087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59536579093658226931829449 44652434320243670198872087)
            ·
              refine ⟨66978651480365505298308131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44652434320243670198872087 66978651480365505298308131)
              ·
                refine ⟨100467977220548257947462197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66978651480365505298308131 100467977220548257947462197)
                ·
                  refine ⟨9418872864426399182574581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 100467977220548257947462197 9418872864426399182574581)
                  ·
                    refine ⟨883019331039974923366367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9418872864426399182574581 883019331039974923366367)
                    ·
                      rfl

theorem cell22_2579511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 5, 5].length) (baseStart_2579511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2579511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2579511 prefixEnd_2579511 := by exact prefixLift 2579511
  have htrace : WordTrace (prefixWord ++ tailWord_2579511) baseStart_2579511 baseEnd_2579511 := by
    simpa [prefixWord, tailWord_2579511, baseEnd_2579511] using wordTrace_append hprefix tailTrace_2579511
  have hstable : (prefixWord ++ tailWord_2579511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2579511).length < 2 ^ (prefixWord ++ tailWord_2579511).sum := by decide
  have hdescent : baseEnd_2579511 < baseStart_2579511 := by decide
  rcases family_descends (prefixWord ++ tailWord_2579511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2579528 : List Nat := [2, 1, 3, 1, 1, 1, 6, 1, 1, 5]
def baseStart_2579528 : Nat := 118140960795 + 2579528 * 2 ^ 59
def prefixEnd_2579528 : Nat := 4983230072969 + 3 ^ 40 * 2579528 * 2
def baseEnd_2579528 : Nat := 883025150487392545691315

theorem tailTrace_2579528 : CollatzResearch.WordTrace tailWord_2579528 prefixEnd_2579528 883025150487392545691315 := by
  unfold tailWord_2579528
  simp only [CollatzResearch.WordTrace]
  refine ⟨47041557699409039576833619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62722076932545386102444825 47041557699409039576833619)
  ·
    refine ⟨70562336549113559365250429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47041557699409039576833619 70562336549113559365250429)
    ·
      refine ⟨26460876205917584761968911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70562336549113559365250429 26460876205917584761968911)
      ·
        refine ⟨39691314308876377142953367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26460876205917584761968911 39691314308876377142953367)
        ·
          refine ⟨59536971463314565714430051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39691314308876377142953367 59536971463314565714430051)
          ·
            refine ⟨89305457194971848571645077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59536971463314565714430051 89305457194971848571645077)
            ·
              refine ⟨4186193306014305401795863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 89305457194971848571645077 4186193306014305401795863)
              ·
                refine ⟨6279289959021458102693795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4186193306014305401795863 6279289959021458102693795)
                ·
                  refine ⟨9418934938532187154040693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6279289959021458102693795 9418934938532187154040693)
                  ·
                    refine ⟨883025150487392545691315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9418934938532187154040693 883025150487392545691315)
                    ·
                      rfl

theorem cell22_2579528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 6, 1, 1, 5].length) (baseStart_2579528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2579528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2579528 prefixEnd_2579528 := by exact prefixLift 2579528
  have htrace : WordTrace (prefixWord ++ tailWord_2579528) baseStart_2579528 baseEnd_2579528 := by
    simpa [prefixWord, tailWord_2579528, baseEnd_2579528] using wordTrace_append hprefix tailTrace_2579528
  have hstable : (prefixWord ++ tailWord_2579528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2579528).length < 2 ^ (prefixWord ++ tailWord_2579528).sum := by decide
  have hdescent : baseEnd_2579528 < baseStart_2579528 := by decide
  rcases family_descends (prefixWord ++ tailWord_2579528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2579562 : List Nat := [3, 1, 3, 2, 2, 1, 3, 2, 2, 3]
def baseStart_2579562 : Nat := 118140960795 + 2579562 * 2 ^ 59
def prefixEnd_2579562 : Nat := 4983230072969 + 3 ^ 40 * 2579562 * 2
def baseEnd_2579562 : Nat := 883036789382227790341211

theorem tailTrace_2579562 : CollatzResearch.WordTrace tailWord_2579562 prefixEnd_2579562 883036789382227790341211 := by
  unfold tailWord_2579562
  simp only [CollatzResearch.WordTrace]
  refine ⟨23521088870173725740101235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62722903653796601973603293 23521088870173725740101235)
  ·
    refine ⟨35281633305260588610151853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23521088870173725740101235 35281633305260588610151853)
    ·
      refine ⟨13230612489472720728806945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35281633305260588610151853 13230612489472720728806945)
      ·
        refine ⟨9922959367104540546605209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13230612489472720728806945 9922959367104540546605209)
        ·
          refine ⟨7442219525328405409953907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9922959367104540546605209 7442219525328405409953907)
          ·
            refine ⟨11163329287992608114930861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7442219525328405409953907 11163329287992608114930861)
            ·
              refine ⟨4186248482997228043099073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11163329287992608114930861 4186248482997228043099073)
              ·
                refine ⟨3139686362247921032324305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4186248482997228043099073 3139686362247921032324305)
                ·
                  refine ⟨2354764771685940774243229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3139686362247921032324305 2354764771685940774243229)
                  ·
                    refine ⟨883036789382227790341211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2354764771685940774243229 883036789382227790341211)
                    ·
                      rfl

theorem cell22_2579562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 3, 2, 2, 3].length) (baseStart_2579562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2579562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2579562 prefixEnd_2579562 := by exact prefixLift 2579562
  have htrace : WordTrace (prefixWord ++ tailWord_2579562) baseStart_2579562 baseEnd_2579562 := by
    simpa [prefixWord, tailWord_2579562, baseEnd_2579562] using wordTrace_append hprefix tailTrace_2579562
  have hstable : (prefixWord ++ tailWord_2579562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2579562).length < 2 ^ (prefixWord ++ tailWord_2579562).sum := by decide
  have hdescent : baseEnd_2579562 < baseStart_2579562 := by decide
  rcases family_descends (prefixWord ++ tailWord_2579562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2579592 : List Nat := [2, 1, 3, 4, 2, 2, 2, 6]
def baseStart_2579592 : Nat := 118140960795 + 2579592 * 2 ^ 59
def prefixEnd_2579592 : Nat := 4983230072969 + 3 ^ 40 * 2579592 * 2
def baseEnd_2579592 : Nat := 98116339888368634676791

theorem tailTrace_2579592 : CollatzResearch.WordTrace tailWord_2579592 prefixEnd_2579592 98116339888368634676791 := by
  unfold tailWord_2579592
  simp only [CollatzResearch.WordTrace]
  refine ⟨47042724835293109041998515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62723633113724145389331353 47042724835293109041998515)
  ·
    refine ⟨70564087252939663562997773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47042724835293109041998515 70564087252939663562997773)
    ·
      refine ⟨26461532719852373836124165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70564087252939663562997773 26461532719852373836124165)
      ·
        refine ⟨4961537384972320094273281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26461532719852373836124165 4961537384972320094273281)
        ·
          refine ⟨3721153038729240070704961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4961537384972320094273281 3721153038729240070704961)
          ·
            refine ⟨2790864779046930053028721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3721153038729240070704961 2790864779046930053028721)
            ·
              refine ⟨2093148584285197539771541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2790864779046930053028721 2093148584285197539771541)
              ·
                refine ⟨98116339888368634676791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2093148584285197539771541 98116339888368634676791)
                ·
                  rfl

theorem cell22_2579592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 2, 6].length) (baseStart_2579592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2579592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2579592 prefixEnd_2579592 := by exact prefixLift 2579592
  have htrace : WordTrace (prefixWord ++ tailWord_2579592) baseStart_2579592 baseEnd_2579592 := by
    simpa [prefixWord, tailWord_2579592, baseEnd_2579592] using wordTrace_append hprefix tailTrace_2579592
  have hstable : (prefixWord ++ tailWord_2579592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2579592).length < 2 ^ (prefixWord ++ tailWord_2579592).sum := by decide
  have hdescent : baseEnd_2579592 < baseStart_2579592 := by decide
  rcases family_descends (prefixWord ++ tailWord_2579592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2579665 : List Nat := [1, 2, 2, 1, 2, 2, 1, 7, 4]
def baseStart_2579665 : Nat := 118140960795 + 2579665 * 2 ^ 59
def prefixEnd_2579665 : Nat := 4983230072969 + 3 ^ 40 * 2579665 * 2
def baseEnd_2579665 : Nat := 294357349462389951671965

theorem tailTrace_2579665 : CollatzResearch.WordTrace tailWord_2579665 prefixEnd_2579665 294357349462389951671965 := by
  unfold tailWord_2579665
  simp only [CollatzResearch.WordTrace]
  refine ⟨94088112199321751551404449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62725408132881167700936299 94088112199321751551404449)
  ·
    refine ⟨70566084149491313663553337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94088112199321751551404449 70566084149491313663553337)
    ·
      refine ⟨52924563112118485247665003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70566084149491313663553337 52924563112118485247665003)
      ·
        refine ⟨79386844668177727871497505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52924563112118485247665003 79386844668177727871497505)
        ·
          refine ⟨59540133501133295903623129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79386844668177727871497505 59540133501133295903623129)
          ·
            refine ⟨44655100125849971927717347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59540133501133295903623129 44655100125849971927717347)
            ·
              refine ⟨66982650188774957891576021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44655100125849971927717347 66982650188774957891576021)
              ·
                refine ⟨1569905863799413075583813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 66982650188774957891576021 1569905863799413075583813)
                ·
                  refine ⟨294357349462389951671965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1569905863799413075583813 294357349462389951671965)
                  ·
                    rfl

theorem cell22_2579665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 7, 4].length) (baseStart_2579665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2579665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2579665 prefixEnd_2579665 := by exact prefixLift 2579665
  have htrace : WordTrace (prefixWord ++ tailWord_2579665) baseStart_2579665 baseEnd_2579665 := by
    simpa [prefixWord, tailWord_2579665, baseEnd_2579665] using wordTrace_append hprefix tailTrace_2579665
  have hstable : (prefixWord ++ tailWord_2579665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2579665).length < 2 ^ (prefixWord ++ tailWord_2579665).sum := by decide
  have hdescent : baseEnd_2579665 < baseStart_2579665 := by decide
  rcases family_descends (prefixWord ++ tailWord_2579665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2579753 : List Nat := [1, 2, 1, 1, 1, 1, 1, 2, 5, 7]
def baseStart_2579753 : Nat := 118140960795 + 2579753 * 2 ^ 59
def prefixEnd_2579753 : Nat := 4983230072969 + 3 ^ 40 * 2579753 * 2
def baseEnd_2579753 : Nat := 883102172585566958815625

theorem tailTrace_2579753 : CollatzResearch.WordTrace tailWord_2579753 prefixEnd_2579753 883102172585566958815625 := by
  unfold tailWord_2579753
  simp only [CollatzResearch.WordTrace]
  refine ⟨94091321823002942580607913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62727547882001961720405275 94091321823002942580607913)
  ·
    refine ⟨70568491367252206935455935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94091321823002942580607913 70568491367252206935455935)
    ·
      refine ⟨105852737050878310403183903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70568491367252206935455935 105852737050878310403183903)
      ·
        refine ⟨158779105576317465604775855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105852737050878310403183903 158779105576317465604775855)
        ·
          refine ⟨238168658364476198407163783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158779105576317465604775855 238168658364476198407163783)
          ·
            refine ⟨357252987546714297610745675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 238168658364476198407163783 357252987546714297610745675)
            ·
              refine ⟨535879481320071446416118513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 357252987546714297610745675 535879481320071446416118513)
              ·
                refine ⟨401909610990053584812088885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 535879481320071446416118513 401909610990053584812088885)
                ·
                  refine ⟨37679026030317523576133333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 401909610990053584812088885 37679026030317523576133333)
                  ·
                    refine ⟨883102172585566958815625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37679026030317523576133333 883102172585566958815625)
                    ·
                      rfl

theorem cell22_2579753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 5, 7].length) (baseStart_2579753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2579753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2579753 prefixEnd_2579753 := by exact prefixLift 2579753
  have htrace : WordTrace (prefixWord ++ tailWord_2579753) baseStart_2579753 baseEnd_2579753 := by
    simpa [prefixWord, tailWord_2579753, baseEnd_2579753] using wordTrace_append hprefix tailTrace_2579753
  have hstable : (prefixWord ++ tailWord_2579753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2579753).length < 2 ^ (prefixWord ++ tailWord_2579753).sum := by decide
  have hdescent : baseEnd_2579753 < baseStart_2579753 := by decide
  rcases family_descends (prefixWord ++ tailWord_2579753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2579847 : List Nat := [1, 1, 4, 2, 2, 2, 2, 2, 2, 4]
def baseStart_2579847 : Nat := 118140960795 + 2579847 * 2 ^ 59
def prefixEnd_2579847 : Nat := 4983230072969 + 3 ^ 40 * 2579847 * 2
def baseEnd_2579847 : Nat := 883134350706582046965337

theorem tailTrace_2579847 : CollatzResearch.WordTrace tailWord_2579847 prefixEnd_2579847 883134350706582046965337 := by
  unfold tailWord_2579847
  simp only [CollatzResearch.WordTrace]
  refine ⟨94094750284662396634529795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62729833523108264423019863 94094750284662396634529795)
  ·
    refine ⟨141142125426993594951794693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94094750284662396634529795 141142125426993594951794693)
    ·
      refine ⟨26464148517561299053461505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 141142125426993594951794693 26464148517561299053461505)
      ·
        refine ⟨19848111388170974290096129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26464148517561299053461505 19848111388170974290096129)
        ·
          refine ⟨14886083541128230717572097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19848111388170974290096129 14886083541128230717572097)
          ·
            refine ⟨11164562655846173038179073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14886083541128230717572097 11164562655846173038179073)
            ·
              refine ⟨8373421991884629778634305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11164562655846173038179073 8373421991884629778634305)
              ·
                refine ⟨6280066493913472333975729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8373421991884629778634305 6280066493913472333975729)
                ·
                  refine ⟨4710049870435104250481797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6280066493913472333975729 4710049870435104250481797)
                  ·
                    refine ⟨883134350706582046965337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4710049870435104250481797 883134350706582046965337)
                    ·
                      rfl

theorem cell22_2579847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 2, 2, 4].length) (baseStart_2579847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2579847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2579847 prefixEnd_2579847 := by exact prefixLift 2579847
  have htrace : WordTrace (prefixWord ++ tailWord_2579847) baseStart_2579847 baseEnd_2579847 := by
    simpa [prefixWord, tailWord_2579847, baseEnd_2579847] using wordTrace_append hprefix tailTrace_2579847
  have hstable : (prefixWord ++ tailWord_2579847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2579847).length < 2 ^ (prefixWord ++ tailWord_2579847).sum := by decide
  have hdescent : baseEnd_2579847 < baseStart_2579847 := by decide
  rcases family_descends (prefixWord ++ tailWord_2579847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2579875 : List Nat := [1, 1, 1, 4, 1, 3, 1, 2, 2, 6]
def baseStart_2579875 : Nat := 118140960795 + 2579875 * 2 ^ 59
def prefixEnd_2579875 : Nat := 4983230072969 + 3 ^ 40 * 2579875 * 2
def baseEnd_2579875 : Nat := 883143935678799307265251

theorem tailTrace_2579875 : CollatzResearch.WordTrace tailWord_2579875 prefixEnd_2579875 883143935678799307265251 := by
  unfold tailWord_2579875
  simp only [CollatzResearch.WordTrace]
  refine ⟨94095771528560957416549079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62730514352373971611032719 94095771528560957416549079)
  ·
    refine ⟨141143657292841436124823619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94095771528560957416549079 141143657292841436124823619)
    ·
      refine ⟨211715485939262154187235429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141143657292841436124823619 211715485939262154187235429)
      ·
        refine ⟨39696653613611653910106643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 211715485939262154187235429 39696653613611653910106643)
        ·
          refine ⟨59544980420417480865159965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39696653613611653910106643 59544980420417480865159965)
          ·
            refine ⟨22329367657656555324434987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59544980420417480865159965 22329367657656555324434987)
            ·
              refine ⟨33494051486484832986652481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22329367657656555324434987 33494051486484832986652481)
              ·
                refine ⟨25120538614863624739989361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33494051486484832986652481 25120538614863624739989361)
                ·
                  refine ⟨18840403961147718554992021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25120538614863624739989361 18840403961147718554992021)
                  ·
                    refine ⟨883143935678799307265251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18840403961147718554992021 883143935678799307265251)
                    ·
                      rfl

theorem cell22_2579875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 2, 2, 6].length) (baseStart_2579875 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2579875 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2579875 prefixEnd_2579875 := by exact prefixLift 2579875
  have htrace : WordTrace (prefixWord ++ tailWord_2579875) baseStart_2579875 baseEnd_2579875 := by
    simpa [prefixWord, tailWord_2579875, baseEnd_2579875] using wordTrace_append hprefix tailTrace_2579875
  have hstable : (prefixWord ++ tailWord_2579875).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2579875).length < 2 ^ (prefixWord ++ tailWord_2579875).sum := by decide
  have hdescent : baseEnd_2579875 < baseStart_2579875 := by decide
  rcases family_descends (prefixWord ++ tailWord_2579875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2579907 : List Nat := [1, 1, 1, 3, 1, 1, 7, 2, 5]
def baseStart_2579907 : Nat := 118140960795 + 2579907 * 2 ^ 59
def prefixEnd_2579907 : Nat := 4983230072969 + 3 ^ 40 * 2579907 * 2
def baseEnd_2579907 : Nat := 294384963310920630155051

theorem tailTrace_2579907 : CollatzResearch.WordTrace tailWord_2579907 prefixEnd_2579907 294384963310920630155051 := by
  unfold tailWord_2579907
  simp only [CollatzResearch.WordTrace]
  refine ⟨94096938664445026881713975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62731292442963351254475983 94096938664445026881713975)
  ·
    refine ⟨141145407996667540322570963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94096938664445026881713975 141145407996667540322570963)
    ·
      refine ⟨211718111995001310483856445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141145407996667540322570963 211718111995001310483856445)
      ·
        refine ⟨79394291998125491431446167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 211718111995001310483856445 79394291998125491431446167)
        ·
          refine ⟨119091437997188237147169251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79394291998125491431446167 119091437997188237147169251)
          ·
            refine ⟨178637156995782355720753877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119091437997188237147169251 178637156995782355720753877)
            ·
              refine ⟨4186808367088648962205169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 178637156995782355720753877 4186808367088648962205169)
              ·
                refine ⟨3140106275316486721653877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4186808367088648962205169 3140106275316486721653877)
                ·
                  refine ⟨294384963310920630155051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3140106275316486721653877 294384963310920630155051)
                  ·
                    rfl

theorem cell22_2579907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 7, 2, 5].length) (baseStart_2579907 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2579907 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2579907 prefixEnd_2579907 := by exact prefixLift 2579907
  have htrace : WordTrace (prefixWord ++ tailWord_2579907) baseStart_2579907 baseEnd_2579907 := by
    simpa [prefixWord, tailWord_2579907, baseEnd_2579907] using wordTrace_append hprefix tailTrace_2579907
  have hstable : (prefixWord ++ tailWord_2579907).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2579907).length < 2 ^ (prefixWord ++ tailWord_2579907).sum := by decide
  have hdescent : baseEnd_2579907 < baseStart_2579907 := by decide
  rcases family_descends (prefixWord ++ tailWord_2579907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2579997 : List Nat := [1, 4, 2, 2, 1, 1, 1, 10]
def baseStart_2579997 : Nat := 118140960795 + 2579997 * 2 ^ 59
def prefixEnd_2579997 : Nat := 4983230072969 + 3 ^ 40 * 2579997 * 2
def baseEnd_2579997 : Nat := 98131744308003517301653

theorem tailTrace_2579997 : CollatzResearch.WordTrace tailWord_2579997 prefixEnd_2579997 98131744308003517301653 := by
  unfold tailWord_2579997
  simp only [CollatzResearch.WordTrace]
  refine ⟨94100221234118972252490245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62733480822745981501660163 94100221234118972252490245)
  ·
    refine ⟨17643791481397307297341921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94100221234118972252490245 17643791481397307297341921)
    ·
      refine ⟨13232843611047980473006441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17643791481397307297341921 13232843611047980473006441)
      ·
        refine ⟨9924632708285985354754831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13232843611047980473006441 9924632708285985354754831)
        ·
          refine ⟨14886949062428978032132247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9924632708285985354754831 14886949062428978032132247)
          ·
            refine ⟨22330423593643467048198371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14886949062428978032132247 22330423593643467048198371)
            ·
              refine ⟨33495635390465200572297557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22330423593643467048198371 33495635390465200572297557)
              ·
                refine ⟨98131744308003517301653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 33495635390465200572297557 98131744308003517301653)
                ·
                  rfl

theorem cell22_2579997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 10].length) (baseStart_2579997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2579997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2579997 prefixEnd_2579997 := by exact prefixLift 2579997
  have htrace : WordTrace (prefixWord ++ tailWord_2579997) baseStart_2579997 baseEnd_2579997 := by
    simpa [prefixWord, tailWord_2579997, baseEnd_2579997] using wordTrace_append hprefix tailTrace_2579997
  have hstable : (prefixWord ++ tailWord_2579997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2579997).length < 2 ^ (prefixWord ++ tailWord_2579997).sum := by decide
  have hdescent : baseEnd_2579997 < baseStart_2579997 := by decide
  rcases family_descends (prefixWord ++ tailWord_2579997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2580074 : List Nat := [3, 1, 3, 2, 1, 2, 1, 2, 2, 5]
def baseStart_2580074 : Nat := 118140960795 + 2580074 * 2 ^ 59
def prefixEnd_2580074 : Nat := 4983230072969 + 3 ^ 40 * 2580074 * 2
def baseEnd_2580074 : Nat := 883212057445629121539641

theorem tailTrace_2580074 : CollatzResearch.WordTrace tailWord_2580074 prefixEnd_2580074 883212057445629121539641 := by
  unfold tailWord_2580074
  simp only [CollatzResearch.WordTrace]
  refine ⟨23525757413710003600760819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62735353103226676268695517 23525757413710003600760819)
  ·
    refine ⟨35288636120565005401141229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23525757413710003600760819 35288636120565005401141229)
    ·
      refine ⟨13233238545211877025427961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35288636120565005401141229 13233238545211877025427961)
      ·
        refine ⟨9924928908908907769070971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13233238545211877025427961 9924928908908907769070971)
        ·
          refine ⟨14887393363363361653606457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9924928908908907769070971 14887393363363361653606457)
          ·
            refine ⟨11165545022522521240204843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14887393363363361653606457 11165545022522521240204843)
            ·
              refine ⟨16748317533783781860307265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11165545022522521240204843 16748317533783781860307265)
              ·
                refine ⟨12561238150337836395230449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16748317533783781860307265 12561238150337836395230449)
                ·
                  refine ⟨9420928612753377296422837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12561238150337836395230449 9420928612753377296422837)
                  ·
                    refine ⟨883212057445629121539641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9420928612753377296422837 883212057445629121539641)
                    ·
                      rfl

theorem cell22_2580074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 2, 2, 5].length) (baseStart_2580074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2580074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2580074 prefixEnd_2580074 := by exact prefixLift 2580074
  have htrace : WordTrace (prefixWord ++ tailWord_2580074) baseStart_2580074 baseEnd_2580074 := by
    simpa [prefixWord, tailWord_2580074, baseEnd_2580074] using wordTrace_append hprefix tailTrace_2580074
  have hstable : (prefixWord ++ tailWord_2580074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2580074).length < 2 ^ (prefixWord ++ tailWord_2580074).sum := by decide
  have hdescent : baseEnd_2580074 < baseStart_2580074 := by decide
  rcases family_descends (prefixWord ++ tailWord_2580074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2580106 : List Nat := [3, 1, 2, 3, 2, 1, 1, 4, 1, 4]
def baseStart_2580106 : Nat := 118140960795 + 2580106 * 2 ^ 59
def prefixEnd_2580106 : Nat := 4983230072969 + 3 ^ 40 * 2580106 * 2
def baseEnd_2580106 : Nat := 883223011699591704739543

theorem tailTrace_2580106 : CollatzResearch.WordTrace tailWord_2580106 prefixEnd_2580106 883223011699591704739543 := by
  unfold tailWord_2580106
  simp only [CollatzResearch.WordTrace]
  refine ⟨23526049197681020967052043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62736131193816055912138781 23526049197681020967052043)
  ·
    refine ⟨35289073796521531450578065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23526049197681020967052043 35289073796521531450578065)
    ·
      refine ⟨26466805347391148587933549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35289073796521531450578065 26466805347391148587933549)
      ·
        refine ⟨9925052005271680720475081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26466805347391148587933549 9925052005271680720475081)
        ·
          refine ⟨7443789003953760540356311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9925052005271680720475081 7443789003953760540356311)
          ·
            refine ⟨11165683505930640810534467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7443789003953760540356311 11165683505930640810534467)
            ·
              refine ⟨16748525258895961215801701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11165683505930640810534467 16748525258895961215801701)
              ·
                refine ⟨3140348486042992727962819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16748525258895961215801701 3140348486042992727962819)
                ·
                  refine ⟨4710522729064489091944229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3140348486042992727962819 4710522729064489091944229)
                  ·
                    refine ⟨883223011699591704739543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4710522729064489091944229 883223011699591704739543)
                    ·
                      rfl

theorem cell22_2580106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 4, 1, 4].length) (baseStart_2580106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2580106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2580106 prefixEnd_2580106 := by exact prefixLift 2580106
  have htrace : WordTrace (prefixWord ++ tailWord_2580106) baseStart_2580106 baseEnd_2580106 := by
    simpa [prefixWord, tailWord_2580106, baseEnd_2580106] using wordTrace_append hprefix tailTrace_2580106
  have hstable : (prefixWord ++ tailWord_2580106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2580106).length < 2 ^ (prefixWord ++ tailWord_2580106).sum := by decide
  have hdescent : baseEnd_2580106 < baseStart_2580106 := by decide
  rcases family_descends (prefixWord ++ tailWord_2580106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2580153 : List Nat := [1, 2, 1, 4, 1, 1, 6, 1, 2, 3]
def baseStart_2580153 : Nat := 118140960795 + 2580153 * 2 ^ 59
def prefixEnd_2580153 : Nat := 4983230072969 + 3 ^ 40 * 2580153 * 2
def baseEnd_2580153 : Nat := 883239100760099248814399

theorem tailTrace_2580153 : CollatzResearch.WordTrace tailWord_2580153 prefixEnd_2580153 883239100760099248814399 := by
  unfold tailWord_2580153
  simp only [CollatzResearch.WordTrace]
  refine ⟨94105911021553810895169113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62737274014369207263446075 94105911021553810895169113)
  ·
    refine ⟨70579433266165358171376835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94105911021553810895169113 70579433266165358171376835)
    ·
      refine ⟨105869149899248037257065253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70579433266165358171376835 105869149899248037257065253)
      ·
        refine ⟨19850465606109006985699735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 105869149899248037257065253 19850465606109006985699735)
        ·
          refine ⟨29775698409163510478549603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19850465606109006985699735 29775698409163510478549603)
          ·
            refine ⟨44663547613745265717824405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29775698409163510478549603 44663547613745265717824405)
            ·
              refine ⟨2093603794394309330523019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 44663547613745265717824405 2093603794394309330523019)
              ·
                refine ⟨3140405691591463995784529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2093603794394309330523019 3140405691591463995784529)
                ·
                  refine ⟨2355304268693597996838397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3140405691591463995784529 2355304268693597996838397)
                  ·
                    refine ⟨883239100760099248814399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2355304268693597996838397 883239100760099248814399)
                    ·
                      rfl

theorem cell22_2580153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 6, 1, 2, 3].length) (baseStart_2580153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2580153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2580153 prefixEnd_2580153 := by exact prefixLift 2580153
  have htrace : WordTrace (prefixWord ++ tailWord_2580153) baseStart_2580153 baseEnd_2580153 := by
    simpa [prefixWord, tailWord_2580153, baseEnd_2580153] using wordTrace_append hprefix tailTrace_2580153
  have hstable : (prefixWord ++ tailWord_2580153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2580153).length < 2 ^ (prefixWord ++ tailWord_2580153).sum := by decide
  have hdescent : baseEnd_2580153 < baseStart_2580153 := by decide
  rcases family_descends (prefixWord ++ tailWord_2580153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2580189 : List Nat := [1, 4, 3, 3, 2, 1, 2, 2, 4]
def baseStart_2580189 : Nat := 118140960795 + 2580189 * 2 ^ 59
def prefixEnd_2580189 : Nat := 4983230072969 + 3 ^ 40 * 2580189 * 2
def baseEnd_2580189 : Nat := 294417141431935718304763

theorem tailTrace_2580189 : CollatzResearch.WordTrace tailWord_2580189 prefixEnd_2580189 294417141431935718304763 := by
  unfold tailWord_2580189
  simp only [CollatzResearch.WordTrace]
  refine ⟨94107224049423389043479621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62738149366282259362319747 94107224049423389043479621)
  ·
    refine ⟨17645104509266885445652429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94107224049423389043479621 17645104509266885445652429)
    ·
      refine ⟨6616914190975082042119661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17645104509266885445652429 6616914190975082042119661)
      ·
        refine ⟨2481342821615655765794873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6616914190975082042119661 2481342821615655765794873)
        ·
          refine ⟨1861007116211741824346155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2481342821615655765794873 1861007116211741824346155)
          ·
            refine ⟨2791510674317612736519233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1861007116211741824346155 2791510674317612736519233)
            ·
              refine ⟨2093633005738209552389425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2791510674317612736519233 2093633005738209552389425)
              ·
                refine ⟨1570224754303657164292069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2093633005738209552389425 1570224754303657164292069)
                ·
                  refine ⟨294417141431935718304763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1570224754303657164292069 294417141431935718304763)
                  ·
                    rfl

theorem cell22_2580189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 2, 2, 4].length) (baseStart_2580189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2580189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2580189 prefixEnd_2580189 := by exact prefixLift 2580189
  have htrace : WordTrace (prefixWord ++ tailWord_2580189) baseStart_2580189 baseEnd_2580189 := by
    simpa [prefixWord, tailWord_2580189, baseEnd_2580189] using wordTrace_append hprefix tailTrace_2580189
  have hstable : (prefixWord ++ tailWord_2580189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2580189).length < 2 ^ (prefixWord ++ tailWord_2580189).sum := by decide
  have hdescent : baseEnd_2580189 < baseStart_2580189 := by decide
  rcases family_descends (prefixWord ++ tailWord_2580189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2580209 : List Nat := [1, 2, 2, 2, 2, 3, 1, 1, 1, 7]
def baseStart_2580209 : Nat := 118140960795 + 2580209 * 2 ^ 59
def prefixEnd_2580209 : Nat := 4983230072969 + 3 ^ 40 * 2580209 * 2
def baseEnd_2580209 : Nat := 883258270704533769414227

theorem tailTrace_2580209 : CollatzResearch.WordTrace tailWord_2580209 prefixEnd_2580209 883258270704533769414227 := by
  unfold tailWord_2580209
  simp only [CollatzResearch.WordTrace]
  refine ⟨94107953509350932459207681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62738635672900621639471787 94107953509350932459207681)
  ·
    refine ⟨70580965132013199344405761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94107953509350932459207681 70580965132013199344405761)
    ·
      refine ⟨52935723849009899508304321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70580965132013199344405761 52935723849009899508304321)
      ·
        refine ⟨39701792886757424631228241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52935723849009899508304321 39701792886757424631228241)
        ·
          refine ⟨29776344665068068473421181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39701792886757424631228241 29776344665068068473421181)
          ·
            refine ⟨11166129249400525677532943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29776344665068068473421181 11166129249400525677532943)
            ·
              refine ⟨16749193874100788516299415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11166129249400525677532943 16749193874100788516299415)
              ·
                refine ⟨25123790811151182774449123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16749193874100788516299415 25123790811151182774449123)
                ·
                  refine ⟨37685686216726774161673685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25123790811151182774449123 37685686216726774161673685)
                  ·
                    refine ⟨883258270704533769414227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37685686216726774161673685 883258270704533769414227)
                    ·
                      rfl

theorem cell22_2580209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 1, 1, 7].length) (baseStart_2580209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2580209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2580209 prefixEnd_2580209 := by exact prefixLift 2580209
  have htrace : WordTrace (prefixWord ++ tailWord_2580209) baseStart_2580209 baseEnd_2580209 := by
    simpa [prefixWord, tailWord_2580209, baseEnd_2580209] using wordTrace_append hprefix tailTrace_2580209
  have hstable : (prefixWord ++ tailWord_2580209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2580209).length < 2 ^ (prefixWord ++ tailWord_2580209).sum := by decide
  have hdescent : baseEnd_2580209 < baseStart_2580209 := by decide
  rcases family_descends (prefixWord ++ tailWord_2580209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2580226 : List Nat := [3, 4, 1, 1, 1, 1, 1, 2, 1, 7]
def baseStart_2580226 : Nat := 118140960795 + 2580226 * 2 ^ 59
def prefixEnd_2580226 : Nat := 4983230072969 + 3 ^ 40 * 2580226 * 2
def baseEnd_2580226 : Nat := 883264090151951391739175

theorem tailTrace_2580226 : CollatzResearch.WordTrace tailWord_2580226 prefixEnd_2580226 883264090151951391739175 := by
  unfold tailWord_2580226
  simp only [CollatzResearch.WordTrace]
  refine ⟨23527143387572336090644133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62739049033526229575051021 23527143387572336090644133)
  ·
    refine ⟨4411339385169813016995775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23527143387572336090644133 4411339385169813016995775)
    ·
      refine ⟨6617009077754719525493663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4411339385169813016995775 6617009077754719525493663)
      ·
        refine ⟨9925513616632079288240495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6617009077754719525493663 9925513616632079288240495)
        ·
          refine ⟨14888270424948118932360743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9925513616632079288240495 14888270424948118932360743)
          ·
            refine ⟨22332405637422178398541115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14888270424948118932360743 22332405637422178398541115)
            ·
              refine ⟨33498608456133267597811673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22332405637422178398541115 33498608456133267597811673)
              ·
                refine ⟨25123956342099950698358755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33498608456133267597811673 25123956342099950698358755)
                ·
                  refine ⟨37685934513149926047538133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25123956342099950698358755 37685934513149926047538133)
                  ·
                    refine ⟨883264090151951391739175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37685934513149926047538133 883264090151951391739175)
                    ·
                      rfl

theorem cell22_2580226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_2580226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2580226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2580226 prefixEnd_2580226 := by exact prefixLift 2580226
  have htrace : WordTrace (prefixWord ++ tailWord_2580226) baseStart_2580226 baseEnd_2580226 := by
    simpa [prefixWord, tailWord_2580226, baseEnd_2580226] using wordTrace_append hprefix tailTrace_2580226
  have hstable : (prefixWord ++ tailWord_2580226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2580226).length < 2 ^ (prefixWord ++ tailWord_2580226).sum := by decide
  have hdescent : baseEnd_2580226 < baseStart_2580226 := by decide
  rcases family_descends (prefixWord ++ tailWord_2580226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2580256 : List Nat := [2, 1, 1, 5, 1, 1, 4, 1, 6]
def baseStart_2580256 : Nat := 118140960795 + 2580256 * 2 ^ 59
def prefixEnd_2580256 : Nat := 4983230072969 + 3 ^ 40 * 2580256 * 2
def baseEnd_2580256 : Nat := 294424786588347104496361

theorem tailTrace_2580256 : CollatzResearch.WordTrace tailWord_2580256 prefixEnd_2580256 294424786588347104496361 := by
  unfold tailWord_2580256
  simp only [CollatzResearch.WordTrace]
  refine ⟨47054833870090329743084311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62739778493453772990779081 47054833870090329743084311)
  ·
    refine ⟨70582250805135494614626467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47054833870090329743084311 70582250805135494614626467)
    ·
      refine ⟨105873376207703241921939701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70582250805135494614626467 105873376207703241921939701)
      ·
        refine ⟨9925629019472178930181847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 105873376207703241921939701 9925629019472178930181847)
        ·
          refine ⟨14888443529208268395272771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9925629019472178930181847 14888443529208268395272771)
          ·
            refine ⟨22332665293812402592909157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14888443529208268395272771 22332665293812402592909157)
            ·
              refine ⟨4187374742589825486170467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22332665293812402592909157 4187374742589825486170467)
              ·
                refine ⟨6281062113884738229255701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4187374742589825486170467 6281062113884738229255701)
                ·
                  refine ⟨294424786588347104496361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6281062113884738229255701 294424786588347104496361)
                  ·
                    rfl

theorem cell22_2580256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 4, 1, 6].length) (baseStart_2580256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2580256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2580256 prefixEnd_2580256 := by exact prefixLift 2580256
  have htrace : WordTrace (prefixWord ++ tailWord_2580256) baseStart_2580256 baseEnd_2580256 := by
    simpa [prefixWord, tailWord_2580256, baseEnd_2580256] using wordTrace_append hprefix tailTrace_2580256
  have hstable : (prefixWord ++ tailWord_2580256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2580256).length < 2 ^ (prefixWord ++ tailWord_2580256).sum := by decide
  have hdescent : baseEnd_2580256 < baseStart_2580256 := by decide
  rcases family_descends (prefixWord ++ tailWord_2580256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2580322 : List Nat := [3, 3, 2, 1, 2, 1, 4, 1, 2, 3]
def baseStart_2580322 : Nat := 118140960795 + 2580322 * 2 ^ 59
def prefixEnd_2580322 : Nat := 4983230072969 + 3 ^ 40 * 2580322 * 2
def baseEnd_2580322 : Nat := 883296952913839141338881

theorem tailTrace_2580322 : CollatzResearch.WordTrace tailWord_2580322 prefixEnd_2580322 883296952913839141338881 := by
  unfold tailWord_2580322
  simp only [CollatzResearch.WordTrace]
  refine ⟨23528018739485388189517805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62741383305294368505380813 23528018739485388189517805)
  ·
    refine ⟨8823007027307020571069177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23528018739485388189517805 8823007027307020571069177)
    ·
      refine ⟨6617255270480265428301883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8823007027307020571069177 6617255270480265428301883)
      ·
        refine ⟨9925882905720398142452825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6617255270480265428301883 9925882905720398142452825)
        ·
          refine ⟨7444412179290298606839619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9925882905720398142452825 7444412179290298606839619)
          ·
            refine ⟨11166618268935447910259429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7444412179290298606839619 11166618268935447910259429)
            ·
              refine ⟨2093740925425396483173643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11166618268935447910259429 2093740925425396483173643)
              ·
                refine ⟨3140611388138094724760465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2093740925425396483173643 3140611388138094724760465)
                ·
                  refine ⟨2355458541103571043570349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3140611388138094724760465 2355458541103571043570349)
                  ·
                    refine ⟨883296952913839141338881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2355458541103571043570349 883296952913839141338881)
                    ·
                      rfl

theorem cell22_2580322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 4, 1, 2, 3].length) (baseStart_2580322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2580322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2580322 prefixEnd_2580322 := by exact prefixLift 2580322
  have htrace : WordTrace (prefixWord ++ tailWord_2580322) baseStart_2580322 baseEnd_2580322 := by
    simpa [prefixWord, tailWord_2580322, baseEnd_2580322] using wordTrace_append hprefix tailTrace_2580322
  have hstable : (prefixWord ++ tailWord_2580322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2580322).length < 2 ^ (prefixWord ++ tailWord_2580322).sum := by decide
  have hdescent : baseEnd_2580322 < baseStart_2580322 := by decide
  rcases family_descends (prefixWord ++ tailWord_2580322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2580333 : List Nat := [1, 5, 1, 1, 1, 1, 2, 4, 3, 3]
def baseStart_2580333 : Nat := 118140960795 + 2580333 * 2 ^ 59
def prefixEnd_2580333 : Nat := 4983230072969 + 3 ^ 40 * 2580333 * 2
def baseEnd_2580333 : Nat := 883300718438638779313847

theorem tailTrace_2580333 : CollatzResearch.WordTrace tailWord_2580333 prefixEnd_2580333 883300718438638779313847 := by
  unfold tailWord_2580333
  simp only [CollatzResearch.WordTrace]
  refine ⟨94112476160901701636721653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62741650773934467757814435 94112476160901701636721653)
  ·
    refine ⟨8823044640084534528442655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 94112476160901701636721653 8823044640084534528442655)
    ·
      refine ⟨13234566960126801792663983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8823044640084534528442655 13234566960126801792663983)
      ·
        refine ⟨19851850440190202688995975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13234566960126801792663983 19851850440190202688995975)
        ·
          refine ⟨29777775660285304033493963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19851850440190202688995975 29777775660285304033493963)
          ·
            refine ⟨44666663490427956050240945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29777775660285304033493963 44666663490427956050240945)
            ·
              refine ⟨33499997617820967037680709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44666663490427956050240945 33499997617820967037680709)
              ·
                refine ⟨6281249553341431319565133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33499997617820967037680709 6281249553341431319565133)
                ·
                  refine ⟨2355468582503036744836925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6281249553341431319565133 2355468582503036744836925)
                  ·
                    refine ⟨883300718438638779313847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2355468582503036744836925 883300718438638779313847)
                    ·
                      rfl

theorem cell22_2580333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 4, 3, 3].length) (baseStart_2580333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2580333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2580333 prefixEnd_2580333 := by exact prefixLift 2580333
  have htrace : WordTrace (prefixWord ++ tailWord_2580333) baseStart_2580333 baseEnd_2580333 := by
    simpa [prefixWord, tailWord_2580333, baseEnd_2580333] using wordTrace_append hprefix tailTrace_2580333
  have hstable : (prefixWord ++ tailWord_2580333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2580333).length < 2 ^ (prefixWord ++ tailWord_2580333).sum := by decide
  have hdescent : baseEnd_2580333 < baseStart_2580333 := by decide
  rcases family_descends (prefixWord ++ tailWord_2580333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2580361 : List Nat := [1, 2, 1, 1, 5, 1, 2, 2, 2, 5]
def baseStart_2580361 : Nat := 118140960795 + 2580361 * 2 ^ 59
def prefixEnd_2580361 : Nat := 4983230072969 + 3 ^ 40 * 2580361 * 2
def baseEnd_2580361 : Nat := 883310303410856039613761

theorem tailTrace_2580361 : CollatzResearch.WordTrace tailWord_2580361 prefixEnd_2580361 883310303410856039613761 := by
  unfold tailWord_2580361
  simp only [CollatzResearch.WordTrace]
  refine ⟨94113497404800262418740937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62742331603200174945827291 94113497404800262418740937)
  ·
    refine ⟨70585123053600196814055703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94113497404800262418740937 70585123053600196814055703)
    ·
      refine ⟨105877684580400295221083555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70585123053600196814055703 105877684580400295221083555)
      ·
        refine ⟨158816526870600442831625333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105877684580400295221083555 158816526870600442831625333)
        ·
          refine ⟨14889049394118791515464875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 158816526870600442831625333 14889049394118791515464875)
          ·
            refine ⟨22333574091178187273197313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14889049394118791515464875 22333574091178187273197313)
            ·
              refine ⟨16750180568383640454897985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22333574091178187273197313 16750180568383640454897985)
              ·
                refine ⟨12562635426287730341173489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16750180568383640454897985 12562635426287730341173489)
                ·
                  refine ⟨9421976569715797755880117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12562635426287730341173489 9421976569715797755880117)
                  ·
                    refine ⟨883310303410856039613761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9421976569715797755880117 883310303410856039613761)
                    ·
                      rfl

theorem cell22_2580361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 2, 2, 5].length) (baseStart_2580361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2580361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2580361 prefixEnd_2580361 := by exact prefixLift 2580361
  have htrace : WordTrace (prefixWord ++ tailWord_2580361) baseStart_2580361 baseEnd_2580361 := by
    simpa [prefixWord, tailWord_2580361, baseEnd_2580361] using wordTrace_append hprefix tailTrace_2580361
  have hstable : (prefixWord ++ tailWord_2580361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2580361).length < 2 ^ (prefixWord ++ tailWord_2580361).sum := by decide
  have hdescent : baseEnd_2580361 < baseStart_2580361 := by decide
  rcases family_descends (prefixWord ++ tailWord_2580361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2580378 : List Nat := [3, 1, 1, 4, 2, 2, 1, 1, 2, 5]
def baseStart_2580378 : Nat := 118140960795 + 2580378 * 2 ^ 59
def prefixEnd_2580378 : Nat := 4983230072969 + 3 ^ 40 * 2580378 * 2
def baseEnd_2580378 : Nat := 883316122858273661938709

theorem tailTrace_2580378 : CollatzResearch.WordTrace tailWord_2580378 prefixEnd_2580378 883316122858273661938709 := by
  unfold tailWord_2580378
  simp only [CollatzResearch.WordTrace]
  refine ⟨23528529361434668580527447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62742744963825782881406525 23528529361434668580527447)
  ·
    refine ⟨35292794042152002870791171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23528529361434668580527447 35292794042152002870791171)
    ·
      refine ⟨52939191063228004306186757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35292794042152002870791171 52939191063228004306186757)
      ·
        refine ⟨9926098324355250807410017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52939191063228004306186757 9926098324355250807410017)
        ·
          refine ⟨7444573743266438105557513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9926098324355250807410017 7444573743266438105557513)
          ·
            refine ⟨5583430307449828579168135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7444573743266438105557513 5583430307449828579168135)
            ·
              refine ⟨8375145461174742868752203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5583430307449828579168135 8375145461174742868752203)
              ·
                refine ⟨12562718191762114303128305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8375145461174742868752203 12562718191762114303128305)
                ·
                  refine ⟨9422038643821585727346229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12562718191762114303128305 9422038643821585727346229)
                  ·
                    refine ⟨883316122858273661938709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9422038643821585727346229 883316122858273661938709)
                    ·
                      rfl

theorem cell22_2580378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 1, 2, 5].length) (baseStart_2580378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2580378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2580378 prefixEnd_2580378 := by exact prefixLift 2580378
  have htrace : WordTrace (prefixWord ++ tailWord_2580378) baseStart_2580378 baseEnd_2580378 := by
    simpa [prefixWord, tailWord_2580378, baseEnd_2580378] using wordTrace_append hprefix tailTrace_2580378
  have hstable : (prefixWord ++ tailWord_2580378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2580378).length < 2 ^ (prefixWord ++ tailWord_2580378).sum := by decide
  have hdescent : baseEnd_2580378 < baseStart_2580378 := by decide
  rcases family_descends (prefixWord ++ tailWord_2580378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2580470 : List Nat := [5, 1, 1, 1, 4, 2, 8]
def baseStart_2580470 : Nat := 118140960795 + 2580470 * 2 ^ 59
def prefixEnd_2580470 : Nat := 4983230072969 + 3 ^ 40 * 2580470 * 2
def baseEnd_2580470 : Nat := 32716578382904299579201

theorem tailTrace_2580470 : CollatzResearch.WordTrace tailWord_2580470 prefixEnd_2580470 32716578382904299579201 := by
  unfold tailWord_2580470
  simp only [CollatzResearch.WordTrace]
  refine ⟨5882342060087835877153679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 62744981974270249356305909 5882342060087835877153679)
  ·
    refine ⟨8823513090131753815730519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5882342060087835877153679 8823513090131753815730519)
    ·
      refine ⟨13235269635197630723595779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8823513090131753815730519 13235269635197630723595779)
      ·
        refine ⟨19852904452796446085393669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13235269635197630723595779 19852904452796446085393669)
        ·
          refine ⟨3722419584899333641011313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19852904452796446085393669 3722419584899333641011313)
          ·
            refine ⟨2791814688674500230758485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3722419584899333641011313 2791814688674500230758485)
            ·
              refine ⟨32716578382904299579201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2791814688674500230758485 32716578382904299579201)
              ·
                rfl

theorem cell22_2580470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 8].length) (baseStart_2580470 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2580470 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2580470 prefixEnd_2580470 := by exact prefixLift 2580470
  have htrace : WordTrace (prefixWord ++ tailWord_2580470) baseStart_2580470 baseEnd_2580470 := by
    simpa [prefixWord, tailWord_2580470, baseEnd_2580470] using wordTrace_append hprefix tailTrace_2580470
  have hstable : (prefixWord ++ tailWord_2580470).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2580470).length < 2 ^ (prefixWord ++ tailWord_2580470).sum := by decide
  have hdescent : baseEnd_2580470 < baseStart_2580470 := by decide
  rcases family_descends (prefixWord ++ tailWord_2580470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2580485 : List Nat := [1, 3, 1, 1, 2, 4, 3, 1, 3, 3]
def baseStart_2580485 : Nat := 118140960795 + 2580485 * 2 ^ 59
def prefixEnd_2580485 : Nat := 4983230072969 + 3 ^ 40 * 2580485 * 2
def baseEnd_2580485 : Nat := 883352751144961049513381

theorem tailTrace_2580485 : CollatzResearch.WordTrace tailWord_2580485 prefixEnd_2580485 883352751144961049513381 := by
  unfold tailWord_2580485
  simp only [CollatzResearch.WordTrace]
  refine ⟨94118020056351031596254909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62745346704234021064169939 94118020056351031596254909)
  ·
    refine ⟨35294257521131636848595591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94118020056351031596254909 35294257521131636848595591)
    ·
      refine ⟨52941386281697455272893387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35294257521131636848595591 52941386281697455272893387)
      ·
        refine ⟨79412079422546182909340081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52941386281697455272893387 79412079422546182909340081)
        ·
          refine ⟨59559059566909637182005061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79412079422546182909340081 59559059566909637182005061)
          ·
            refine ⟨11167323668795556971625949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59559059566909637182005061 11167323668795556971625949)
            ·
              refine ⟨4187746375798333864359731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11167323668795556971625949 4187746375798333864359731)
              ·
                refine ⟨6281619563697500796539597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4187746375798333864359731 6281619563697500796539597)
                ·
                  refine ⟨2355607336386562798702349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6281619563697500796539597 2355607336386562798702349)
                  ·
                    refine ⟨883352751144961049513381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2355607336386562798702349 883352751144961049513381)
                    ·
                      rfl

theorem cell22_2580485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 3, 3].length) (baseStart_2580485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2580485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2580485 prefixEnd_2580485 := by exact prefixLift 2580485
  have htrace : WordTrace (prefixWord ++ tailWord_2580485) baseStart_2580485 baseEnd_2580485 := by
    simpa [prefixWord, tailWord_2580485, baseEnd_2580485] using wordTrace_append hprefix tailTrace_2580485
  have hstable : (prefixWord ++ tailWord_2580485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2580485).length < 2 ^ (prefixWord ++ tailWord_2580485).sum := by decide
  have hdescent : baseEnd_2580485 < baseStart_2580485 := by decide
  rcases family_descends (prefixWord ++ tailWord_2580485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2580536 : List Nat := [2, 1, 2, 1, 6, 2, 2, 2, 1, 3]
def baseStart_2580536 : Nat := 118140960795 + 2580536 * 2 ^ 59
def prefixEnd_2580536 : Nat := 4983230072969 + 3 ^ 40 * 2580536 * 2
def baseEnd_2580536 : Nat := 883370209487213916488225

theorem tailTrace_2580536 : CollatzResearch.WordTrace tailWord_2580536 prefixEnd_2580536 883370209487213916488225 := by
  unfold tailWord_2580536
  simp only [CollatzResearch.WordTrace]
  refine ⟨47059940089583133653180731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62746586786110844870907641 47059940089583133653180731)
  ·
    refine ⟨70589910134374700479771097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47059940089583133653180731 70589910134374700479771097)
    ·
      refine ⟨52942432600781025359828323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70589910134374700479771097 52942432600781025359828323)
      ·
        refine ⟨79413648901171538039742485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52942432600781025359828323 79413648901171538039742485)
        ·
          refine ⟨3722514792242415845612929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 79413648901171538039742485 3722514792242415845612929)
          ·
            refine ⟨2791886094181811884209697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3722514792242415845612929 2791886094181811884209697)
            ·
              refine ⟨2093914570636358913157273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2791886094181811884209697 2093914570636358913157273)
              ·
                refine ⟨1570435927977269184867955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2093914570636358913157273 1570435927977269184867955)
                ·
                  refine ⟨2355653891965903777301933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1570435927977269184867955 2355653891965903777301933)
                  ·
                    refine ⟨883370209487213916488225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2355653891965903777301933 883370209487213916488225)
                    ·
                      rfl

theorem cell22_2580536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 2, 2, 1, 3].length) (baseStart_2580536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2580536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2580536 prefixEnd_2580536 := by exact prefixLift 2580536
  have htrace : WordTrace (prefixWord ++ tailWord_2580536) baseStart_2580536 baseEnd_2580536 := by
    simpa [prefixWord, tailWord_2580536, baseEnd_2580536] using wordTrace_append hprefix tailTrace_2580536
  have hstable : (prefixWord ++ tailWord_2580536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2580536).length < 2 ^ (prefixWord ++ tailWord_2580536).sum := by decide
  have hdescent : baseEnd_2580536 < baseStart_2580536 := by decide
  rcases family_descends (prefixWord ++ tailWord_2580536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2580545 : List Nat := [1, 2, 5, 1, 2, 1, 1, 2, 3, 4]
def baseStart_2580545 : Nat := 118140960795 + 2580545 * 2 ^ 59
def prefixEnd_2580545 : Nat := 4983230072969 + 3 ^ 40 * 2580545 * 2
def baseEnd_2580545 : Nat := 883373290371140893013197

theorem tailTrace_2580545 : CollatzResearch.WordTrace tailWord_2580545 prefixEnd_2580545 883373290371140893013197 := by
  unfold tailWord_2580545
  simp only [CollatzResearch.WordTrace]
  refine ⟨94120208436133661843439089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62746805624089107895626059 94120208436133661843439089)
  ·
    refine ⟨70590156327100246382579317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94120208436133661843439089 70590156327100246382579317)
    ·
      refine ⟨6617827155665648098366811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 70590156327100246382579317 6617827155665648098366811)
      ·
        refine ⟨9926740733498472147550217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6617827155665648098366811 9926740733498472147550217)
        ·
          refine ⟨7445055550123854110662663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9926740733498472147550217 7445055550123854110662663)
          ·
            refine ⟨11167583325185781165993995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7445055550123854110662663 11167583325185781165993995)
            ·
              refine ⟨16751374987778671748990993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11167583325185781165993995 16751374987778671748990993)
              ·
                refine ⟨12563531240834003811743245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16751374987778671748990993 12563531240834003811743245)
                ·
                  refine ⟨4711324215312751429403717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12563531240834003811743245 4711324215312751429403717)
                  ·
                    refine ⟨883373290371140893013197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4711324215312751429403717 883373290371140893013197)
                    ·
                      rfl

theorem cell22_2580545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_2580545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2580545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2580545 prefixEnd_2580545 := by exact prefixLift 2580545
  have htrace : WordTrace (prefixWord ++ tailWord_2580545) baseStart_2580545 baseEnd_2580545 := by
    simpa [prefixWord, tailWord_2580545, baseEnd_2580545] using wordTrace_append hprefix tailTrace_2580545
  have hstable : (prefixWord ++ tailWord_2580545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2580545).length < 2 ^ (prefixWord ++ tailWord_2580545).sum := by decide
  have hdescent : baseEnd_2580545 < baseStart_2580545 := by decide
  rcases family_descends (prefixWord ++ tailWord_2580545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2580588 : List Nat := [2, 2, 1, 1, 3, 4, 9]
def baseStart_2580588 : Nat := 118140960795 + 2580588 * 2 ^ 59
def prefixEnd_2580588 : Nat := 4983230072969 + 3 ^ 40 * 2580588 * 2
def baseEnd_2580588 : Nat := 32718074449996411636595

theorem tailTrace_2580588 : CollatzResearch.WordTrace tailWord_2580588 prefixEnd_2580588 32718074449996411636595 := by
  unfold tailWord_2580588
  simp only [CollatzResearch.WordTrace]
  refine ⟨47060888387488940093627209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62747851183318586791502945 47060888387488940093627209)
  ·
    refine ⟨35295666290616705070220407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47060888387488940093627209 35295666290616705070220407)
    ·
      refine ⟨52943499435925057605330611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35295666290616705070220407 52943499435925057605330611)
      ·
        refine ⟨79415249153887586407995917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52943499435925057605330611 79415249153887586407995917)
        ·
          refine ⟨29780718432707844902998469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79415249153887586407995917 29780718432707844902998469)
          ·
            refine ⟨5583884706132720919312213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29780718432707844902998469 5583884706132720919312213)
            ·
              refine ⟨32718074449996411636595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5583884706132720919312213 32718074449996411636595)
              ·
                rfl

theorem cell22_2580588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 9].length) (baseStart_2580588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2580588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2580588 prefixEnd_2580588 := by exact prefixLift 2580588
  have htrace : WordTrace (prefixWord ++ tailWord_2580588) baseStart_2580588 baseEnd_2580588 := by
    simpa [prefixWord, tailWord_2580588, baseEnd_2580588] using wordTrace_append hprefix tailTrace_2580588
  have hstable : (prefixWord ++ tailWord_2580588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2580588).length < 2 ^ (prefixWord ++ tailWord_2580588).sum := by decide
  have hdescent : baseEnd_2580588 < baseStart_2580588 := by decide
  rcases family_descends (prefixWord ++ tailWord_2580588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2580590 : List Nat := [4, 1, 2, 2, 1, 1, 2, 1, 4, 4]
def baseStart_2580590 : Nat := 118140960795 + 2580590 * 2 ^ 59
def prefixEnd_2580590 : Nat := 4983230072969 + 3 ^ 40 * 2580590 * 2
def baseEnd_2580590 : Nat := 883388694790775775638059

theorem tailTrace_2580590 : CollatzResearch.WordTrace tailWord_2580590 prefixEnd_2580590 883388694790775775638059 := by
  unfold tailWord_2580590
  simp only [CollatzResearch.WordTrace]
  refine ⟨11765231215121329316103403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62747899813980423019218149 11765231215121329316103403)
  ·
    refine ⟨17647846822681993974155105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11765231215121329316103403 17647846822681993974155105)
    ·
      refine ⟨13235885117011495480616329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17647846822681993974155105 13235885117011495480616329)
      ·
        refine ⟨9926913837758621610462247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13235885117011495480616329 9926913837758621610462247)
        ·
          refine ⟨14890370756637932415693371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9926913837758621610462247 14890370756637932415693371)
          ·
            refine ⟨22335556134956898623540057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14890370756637932415693371 22335556134956898623540057)
            ·
              refine ⟨16751667101217673967655043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22335556134956898623540057 16751667101217673967655043)
              ·
                refine ⟨25127500651826510951482565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16751667101217673967655043 25127500651826510951482565)
                ·
                  refine ⟨4711406372217470803402981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25127500651826510951482565 4711406372217470803402981)
                  ·
                    refine ⟨883388694790775775638059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4711406372217470803402981 883388694790775775638059)
                    ·
                      rfl

theorem cell22_2580590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 1, 4, 4].length) (baseStart_2580590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2580590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2580590 prefixEnd_2580590 := by exact prefixLift 2580590
  have htrace : WordTrace (prefixWord ++ tailWord_2580590) baseStart_2580590 baseEnd_2580590 := by
    simpa [prefixWord, tailWord_2580590, baseEnd_2580590] using wordTrace_append hprefix tailTrace_2580590
  have hstable : (prefixWord ++ tailWord_2580590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2580590).length < 2 ^ (prefixWord ++ tailWord_2580590).sum := by decide
  have hdescent : baseEnd_2580590 < baseStart_2580590 := by decide
  rcases family_descends (prefixWord ++ tailWord_2580590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2580592 : List Nat := [2, 1, 1, 1, 5, 2, 3, 2, 2, 3]
def baseStart_2580592 : Nat := 118140960795 + 2580592 * 2 ^ 59
def prefixEnd_2580592 : Nat := 4983230072969 + 3 ^ 40 * 2580592 * 2
def baseEnd_2580592 : Nat := 883389379431648437088053

theorem tailTrace_2580592 : CollatzResearch.WordTrace tailWord_2580592 prefixEnd_2580592 883389379431648437088053 := by
  unfold tailWord_2580592
  simp only [CollatzResearch.WordTrace]
  refine ⟨47060961333481694435200015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62747948444642259246933353 47060961333481694435200015)
  ·
    refine ⟨70591442000222541652800023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47060961333481694435200015 70591442000222541652800023)
    ·
      refine ⟨105887163000333812479200035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70591442000222541652800023 105887163000333812479200035)
      ·
        refine ⟨158830744500500718718800053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105887163000333812479200035 158830744500500718718800053)
        ·
          refine ⟨14890382296921942379887505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 158830744500500718718800053 14890382296921942379887505)
          ·
            refine ⟨11167786722691456784915629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14890382296921942379887505 11167786722691456784915629)
            ·
              refine ⟨4187920021009296294343361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11167786722691456784915629 4187920021009296294343361)
              ·
                refine ⟨3140940015756972220757521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4187920021009296294343361 3140940015756972220757521)
                ·
                  refine ⟨2355705011817729165568141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3140940015756972220757521 2355705011817729165568141)
                  ·
                    refine ⟨883389379431648437088053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2355705011817729165568141 883389379431648437088053)
                    ·
                      rfl

theorem cell22_2580592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 3, 2, 2, 3].length) (baseStart_2580592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2580592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2580592 prefixEnd_2580592 := by exact prefixLift 2580592
  have htrace : WordTrace (prefixWord ++ tailWord_2580592) baseStart_2580592 baseEnd_2580592 := by
    simpa [prefixWord, tailWord_2580592, baseEnd_2580592] using wordTrace_append hprefix tailTrace_2580592
  have hstable : (prefixWord ++ tailWord_2580592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2580592).length < 2 ^ (prefixWord ++ tailWord_2580592).sum := by decide
  have hdescent : baseEnd_2580592 < baseStart_2580592 := by decide
  rcases family_descends (prefixWord ++ tailWord_2580592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2580609 : List Nat := [1, 2, 4, 2, 4, 1, 1, 1, 1, 5]
def baseStart_2580609 : Nat := 118140960795 + 2580609 * 2 ^ 59
def prefixEnd_2580609 : Nat := 4983230072969 + 3 ^ 40 * 2580609 * 2
def baseEnd_2580609 : Nat := 883395198879066059413001

theorem tailTrace_2580609 : CollatzResearch.WordTrace tailWord_2580609 prefixEnd_2580609 883395198879066059413001 := by
  unfold tailWord_2580609
  simp only [CollatzResearch.WordTrace]
  refine ⟨94122542707901800773768881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62748361805267867182512587 94122542707901800773768881)
  ·
    refine ⟨70591907030926350580326661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94122542707901800773768881 70591907030926350580326661)
    ·
      refine ⟨13235982568298690733811249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70591907030926350580326661 13235982568298690733811249)
      ·
        refine ⟨9926986926224018050358437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13235982568298690733811249 9926986926224018050358437)
        ·
          refine ⟨1861310048667003384442207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9926986926224018050358437 1861310048667003384442207)
          ·
            refine ⟨2791965073000505076663311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1861310048667003384442207 2791965073000505076663311)
            ·
              refine ⟨4187947609500757614994967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2791965073000505076663311 4187947609500757614994967)
              ·
                refine ⟨6281921414251136422492451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4187947609500757614994967 6281921414251136422492451)
                ·
                  refine ⟨9422882121376704633738677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6281921414251136422492451 9422882121376704633738677)
                  ·
                    refine ⟨883395198879066059413001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9422882121376704633738677 883395198879066059413001)
                    ·
                      rfl

theorem cell22_2580609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 1, 1, 1, 5].length) (baseStart_2580609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2580609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2580609 prefixEnd_2580609 := by exact prefixLift 2580609
  have htrace : WordTrace (prefixWord ++ tailWord_2580609) baseStart_2580609 baseEnd_2580609 := by
    simpa [prefixWord, tailWord_2580609, baseEnd_2580609] using wordTrace_append hprefix tailTrace_2580609
  have hstable : (prefixWord ++ tailWord_2580609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2580609).length < 2 ^ (prefixWord ++ tailWord_2580609).sum := by decide
  have hdescent : baseEnd_2580609 < baseStart_2580609 := by decide
  rcases family_descends (prefixWord ++ tailWord_2580609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2580628 : List Nat := [2, 4, 2, 3, 2, 1, 1, 3, 4]
def baseStart_2580628 : Nat := 118140960795 + 2580628 * 2 ^ 59
def prefixEnd_2580628 : Nat := 4983230072969 + 3 ^ 40 * 2580628 * 2
def baseEnd_2580628 : Nat := 294467234322452114395981

theorem tailTrace_2580628 : CollatzResearch.WordTrace tailWord_2580628 prefixEnd_2580628 294467234322452114395981 := by
  unfold tailWord_2580628
  simp only [CollatzResearch.WordTrace]
  refine ⟨47061617847416483509355269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62748823796555311345807025 47061617847416483509355269)
  ·
    refine ⟨8824053346390590658004113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47061617847416483509355269 8824053346390590658004113)
    ·
      refine ⟨6618040009792942993503085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8824053346390590658004113 6618040009792942993503085)
      ·
        refine ⟨2481765003672353622563657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6618040009792942993503085 2481765003672353622563657)
        ·
          refine ⟨1861323752754265216922743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2481765003672353622563657 1861323752754265216922743)
          ·
            refine ⟨2791985629131397825384115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1861323752754265216922743 2791985629131397825384115)
            ·
              refine ⟨4187978443697096738076173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2791985629131397825384115 4187978443697096738076173)
              ·
                refine ⟨1570491916386411276778565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4187978443697096738076173 1570491916386411276778565)
                ·
                  refine ⟨294467234322452114395981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1570491916386411276778565 294467234322452114395981)
                  ·
                    rfl

theorem cell22_2580628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 1, 3, 4].length) (baseStart_2580628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2580628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2580628 prefixEnd_2580628 := by exact prefixLift 2580628
  have htrace : WordTrace (prefixWord ++ tailWord_2580628) baseStart_2580628 baseEnd_2580628 := by
    simpa [prefixWord, tailWord_2580628, baseEnd_2580628] using wordTrace_append hprefix tailTrace_2580628
  have hstable : (prefixWord ++ tailWord_2580628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2580628).length < 2 ^ (prefixWord ++ tailWord_2580628).sum := by decide
  have hdescent : baseEnd_2580628 < baseStart_2580628 := by decide
  rcases family_descends (prefixWord ++ tailWord_2580628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2580778 : List Nat := [3, 1, 4, 2, 2, 1, 3, 1, 2, 3]
def baseStart_2580778 : Nat := 118140960795 + 2580778 * 2 ^ 59
def prefixEnd_2580778 : Nat := 4983230072969 + 3 ^ 40 * 2580778 * 2
def baseEnd_2580778 : Nat := 883453051032805951937483

theorem tailTrace_2580778 : CollatzResearch.WordTrace tailWord_2580778 prefixEnd_2580778 883453051032805951937483 := by
  unfold tailWord_2580778
  simp only [CollatzResearch.WordTrace]
  refine ⟨23532176661072385659167747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62752471096193028424447325 23532176661072385659167747)
  ·
    refine ⟨35298264991608578488751621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23532176661072385659167747 35298264991608578488751621)
    ·
      refine ⟨6618424685926608466640929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35298264991608578488751621 6618424685926608466640929)
      ·
        refine ⟨4963818514444956349980697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6618424685926608466640929 4963818514444956349980697)
        ·
          refine ⟨3722863885833717262485523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4963818514444956349980697 3722863885833717262485523)
          ·
            refine ⟨5584295828750575893728285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3722863885833717262485523 5584295828750575893728285)
            ·
              refine ⟨2094110935781465960148107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5584295828750575893728285 2094110935781465960148107)
              ·
                refine ⟨3141166403672198940222161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2094110935781465960148107 3141166403672198940222161)
                ·
                  refine ⟨2355874802754149205166621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3141166403672198940222161 2355874802754149205166621)
                  ·
                    refine ⟨883453051032805951937483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2355874802754149205166621 883453051032805951937483)
                    ·
                      rfl

theorem cell22_2580778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 3, 1, 2, 3].length) (baseStart_2580778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2580778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2580778 prefixEnd_2580778 := by exact prefixLift 2580778
  have htrace : WordTrace (prefixWord ++ tailWord_2580778) baseStart_2580778 baseEnd_2580778 := by
    simpa [prefixWord, tailWord_2580778, baseEnd_2580778] using wordTrace_append hprefix tailTrace_2580778
  have hstable : (prefixWord ++ tailWord_2580778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2580778).length < 2 ^ (prefixWord ++ tailWord_2580778).sum := by decide
  have hdescent : baseEnd_2580778 < baseStart_2580778 := by decide
  rcases family_descends (prefixWord ++ tailWord_2580778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2580800 : List Nat := [2, 1, 1, 2, 2, 1, 2, 2, 4, 5]
def baseStart_2580800 : Nat := 118140960795 + 2580800 * 2 ^ 59
def prefixEnd_2580800 : Nat := 4983230072969 + 3 ^ 40 * 2580800 * 2
def baseEnd_2580800 : Nat := 883460582082405227887415

theorem tailTrace_2580800 : CollatzResearch.WordTrace tailWord_2580800 prefixEnd_2580800 883460582082405227887415 := by
  unfold tailWord_2580800
  simp only [CollatzResearch.WordTrace]
  refine ⟨47064754525104920196985927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62753006033473226929314569 47064754525104920196985927)
  ·
    refine ⟨70597131787657380295478891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47064754525104920196985927 70597131787657380295478891)
    ·
      refine ⟨105895697681486070443218337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70597131787657380295478891 105895697681486070443218337)
      ·
        refine ⟨79421773261114552832413753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105895697681486070443218337 79421773261114552832413753)
        ·
          refine ⟨59566329945835914624310315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79421773261114552832413753 59566329945835914624310315)
          ·
            refine ⟨89349494918753871936465473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59566329945835914624310315 89349494918753871936465473)
            ·
              refine ⟨67012121189065403952349105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89349494918753871936465473 67012121189065403952349105)
              ·
                refine ⟨50259090891799052964261829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67012121189065403952349105 50259090891799052964261829)
                ·
                  refine ⟨9423579542212322430799093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50259090891799052964261829 9423579542212322430799093)
                  ·
                    refine ⟨883460582082405227887415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9423579542212322430799093 883460582082405227887415)
                    ·
                      rfl

theorem cell22_2580800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 4, 5].length) (baseStart_2580800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2580800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2580800 prefixEnd_2580800 := by exact prefixLift 2580800
  have htrace : WordTrace (prefixWord ++ tailWord_2580800) baseStart_2580800 baseEnd_2580800 := by
    simpa [prefixWord, tailWord_2580800, baseEnd_2580800] using wordTrace_append hprefix tailTrace_2580800
  have hstable : (prefixWord ++ tailWord_2580800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2580800).length < 2 ^ (prefixWord ++ tailWord_2580800).sum := by decide
  have hdescent : baseEnd_2580800 < baseStart_2580800 := by decide
  rcases family_descends (prefixWord ++ tailWord_2580800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2580875 : List Nat := [1, 1, 1, 1, 4, 14]
def baseStart_2580875 : Nat := 118140960795 + 2580875 * 2 ^ 59
def prefixEnd_2580875 : Nat := 4983230072969 + 3 ^ 40 * 2580875 * 2
def baseEnd_2580875 : Nat := 10907237729816420151385

theorem tailTrace_2580875 : CollatzResearch.WordTrace tailWord_2580875 prefixEnd_2580875 10907237729816420151385 := by
  unfold tailWord_2580875
  simp only [CollatzResearch.WordTrace]
  refine ⟨94132244524938128202952079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62754829683292085468634719 94132244524938128202952079)
  ·
    refine ⟨141198366787407192304428119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94132244524938128202952079 141198366787407192304428119)
    ·
      refine ⟨211797550181110788456642179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141198366787407192304428119 211797550181110788456642179)
      ·
        refine ⟨317696325271666182684963269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211797550181110788456642179 317696325271666182684963269)
        ·
          refine ⟨59568060988437409253430613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 317696325271666182684963269 59568060988437409253430613)
          ·
            refine ⟨10907237729816420151385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 59568060988437409253430613 10907237729816420151385)
            ·
              rfl

theorem cell22_2580875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 14].length) (baseStart_2580875 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2580875 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2580875 prefixEnd_2580875 := by exact prefixLift 2580875
  have htrace : WordTrace (prefixWord ++ tailWord_2580875) baseStart_2580875 baseEnd_2580875 := by
    simpa [prefixWord, tailWord_2580875, baseEnd_2580875] using wordTrace_append hprefix tailTrace_2580875
  have hstable : (prefixWord ++ tailWord_2580875).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2580875).length < 2 ^ (prefixWord ++ tailWord_2580875).sum := by decide
  have hdescent : baseEnd_2580875 < baseStart_2580875 := by decide
  rcases family_descends (prefixWord ++ tailWord_2580875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2580984 : List Nat := [2, 1, 2, 1, 1, 4, 1, 5, 1, 4]
def baseStart_2580984 : Nat := 118140960795 + 2580984 * 2 ^ 59
def prefixEnd_2580984 : Nat := 4983230072969 + 3 ^ 40 * 2580984 * 2
def baseEnd_2580984 : Nat := 883523569042690081286851

theorem tailTrace_2580984 : CollatzResearch.WordTrace tailWord_2580984 prefixEnd_2580984 883523569042690081286851 := by
  unfold tailWord_2580984
  simp only [CollatzResearch.WordTrace]
  refine ⟨47068110040771619909335003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62757480054362159879113337 47068110040771619909335003)
  ·
    refine ⟨70602165061157429864002505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47068110040771619909335003 70602165061157429864002505)
    ·
      refine ⟨52951623795868072398001879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70602165061157429864002505 52951623795868072398001879)
      ·
        refine ⟨79427435693802108597002819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52951623795868072398001879 79427435693802108597002819)
        ·
          refine ⟨119141153540703162895504229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79427435693802108597002819 119141153540703162895504229)
          ·
            refine ⟨22338966288881843042907043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 119141153540703162895504229 22338966288881843042907043)
            ·
              refine ⟨33508449433322764564360565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22338966288881843042907043 33508449433322764564360565)
              ·
                refine ⟨3141417134374009177908803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33508449433322764564360565 3141417134374009177908803)
                ·
                  refine ⟨4712125701561013766863205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3141417134374009177908803 4712125701561013766863205)
                  ·
                    refine ⟨883523569042690081286851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4712125701561013766863205 883523569042690081286851)
                    ·
                      rfl

theorem cell22_2580984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 5, 1, 4].length) (baseStart_2580984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2580984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2580984 prefixEnd_2580984 := by exact prefixLift 2580984
  have htrace : WordTrace (prefixWord ++ tailWord_2580984) baseStart_2580984 baseEnd_2580984 := by
    simpa [prefixWord, tailWord_2580984, baseEnd_2580984] using wordTrace_append hprefix tailTrace_2580984
  have hstable : (prefixWord ++ tailWord_2580984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2580984).length < 2 ^ (prefixWord ++ tailWord_2580984).sum := by decide
  have hdescent : baseEnd_2580984 < baseStart_2580984 := by decide
  rcases family_descends (prefixWord ++ tailWord_2580984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2581005 : List Nat := [1, 7, 1, 1, 1, 1, 4, 1, 5]
def baseStart_2581005 : Nat := 118140960795 + 2581005 * 2 ^ 59
def prefixEnd_2581005 : Nat := 4983230072969 + 3 ^ 40 * 2581005 * 2
def baseEnd_2581005 : Nat := 294510252590617675503929

theorem tailTrace_2581005 : CollatzResearch.WordTrace tailWord_2581005 prefixEnd_2581005 294510252590617675503929 := by
  unfold tailWord_2581005
  simp only [CollatzResearch.WordTrace]
  refine ⟨94136986014467160405184469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62757990676311440270122979 94136986014467160405184469)
  ·
    refine ⟨2206335609714074071996511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 94136986014467160405184469 2206335609714074071996511)
    ·
      refine ⟨3309503414571111107994767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2206335609714074071996511 3309503414571111107994767)
      ·
        refine ⟨4964255121856666661992151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3309503414571111107994767 4964255121856666661992151)
        ·
          refine ⟨7446382682784999992988227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4964255121856666661992151 7446382682784999992988227)
          ·
            refine ⟨11169574024177499989482341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7446382682784999992988227 11169574024177499989482341)
            ·
              refine ⟨2094295129533281248027939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11169574024177499989482341 2094295129533281248027939)
              ·
                refine ⟨3141442694299921872041909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2094295129533281248027939 3141442694299921872041909)
                ·
                  refine ⟨294510252590617675503929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3141442694299921872041909 294510252590617675503929)
                  ·
                    rfl

theorem cell22_2581005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_2581005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2581005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2581005 prefixEnd_2581005 := by exact prefixLift 2581005
  have htrace : WordTrace (prefixWord ++ tailWord_2581005) baseStart_2581005 baseEnd_2581005 := by
    simpa [prefixWord, tailWord_2581005, baseEnd_2581005] using wordTrace_append hprefix tailTrace_2581005
  have hstable : (prefixWord ++ tailWord_2581005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2581005).length < 2 ^ (prefixWord ++ tailWord_2581005).sum := by decide
  have hdescent : baseEnd_2581005 < baseStart_2581005 := by decide
  rcases family_descends (prefixWord ++ tailWord_2581005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2581029 : List Nat := [1, 3, 1, 2, 2, 1, 3, 3, 2, 4]
def baseStart_2581029 : Nat := 118140960795 + 2581029 * 2 ^ 59
def prefixEnd_2581029 : Nat := 4983230072969 + 3 ^ 40 * 2581029 * 2
def baseEnd_2581029 : Nat := 883538973462324963911713

theorem tailTrace_2581029 : CollatzResearch.WordTrace tailWord_2581029 prefixEnd_2581029 883538973462324963911713 := by
  unfold tailWord_2581029
  simp only [CollatzResearch.WordTrace]
  refine ⟨94137861366380212504058141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62758574244253475002705427 94137861366380212504058141)
  ·
    refine ⟨35301698012392579689021803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94137861366380212504058141 35301698012392579689021803)
    ·
      refine ⟨52952547018588869533532705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35301698012392579689021803 52952547018588869533532705)
      ·
        refine ⟨39714410263941652150149529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52952547018588869533532705 39714410263941652150149529)
        ·
          refine ⟨29785807697956239112612147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39714410263941652150149529 29785807697956239112612147)
          ·
            refine ⟨44678711546934358668918221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29785807697956239112612147 44678711546934358668918221)
            ·
              refine ⟨16754516830100384500844333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44678711546934358668918221 16754516830100384500844333)
              ·
                refine ⟨6282943811287644187816625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16754516830100384500844333 6282943811287644187816625)
                ·
                  refine ⟨4712207858465733140862469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6282943811287644187816625 4712207858465733140862469)
                  ·
                    refine ⟨883538973462324963911713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4712207858465733140862469 883538973462324963911713)
                    ·
                      rfl

theorem cell22_2581029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 3, 2, 4].length) (baseStart_2581029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2581029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2581029 prefixEnd_2581029 := by exact prefixLift 2581029
  have htrace : WordTrace (prefixWord ++ tailWord_2581029) baseStart_2581029 baseEnd_2581029 := by
    simpa [prefixWord, tailWord_2581029, baseEnd_2581029] using wordTrace_append hprefix tailTrace_2581029
  have hstable : (prefixWord ++ tailWord_2581029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2581029).length < 2 ^ (prefixWord ++ tailWord_2581029).sum := by decide
  have hdescent : baseEnd_2581029 < baseStart_2581029 := by decide
  rcases family_descends (prefixWord ++ tailWord_2581029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2581059 : List Nat := [1, 1, 1, 3, 1, 2, 1, 2, 7, 3]
def baseStart_2581059 : Nat := 118140960795 + 2581059 * 2 ^ 59
def prefixEnd_2581059 : Nat := 4983230072969 + 3 ^ 40 * 2581059 * 2
def baseEnd_2581059 : Nat := 883549243075414885661621

theorem tailTrace_2581059 : CollatzResearch.WordTrace tailWord_2581059 prefixEnd_2581059 883549243075414885661621 := by
  unfold tailWord_2581059
  simp only [CollatzResearch.WordTrace]
  refine ⟨94138955556271527627650231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62759303704181018418433487 94138955556271527627650231)
  ·
    refine ⟨141208433334407291441475347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94138955556271527627650231 141208433334407291441475347)
    ·
      refine ⟨211812650001610937162213021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141208433334407291441475347 211812650001610937162213021)
      ·
        refine ⟨79429743750604101435829883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 211812650001610937162213021 79429743750604101435829883)
        ·
          refine ⟨119144615625906152153744825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79429743750604101435829883 119144615625906152153744825)
          ·
            refine ⟨89358461719429614115308619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119144615625906152153744825 89358461719429614115308619)
            ·
              refine ⟨134037692579144421172962929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89358461719429614115308619 134037692579144421172962929)
              ·
                refine ⟨100528269434358315879722197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 134037692579144421172962929 100528269434358315879722197)
                ·
                  refine ⟨2356131314867773028430989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 100528269434358315879722197 2356131314867773028430989)
                  ·
                    refine ⟨883549243075414885661621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2356131314867773028430989 883549243075414885661621)
                    ·
                      rfl

theorem cell22_2581059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 7, 3].length) (baseStart_2581059 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2581059 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2581059 prefixEnd_2581059 := by exact prefixLift 2581059
  have htrace : WordTrace (prefixWord ++ tailWord_2581059) baseStart_2581059 baseEnd_2581059 := by
    simpa [prefixWord, tailWord_2581059, baseEnd_2581059] using wordTrace_append hprefix tailTrace_2581059
  have hstable : (prefixWord ++ tailWord_2581059).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2581059).length < 2 ^ (prefixWord ++ tailWord_2581059).sum := by decide
  have hdescent : baseEnd_2581059 < baseStart_2581059 := by decide
  rcases family_descends (prefixWord ++ tailWord_2581059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2581074 : List Nat := [3, 2, 2, 1, 2, 1, 1, 2, 2, 6]
def baseStart_2581074 : Nat := 118140960795 + 2581074 * 2 ^ 59
def prefixEnd_2581074 : Nat := 4983230072969 + 3 ^ 40 * 2581074 * 2
def baseEnd_2581074 : Nat := 883554377881959846536575

theorem tailTrace_2581074 : CollatzResearch.WordTrace tailWord_2581074 prefixEnd_2581074 883554377881959846536575 := by
  unfold tailWord_2581074
  simp only [CollatzResearch.WordTrace]
  refine ⟨23534875662804296297361569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62759668434144790126297517 23534875662804296297361569)
  ·
    refine ⟨17651156747103222223021177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23534875662804296297361569 17651156747103222223021177)
    ·
      refine ⟨13238367560327416667265883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17651156747103222223021177 13238367560327416667265883)
      ·
        refine ⟨19857551340491125000898825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13238367560327416667265883 19857551340491125000898825)
        ·
          refine ⟨14893163505368343750674119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19857551340491125000898825 14893163505368343750674119)
          ·
            refine ⟨22339745258052515626011179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14893163505368343750674119 22339745258052515626011179)
            ·
              refine ⟨33509617887078773439016769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22339745258052515626011179 33509617887078773439016769)
              ·
                refine ⟨25132213415309080079262577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33509617887078773439016769 25132213415309080079262577)
                ·
                  refine ⟨18849160061481810059446933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25132213415309080079262577 18849160061481810059446933)
                  ·
                    refine ⟨883554377881959846536575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18849160061481810059446933 883554377881959846536575)
                    ·
                      rfl

theorem cell22_2581074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 2, 2, 6].length) (baseStart_2581074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2581074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2581074 prefixEnd_2581074 := by exact prefixLift 2581074
  have htrace : WordTrace (prefixWord ++ tailWord_2581074) baseStart_2581074 baseEnd_2581074 := by
    simpa [prefixWord, tailWord_2581074, baseEnd_2581074] using wordTrace_append hprefix tailTrace_2581074
  have hstable : (prefixWord ++ tailWord_2581074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2581074).length < 2 ^ (prefixWord ++ tailWord_2581074).sum := by decide
  have hdescent : baseEnd_2581074 < baseStart_2581074 := by decide
  rcases family_descends (prefixWord ++ tailWord_2581074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2581076 : List Nat := [2, 4, 1, 1, 1, 3, 1, 1, 5, 3]
def baseStart_2581076 : Nat := 118140960795 + 2581076 * 2 ^ 59
def prefixEnd_2581076 : Nat := 4983230072969 + 3 ^ 40 * 2581076 * 2
def baseEnd_2581076 : Nat := 883555062522832507986569

theorem tailTrace_2581076 : CollatzResearch.WordTrace tailWord_2581076 prefixEnd_2581076 883555062522832507986569 := by
  unfold tailWord_2581076
  simp only [CollatzResearch.WordTrace]
  refine ⟨47069787798604969765509541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62759717064806626354012721 47069787798604969765509541)
  ·
    refine ⟨8825585212238431831033039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47069787798604969765509541 8825585212238431831033039)
    ·
      refine ⟨13238377818357647746549559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8825585212238431831033039 13238377818357647746549559)
      ·
        refine ⟨19857566727536471619824339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13238377818357647746549559 19857566727536471619824339)
        ·
          refine ⟨29786350091304707429736509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19857566727536471619824339 29786350091304707429736509)
          ·
            refine ⟨11169881284239265286151191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29786350091304707429736509 11169881284239265286151191)
            ·
              refine ⟨16754821926358897929226787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11169881284239265286151191 16754821926358897929226787)
              ·
                refine ⟨25132232889538346893840181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16754821926358897929226787 25132232889538346893840181)
                ·
                  refine ⟨2356146833394220021297517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25132232889538346893840181 2356146833394220021297517)
                  ·
                    refine ⟨883555062522832507986569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2356146833394220021297517 883555062522832507986569)
                    ·
                      rfl

theorem cell22_2581076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 1, 5, 3].length) (baseStart_2581076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2581076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2581076 prefixEnd_2581076 := by exact prefixLift 2581076
  have htrace : WordTrace (prefixWord ++ tailWord_2581076) baseStart_2581076 baseEnd_2581076 := by
    simpa [prefixWord, tailWord_2581076, baseEnd_2581076] using wordTrace_append hprefix tailTrace_2581076
  have hstable : (prefixWord ++ tailWord_2581076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2581076).length < 2 ^ (prefixWord ++ tailWord_2581076).sum := by decide
  have hdescent : baseEnd_2581076 < baseStart_2581076 := by decide
  rcases family_descends (prefixWord ++ tailWord_2581076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2581086 : List Nat := [4, 4, 1, 2, 2, 1, 2, 1, 1, 4]
def baseStart_2581086 : Nat := 118140960795 + 2581086 * 2 ^ 59
def prefixEnd_2581086 : Nat := 4983230072969 + 3 ^ 40 * 2581086 * 2
def baseEnd_2581086 : Nat := 883558485727195815236539

theorem tailTrace_2581086 : CollatzResearch.WordTrace tailWord_2581086 prefixEnd_2581086 883558485727195815236539 := by
  unfold tailWord_2581086
  simp only [CollatzResearch.WordTrace]
  refine ⟨11767492540896713904860389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62759960218115807492588741 11767492540896713904860389)
  ·
    refine ⟨2206404851418133857161323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11767492540896713904860389 2206404851418133857161323)
    ·
      refine ⟨3309607277127200785741985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2206404851418133857161323 3309607277127200785741985)
      ·
        refine ⟨2482205457845400589306489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3309607277127200785741985 2482205457845400589306489)
        ·
          refine ⟨1861654093384050441979867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2482205457845400589306489 1861654093384050441979867)
          ·
            refine ⟨2792481140076075662969801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1861654093384050441979867 2792481140076075662969801)
            ·
              refine ⟨2094360855057056747227351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2792481140076075662969801 2094360855057056747227351)
              ·
                refine ⟨3141541282585585120841027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2094360855057056747227351 3141541282585585120841027)
                ·
                  refine ⟨4712311923878377681261541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3141541282585585120841027 4712311923878377681261541)
                  ·
                    refine ⟨883558485727195815236539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4712311923878377681261541 883558485727195815236539)
                    ·
                      rfl

theorem cell22_2581086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_2581086 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2581086 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2581086 prefixEnd_2581086 := by exact prefixLift 2581086
  have htrace : WordTrace (prefixWord ++ tailWord_2581086) baseStart_2581086 baseEnd_2581086 := by
    simpa [prefixWord, tailWord_2581086, baseEnd_2581086] using wordTrace_append hprefix tailTrace_2581086
  have hstable : (prefixWord ++ tailWord_2581086).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2581086).length < 2 ^ (prefixWord ++ tailWord_2581086).sum := by decide
  have hdescent : baseEnd_2581086 < baseStart_2581086 := by decide
  rcases family_descends (prefixWord ++ tailWord_2581086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2581106 : List Nat := [3, 2, 1, 2, 4, 1, 1, 1, 7]
def baseStart_2581106 : Nat := 118140960795 + 2581106 * 2 ^ 59
def prefixEnd_2581106 : Nat := 4983230072969 + 3 ^ 40 * 2581106 * 2
def baseEnd_2581106 : Nat := 294521777378640809912159

theorem tailTrace_2581106 : CollatzResearch.WordTrace tailWord_2581106 prefixEnd_2581106 294521777378640809912159 := by
  unfold tailWord_2581106
  simp only [CollatzResearch.WordTrace]
  refine ⟨23535167446775313663652793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62760446524734169769740781 23535167446775313663652793)
  ·
    refine ⟨17651375585081485247739595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23535167446775313663652793 17651375585081485247739595)
    ·
      refine ⟨26477063377622227871609393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17651375585081485247739595 26477063377622227871609393)
      ·
        refine ⟨19857797533216670903707045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26477063377622227871609393 19857797533216670903707045)
        ·
          refine ⟨3723337037478125794445071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19857797533216670903707045 3723337037478125794445071)
          ·
            refine ⟨5585005556217188691667607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3723337037478125794445071 5585005556217188691667607)
            ·
              refine ⟨8377508334325783037501411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5585005556217188691667607 8377508334325783037501411)
              ·
                refine ⟨12566262501488674556252117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8377508334325783037501411 12566262501488674556252117)
                ·
                  refine ⟨294521777378640809912159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12566262501488674556252117 294521777378640809912159)
                  ·
                    rfl

theorem cell22_2581106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 1, 7].length) (baseStart_2581106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2581106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2581106 prefixEnd_2581106 := by exact prefixLift 2581106
  have htrace : WordTrace (prefixWord ++ tailWord_2581106) baseStart_2581106 baseEnd_2581106 := by
    simpa [prefixWord, tailWord_2581106, baseEnd_2581106] using wordTrace_append hprefix tailTrace_2581106
  have hstable : (prefixWord ++ tailWord_2581106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2581106).length < 2 ^ (prefixWord ++ tailWord_2581106).sum := by decide
  have hdescent : baseEnd_2581106 < baseStart_2581106 := by decide
  rcases family_descends (prefixWord ++ tailWord_2581106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2581110 : List Nat := [5, 1, 1, 2, 3, 1, 2, 1, 3, 3]
def baseStart_2581110 : Nat := 118140960795 + 2581110 * 2 ^ 59
def prefixEnd_2581110 : Nat := 4983230072969 + 3 ^ 40 * 2581110 * 2
def baseEnd_2581110 : Nat := 883566701417667752636465

theorem tailTrace_2581110 : CollatzResearch.WordTrace tailWord_2581110 prefixEnd_2581110 883566701417667752636465 := by
  unfold tailWord_2581110
  simp only [CollatzResearch.WordTrace]
  refine ⟨5883800979942922708609799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 62760543786057842225171189 5883800979942922708609799)
  ·
    refine ⟨8825701469914384062914699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5883800979942922708609799 8825701469914384062914699)
    ·
      refine ⟨13238552204871576094372049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8825701469914384062914699 13238552204871576094372049)
      ·
        refine ⟨9928914153653682070779037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13238552204871576094372049 9928914153653682070779037)
        ·
          refine ⟨3723342807620130776542139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9928914153653682070779037 3723342807620130776542139)
          ·
            refine ⟨5585014211430196164813209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3723342807620130776542139 5585014211430196164813209)
            ·
              refine ⟨4188760658572647123609907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5585014211430196164813209 4188760658572647123609907)
              ·
                refine ⟨6283140987858970685414861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4188760658572647123609907 6283140987858970685414861)
                ·
                  refine ⟨2356177870447114007030573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6283140987858970685414861 2356177870447114007030573)
                  ·
                    refine ⟨883566701417667752636465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2356177870447114007030573 883566701417667752636465)
                    ·
                      rfl

theorem cell22_2581110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 2, 1, 3, 3].length) (baseStart_2581110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2581110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2581110 prefixEnd_2581110 := by exact prefixLift 2581110
  have htrace : WordTrace (prefixWord ++ tailWord_2581110) baseStart_2581110 baseEnd_2581110 := by
    simpa [prefixWord, tailWord_2581110, baseEnd_2581110] using wordTrace_append hprefix tailTrace_2581110
  have hstable : (prefixWord ++ tailWord_2581110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2581110).length < 2 ^ (prefixWord ++ tailWord_2581110).sum := by decide
  have hdescent : baseEnd_2581110 < baseStart_2581110 := by decide
  rcases family_descends (prefixWord ++ tailWord_2581110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2581119 : List Nat := [1, 1, 2, 2, 1, 1, 1, 6, 3, 4]
def baseStart_2581119 : Nat := 118140960795 + 2581119 * 2 ^ 59
def prefixEnd_2581119 : Nat := 4983230072969 + 3 ^ 40 * 2581119 * 2
def baseEnd_2581119 : Nat := 883569782301594729161437

theorem tailTrace_2581119 : CollatzResearch.WordTrace tailWord_2581119 prefixEnd_2581119 883569782301594729161437 := by
  unfold tailWord_2581119
  simp only [CollatzResearch.WordTrace]
  refine ⟨94141143936054157874834411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62760762624036105249889607 94141143936054157874834411)
  ·
    refine ⟨141211715904081236812251617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94141143936054157874834411 141211715904081236812251617)
    ·
      refine ⟨105908786928060927609188713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141211715904081236812251617 105908786928060927609188713)
      ·
        refine ⟨79431590196045695706891535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105908786928060927609188713 79431590196045695706891535)
        ·
          refine ⟨119147385294068543560337303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79431590196045695706891535 119147385294068543560337303)
          ·
            refine ⟨178721077941102815340505955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119147385294068543560337303 178721077941102815340505955)
            ·
              refine ⟨268081616911654223010758933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 178721077941102815340505955 268081616911654223010758933)
              ·
                refine ⟨12566325792733791703629325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 268081616911654223010758933 12566325792733791703629325)
                ·
                  refine ⟨4712372172275171888860997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12566325792733791703629325 4712372172275171888860997)
                  ·
                    refine ⟨883569782301594729161437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4712372172275171888860997 883569782301594729161437)
                    ·
                      rfl

theorem cell22_2581119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 6, 3, 4].length) (baseStart_2581119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2581119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2581119 prefixEnd_2581119 := by exact prefixLift 2581119
  have htrace : WordTrace (prefixWord ++ tailWord_2581119) baseStart_2581119 baseEnd_2581119 := by
    simpa [prefixWord, tailWord_2581119, baseEnd_2581119] using wordTrace_append hprefix tailTrace_2581119
  have hstable : (prefixWord ++ tailWord_2581119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2581119).length < 2 ^ (prefixWord ++ tailWord_2581119).sum := by decide
  have hdescent : baseEnd_2581119 < baseStart_2581119 := by decide
  rcases family_descends (prefixWord ++ tailWord_2581119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2581174 : List Nat := [5, 1, 3, 1, 3, 1, 2, 1, 5]
def baseStart_2581174 : Nat := 118140960795 + 2581174 * 2 ^ 59
def prefixEnd_2581174 : Nat := 4983230072969 + 3 ^ 40 * 2581174 * 2
def baseEnd_2581174 : Nat := 294529536641864306345423

theorem tailTrace_2581174 : CollatzResearch.WordTrace tailWord_2581174 prefixEnd_2581174 294529536641864306345423 := by
  unfold tailWord_2581174
  simp only [CollatzResearch.WordTrace]
  refine ⟨5883946871928431391755411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 62762099967236601512057717 5883946871928431391755411)
  ·
    refine ⟨8825920307892647087633117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5883946871928431391755411 8825920307892647087633117)
    ·
      refine ⟨3309720115459742657862419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8825920307892647087633117 3309720115459742657862419)
      ·
        refine ⟨4964580173189613986793629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3309720115459742657862419 4964580173189613986793629)
        ·
          refine ⟨1861717564946105245047611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4964580173189613986793629 1861717564946105245047611)
          ·
            refine ⟨2792576347419157867571417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1861717564946105245047611 2792576347419157867571417)
            ·
              refine ⟨2094432260564368400678563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2792576347419157867571417 2094432260564368400678563)
              ·
                refine ⟨3141648390846552601017845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2094432260564368400678563 3141648390846552601017845)
                ·
                  refine ⟨294529536641864306345423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3141648390846552601017845 294529536641864306345423)
                  ·
                    rfl

theorem cell22_2581174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 2, 1, 5].length) (baseStart_2581174 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2581174 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2581174 prefixEnd_2581174 := by exact prefixLift 2581174
  have htrace : WordTrace (prefixWord ++ tailWord_2581174) baseStart_2581174 baseEnd_2581174 := by
    simpa [prefixWord, tailWord_2581174, baseEnd_2581174] using wordTrace_append hprefix tailTrace_2581174
  have hstable : (prefixWord ++ tailWord_2581174).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2581174).length < 2 ^ (prefixWord ++ tailWord_2581174).sum := by decide
  have hdescent : baseEnd_2581174 < baseStart_2581174 := by decide
  rcases family_descends (prefixWord ++ tailWord_2581174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2581183 : List Nat := [1, 1, 2, 2, 2, 5, 1, 3, 2, 3]
def baseStart_2581183 : Nat := 118140960795 + 2581183 * 2 ^ 59
def prefixEnd_2581183 : Nat := 4983230072969 + 3 ^ 40 * 2581183 * 2
def baseEnd_2581183 : Nat := 883591690809519895561241

theorem tailTrace_2581183 : CollatzResearch.WordTrace tailWord_2581183 prefixEnd_2581183 883591690809519895561241 := by
  unfold tailWord_2581183
  simp only [CollatzResearch.WordTrace]
  refine ⟨94143478207822296805164203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62762318805214864536776135 94143478207822296805164203)
  ·
    refine ⟨141215217311733445207746305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94143478207822296805164203 141215217311733445207746305)
    ·
      refine ⟨105911412983800083905809729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141215217311733445207746305 105911412983800083905809729)
      ·
        refine ⟨79433559737850062929357297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105911412983800083905809729 79433559737850062929357297)
        ·
          refine ⟨59575169803387547197017973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79433559737850062929357297 59575169803387547197017973)
          ·
            refine ⟨5585172169067582549720435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 59575169803387547197017973 5585172169067582549720435)
            ·
              refine ⟨8377758253601373824580653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5585172169067582549720435 8377758253601373824580653)
              ·
                refine ⟨3141659345100515184217745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8377758253601373824580653 3141659345100515184217745)
                ·
                  refine ⟨2356244508825386388163309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3141659345100515184217745 2356244508825386388163309)
                  ·
                    refine ⟨883591690809519895561241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2356244508825386388163309 883591690809519895561241)
                    ·
                      rfl

theorem cell22_2581183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 3, 2, 3].length) (baseStart_2581183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2581183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2581183 prefixEnd_2581183 := by exact prefixLift 2581183
  have htrace : WordTrace (prefixWord ++ tailWord_2581183) baseStart_2581183 baseEnd_2581183 := by
    simpa [prefixWord, tailWord_2581183, baseEnd_2581183] using wordTrace_append hprefix tailTrace_2581183
  have hstable : (prefixWord ++ tailWord_2581183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2581183).length < 2 ^ (prefixWord ++ tailWord_2581183).sum := by decide
  have hdescent : baseEnd_2581183 < baseStart_2581183 := by decide
  rcases family_descends (prefixWord ++ tailWord_2581183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2581196 : List Nat := [2, 2, 1, 5, 1, 1, 2, 8]
def baseStart_2581196 : Nat := 118140960795 + 2581196 * 2 ^ 59
def prefixEnd_2581196 : Nat := 4983230072969 + 3 ^ 40 * 2581196 * 2
def baseEnd_2581196 : Nat := 98177348997243577220689

theorem tailTrace_2581196 : CollatzResearch.WordTrace tailWord_2581196 prefixEnd_2581196 98177348997243577220689 := by
  unfold tailWord_2581196
  simp only [CollatzResearch.WordTrace]
  refine ⟨47071976178387600012693721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62762634904516800016924961 47071976178387600012693721)
  ·
    refine ⟨35303982133790700009520291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47071976178387600012693721 35303982133790700009520291)
    ·
      refine ⟨52955973200686050014280437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35303982133790700009520291 52955973200686050014280437)
      ·
        refine ⟨4964622487564317188838791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 52955973200686050014280437 4964622487564317188838791)
        ·
          refine ⟨7446933731346475783258187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4964622487564317188838791 7446933731346475783258187)
          ·
            refine ⟨11170400597019713674887281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7446933731346475783258187 11170400597019713674887281)
            ·
              refine ⟨8377800447764785256165461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11170400597019713674887281 8377800447764785256165461)
              ·
                refine ⟨98177348997243577220689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8377800447764785256165461 98177348997243577220689)
                ·
                  rfl

theorem cell22_2581196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 8].length) (baseStart_2581196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2581196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2581196 prefixEnd_2581196 := by exact prefixLift 2581196
  have htrace : WordTrace (prefixWord ++ tailWord_2581196) baseStart_2581196 baseEnd_2581196 := by
    simpa [prefixWord, tailWord_2581196, baseEnd_2581196] using wordTrace_append hprefix tailTrace_2581196
  have hstable : (prefixWord ++ tailWord_2581196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2581196).length < 2 ^ (prefixWord ++ tailWord_2581196).sum := by decide
  have hdescent : baseEnd_2581196 < baseStart_2581196 := by decide
  rcases family_descends (prefixWord ++ tailWord_2581196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2581198 : List Nat := [4, 1, 1, 1, 3, 3, 2, 1, 2, 4]
def baseStart_2581198 : Nat := 118140960795 + 2581198 * 2 ^ 59
def prefixEnd_2581198 : Nat := 4983230072969 + 3 ^ 40 * 2581198 * 2
def baseEnd_2581198 : Nat := 883596825616064856436195

theorem tailTrace_2581198 : CollatzResearch.WordTrace tailWord_2581198 prefixEnd_2581198 883596825616064856436195 := by
  unfold tailWord_2581198
  simp only [CollatzResearch.WordTrace]
  refine ⟨11768003162845994295870031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62762683535178636244640165 11768003162845994295870031)
  ·
    refine ⟨17652004744268991443805047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11768003162845994295870031 17652004744268991443805047)
    ·
      refine ⟨26478007116403487165707571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17652004744268991443805047 26478007116403487165707571)
      ·
        refine ⟨39717010674605230748561357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26478007116403487165707571 39717010674605230748561357)
        ·
          refine ⟨14893879002976961530710509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39717010674605230748561357 14893879002976961530710509)
          ·
            refine ⟨5585204626116360574016441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14893879002976961530710509 5585204626116360574016441)
            ·
              refine ⟨4188903469587270430512331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5585204626116360574016441 4188903469587270430512331)
              ·
                refine ⟨6283355204380905645768497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4188903469587270430512331 6283355204380905645768497)
                ·
                  refine ⟨4712516403285679234326373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6283355204380905645768497 4712516403285679234326373)
                  ·
                    refine ⟨883596825616064856436195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4712516403285679234326373 883596825616064856436195)
                    ·
                      rfl

theorem cell22_2581198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 2, 1, 2, 4].length) (baseStart_2581198 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2581198 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2581198 prefixEnd_2581198 := by exact prefixLift 2581198
  have htrace : WordTrace (prefixWord ++ tailWord_2581198) baseStart_2581198 baseEnd_2581198 := by
    simpa [prefixWord, tailWord_2581198, baseEnd_2581198] using wordTrace_append hprefix tailTrace_2581198
  have hstable : (prefixWord ++ tailWord_2581198).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2581198).length < 2 ^ (prefixWord ++ tailWord_2581198).sum := by decide
  have hdescent : baseEnd_2581198 < baseStart_2581198 := by decide
  rcases family_descends (prefixWord ++ tailWord_2581198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2581333 : List Nat := [1, 3, 2, 2, 2, 1, 3, 2, 2, 4]
def baseStart_2581333 : Nat := 118140960795 + 2581333 * 2 ^ 59
def prefixEnd_2581333 : Nat := 4983230072969 + 3 ^ 40 * 2581333 * 2
def baseEnd_2581333 : Nat := 883643038874969504310781

theorem tailTrace_2581333 : CollatzResearch.WordTrace tailWord_2581333 prefixEnd_2581333 883643038874969504310781 := by
  unfold tailWord_2581333
  simp only [CollatzResearch.WordTrace]
  refine ⟨94148949157278872423124653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62765966104852581615416435 94148949157278872423124653)
  ·
    refine ⟨35305855933979577158671745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94148949157278872423124653 35305855933979577158671745)
    ·
      refine ⟨26479391950484682869003809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35305855933979577158671745 26479391950484682869003809)
      ·
        refine ⟨19859543962863512151752857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26479391950484682869003809 19859543962863512151752857)
        ·
          refine ⟨14894657972147634113814643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19859543962863512151752857 14894657972147634113814643)
          ·
            refine ⟨22341986958221451170721965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14894657972147634113814643 22341986958221451170721965)
            ·
              refine ⟨8378245109333044189020737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22341986958221451170721965 8378245109333044189020737)
              ·
                refine ⟨6283683831999783141765553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8378245109333044189020737 6283683831999783141765553)
                ·
                  refine ⟨4712762873999837356324165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6283683831999783141765553 4712762873999837356324165)
                  ·
                    refine ⟨883643038874969504310781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4712762873999837356324165 883643038874969504310781)
                    ·
                      rfl

theorem cell22_2581333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 2, 2, 4].length) (baseStart_2581333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2581333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2581333 prefixEnd_2581333 := by exact prefixLift 2581333
  have htrace : WordTrace (prefixWord ++ tailWord_2581333) baseStart_2581333 baseEnd_2581333 := by
    simpa [prefixWord, tailWord_2581333, baseEnd_2581333] using wordTrace_append hprefix tailTrace_2581333
  have hstable : (prefixWord ++ tailWord_2581333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2581333).length < 2 ^ (prefixWord ++ tailWord_2581333).sum := by decide
  have hdescent : baseEnd_2581333 < baseStart_2581333 := by decide
  rcases family_descends (prefixWord ++ tailWord_2581333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2581348 : List Nat := [2, 3, 1, 1, 4, 2, 2, 7]
def baseStart_2581348 : Nat := 118140960795 + 2581348 * 2 ^ 59
def prefixEnd_2581348 : Nat := 4983230072969 + 3 ^ 40 * 2581348 * 2
def baseEnd_2581348 : Nat := 98183130409057162798415

theorem tailTrace_2581348 : CollatzResearch.WordTrace tailWord_2581348 prefixEnd_2581348 98183130409057162798415 := by
  unfold tailWord_2581348
  simp only [CollatzResearch.WordTrace]
  refine ⟨47074748126112264992460349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62766330834816353323280465 47074748126112264992460349)
  ·
    refine ⟨17653030547292099372172631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47074748126112264992460349 17653030547292099372172631)
    ·
      refine ⟨26479545820938149058258947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17653030547292099372172631 26479545820938149058258947)
      ·
        refine ⟨39719318731407223587388421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26479545820938149058258947 39719318731407223587388421)
        ·
          refine ⟨7447372262138854422635329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39719318731407223587388421 7447372262138854422635329)
          ·
            refine ⟨5585529196604140816976497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7447372262138854422635329 5585529196604140816976497)
            ·
              refine ⟨4189146897453105612732373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5585529196604140816976497 4189146897453105612732373)
              ·
                refine ⟨98183130409057162798415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4189146897453105612732373 98183130409057162798415)
                ·
                  rfl

theorem cell22_2581348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 2, 7].length) (baseStart_2581348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2581348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2581348 prefixEnd_2581348 := by exact prefixLift 2581348
  have htrace : WordTrace (prefixWord ++ tailWord_2581348) baseStart_2581348 baseEnd_2581348 := by
    simpa [prefixWord, tailWord_2581348, baseEnd_2581348] using wordTrace_append hprefix tailTrace_2581348
  have hstable : (prefixWord ++ tailWord_2581348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2581348).length < 2 ^ (prefixWord ++ tailWord_2581348).sum := by decide
  have hdescent : baseEnd_2581348 < baseStart_2581348 := by decide
  rcases family_descends (prefixWord ++ tailWord_2581348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2581352 : List Nat := [2, 1, 4, 2, 1, 2, 4, 1, 2, 3]
def baseStart_2581352 : Nat := 118140960795 + 2581352 * 2 ^ 59
def prefixEnd_2581352 : Nat := 4983230072969 + 3 ^ 40 * 2581352 * 2
def baseEnd_2581352 : Nat := 883649542963259788085723

theorem tailTrace_2581352 : CollatzResearch.WordTrace tailWord_2581352 prefixEnd_2581352 883649542963259788085723 := by
  unfold tailWord_2581352
  simp only [CollatzResearch.WordTrace]
  refine ⟨47074821072105019334033155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62766428096140025778710873 47074821072105019334033155)
  ·
    refine ⟨70612231608157529001049733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47074821072105019334033155 70612231608157529001049733)
    ·
      refine ⟨13239793426529536687696825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70612231608157529001049733 13239793426529536687696825)
      ·
        refine ⟨9929845069897152515772619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13239793426529536687696825 9929845069897152515772619)
        ·
          refine ⟨14894767604845728773658929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9929845069897152515772619 14894767604845728773658929)
          ·
            refine ⟨11171075703634296580244197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14894767604845728773658929 11171075703634296580244197)
            ·
              refine ⟨2094576694431430608795787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11171075703634296580244197 2094576694431430608795787)
              ·
                refine ⟨3141865041647145913193681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2094576694431430608795787 3141865041647145913193681)
                ·
                  refine ⟨2356398781235359434895261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3141865041647145913193681 2356398781235359434895261)
                  ·
                    refine ⟨883649542963259788085723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2356398781235359434895261 883649542963259788085723)
                    ·
                      rfl

theorem cell22_2581352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 4, 1, 2, 3].length) (baseStart_2581352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2581352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2581352 prefixEnd_2581352 := by exact prefixLift 2581352
  have htrace : WordTrace (prefixWord ++ tailWord_2581352) baseStart_2581352 baseEnd_2581352 := by
    simpa [prefixWord, tailWord_2581352, baseEnd_2581352] using wordTrace_append hprefix tailTrace_2581352
  have hstable : (prefixWord ++ tailWord_2581352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2581352).length < 2 ^ (prefixWord ++ tailWord_2581352).sum := by decide
  have hdescent : baseEnd_2581352 < baseStart_2581352 := by decide
  rcases family_descends (prefixWord ++ tailWord_2581352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2581363 : List Nat := [1, 1, 1, 2, 2, 1, 4, 4, 3, 3]
def baseStart_2581363 : Nat := 118140960795 + 2581363 * 2 ^ 59
def prefixEnd_2581363 : Nat := 4983230072969 + 3 ^ 40 * 2581363 * 2
def baseEnd_2581363 : Nat := 883653308488059426060689

theorem tailTrace_2581363 : CollatzResearch.WordTrace tailWord_2581363 prefixEnd_2581363 883653308488059426060689 := by
  unfold tailWord_2581363
  simp only [CollatzResearch.WordTrace]
  refine ⟨94150043347170187546716743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62766695564780125031144495 94150043347170187546716743)
  ·
    refine ⟨141225065020755281320075115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94150043347170187546716743 141225065020755281320075115)
    ·
      refine ⟨211837597531132921980112673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141225065020755281320075115 211837597531132921980112673)
      ·
        refine ⟨158878198148349691485084505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 211837597531132921980112673 158878198148349691485084505)
        ·
          refine ⟨119158648611262268613813379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 158878198148349691485084505 119158648611262268613813379)
          ·
            refine ⟨178737972916893402920720069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119158648611262268613813379 178737972916893402920720069)
            ·
              refine ⟨33513369921917513047635013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 178737972916893402920720069 33513369921917513047635013)
              ·
                refine ⟨6283756860359533696431565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33513369921917513047635013 6283756860359533696431565)
                ·
                  refine ⟨2356408822634825136161837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6283756860359533696431565 2356408822634825136161837)
                  ·
                    refine ⟨883653308488059426060689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2356408822634825136161837 883653308488059426060689)
                    ·
                      rfl

theorem cell22_2581363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 4, 3, 3].length) (baseStart_2581363 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2581363 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2581363 prefixEnd_2581363 := by exact prefixLift 2581363
  have htrace : WordTrace (prefixWord ++ tailWord_2581363) baseStart_2581363 baseEnd_2581363 := by
    simpa [prefixWord, tailWord_2581363, baseEnd_2581363] using wordTrace_append hprefix tailTrace_2581363
  have hstable : (prefixWord ++ tailWord_2581363).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2581363).length < 2 ^ (prefixWord ++ tailWord_2581363).sum := by decide
  have hdescent : baseEnd_2581363 < baseStart_2581363 := by decide
  rcases family_descends (prefixWord ++ tailWord_2581363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2581376 : List Nat := [2, 1, 1, 2, 1, 2, 2, 4, 7]
def baseStart_2581376 : Nat := 118140960795 + 2581376 * 2 ^ 59
def prefixEnd_2581376 : Nat := 4983230072969 + 3 ^ 40 * 2581376 * 2
def baseEnd_2581376 : Nat := 294552586217910575161883

theorem tailTrace_2581376 : CollatzResearch.WordTrace tailWord_2581376 prefixEnd_2581376 294552586217910575161883 := by
  unfold tailWord_2581376
  simp only [CollatzResearch.WordTrace]
  refine ⟨47075258748061545383469991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62767011664082060511293321 47075258748061545383469991)
  ·
    refine ⟨70612888122092318075204987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47075258748061545383469991 70612888122092318075204987)
    ·
      refine ⟨105919332183138477112807481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70612888122092318075204987 105919332183138477112807481)
      ·
        refine ⟨79439499137353857834605611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105919332183138477112807481 79439499137353857834605611)
        ·
          refine ⟨119159248706030786751908417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79439499137353857834605611 119159248706030786751908417)
          ·
            refine ⟨89369436529523090063931313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119159248706030786751908417 89369436529523090063931313)
            ·
              refine ⟨67027077397142317547948485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89369436529523090063931313 67027077397142317547948485)
              ·
                refine ⟨12567577011964184540240341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 67027077397142317547948485 12567577011964184540240341)
                ·
                  refine ⟨294552586217910575161883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12567577011964184540240341 294552586217910575161883)
                  ·
                    rfl

theorem cell22_2581376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 4, 7].length) (baseStart_2581376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2581376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2581376 prefixEnd_2581376 := by exact prefixLift 2581376
  have htrace : WordTrace (prefixWord ++ tailWord_2581376) baseStart_2581376 baseEnd_2581376 := by
    simpa [prefixWord, tailWord_2581376, baseEnd_2581376] using wordTrace_append hprefix tailTrace_2581376
  have hstable : (prefixWord ++ tailWord_2581376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2581376).length < 2 ^ (prefixWord ++ tailWord_2581376).sum := by decide
  have hdescent : baseEnd_2581376 < baseStart_2581376 := by decide
  rcases family_descends (prefixWord ++ tailWord_2581376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2581397 : List Nat := [1, 3, 2, 1, 1, 5, 1, 4, 1, 3]
def baseStart_2581397 : Nat := 118140960795 + 2581397 * 2 ^ 59
def prefixEnd_2581397 : Nat := 4983230072969 + 3 ^ 40 * 2581397 * 2
def baseEnd_2581397 : Nat := 883664947382894670710585

theorem tailTrace_2581397 : CollatzResearch.WordTrace tailWord_2581397 prefixEnd_2581397 883664947382894670710585 := by
  unfold tailWord_2581397
  simp only [CollatzResearch.WordTrace]
  refine ⟨94151283429047011353454445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62767522286031340902302963 94151283429047011353454445)
  ·
    refine ⟨35306731285892629257545417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94151283429047011353454445 35306731285892629257545417)
    ·
      refine ⟨26480048464419471943159063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35306731285892629257545417 26480048464419471943159063)
      ·
        refine ⟨39720072696629207914738595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26480048464419471943159063 39720072696629207914738595)
        ·
          refine ⟨59580109044943811872107893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39720072696629207914738595 59580109044943811872107893)
          ·
            refine ⟨5585635222963482363010115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 59580109044943811872107893 5585635222963482363010115)
            ·
              refine ⟨8378452834445223544515173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5585635222963482363010115 8378452834445223544515173)
              ·
                refine ⟨1570959906458479414596595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8378452834445223544515173 1570959906458479414596595)
                ·
                  refine ⟨2356439859687719121894893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1570959906458479414596595 2356439859687719121894893)
                  ·
                    refine ⟨883664947382894670710585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2356439859687719121894893 883664947382894670710585)
                    ·
                      rfl

theorem cell22_2581397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 4, 1, 3].length) (baseStart_2581397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2581397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2581397 prefixEnd_2581397 := by exact prefixLift 2581397
  have htrace : WordTrace (prefixWord ++ tailWord_2581397) baseStart_2581397 baseEnd_2581397 := by
    simpa [prefixWord, tailWord_2581397, baseEnd_2581397] using wordTrace_append hprefix tailTrace_2581397
  have hstable : (prefixWord ++ tailWord_2581397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2581397).length < 2 ^ (prefixWord ++ tailWord_2581397).sum := by decide
  have hdescent : baseEnd_2581397 < baseStart_2581397 := by decide
  rcases family_descends (prefixWord ++ tailWord_2581397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2581410 : List Nat := [3, 3, 1, 2, 2, 1, 2, 3, 5]
def baseStart_2581410 : Nat := 118140960795 + 2581410 * 2 ^ 59
def prefixEnd_2581410 : Nat := 4983230072969 + 3 ^ 40 * 2581410 * 2
def baseEnd_2581410 : Nat := 294556465849522323378515

theorem tailTrace_2581410 : CollatzResearch.WordTrace tailWord_2581410 prefixEnd_2581410 294556465849522323378515 := by
  unfold tailWord_2581410
  simp only [CollatzResearch.WordTrace]
  refine ⟨23537939394499978643419421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62767838385333276382451789 23537939394499978643419421)
  ·
    refine ⟨8826727272937491991282283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23537939394499978643419421 8826727272937491991282283)
    ·
      refine ⟨13240090909406237986923425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8826727272937491991282283 13240090909406237986923425)
      ·
        refine ⟨9930068182054678490192569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13240090909406237986923425 9930068182054678490192569)
        ·
          refine ⟨7447551136541008867644427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9930068182054678490192569 7447551136541008867644427)
          ·
            refine ⟨11171326704811513301466641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7447551136541008867644427 11171326704811513301466641)
            ·
              refine ⟨8378495028608634976099981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11171326704811513301466641 8378495028608634976099981)
              ·
                refine ⟨3141935635728238116037493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8378495028608634976099981 3141935635728238116037493)
                ·
                  refine ⟨294556465849522323378515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3141935635728238116037493 294556465849522323378515)
                  ·
                    rfl

theorem cell22_2581410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 3, 5].length) (baseStart_2581410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2581410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2581410 prefixEnd_2581410 := by exact prefixLift 2581410
  have htrace : WordTrace (prefixWord ++ tailWord_2581410) baseStart_2581410 baseEnd_2581410 := by
    simpa [prefixWord, tailWord_2581410, baseEnd_2581410] using wordTrace_append hprefix tailTrace_2581410
  have hstable : (prefixWord ++ tailWord_2581410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2581410).length < 2 ^ (prefixWord ++ tailWord_2581410).sum := by decide
  have hdescent : baseEnd_2581410 < baseStart_2581410 := by decide
  rcases family_descends (prefixWord ++ tailWord_2581410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2581438 : List Nat := [4, 2, 1, 1, 1, 2, 1, 2, 8]
def baseStart_2581438 : Nat := 118140960795 + 2581438 * 2 ^ 59
def prefixEnd_2581438 : Nat := 4983230072969 + 3 ^ 40 * 2581438 * 2
def baseEnd_2581438 : Nat := 294559660840261410145153

theorem tailTrace_2581438 : CollatzResearch.WordTrace tailWord_2581438 prefixEnd_2581438 294559660840261410145153 := by
  unfold tailWord_2581438
  simp only [CollatzResearch.WordTrace]
  refine ⟨11769097352737309419462121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62768519214598983570464645 11769097352737309419462121)
  ·
    refine ⟨8826823014552982064596591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11769097352737309419462121 8826823014552982064596591)
    ·
      refine ⟨13240234521829473096894887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8826823014552982064596591 13240234521829473096894887)
      ·
        refine ⟨19860351782744209645342331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13240234521829473096894887 19860351782744209645342331)
        ·
          refine ⟨29790527674116314468013497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19860351782744209645342331 29790527674116314468013497)
          ·
            refine ⟨22342895755587235851010123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29790527674116314468013497 22342895755587235851010123)
            ·
              refine ⟨33514343633380853776515185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22342895755587235851010123 33514343633380853776515185)
              ·
                refine ⟨25135757725035640332386389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33514343633380853776515185 25135757725035640332386389)
                ·
                  refine ⟨294559660840261410145153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25135757725035640332386389 294559660840261410145153)
                  ·
                    rfl

theorem cell22_2581438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 2, 8].length) (baseStart_2581438 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2581438 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2581438 prefixEnd_2581438 := by exact prefixLift 2581438
  have htrace : WordTrace (prefixWord ++ tailWord_2581438) baseStart_2581438 baseEnd_2581438 := by
    simpa [prefixWord, tailWord_2581438, baseEnd_2581438] using wordTrace_append hprefix tailTrace_2581438
  have hstable : (prefixWord ++ tailWord_2581438).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2581438).length < 2 ^ (prefixWord ++ tailWord_2581438).sum := by decide
  have hdescent : baseEnd_2581438 < baseStart_2581438 := by decide
  rcases family_descends (prefixWord ++ tailWord_2581438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2581440 : List Nat := [2, 1, 1, 2, 3, 4, 1, 3, 1, 4]
def baseStart_2581440 : Nat := 118140960795 + 2581440 * 2 ^ 59
def prefixEnd_2581440 : Nat := 4983230072969 + 3 ^ 40 * 2581440 * 2
def baseEnd_2581440 : Nat := 883679667161656891885453

theorem tailTrace_2581440 : CollatzResearch.WordTrace tailWord_2581440 prefixEnd_2581440 883679667161656891885453 := by
  unfold tailWord_2581440
  simp only [CollatzResearch.WordTrace]
  refine ⟨47076425883945614848634887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62768567845260819798179849 47076425883945614848634887)
  ·
    refine ⟨70614638825918422272952331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47076425883945614848634887 70614638825918422272952331)
    ·
      refine ⟨105921958238877633409428497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70614638825918422272952331 105921958238877633409428497)
      ·
        refine ⟨79441468679158225057071373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105921958238877633409428497 79441468679158225057071373)
        ·
          refine ⟨29790550754684334396401765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79441468679158225057071373 29790550754684334396401765)
          ·
            refine ⟨5585728266503312699325331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29790550754684334396401765 5585728266503312699325331)
            ·
              refine ⟨8378592399754969048987997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5585728266503312699325331 8378592399754969048987997)
              ·
                refine ⟨3141972149908113393370499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8378592399754969048987997 3141972149908113393370499)
                ·
                  refine ⟨4712958224862170090055749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3141972149908113393370499 4712958224862170090055749)
                  ·
                    refine ⟨883679667161656891885453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4712958224862170090055749 883679667161656891885453)
                    ·
                      rfl

theorem cell22_2581440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 3, 1, 4].length) (baseStart_2581440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2581440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2581440 prefixEnd_2581440 := by exact prefixLift 2581440
  have htrace : WordTrace (prefixWord ++ tailWord_2581440) baseStart_2581440 baseEnd_2581440 := by
    simpa [prefixWord, tailWord_2581440, baseEnd_2581440] using wordTrace_append hprefix tailTrace_2581440
  have hstable : (prefixWord ++ tailWord_2581440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2581440).length < 2 ^ (prefixWord ++ tailWord_2581440).sum := by decide
  have hdescent : baseEnd_2581440 < baseStart_2581440 := by decide
  rcases family_descends (prefixWord ++ tailWord_2581440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2581444 : List Nat := [2, 3, 3, 3, 1, 2, 1, 2, 5]
def baseStart_2581444 : Nat := 118140960795 + 2581444 * 2 ^ 59
def prefixEnd_2581444 : Nat := 4983230072969 + 3 ^ 40 * 2581444 * 2
def baseEnd_2581444 : Nat := 294560345481134071595147

theorem tailTrace_2581444 : CollatzResearch.WordTrace tailWord_2581444 prefixEnd_2581444 294560345481134071595147 := by
  unfold tailWord_2581444
  simp only [CollatzResearch.WordTrace]
  refine ⟨47076498829938369190207693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62768665106584492253610257 47076498829938369190207693)
  ·
    refine ⟨17653687061226888446327885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47076498829938369190207693 17653687061226888446327885)
    ·
      refine ⟨6620132647960083167372957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17653687061226888446327885 6620132647960083167372957)
      ·
        refine ⟨2482549742985031187764859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6620132647960083167372957 2482549742985031187764859)
        ·
          refine ⟨3723824614477546781647289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2482549742985031187764859 3723824614477546781647289)
          ·
            refine ⟨2792868460858160086235467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3723824614477546781647289 2792868460858160086235467)
            ·
              refine ⟨4189302691287240129353201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2792868460858160086235467 4189302691287240129353201)
              ·
                refine ⟨3141977018465430097014901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4189302691287240129353201 3141977018465430097014901)
                ·
                  refine ⟨294560345481134071595147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3141977018465430097014901 294560345481134071595147)
                  ·
                    rfl

theorem cell22_2581444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 1, 2, 5].length) (baseStart_2581444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2581444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2581444 prefixEnd_2581444 := by exact prefixLift 2581444
  have htrace : WordTrace (prefixWord ++ tailWord_2581444) baseStart_2581444 baseEnd_2581444 := by
    simpa [prefixWord, tailWord_2581444, baseEnd_2581444] using wordTrace_append hprefix tailTrace_2581444
  have hstable : (prefixWord ++ tailWord_2581444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2581444).length < 2 ^ (prefixWord ++ tailWord_2581444).sum := by decide
  have hdescent : baseEnd_2581444 < baseStart_2581444 := by decide
  rcases family_descends (prefixWord ++ tailWord_2581444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2581455 : List Nat := [1, 1, 2, 1, 1, 6, 2, 4, 4]
def baseStart_2581455 : Nat := 118140960795 + 2581455 * 2 ^ 59
def prefixEnd_2581455 : Nat := 4983230072969 + 3 ^ 40 * 2581455 * 2
def baseEnd_2581455 : Nat := 294561600656067284253469

theorem tailTrace_2581455 : CollatzResearch.WordTrace tailWord_2581455 prefixEnd_2581455 294561600656067284253469 := by
  unfold tailWord_2581455
  simp only [CollatzResearch.WordTrace]
  refine ⟨94153398862836887259065819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62768932575224591506043879 94153398862836887259065819)
  ·
    refine ⟨141230098294255330888598729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94153398862836887259065819 141230098294255330888598729)
    ·
      refine ⟨105922573720691498166449047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141230098294255330888598729 105922573720691498166449047)
      ·
        refine ⟨158883860581037247249673571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105922573720691498166449047 158883860581037247249673571)
        ·
          refine ⟨238325790871555870874510357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158883860581037247249673571 238325790871555870874510357)
          ·
            refine ⟨11171521447104181447242673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 238325790871555870874510357 11171521447104181447242673)
            ·
              refine ⟨8378641085328136085432005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11171521447104181447242673 8378641085328136085432005)
              ·
                refine ⟨1570995203499025516018501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8378641085328136085432005 1570995203499025516018501)
                ·
                  refine ⟨294561600656067284253469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1570995203499025516018501 294561600656067284253469)
                  ·
                    rfl

theorem cell22_2581455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 4, 4].length) (baseStart_2581455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2581455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2581455 prefixEnd_2581455 := by exact prefixLift 2581455
  have htrace : WordTrace (prefixWord ++ tailWord_2581455) baseStart_2581455 baseEnd_2581455 := by
    simpa [prefixWord, tailWord_2581455, baseEnd_2581455] using wordTrace_append hprefix tailTrace_2581455
  have hstable : (prefixWord ++ tailWord_2581455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2581455).length < 2 ^ (prefixWord ++ tailWord_2581455).sum := by decide
  have hdescent : baseEnd_2581455 < baseStart_2581455 := by decide
  rcases family_descends (prefixWord ++ tailWord_2581455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2581474 : List Nat := [3, 3, 3, 1, 1, 2, 2, 2, 1, 4]
def baseStart_2581474 : Nat := 118140960795 + 2581474 * 2 ^ 59
def prefixEnd_2581474 : Nat := 4983230072969 + 3 ^ 40 * 2581474 * 2
def baseEnd_2581474 : Nat := 883691306056492136535349

theorem tailTrace_2581474 : CollatzResearch.WordTrace tailWord_2581474 prefixEnd_2581474 883691306056492136535349 := by
  unfold tailWord_2581474
  simp only [CollatzResearch.WordTrace]
  refine ⟨23538522962442013376001869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62769394566512035669338317 23538522962442013376001869)
  ·
    refine ⟨8826946110915755016000701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23538522962442013376001869 8826946110915755016000701)
    ·
      refine ⟨3310104791593408131000263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8826946110915755016000701 3310104791593408131000263)
      ·
        refine ⟨4965157187390112196500395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3310104791593408131000263 4965157187390112196500395)
        ·
          refine ⟨7447735781085168294750593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4965157187390112196500395 7447735781085168294750593)
          ·
            refine ⟨5585801835813876221062945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7447735781085168294750593 5585801835813876221062945)
            ·
              refine ⟨4189351376860407165797209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5585801835813876221062945 4189351376860407165797209)
              ·
                refine ⟨3142013532645305374347907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4189351376860407165797209 3142013532645305374347907)
                ·
                  refine ⟨4713020298967958061521861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3142013532645305374347907 4713020298967958061521861)
                  ·
                    refine ⟨883691306056492136535349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4713020298967958061521861 883691306056492136535349)
                    ·
                      rfl

theorem cell22_2581474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_2581474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2581474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2581474 prefixEnd_2581474 := by exact prefixLift 2581474
  have htrace : WordTrace (prefixWord ++ tailWord_2581474) baseStart_2581474 baseEnd_2581474 := by
    simpa [prefixWord, tailWord_2581474, baseEnd_2581474] using wordTrace_append hprefix tailTrace_2581474
  have hstable : (prefixWord ++ tailWord_2581474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2581474).length < 2 ^ (prefixWord ++ tailWord_2581474).sum := by decide
  have hdescent : baseEnd_2581474 < baseStart_2581474 := by decide
  rcases family_descends (prefixWord ++ tailWord_2581474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2581506 : List Nat := [3, 4, 1, 3, 2, 1, 1, 1, 6]
def baseStart_2581506 : Nat := 118140960795 + 2581506 * 2 ^ 59
def prefixEnd_2581506 : Nat := 4983230072969 + 3 ^ 40 * 2581506 * 2
def baseEnd_2581506 : Nat := 294567420103484906578417

theorem tailTrace_2581506 : CollatzResearch.WordTrace tailWord_2581506 prefixEnd_2581506 294567420103484906578417 := by
  unfold tailWord_2581506
  simp only [CollatzResearch.WordTrace]
  refine ⟨23538814746413030742293093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62770172657101415312781581 23538814746413030742293093)
  ·
    refine ⟨4413527764952443264179955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23538814746413030742293093 4413527764952443264179955)
    ·
      refine ⟨6620291647428664896269933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4413527764952443264179955 6620291647428664896269933)
      ·
        refine ⟨2482609367785749336101225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6620291647428664896269933 2482609367785749336101225)
        ·
          refine ⟨1861957025839312002075919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2482609367785749336101225 1861957025839312002075919)
          ·
            refine ⟨2792935538758968003113879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1861957025839312002075919 2792935538758968003113879)
            ·
              refine ⟨4189403308138452004670819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2792935538758968003113879 4189403308138452004670819)
              ·
                refine ⟨6284104962207678007006229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4189403308138452004670819 6284104962207678007006229)
                ·
                  refine ⟨294567420103484906578417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6284104962207678007006229 294567420103484906578417)
                  ·
                    rfl

theorem cell22_2581506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 1, 1, 6].length) (baseStart_2581506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2581506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2581506 prefixEnd_2581506 := by exact prefixLift 2581506
  have htrace : WordTrace (prefixWord ++ tailWord_2581506) baseStart_2581506 baseEnd_2581506 := by
    simpa [prefixWord, tailWord_2581506, baseEnd_2581506] using wordTrace_append hprefix tailTrace_2581506
  have hstable : (prefixWord ++ tailWord_2581506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2581506).length < 2 ^ (prefixWord ++ tailWord_2581506).sum := by decide
  have hdescent : baseEnd_2581506 < baseStart_2581506 := by decide
  rcases family_descends (prefixWord ++ tailWord_2581506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2581566 : List Nat := [4, 2, 1, 3, 1, 2, 1, 4, 1, 3]
def baseStart_2581566 : Nat := 118140960795 + 2581566 * 2 ^ 59
def prefixEnd_2581566 : Nat := 4983230072969 + 3 ^ 40 * 2581566 * 2
def baseEnd_2581566 : Nat := 883722799536634563235067

theorem tailTrace_2581566 : CollatzResearch.WordTrace tailWord_2581566 prefixEnd_2581566 883722799536634563235067 := by
  unfold tailWord_2581566
  simp only [CollatzResearch.WordTrace]
  refine ⟨11769680920679344152044569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62771631576956502144237701 11769680920679344152044569)
  ·
    refine ⟨8827260690509508114033427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11769680920679344152044569 8827260690509508114033427)
    ·
      refine ⟨13240891035764262171050141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8827260690509508114033427 13240891035764262171050141)
      ·
        refine ⟨4965334138411598314143803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13240891035764262171050141 4965334138411598314143803)
        ·
          refine ⟨7448001207617397471215705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4965334138411598314143803 7448001207617397471215705)
          ·
            refine ⟨5586000905713048103411779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7448001207617397471215705 5586000905713048103411779)
            ·
              refine ⟨8379001358569572155117669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5586000905713048103411779 8379001358569572155117669)
              ·
                refine ⟨1571062754731794779084563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8379001358569572155117669 1571062754731794779084563)
                ·
                  refine ⟨2356594132097692168626845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1571062754731794779084563 2356594132097692168626845)
                  ·
                    refine ⟨883722799536634563235067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2356594132097692168626845 883722799536634563235067)
                    ·
                      rfl

theorem cell22_2581566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 4, 1, 3].length) (baseStart_2581566 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2581566 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2581566 prefixEnd_2581566 := by exact prefixLift 2581566
  have htrace : WordTrace (prefixWord ++ tailWord_2581566) baseStart_2581566 baseEnd_2581566 := by
    simpa [prefixWord, tailWord_2581566, baseEnd_2581566] using wordTrace_append hprefix tailTrace_2581566
  have hstable : (prefixWord ++ tailWord_2581566).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2581566).length < 2 ^ (prefixWord ++ tailWord_2581566).sum := by decide
  have hdescent : baseEnd_2581566 < baseStart_2581566 := by decide
  rcases family_descends (prefixWord ++ tailWord_2581566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2581575 : List Nat := [1, 1, 4, 1, 3, 2, 1, 2, 3, 4]
def baseStart_2581575 : Nat := 118140960795 + 2581575 * 2 ^ 59
def prefixEnd_2581575 : Nat := 4983230072969 + 3 ^ 40 * 2581575 * 2
def baseEnd_2581575 : Nat := 883725880420561539760039

theorem tailTrace_2581575 : CollatzResearch.WordTrace tailWord_2581575 prefixEnd_2581575 883725880420561539760039 := by
  unfold tailWord_2581575
  simp only [CollatzResearch.WordTrace]
  refine ⟨94157775622402147753434179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62771850414934765168956119 94157775622402147753434179)
  ·
    refine ⟨141236663433603221630151269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94157775622402147753434179 141236663433603221630151269)
    ·
      refine ⟨26481874393800604055653363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 141236663433603221630151269 26481874393800604055653363)
      ·
        refine ⟨39722811590700906083480045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26481874393800604055653363 39722811590700906083480045)
        ·
          refine ⟨14896054346512839781305017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39722811590700906083480045 14896054346512839781305017)
          ·
            refine ⟨11172040759884629835978763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14896054346512839781305017 11172040759884629835978763)
            ·
              refine ⟨16758061139826944753968145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11172040759884629835978763 16758061139826944753968145)
              ·
                refine ⟨12568545854870208565476109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16758061139826944753968145 12568545854870208565476109)
                ·
                  refine ⟨4713204695576328212053541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12568545854870208565476109 4713204695576328212053541)
                  ·
                    refine ⟨883725880420561539760039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4713204695576328212053541 883725880420561539760039)
                    ·
                      rfl

theorem cell22_2581575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 2, 3, 4].length) (baseStart_2581575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2581575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2581575 prefixEnd_2581575 := by exact prefixLift 2581575
  have htrace : WordTrace (prefixWord ++ tailWord_2581575) baseStart_2581575 baseEnd_2581575 := by
    simpa [prefixWord, tailWord_2581575, baseEnd_2581575] using wordTrace_append hprefix tailTrace_2581575
  have hstable : (prefixWord ++ tailWord_2581575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2581575).length < 2 ^ (prefixWord ++ tailWord_2581575).sum := by decide
  have hdescent : baseEnd_2581575 < baseStart_2581575 := by decide
  rcases family_descends (prefixWord ++ tailWord_2581575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2581605 : List Nat := [1, 3, 1, 3, 2, 1, 1, 4, 1, 5]
def baseStart_2581605 : Nat := 118140960795 + 2581605 * 2 ^ 59
def prefixEnd_2581605 : Nat := 4983230072969 + 3 ^ 40 * 2581605 * 2
def baseEnd_2581605 : Nat := 883736150033651461509947

theorem tailTrace_2581605 : CollatzResearch.WordTrace tailWord_2581605 prefixEnd_2581605 883736150033651461509947 := by
  unfold tailWord_2581605
  simp only [CollatzResearch.WordTrace]
  refine ⟨94158869812293462877026269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62772579874862308584684179 94158869812293462877026269)
  ·
    refine ⟨35309576179610048578884851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94158869812293462877026269 35309576179610048578884851)
    ·
      refine ⟨52964364269415072868327277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35309576179610048578884851 52964364269415072868327277)
      ·
        refine ⟨19861636601030652325622729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52964364269415072868327277 19861636601030652325622729)
        ·
          refine ⟨14896227450772989244217047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19861636601030652325622729 14896227450772989244217047)
          ·
            refine ⟨22344341176159483866325571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14896227450772989244217047 22344341176159483866325571)
            ·
              refine ⟨33516511764239225799488357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22344341176159483866325571 33516511764239225799488357)
              ·
                refine ⟨6284345955794854837404067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33516511764239225799488357 6284345955794854837404067)
                ·
                  refine ⟨9426518933692282256106101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6284345955794854837404067 9426518933692282256106101)
                  ·
                    refine ⟨883736150033651461509947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9426518933692282256106101 883736150033651461509947)
                    ·
                      rfl

theorem cell22_2581605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 4, 1, 5].length) (baseStart_2581605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2581605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2581605 prefixEnd_2581605 := by exact prefixLift 2581605
  have htrace : WordTrace (prefixWord ++ tailWord_2581605) baseStart_2581605 baseEnd_2581605 := by
    simpa [prefixWord, tailWord_2581605, baseEnd_2581605] using wordTrace_append hprefix tailTrace_2581605
  have hstable : (prefixWord ++ tailWord_2581605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2581605).length < 2 ^ (prefixWord ++ tailWord_2581605).sum := by decide
  have hdescent : baseEnd_2581605 < baseStart_2581605 := by decide
  rcases family_descends (prefixWord ++ tailWord_2581605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2581607 : List Nat := [1, 1, 5, 1, 1, 3, 1, 5, 4]
def baseStart_2581607 : Nat := 118140960795 + 2581607 * 2 ^ 59
def prefixEnd_2581607 : Nat := 4983230072969 + 3 ^ 40 * 2581607 * 2
def baseEnd_2581607 : Nat := 294578944891508040986647

theorem tailTrace_2581607 : CollatzResearch.WordTrace tailWord_2581607 prefixEnd_2581607 294578944891508040986647 := by
  unfold tailWord_2581607
  simp only [CollatzResearch.WordTrace]
  refine ⟨94158942758286217218599075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62772628505524144812399383 94158942758286217218599075)
  ·
    refine ⟨141238414137429325827898613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94158942758286217218599075 141238414137429325827898613)
    ·
      refine ⟨13241101325383999296365495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 141238414137429325827898613 13241101325383999296365495)
      ·
        refine ⟨19861651988075998944548243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13241101325383999296365495 19861651988075998944548243)
        ·
          refine ⟨29792477982113998416822365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19861651988075998944548243 29792477982113998416822365)
          ·
            refine ⟨11172179243292749406308387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29792477982113998416822365 11172179243292749406308387)
            ·
              refine ⟨16758268864939124109462581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11172179243292749406308387 16758268864939124109462581)
              ·
                refine ⟨1571087706088042885262117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16758268864939124109462581 1571087706088042885262117)
                ·
                  refine ⟨294578944891508040986647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1571087706088042885262117 294578944891508040986647)
                  ·
                    rfl

theorem cell22_2581607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 5, 4].length) (baseStart_2581607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2581607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2581607 prefixEnd_2581607 := by exact prefixLift 2581607
  have htrace : WordTrace (prefixWord ++ tailWord_2581607) baseStart_2581607 baseEnd_2581607 := by
    simpa [prefixWord, tailWord_2581607, baseEnd_2581607] using wordTrace_append hprefix tailTrace_2581607
  have hstable : (prefixWord ++ tailWord_2581607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2581607).length < 2 ^ (prefixWord ++ tailWord_2581607).sum := by decide
  have hdescent : baseEnd_2581607 < baseStart_2581607 := by decide
  rcases family_descends (prefixWord ++ tailWord_2581607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2581609 : List Nat := [1, 2, 1, 1, 1, 8, 2, 1, 1, 4]
def baseStart_2581609 : Nat := 118140960795 + 2581609 * 2 ^ 59
def prefixEnd_2581609 : Nat := 4983230072969 + 3 ^ 40 * 2581609 * 2
def baseEnd_2581609 : Nat := 883737519315396784409935

theorem tailTrace_2581609 : CollatzResearch.WordTrace tailWord_2581609 prefixEnd_2581609 883737519315396784409935 := by
  unfold tailWord_2581609
  simp only [CollatzResearch.WordTrace]
  refine ⟨94159015704278971560171881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62772677136185981040114587 94159015704278971560171881)
  ·
    refine ⟨70619261778209228670128911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94159015704278971560171881 70619261778209228670128911)
    ·
      refine ⟨105928892667313843005193367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70619261778209228670128911 105928892667313843005193367)
      ·
        refine ⟨158893339000970764507790051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105928892667313843005193367 158893339000970764507790051)
        ·
          refine ⟨238340008501456146761685077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158893339000970764507790051 238340008501456146761685077)
          ·
            refine ⟨2793046974626439219863497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 238340008501456146761685077 2793046974626439219863497)
            ·
              refine ⟨2094785230969829414897623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2793046974626439219863497 2094785230969829414897623)
              ·
                refine ⟨3142177846454744122346435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2094785230969829414897623 3142177846454744122346435)
                ·
                  refine ⟨4713266769682116183519653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3142177846454744122346435 4713266769682116183519653)
                  ·
                    refine ⟨883737519315396784409935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4713266769682116183519653 883737519315396784409935)
                    ·
                      rfl

theorem cell22_2581609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 2, 1, 1, 4].length) (baseStart_2581609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2581609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2581609 prefixEnd_2581609 := by exact prefixLift 2581609
  have htrace : WordTrace (prefixWord ++ tailWord_2581609) baseStart_2581609 baseEnd_2581609 := by
    simpa [prefixWord, tailWord_2581609, baseEnd_2581609] using wordTrace_append hprefix tailTrace_2581609
  have hstable : (prefixWord ++ tailWord_2581609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2581609).length < 2 ^ (prefixWord ++ tailWord_2581609).sum := by decide
  have hdescent : baseEnd_2581609 < baseStart_2581609 := by decide
  rcases family_descends (prefixWord ++ tailWord_2581609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2581686 : List Nat := [5, 1, 3, 2, 1, 1, 2, 7]
def baseStart_2581686 : Nat := 118140960795 + 2581686 * 2 ^ 59
def prefixEnd_2581686 : Nat := 4983230072969 + 3 ^ 40 * 2581686 * 2
def baseEnd_2581686 : Nat := 98195986443221583359411

theorem tailTrace_2581686 : CollatzResearch.WordTrace tailWord_2581686 prefixEnd_2581686 98195986443221583359411 := by
  unfold tailWord_2581686
  simp only [CollatzResearch.WordTrace]
  refine ⟨5885114007812500856920307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 62774549416666675807149941 5885114007812500856920307)
  ·
    refine ⟨8827671011718751285380461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5885114007812500856920307 8827671011718751285380461)
    ·
      refine ⟨3310376629394531732017673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8827671011718751285380461 3310376629394531732017673)
      ·
        refine ⟨2482782472045898799013255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3310376629394531732017673 2482782472045898799013255)
        ·
          refine ⟨3724173708068848198519883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2482782472045898799013255 3724173708068848198519883)
          ·
            refine ⟨5586260562103272297779825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3724173708068848198519883 5586260562103272297779825)
            ·
              refine ⟨4189695421577454223334869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5586260562103272297779825 4189695421577454223334869)
              ·
                refine ⟨98195986443221583359411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4189695421577454223334869 98195986443221583359411)
                ·
                  rfl

theorem cell22_2581686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 2, 7].length) (baseStart_2581686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2581686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2581686 prefixEnd_2581686 := by exact prefixLift 2581686
  have htrace : WordTrace (prefixWord ++ tailWord_2581686) baseStart_2581686 baseEnd_2581686 := by
    simpa [prefixWord, tailWord_2581686, baseEnd_2581686] using wordTrace_append hprefix tailTrace_2581686
  have hstable : (prefixWord ++ tailWord_2581686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2581686).length < 2 ^ (prefixWord ++ tailWord_2581686).sum := by decide
  have hdescent : baseEnd_2581686 < baseStart_2581686 := by decide
  rcases family_descends (prefixWord ++ tailWord_2581686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2581695 : List Nat := [1, 1, 2, 2, 2, 2, 2, 3, 2, 5]
def baseStart_2581695 : Nat := 118140960795 + 2581695 * 2 ^ 59
def prefixEnd_2581695 : Nat := 4983230072969 + 3 ^ 40 * 2581695 * 2
def baseEnd_2581695 : Nat := 883766958872921226759671

theorem tailTrace_2581695 : CollatzResearch.WordTrace tailWord_2581695 prefixEnd_2581695 883766958872921226759671 := by
  unfold tailWord_2581695
  simp only [CollatzResearch.WordTrace]
  refine ⟨94162152381967408247802539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62774768254644938831868359 94162152381967408247802539)
  ·
    refine ⟨141243228572951112371703809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94162152381967408247802539 141243228572951112371703809)
    ·
      refine ⟨105932421429713334278777857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141243228572951112371703809 105932421429713334278777857)
      ·
        refine ⟨79449316072285000709083393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105932421429713334278777857 79449316072285000709083393)
        ·
          refine ⟨59586987054213750531812545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79449316072285000709083393 59586987054213750531812545)
          ·
            refine ⟨44690240290660312898859409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59586987054213750531812545 44690240290660312898859409)
            ·
              refine ⟨33517680217995234674144557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44690240290660312898859409 33517680217995234674144557)
              ·
                refine ⟨12569130081748213002804209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33517680217995234674144557 12569130081748213002804209)
                ·
                  refine ⟨9426847561311159752103157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12569130081748213002804209 9426847561311159752103157)
                  ·
                    refine ⟨883766958872921226759671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9426847561311159752103157 883766958872921226759671)
                    ·
                      rfl

theorem cell22_2581695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3, 2, 5].length) (baseStart_2581695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2581695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2581695 prefixEnd_2581695 := by exact prefixLift 2581695
  have htrace : WordTrace (prefixWord ++ tailWord_2581695) baseStart_2581695 baseEnd_2581695 := by
    simpa [prefixWord, tailWord_2581695, baseEnd_2581695] using wordTrace_append hprefix tailTrace_2581695
  have hstable : (prefixWord ++ tailWord_2581695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2581695).length < 2 ^ (prefixWord ++ tailWord_2581695).sum := by decide
  have hdescent : baseEnd_2581695 < baseStart_2581695 := by decide
  rcases family_descends (prefixWord ++ tailWord_2581695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2581727 : List Nat := [1, 1, 2, 3, 2, 1, 2, 5, 1, 4]
def baseStart_2581727 : Nat := 118140960795 + 2581727 * 2 ^ 59
def prefixEnd_2581727 : Nat := 4983230072969 + 3 ^ 40 * 2581727 * 2
def baseEnd_2581727 : Nat := 883777913126883809959573

theorem tailTrace_2581727 : CollatzResearch.WordTrace tailWord_2581727 prefixEnd_2581727 883777913126883809959573 := by
  unfold tailWord_2581727
  simp only [CollatzResearch.WordTrace]
  refine ⟨94163319517851477712967435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62775546345234318475311623 94163319517851477712967435)
  ·
    refine ⟨141244979276777216569451153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94163319517851477712967435 141244979276777216569451153)
    ·
      refine ⟨105933734457582912427088365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141244979276777216569451153 105933734457582912427088365)
      ·
        refine ⟨39725150421593592160158137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105933734457582912427088365 39725150421593592160158137)
        ·
          refine ⟨29793862816195194120118603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39725150421593592160158137 29793862816195194120118603)
          ·
            refine ⟨44690794224292791180177905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29793862816195194120118603 44690794224292791180177905)
            ·
              refine ⟨33518095668219593385133429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44690794224292791180177905 33518095668219593385133429)
              ·
                refine ⟨3142321468895586879856259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33518095668219593385133429 3142321468895586879856259)
                ·
                  refine ⟨4713482203343380319784389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3142321468895586879856259 4713482203343380319784389)
                  ·
                    refine ⟨883777913126883809959573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4713482203343380319784389 883777913126883809959573)
                    ·
                      rfl

theorem cell22_2581727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 5, 1, 4].length) (baseStart_2581727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2581727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2581727 prefixEnd_2581727 := by exact prefixLift 2581727
  have htrace : WordTrace (prefixWord ++ tailWord_2581727) baseStart_2581727 baseEnd_2581727 := by
    simpa [prefixWord, tailWord_2581727, baseEnd_2581727] using wordTrace_append hprefix tailTrace_2581727
  have hstable : (prefixWord ++ tailWord_2581727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2581727).length < 2 ^ (prefixWord ++ tailWord_2581727).sum := by decide
  have hdescent : baseEnd_2581727 < baseStart_2581727 := by decide
  rcases family_descends (prefixWord ++ tailWord_2581727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2581735 : List Nat := [1, 1, 5, 3, 2, 2, 2, 2, 1, 3]
def baseStart_2581735 : Nat := 118140960795 + 2581735 * 2 ^ 59
def prefixEnd_2581735 : Nat := 4983230072969 + 3 ^ 40 * 2581735 * 2
def baseEnd_2581735 : Nat := 883780651690374455759549

theorem tailTrace_2581735 : CollatzResearch.WordTrace tailWord_2581735 prefixEnd_2581735 883780651690374455759549 := by
  unfold tailWord_2581735
  simp only [CollatzResearch.WordTrace]
  refine ⟨94163611301822495079258659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62775740867881663386172439 94163611301822495079258659)
  ·
    refine ⟨141245416952733742618887989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94163611301822495079258659 141245416952733742618887989)
    ·
      refine ⟨13241757839318788370520749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 141245416952733742618887989 13241757839318788370520749)
      ·
        refine ⟨4965659189744545638945281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13241757839318788370520749 4965659189744545638945281)
        ·
          refine ⟨3724244392308409229208961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4965659189744545638945281 3724244392308409229208961)
          ·
            refine ⟨2793183294231306921906721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3724244392308409229208961 2793183294231306921906721)
            ·
              refine ⟨2094887470673480191430041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2793183294231306921906721 2094887470673480191430041)
              ·
                refine ⟨1571165603005110143572531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2094887470673480191430041 1571165603005110143572531)
                ·
                  refine ⟨2356748404507665215358797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1571165603005110143572531 2356748404507665215358797)
                  ·
                    refine ⟨883780651690374455759549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2356748404507665215358797 883780651690374455759549)
                    ·
                      rfl

theorem cell22_2581735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 2, 2, 1, 3].length) (baseStart_2581735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2581735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2581735 prefixEnd_2581735 := by exact prefixLift 2581735
  have htrace : WordTrace (prefixWord ++ tailWord_2581735) baseStart_2581735 baseEnd_2581735 := by
    simpa [prefixWord, tailWord_2581735, baseEnd_2581735] using wordTrace_append hprefix tailTrace_2581735
  have hstable : (prefixWord ++ tailWord_2581735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2581735).length < 2 ^ (prefixWord ++ tailWord_2581735).sum := by decide
  have hdescent : baseEnd_2581735 < baseStart_2581735 := by decide
  rcases family_descends (prefixWord ++ tailWord_2581735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2581757 : List Nat := [1, 4, 1, 1, 1, 1, 1, 1, 8, 3]
def baseStart_2581757 : Nat := 118140960795 + 2581757 * 2 ^ 59
def prefixEnd_2581757 : Nat := 4983230072969 + 3 ^ 40 * 2581757 * 2
def baseEnd_2581757 : Nat := 883788182739973731709481

theorem tailTrace_2581757 : CollatzResearch.WordTrace tailWord_2581757 prefixEnd_2581757 883788182739973731709481 := by
  unfold tailWord_2581757
  simp only [CollatzResearch.WordTrace]
  refine ⟨94164413707742792836559525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62776275805161861891039683 94164413707742792836559525)
  ·
    refine ⟨17655827570201773656854911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94164413707742792836559525 17655827570201773656854911)
    ·
      refine ⟨26483741355302660485282367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17655827570201773656854911 26483741355302660485282367)
      ·
        refine ⟨39725612032953990727923551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26483741355302660485282367 39725612032953990727923551)
        ·
          refine ⟨59588418049430986091885327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39725612032953990727923551 59588418049430986091885327)
          ·
            refine ⟨89382627074146479137827991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59588418049430986091885327 89382627074146479137827991)
            ·
              refine ⟨134073940611219718706741987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89382627074146479137827991 134073940611219718706741987)
              ·
                refine ⟨201110910916829578060112981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 134073940611219718706741987 201110910916829578060112981)
                ·
                  refine ⟨2356768487306596617891949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 201110910916829578060112981 2356768487306596617891949)
                  ·
                    refine ⟨883788182739973731709481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2356768487306596617891949 883788182739973731709481)
                    ·
                      rfl

theorem cell22_2581757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 8, 3].length) (baseStart_2581757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2581757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2581757 prefixEnd_2581757 := by exact prefixLift 2581757
  have htrace : WordTrace (prefixWord ++ tailWord_2581757) baseStart_2581757 baseEnd_2581757 := by
    simpa [prefixWord, tailWord_2581757, baseEnd_2581757] using wordTrace_append hprefix tailTrace_2581757
  have hstable : (prefixWord ++ tailWord_2581757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2581757).length < 2 ^ (prefixWord ++ tailWord_2581757).sum := by decide
  have hdescent : baseEnd_2581757 < baseStart_2581757 := by decide
  rcases family_descends (prefixWord ++ tailWord_2581757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2581772 : List Nat := [2, 2, 1, 2, 2, 4, 1, 1, 1, 6]
def baseStart_2581772 : Nat := 118140960795 + 2581772 * 2 ^ 59
def prefixEnd_2581772 : Nat := 4983230072969 + 3 ^ 40 * 2581772 * 2
def baseEnd_2581772 : Nat := 883793317546518692584435

theorem tailTrace_2581772 : CollatzResearch.WordTrace tailWord_2581772 prefixEnd_2581772 883793317546518692584435 := by
  unfold tailWord_2581772
  simp only [CollatzResearch.WordTrace]
  refine ⟨47082480401344225199177785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62776640535125633598903713 47082480401344225199177785)
  ·
    refine ⟨35311860301008168899383339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47082480401344225199177785 35311860301008168899383339)
    ·
      refine ⟨52967790451512253349075009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35311860301008168899383339 52967790451512253349075009)
      ·
        refine ⟨39725842838634190011806257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52967790451512253349075009 39725842838634190011806257)
        ·
          refine ⟨29794382128975642508854693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39725842838634190011806257 29794382128975642508854693)
          ·
            refine ⟨5586446649182932970410255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29794382128975642508854693 5586446649182932970410255)
            ·
              refine ⟨8379669973774399455615383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5586446649182932970410255 8379669973774399455615383)
              ·
                refine ⟨12569504960661599183423075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8379669973774399455615383 12569504960661599183423075)
                ·
                  refine ⟨18854257440992398775134613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12569504960661599183423075 18854257440992398775134613)
                  ·
                    refine ⟨883793317546518692584435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18854257440992398775134613 883793317546518692584435)
                    ·
                      rfl

theorem cell22_2581772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 1, 1, 6].length) (baseStart_2581772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2581772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2581772 prefixEnd_2581772 := by exact prefixLift 2581772
  have htrace : WordTrace (prefixWord ++ tailWord_2581772) baseStart_2581772 baseEnd_2581772 := by
    simpa [prefixWord, tailWord_2581772, baseEnd_2581772] using wordTrace_append hprefix tailTrace_2581772
  have hstable : (prefixWord ++ tailWord_2581772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2581772).length < 2 ^ (prefixWord ++ tailWord_2581772).sum := by decide
  have hdescent : baseEnd_2581772 < baseStart_2581772 := by decide
  rcases family_descends (prefixWord ++ tailWord_2581772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2581778 : List Nat := [3, 2, 4, 2, 1, 1, 1, 3, 1, 4]
def baseStart_2581778 : Nat := 118140960795 + 2581778 * 2 ^ 59
def prefixEnd_2581778 : Nat := 4983230072969 + 3 ^ 40 * 2581778 * 2
def baseEnd_2581778 : Nat := 883795371469136676934417

theorem tailTrace_2581778 : CollatzResearch.WordTrace tailWord_2581778 prefixEnd_2581778 883795371469136676934417 := by
  unfold tailWord_2581778
  simp only [CollatzResearch.WordTrace]
  refine ⟨23541294910166678355768497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62776786427111142282049325 23541294910166678355768497)
  ·
    refine ⟨17655971182625008766826373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23541294910166678355768497 17655971182625008766826373)
    ·
      refine ⟨3310494596742189143779945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17655971182625008766826373 3310494596742189143779945)
      ·
        refine ⟨2482870947556641857834959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3310494596742189143779945 2482870947556641857834959)
        ·
          refine ⟨3724306421334962786752439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2482870947556641857834959 3724306421334962786752439)
          ·
            refine ⟨5586459632002444180128659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3724306421334962786752439 5586459632002444180128659)
            ·
              refine ⟨8379689448003666270192989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5586459632002444180128659 8379689448003666270192989)
              ·
                refine ⟨3142383543001374851322371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8379689448003666270192989 3142383543001374851322371)
                ·
                  refine ⟨4713575314502062276983557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3142383543001374851322371 4713575314502062276983557)
                  ·
                    refine ⟨883795371469136676934417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4713575314502062276983557 883795371469136676934417)
                    ·
                      rfl

theorem cell22_2581778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_2581778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2581778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2581778 prefixEnd_2581778 := by exact prefixLift 2581778
  have htrace : WordTrace (prefixWord ++ tailWord_2581778) baseStart_2581778 baseEnd_2581778 := by
    simpa [prefixWord, tailWord_2581778, baseEnd_2581778] using wordTrace_append hprefix tailTrace_2581778
  have hstable : (prefixWord ++ tailWord_2581778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2581778).length < 2 ^ (prefixWord ++ tailWord_2581778).sum := by decide
  have hdescent : baseEnd_2581778 < baseStart_2581778 := by decide
  rcases family_descends (prefixWord ++ tailWord_2581778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2581785 : List Nat := [1, 2, 1, 2, 1, 1, 1, 1, 3, 9]
def baseStart_2581785 : Nat := 118140960795 + 2581785 * 2 ^ 59
def prefixEnd_2581785 : Nat := 4983230072969 + 3 ^ 40 * 2581785 * 2
def baseEnd_2581785 : Nat := 883797767712190992009395

theorem tailTrace_2581785 : CollatzResearch.WordTrace tailWord_2581785 prefixEnd_2581785 883797767712190992009395 := by
  unfold tailWord_2581785
  simp only [CollatzResearch.WordTrace]
  refine ⟨94165434951641353618578809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62776956634427569079052539 94165434951641353618578809)
  ·
    refine ⟨70624076213731015213934107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94165434951641353618578809 70624076213731015213934107)
    ·
      refine ⟨105936114320596522820901161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70624076213731015213934107 105936114320596522820901161)
      ·
        refine ⟨79452085740447392115675871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105936114320596522820901161 79452085740447392115675871)
        ·
          refine ⟨119178128610671088173513807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79452085740447392115675871 119178128610671088173513807)
          ·
            refine ⟨178767192916006632260270711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119178128610671088173513807 178767192916006632260270711)
            ·
              refine ⟨268150789374009948390406067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 178767192916006632260270711 268150789374009948390406067)
              ·
                refine ⟨402226184061014922585609101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 268150789374009948390406067 402226184061014922585609101)
                ·
                  refine ⟨150834819022880595969603413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 402226184061014922585609101 150834819022880595969603413)
                  ·
                    refine ⟨883797767712190992009395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 150834819022880595969603413 883797767712190992009395)
                    ·
                      rfl

theorem cell22_2581785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 9].length) (baseStart_2581785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2581785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2581785 prefixEnd_2581785 := by exact prefixLift 2581785
  have htrace : WordTrace (prefixWord ++ tailWord_2581785) baseStart_2581785 baseEnd_2581785 := by
    simpa [prefixWord, tailWord_2581785, baseEnd_2581785] using wordTrace_append hprefix tailTrace_2581785
  have hstable : (prefixWord ++ tailWord_2581785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2581785).length < 2 ^ (prefixWord ++ tailWord_2581785).sum := by decide
  have hdescent : baseEnd_2581785 < baseStart_2581785 := by decide
  rcases family_descends (prefixWord ++ tailWord_2581785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2581866 : List Nat := [3, 1, 3, 3, 2, 1, 1, 3, 5]
def baseStart_2581866 : Nat := 118140960795 + 2581866 * 2 ^ 59
def prefixEnd_2581866 : Nat := 4983230072969 + 3 ^ 40 * 2581866 * 2
def baseEnd_2581866 : Nat := 294608498555844593578049

theorem tailTrace_2581866 : CollatzResearch.WordTrace tailWord_2581866 prefixEnd_2581866 294608498555844593578049 := by
  unfold tailWord_2581866
  simp only [CollatzResearch.WordTrace]
  refine ⟨23542097316086976113069363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62778926176231936301518301 23542097316086976113069363)
  ·
    refine ⟨35313145974130464169604045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23542097316086976113069363 35313145974130464169604045)
    ·
      refine ⟨13242429740298924063601517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35313145974130464169604045 13242429740298924063601517)
      ·
        refine ⟨4965911152612096523850569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13242429740298924063601517 4965911152612096523850569)
        ·
          refine ⟨3724433364459072392887927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4965911152612096523850569 3724433364459072392887927)
          ·
            refine ⟨5586650046688608589331891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3724433364459072392887927 5586650046688608589331891)
            ·
              refine ⟨8379975070032912883997837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5586650046688608589331891 8379975070032912883997837)
              ·
                refine ⟨3142490651262342331499189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8379975070032912883997837 3142490651262342331499189)
                ·
                  refine ⟨294608498555844593578049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3142490651262342331499189 294608498555844593578049)
                  ·
                    rfl

theorem cell22_2581866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 3, 5].length) (baseStart_2581866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2581866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2581866 prefixEnd_2581866 := by exact prefixLift 2581866
  have htrace : WordTrace (prefixWord ++ tailWord_2581866) baseStart_2581866 baseEnd_2581866 := by
    simpa [prefixWord, tailWord_2581866, baseEnd_2581866] using wordTrace_append hprefix tailTrace_2581866
  have hstable : (prefixWord ++ tailWord_2581866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2581866).length < 2 ^ (prefixWord ++ tailWord_2581866).sum := by decide
  have hdescent : baseEnd_2581866 < baseStart_2581866 := by decide
  rcases family_descends (prefixWord ++ tailWord_2581866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2581909 : List Nat := [1, 3, 2, 1, 1, 2, 2, 3, 4, 3]
def baseStart_2581909 : Nat := 118140960795 + 2581909 * 2 ^ 59
def prefixEnd_2581909 : Nat := 4983230072969 + 3 ^ 40 * 2581909 * 2
def baseEnd_2581909 : Nat := 883840215446296001909015

theorem tailTrace_2581909 : CollatzResearch.WordTrace tailWord_2581909 prefixEnd_2581909 883840215446296001909015 := by
  unfold tailWord_2581909
  simp only [CollatzResearch.WordTrace]
  refine ⟨94169957603192122796092781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62779971735461415197395187 94169957603192122796092781)
  ·
    refine ⟨35313734101197046048534793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94169957603192122796092781 35313734101197046048534793)
    ·
      refine ⟨26485300575897784536401095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35313734101197046048534793 26485300575897784536401095)
      ·
        refine ⟨39727950863846676804601643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26485300575897784536401095 39727950863846676804601643)
        ·
          refine ⟨59591926295770015206902465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39727950863846676804601643 59591926295770015206902465)
          ·
            refine ⟨44693944721827511405176849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59591926295770015206902465 44693944721827511405176849)
            ·
              refine ⟨33520458541370633553882637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44693944721827511405176849 33520458541370633553882637)
              ·
                refine ⟨12570171953013987582705989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33520458541370633553882637 12570171953013987582705989)
                ·
                  refine ⟨2356907241190122671757373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12570171953013987582705989 2356907241190122671757373)
                  ·
                    refine ⟨883840215446296001909015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2356907241190122671757373 883840215446296001909015)
                    ·
                      rfl

theorem cell22_2581909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 3, 4, 3].length) (baseStart_2581909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2581909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2581909 prefixEnd_2581909 := by exact prefixLift 2581909
  have htrace : WordTrace (prefixWord ++ tailWord_2581909) baseStart_2581909 baseEnd_2581909 := by
    simpa [prefixWord, tailWord_2581909, baseEnd_2581909] using wordTrace_append hprefix tailTrace_2581909
  have hstable : (prefixWord ++ tailWord_2581909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2581909).length < 2 ^ (prefixWord ++ tailWord_2581909).sum := by decide
  have hdescent : baseEnd_2581909 < baseStart_2581909 := by decide
  rcases family_descends (prefixWord ++ tailWord_2581909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2581941 : List Nat := [1, 3, 3, 2, 2, 1, 3, 1, 2, 4]
def baseStart_2581941 : Nat := 118140960795 + 2581941 * 2 ^ 59
def prefixEnd_2581941 : Nat := 4983230072969 + 3 ^ 40 * 2581941 * 2
def baseEnd_2581941 : Nat := 883851169700258585108917

theorem tailTrace_2581941 : CollatzResearch.WordTrace tailWord_2581941 prefixEnd_2581941 883851169700258585108917 := by
  unfold tailWord_2581941
  simp only [CollatzResearch.WordTrace]
  refine ⟨94171124739076192261257677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62780749826050794840838451 94171124739076192261257677)
  ·
    refine ⟨35314171777153572097971629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94171124739076192261257677 35314171777153572097971629)
    ·
      refine ⟨13242814416432589536739361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35314171777153572097971629 13242814416432589536739361)
      ·
        refine ⟨9932110812324442152554521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13242814416432589536739361 9932110812324442152554521)
        ·
          refine ⟨7449083109243331614415891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9932110812324442152554521 7449083109243331614415891)
          ·
            refine ⟨11173624663864997421623837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7449083109243331614415891 11173624663864997421623837)
            ·
              refine ⟨4190109248949374033108939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11173624663864997421623837 4190109248949374033108939)
              ·
                refine ⟨6285163873424061049663409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4190109248949374033108939 6285163873424061049663409)
                ·
                  refine ⟨4713872905068045787247557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6285163873424061049663409 4713872905068045787247557)
                  ·
                    refine ⟨883851169700258585108917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4713872905068045787247557 883851169700258585108917)
                    ·
                      rfl

theorem cell22_2581941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 3, 1, 2, 4].length) (baseStart_2581941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2581941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2581941 prefixEnd_2581941 := by exact prefixLift 2581941
  have htrace : WordTrace (prefixWord ++ tailWord_2581941) baseStart_2581941 baseEnd_2581941 := by
    simpa [prefixWord, tailWord_2581941, baseEnd_2581941] using wordTrace_append hprefix tailTrace_2581941
  have hstable : (prefixWord ++ tailWord_2581941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2581941).length < 2 ^ (prefixWord ++ tailWord_2581941).sum := by decide
  have hdescent : baseEnd_2581941 < baseStart_2581941 := by decide
  rcases family_descends (prefixWord ++ tailWord_2581941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2582048 : List Nat := [2, 1, 1, 6, 1, 1, 3, 2, 1, 4]
def baseStart_2582048 : Nat := 118140960795 + 2582048 * 2 ^ 59
def prefixEnd_2582048 : Nat := 4983230072969 + 3 ^ 40 * 2582048 * 2
def baseEnd_2582048 : Nat := 883887797986945972683589

theorem tailTrace_2582048 : CollatzResearch.WordTrace tailWord_2582048 prefixEnd_2582048 883887797986945972683589 := by
  unfold tailWord_2582048
  simp only [CollatzResearch.WordTrace]
  refine ⟨47087513674844274767701399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62783351566459033023601865 47087513674844274767701399)
  ·
    refine ⟨70631270512266412151552099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47087513674844274767701399 70631270512266412151552099)
    ·
      refine ⟨105946905768399618227328149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70631270512266412151552099 105946905768399618227328149)
      ·
        refine ⟨4966261207893732104406007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 105946905768399618227328149 4966261207893732104406007)
        ·
          refine ⟨7449391811840598156609011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4966261207893732104406007 7449391811840598156609011)
          ·
            refine ⟨11174087717760897234913517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7449391811840598156609011 11174087717760897234913517)
            ·
              refine ⟨4190282894160336463092569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11174087717760897234913517 4190282894160336463092569)
              ·
                refine ⟨3142712170620252347319427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4190282894160336463092569 3142712170620252347319427)
                ·
                  refine ⟨4714068255930378520979141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3142712170620252347319427 4714068255930378520979141)
                  ·
                    refine ⟨883887797986945972683589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4714068255930378520979141 883887797986945972683589)
                    ·
                      rfl

theorem cell22_2582048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 3, 2, 1, 4].length) (baseStart_2582048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2582048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2582048 prefixEnd_2582048 := by exact prefixLift 2582048
  have htrace : WordTrace (prefixWord ++ tailWord_2582048) baseStart_2582048 baseEnd_2582048 := by
    simpa [prefixWord, tailWord_2582048, baseEnd_2582048] using wordTrace_append hprefix tailTrace_2582048
  have hstable : (prefixWord ++ tailWord_2582048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2582048).length < 2 ^ (prefixWord ++ tailWord_2582048).sum := by decide
  have hdescent : baseEnd_2582048 < baseStart_2582048 := by decide
  rcases family_descends (prefixWord ++ tailWord_2582048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2582104 : List Nat := [2, 1, 2, 2, 1, 2, 1, 1, 4, 6]
def baseStart_2582104 : Nat := 118140960795 + 2582104 * 2 ^ 59
def prefixEnd_2582104 : Nat := 4983230072969 + 3 ^ 40 * 2582104 * 2
def baseEnd_2582104 : Nat := 883906967931380493283417

theorem tailTrace_2582104 : CollatzResearch.WordTrace tailWord_2582104 prefixEnd_2582104 883906967931380493283417 := by
  unfold tailWord_2582104
  simp only [CollatzResearch.WordTrace]
  refine ⟨47088534918742835549720683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62784713224990447399627577 47088534918742835549720683)
  ·
    refine ⟨70632802378114253324581025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47088534918742835549720683 70632802378114253324581025)
    ·
      refine ⟨52974601783585689993435769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70632802378114253324581025 52974601783585689993435769)
      ·
        refine ⟨39730951337689267495076827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52974601783585689993435769 39730951337689267495076827)
        ·
          refine ⟨59596427006533901242615241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39730951337689267495076827 59596427006533901242615241)
          ·
            refine ⟨44697320254900425931961431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59596427006533901242615241 44697320254900425931961431)
            ·
              refine ⟨67045980382350638897942147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44697320254900425931961431 67045980382350638897942147)
              ·
                refine ⟨100568970573525958346913221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67045980382350638897942147 100568970573525958346913221)
                ·
                  refine ⟨18856681982536117190046229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 100568970573525958346913221 18856681982536117190046229)
                  ·
                    refine ⟨883906967931380493283417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18856681982536117190046229 883906967931380493283417)
                    ·
                      rfl

theorem cell22_2582104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 4, 6].length) (baseStart_2582104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2582104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2582104 prefixEnd_2582104 := by exact prefixLift 2582104
  have htrace : WordTrace (prefixWord ++ tailWord_2582104) baseStart_2582104 baseEnd_2582104 := by
    simpa [prefixWord, tailWord_2582104, baseEnd_2582104] using wordTrace_append hprefix tailTrace_2582104
  have hstable : (prefixWord ++ tailWord_2582104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2582104).length < 2 ^ (prefixWord ++ tailWord_2582104).sum := by decide
  have hdescent : baseEnd_2582104 < baseStart_2582104 := by decide
  rcases family_descends (prefixWord ++ tailWord_2582104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2582108 : List Nat := [2, 2, 4, 1, 2, 2, 3, 6]
def baseStart_2582108 : Nat := 118140960795 + 2582108 * 2 ^ 59
def prefixEnd_2582108 : Nat := 4983230072969 + 3 ^ 40 * 2582108 * 2
def baseEnd_2582108 : Nat := 98212037468125090687045

theorem tailTrace_2582108 : CollatzResearch.WordTrace tailWord_2582108 prefixEnd_2582108 98212037468125090687045 := by
  unfold tailWord_2582108
  simp only [CollatzResearch.WordTrace]
  refine ⟨47088607864735589891293489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62784810486314119855057985 47088607864735589891293489)
  ·
    refine ⟨35316455898551692418470117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47088607864735589891293489 35316455898551692418470117)
    ·
      refine ⟨6621835480978442328463147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35316455898551692418470117 6621835480978442328463147)
      ·
        refine ⟨9932753221467663492694721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6621835480978442328463147 9932753221467663492694721)
        ·
          refine ⟨7449564916100747619521041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9932753221467663492694721 7449564916100747619521041)
          ·
            refine ⟨5587173687075560714640781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7449564916100747619521041 5587173687075560714640781)
            ·
              refine ⟨2095190132653335267990293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5587173687075560714640781 2095190132653335267990293)
              ·
                refine ⟨98212037468125090687045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2095190132653335267990293 98212037468125090687045)
                ·
                  rfl

theorem cell22_2582108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 3, 6].length) (baseStart_2582108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2582108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2582108 prefixEnd_2582108 := by exact prefixLift 2582108
  have htrace : WordTrace (prefixWord ++ tailWord_2582108) baseStart_2582108 baseEnd_2582108 := by
    simpa [prefixWord, tailWord_2582108, baseEnd_2582108] using wordTrace_append hprefix tailTrace_2582108
  have hstable : (prefixWord ++ tailWord_2582108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2582108).length < 2 ^ (prefixWord ++ tailWord_2582108).sum := by decide
  have hdescent : baseEnd_2582108 < baseStart_2582108 := by decide
  rcases family_descends (prefixWord ++ tailWord_2582108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2582151 : List Nat := [1, 1, 4, 2, 1, 3, 2, 1, 2, 5]
def baseStart_2582151 : Nat := 118140960795 + 2582151 * 2 ^ 59
def prefixEnd_2582151 : Nat := 4983230072969 + 3 ^ 40 * 2582151 * 2
def baseEnd_2582151 : Nat := 883923056991888037358273

theorem tailTrace_2582151 : CollatzResearch.WordTrace tailWord_2582151 prefixEnd_2582151 883923056991888037358273 := by
  unfold tailWord_2582151
  simp only [CollatzResearch.WordTrace]
  refine ⟨94178784068315398126402307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62785856045543598750934871 94178784068315398126402307)
  ·
    refine ⟨141268176102473097189603461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94178784068315398126402307 141268176102473097189603461)
    ·
      refine ⟨26487783019213705723050649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 141268176102473097189603461 26487783019213705723050649)
      ·
        refine ⟨19865837264410279292287987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26487783019213705723050649 19865837264410279292287987)
        ·
          refine ⟨29798755896615418938431981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19865837264410279292287987 29798755896615418938431981)
          ·
            refine ⟨11174533461230782101911993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29798755896615418938431981 11174533461230782101911993)
            ·
              refine ⟨8380900095923086576433995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11174533461230782101911993 8380900095923086576433995)
              ·
                refine ⟨12571350143884629864650993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8380900095923086576433995 12571350143884629864650993)
                ·
                  refine ⟨9428512607913472398488245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12571350143884629864650993 9428512607913472398488245)
                  ·
                    refine ⟨883923056991888037358273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9428512607913472398488245 883923056991888037358273)
                    ·
                      rfl

theorem cell22_2582151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 1, 2, 5].length) (baseStart_2582151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2582151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2582151 prefixEnd_2582151 := by exact prefixLift 2582151
  have htrace : WordTrace (prefixWord ++ tailWord_2582151) baseStart_2582151 baseEnd_2582151 := by
    simpa [prefixWord, tailWord_2582151, baseEnd_2582151] using wordTrace_append hprefix tailTrace_2582151
  have hstable : (prefixWord ++ tailWord_2582151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2582151).length < 2 ^ (prefixWord ++ tailWord_2582151).sum := by decide
  have hdescent : baseEnd_2582151 < baseStart_2582151 := by decide
  rcases family_descends (prefixWord ++ tailWord_2582151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2582174 : List Nat := [4, 3, 1, 1, 1, 4, 1, 3, 1, 3]
def baseStart_2582174 : Nat := 118140960795 + 2582174 * 2 ^ 59
def prefixEnd_2582174 : Nat := 4983230072969 + 3 ^ 40 * 2582174 * 2
def baseEnd_2582174 : Nat := 883930930361923644033203

theorem tailTrace_2582174 : CollatzResearch.WordTrace tailWord_2582174 prefixEnd_2582174 883930930361923644033203 := by
  unfold tailWord_2582174
  simp only [CollatzResearch.WordTrace]
  refine ⟨11772452868404009131811197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62786415298154715369659717 11772452868404009131811197)
  ·
    refine ⟨4414669825651503424429199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11772452868404009131811197 4414669825651503424429199)
    ·
      refine ⟨6622004738477255136643799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4414669825651503424429199 6622004738477255136643799)
      ·
        refine ⟨9933007107715882704965699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6622004738477255136643799 9933007107715882704965699)
        ·
          refine ⟨14899510661573824057448549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9933007107715882704965699 14899510661573824057448549)
          ·
            refine ⟨2793658249045092010771603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14899510661573824057448549 2793658249045092010771603)
            ·
              refine ⟨4190487373567638016157405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2793658249045092010771603 4190487373567638016157405)
              ·
                refine ⟨1571432765087864256059027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4190487373567638016157405 1571432765087864256059027)
                ·
                  refine ⟨2357149147631796384088541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1571432765087864256059027 2357149147631796384088541)
                  ·
                    refine ⟨883930930361923644033203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2357149147631796384088541 883930930361923644033203)
                    ·
                      rfl

theorem cell22_2582174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 1, 3, 1, 3].length) (baseStart_2582174 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2582174 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2582174 prefixEnd_2582174 := by exact prefixLift 2582174
  have htrace : WordTrace (prefixWord ++ tailWord_2582174) baseStart_2582174 baseEnd_2582174 := by
    simpa [prefixWord, tailWord_2582174, baseEnd_2582174] using wordTrace_append hprefix tailTrace_2582174
  have hstable : (prefixWord ++ tailWord_2582174).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2582174).length < 2 ^ (prefixWord ++ tailWord_2582174).sum := by decide
  have hdescent : baseEnd_2582174 < baseStart_2582174 := by decide
  rcases family_descends (prefixWord ++ tailWord_2582174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2582213 : List Nat := [1, 3, 1, 1, 1, 1, 2, 7, 2, 3]
def baseStart_2582213 : Nat := 118140960795 + 2582213 * 2 ^ 59
def prefixEnd_2582213 : Nat := 4983230072969 + 3 ^ 40 * 2582213 * 2
def baseEnd_2582213 : Nat := 883944280858940542308083

theorem tailTrace_2582213 : CollatzResearch.WordTrace tailWord_2582213 prefixEnd_2582213 883944280858940542308083 := by
  unfold tailWord_2582213
  simp only [CollatzResearch.WordTrace]
  refine ⟨94181045394090782715159293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62787363596060521810106195 94181045394090782715159293)
  ·
    refine ⟨35317892022784043518184735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94181045394090782715159293 35317892022784043518184735)
    ·
      refine ⟨52976838034176065277277103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35317892022784043518184735 52976838034176065277277103)
      ·
        refine ⟨79465257051264097915915655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52976838034176065277277103 79465257051264097915915655)
        ·
          refine ⟨119197885576896146873873483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79465257051264097915915655 119197885576896146873873483)
          ·
            refine ⟨178796828365344220310810225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119197885576896146873873483 178796828365344220310810225)
            ·
              refine ⟨134097621274008165233107669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 178796828365344220310810225 134097621274008165233107669)
              ·
                refine ⟨3142912998609566372650961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 134097621274008165233107669 3142912998609566372650961)
                ·
                  refine ⟨2357184748957174779488221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3142912998609566372650961 2357184748957174779488221)
                  ·
                    refine ⟨883944280858940542308083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2357184748957174779488221 883944280858940542308083)
                    ·
                      rfl

theorem cell22_2582213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 7, 2, 3].length) (baseStart_2582213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2582213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2582213 prefixEnd_2582213 := by exact prefixLift 2582213
  have htrace : WordTrace (prefixWord ++ tailWord_2582213) baseStart_2582213 baseEnd_2582213 := by
    simpa [prefixWord, tailWord_2582213, baseEnd_2582213] using wordTrace_append hprefix tailTrace_2582213
  have hstable : (prefixWord ++ tailWord_2582213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2582213).length < 2 ^ (prefixWord ++ tailWord_2582213).sum := by decide
  have hdescent : baseEnd_2582213 < baseStart_2582213 := by decide
  rcases family_descends (prefixWord ++ tailWord_2582213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2582243 : List Nat := [1, 1, 1, 7, 3, 9]
def baseStart_2582243 : Nat := 118140960795 + 2582243 * 2 ^ 59
def prefixEnd_2582243 : Nat := 4983230072969 + 3 ^ 40 * 2582243 * 2
def baseEnd_2582243 : Nat := 10913019141630005729111

theorem tailTrace_2582243 : CollatzResearch.WordTrace tailWord_2582243 prefixEnd_2582243 10913019141630005729111 := by
  unfold tailWord_2582243
  simp only [CollatzResearch.WordTrace]
  refine ⟨94182139583982097838751383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62788093055988065225834255 94182139583982097838751383)
  ·
    refine ⟨141273209375973146758127075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94182139583982097838751383 141273209375973146758127075)
    ·
      refine ⟨211909814063959720137190613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141273209375973146758127075 211909814063959720137190613)
      ·
        refine ⟨4966636267124055940715405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 211909814063959720137190613 4966636267124055940715405)
        ·
          refine ⟨1862488600171520977768277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4966636267124055940715405 1862488600171520977768277)
          ·
            refine ⟨10913019141630005729111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1862488600171520977768277 10913019141630005729111)
            ·
              rfl

theorem cell22_2582243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 9].length) (baseStart_2582243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2582243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2582243 prefixEnd_2582243 := by exact prefixLift 2582243
  have htrace : WordTrace (prefixWord ++ tailWord_2582243) baseStart_2582243 baseEnd_2582243 := by
    simpa [prefixWord, tailWord_2582243, baseEnd_2582243] using wordTrace_append hprefix tailTrace_2582243
  have hstable : (prefixWord ++ tailWord_2582243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2582243).length < 2 ^ (prefixWord ++ tailWord_2582243).sum := by decide
  have hdescent : baseEnd_2582243 < baseStart_2582243 := by decide
  rcases family_descends (prefixWord ++ tailWord_2582243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2582285 : List Nat := [1, 7, 2, 1, 2, 1, 2, 1, 1, 4]
def baseStart_2582285 : Nat := 118140960795 + 2582285 * 2 ^ 59
def prefixEnd_2582285 : Nat := 4983230072969 + 3 ^ 40 * 2582285 * 2
def baseEnd_2582285 : Nat := 883968927930356354507863

theorem tailTrace_2582285 : CollatzResearch.WordTrace tailWord_2582285 prefixEnd_2582285 883968927930356354507863 := by
  unfold tailWord_2582285
  simp only [CollatzResearch.WordTrace]
  refine ⟨94183671449829939011780309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62789114299886626007853539 94183671449829939011780309)
  ·
    refine ⟨2207429799605389195588601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 94183671449829939011780309 2207429799605389195588601)
    ·
      refine ⟨1655572349704041896691451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2207429799605389195588601 1655572349704041896691451)
      ·
        refine ⟨2483358524556062845037177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1655572349704041896691451 2483358524556062845037177)
        ·
          refine ⟨1862518893417047133777883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2483358524556062845037177 1862518893417047133777883)
          ·
            refine ⟨2793778340125570700666825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1862518893417047133777883 2793778340125570700666825)
            ·
              refine ⟨2095333755094178025500119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2793778340125570700666825 2095333755094178025500119)
              ·
                refine ⟨3143000632641267038250179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2095333755094178025500119 3143000632641267038250179)
                ·
                  refine ⟨4714500948961900557375269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3143000632641267038250179 4714500948961900557375269)
                  ·
                    refine ⟨883968927930356354507863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4714500948961900557375269 883968927930356354507863)
                    ·
                      rfl

theorem cell22_2582285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_2582285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2582285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2582285 prefixEnd_2582285 := by exact prefixLift 2582285
  have htrace : WordTrace (prefixWord ++ tailWord_2582285) baseStart_2582285 baseEnd_2582285 := by
    simpa [prefixWord, tailWord_2582285, baseEnd_2582285] using wordTrace_append hprefix tailTrace_2582285
  have hstable : (prefixWord ++ tailWord_2582285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2582285).length < 2 ^ (prefixWord ++ tailWord_2582285).sum := by decide
  have hdescent : baseEnd_2582285 < baseStart_2582285 := by decide
  rcases family_descends (prefixWord ++ tailWord_2582285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2582305 : List Nat := [1, 2, 3, 2, 1, 5, 1, 2, 5]
def baseStart_2582305 : Nat := 118140960795 + 2582305 * 2 ^ 59
def prefixEnd_2582305 : Nat := 4983230072969 + 3 ^ 40 * 2582305 * 2
def baseEnd_2582305 : Nat := 294658591446360989669267

theorem tailTrace_2582305 : CollatzResearch.WordTrace tailWord_2582305 prefixEnd_2582305 294658591446360989669267 := by
  unfold tailWord_2582305
  simp only [CollatzResearch.WordTrace]
  refine ⟨94184400909757482427508369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62789600606504988285005579 94184400909757482427508369)
  ·
    refine ⟨70638300682318111820631277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94184400909757482427508369 70638300682318111820631277)
    ·
      refine ⟨26489362755869291932736729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70638300682318111820631277 26489362755869291932736729)
      ·
        refine ⟨19867022066901968949552547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26489362755869291932736729 19867022066901968949552547)
        ·
          refine ⟨29800533100352953424328821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19867022066901968949552547 29800533100352953424328821)
          ·
            refine ⟨2793799978158089383530827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29800533100352953424328821 2793799978158089383530827)
            ·
              refine ⟨4190699967237134075296241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2793799978158089383530827 4190699967237134075296241)
              ·
                refine ⟨3143024975427850556472181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4190699967237134075296241 3143024975427850556472181)
                ·
                  refine ⟨294658591446360989669267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3143024975427850556472181 294658591446360989669267)
                  ·
                    rfl

theorem cell22_2582305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 1, 2, 5].length) (baseStart_2582305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2582305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2582305 prefixEnd_2582305 := by exact prefixLift 2582305
  have htrace : WordTrace (prefixWord ++ tailWord_2582305) baseStart_2582305 baseEnd_2582305 := by
    simpa [prefixWord, tailWord_2582305, baseEnd_2582305] using wordTrace_append hprefix tailTrace_2582305
  have hstable : (prefixWord ++ tailWord_2582305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2582305).length < 2 ^ (prefixWord ++ tailWord_2582305).sum := by decide
  have hdescent : baseEnd_2582305 < baseStart_2582305 := by decide
  rcases family_descends (prefixWord ++ tailWord_2582305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2582367 : List Nat := [1, 1, 2, 3, 1, 5, 3, 2, 4]
def baseStart_2582367 : Nat := 118140960795 + 2582367 * 2 ^ 59
def prefixEnd_2582367 : Nat := 4983230072969 + 3 ^ 40 * 2582367 * 2
def baseEnd_2582367 : Nat := 294665666068711824652537

theorem tailTrace_2582367 : CollatzResearch.WordTrace tailWord_2582367 prefixEnd_2582367 294665666068711824652537 := by
  unfold tailWord_2582367
  simp only [CollatzResearch.WordTrace]
  refine ⟨94186662235532867016265355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62791108157021911344176903 94186662235532867016265355)
  ·
    refine ⟨141279993353299300524398033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94186662235532867016265355 141279993353299300524398033)
    ·
      refine ⟨105959995014974475393298525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141279993353299300524398033 105959995014974475393298525)
      ·
        refine ⟨39734998130615428272486947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105959995014974475393298525 39734998130615428272486947)
        ·
          refine ⟨59602497195923142408730421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39734998130615428272486947 59602497195923142408730421)
          ·
            refine ⟨5587734112117794600818477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 59602497195923142408730421 5587734112117794600818477)
            ·
              refine ⟨2095400292044172975306929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5587734112117794600818477 2095400292044172975306929)
              ·
                refine ⟨1571550219033129731480197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2095400292044172975306929 1571550219033129731480197)
                ·
                  refine ⟨294665666068711824652537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1571550219033129731480197 294665666068711824652537)
                  ·
                    rfl

theorem cell22_2582367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 3, 2, 4].length) (baseStart_2582367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2582367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2582367 prefixEnd_2582367 := by exact prefixLift 2582367
  have htrace : WordTrace (prefixWord ++ tailWord_2582367) baseStart_2582367 baseEnd_2582367 := by
    simpa [prefixWord, tailWord_2582367, baseEnd_2582367] using wordTrace_append hprefix tailTrace_2582367
  have hstable : (prefixWord ++ tailWord_2582367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2582367).length < 2 ^ (prefixWord ++ tailWord_2582367).sum := by decide
  have hdescent : baseEnd_2582367 < baseStart_2582367 := by decide
  rcases family_descends (prefixWord ++ tailWord_2582367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2582446 : List Nat := [4, 1, 5, 1, 1, 1, 3, 6]
def baseStart_2582446 : Nat := 118140960795 + 2582446 * 2 ^ 59
def prefixEnd_2582446 : Nat := 4983230072969 + 3 ^ 40 * 2582446 * 2
def baseEnd_2582446 : Nat := 98224893502289511248041

theorem tailTrace_2582446 : CollatzResearch.WordTrace tailWord_2582446 prefixEnd_2582446 98224893502289511248041 := by
  unfold tailWord_2582446
  simp only [CollatzResearch.WordTrace]
  refine ⟨11773692950280832938548899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62793029068164442338927461 11773692950280832938548899)
  ·
    refine ⟨17660539425421249407823349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11773692950280832938548899 17660539425421249407823349)
    ·
      refine ⟨1655675571133242131983439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17660539425421249407823349 1655675571133242131983439)
      ·
        refine ⟨2483513356699863197975159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1655675571133242131983439 2483513356699863197975159)
        ·
          refine ⟨3725270035049794796962739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2483513356699863197975159 3725270035049794796962739)
          ·
            refine ⟨5587905052574692195444109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3725270035049794796962739 5587905052574692195444109)
            ·
              refine ⟨2095464394715509573291541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5587905052574692195444109 2095464394715509573291541)
              ·
                refine ⟨98224893502289511248041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2095464394715509573291541 98224893502289511248041)
                ·
                  rfl

theorem cell22_2582446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 3, 6].length) (baseStart_2582446 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2582446 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2582446 prefixEnd_2582446 := by exact prefixLift 2582446
  have htrace : WordTrace (prefixWord ++ tailWord_2582446) baseStart_2582446 baseEnd_2582446 := by
    simpa [prefixWord, tailWord_2582446, baseEnd_2582446] using wordTrace_append hprefix tailTrace_2582446
  have hstable : (prefixWord ++ tailWord_2582446).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2582446).length < 2 ^ (prefixWord ++ tailWord_2582446).sum := by decide
  have hdescent : baseEnd_2582446 < baseStart_2582446 := by decide
  rcases family_descends (prefixWord ++ tailWord_2582446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2582485 : List Nat := [1, 3, 2, 3, 2, 1, 1, 3, 6]
def baseStart_2582485 : Nat := 118140960795 + 2582485 * 2 ^ 59
def prefixEnd_2582485 : Nat := 4983230072969 + 3 ^ 40 * 2582485 * 2
def baseEnd_2582485 : Nat := 294679130672540833169083

theorem tailTrace_2582485 : CollatzResearch.WordTrace tailWord_2582485 prefixEnd_2582485 294679130672540833169083 := by
  unfold tailWord_2582485
  simp only [CollatzResearch.WordTrace]
  refine ⟨94190966049105373169060909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62793977366070248779373939 94190966049105373169060909)
  ·
    refine ⟨35321612268414514938397841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94190966049105373169060909 35321612268414514938397841)
    ·
      refine ⟨26491209201310886203798381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35321612268414514938397841 26491209201310886203798381)
      ·
        refine ⟨9934203450491582326424393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26491209201310886203798381 9934203450491582326424393)
        ·
          refine ⟨7450652587868686744818295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9934203450491582326424393 7450652587868686744818295)
          ·
            refine ⟨11175978881803030117227443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7450652587868686744818295 11175978881803030117227443)
            ·
              refine ⟨16763968322704545175841165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11175978881803030117227443 16763968322704545175841165)
              ·
                refine ⟨6286488121014204440940437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16763968322704545175841165 6286488121014204440940437)
                ·
                  refine ⟨294679130672540833169083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6286488121014204440940437 294679130672540833169083)
                  ·
                    rfl

theorem cell22_2582485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 3, 6].length) (baseStart_2582485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2582485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2582485 prefixEnd_2582485 := by exact prefixLift 2582485
  have htrace : WordTrace (prefixWord ++ tailWord_2582485) baseStart_2582485 baseEnd_2582485 := by
    simpa [prefixWord, tailWord_2582485, baseEnd_2582485] using wordTrace_append hprefix tailTrace_2582485
  have hstable : (prefixWord ++ tailWord_2582485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2582485).length < 2 ^ (prefixWord ++ tailWord_2582485).sum := by decide
  have hdescent : baseEnd_2582485 < baseStart_2582485 := by decide
  rcases family_descends (prefixWord ++ tailWord_2582485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2582562 : List Nat := [3, 3, 1, 1, 1, 2, 2, 1, 5, 3]
def baseStart_2582562 : Nat := 118140960795 + 2582562 * 2 ^ 59
def prefixEnd_2582562 : Nat := 4983230072969 + 3 ^ 40 * 2582562 * 2
def baseEnd_2582562 : Nat := 884063750691219965332013

theorem tailTrace_2582562 : CollatzResearch.WordTrace tailWord_2582562 prefixEnd_2582562 884063750691219965332013 := by
  unfold tailWord_2582562
  simp only [CollatzResearch.WordTrace]
  refine ⟨23548443617456603829903485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62795849646550943546409293 23548443617456603829903485)
  ·
    refine ⟨8830666356546226436213807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23548443617456603829903485 8830666356546226436213807)
    ·
      refine ⟨13245999534819339654320711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8830666356546226436213807 13245999534819339654320711)
      ·
        refine ⟨19868999302229009481481067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13245999534819339654320711 19868999302229009481481067)
        ·
          refine ⟨29803498953343514222221601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19868999302229009481481067 29803498953343514222221601)
          ·
            refine ⟨22352624215007635666666201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29803498953343514222221601 22352624215007635666666201)
            ·
              refine ⟨16764468161255726749999651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22352624215007635666666201 16764468161255726749999651)
              ·
                refine ⟨25146702241883590124999477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16764468161255726749999651 25146702241883590124999477)
                ·
                  refine ⟨2357503335176586574218701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25146702241883590124999477 2357503335176586574218701)
                  ·
                    refine ⟨884063750691219965332013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2357503335176586574218701 884063750691219965332013)
                    ·
                      rfl

theorem cell22_2582562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 1, 5, 3].length) (baseStart_2582562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2582562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2582562 prefixEnd_2582562 := by exact prefixLift 2582562
  have htrace : WordTrace (prefixWord ++ tailWord_2582562) baseStart_2582562 baseEnd_2582562 := by
    simpa [prefixWord, tailWord_2582562, baseEnd_2582562] using wordTrace_append hprefix tailTrace_2582562
  have hstable : (prefixWord ++ tailWord_2582562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2582562).length < 2 ^ (prefixWord ++ tailWord_2582562).sum := by decide
  have hdescent : baseEnd_2582562 < baseStart_2582562 := by decide
  rcases family_descends (prefixWord ++ tailWord_2582562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2582592 : List Nat := [2, 1, 1, 2, 2, 5, 2, 2, 5]
def baseStart_2582592 : Nat := 118140960795 + 2582592 * 2 ^ 59
def prefixEnd_2582592 : Nat := 4983230072969 + 3 ^ 40 * 2582592 * 2
def baseEnd_2582592 : Nat := 294691340101436629027307

theorem tailTrace_2582592 : CollatzResearch.WordTrace tailWord_2582592 prefixEnd_2582592 294691340101436629027307 := by
  unfold tailWord_2582592
  simp only [CollatzResearch.WordTrace]
  refine ⟨47097434329858865221603015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62796579106478486962137353 47097434329858865221603015)
  ·
    refine ⟨70646151494788297832404523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47097434329858865221603015 70646151494788297832404523)
    ·
      refine ⟨105969227242182446748606785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70646151494788297832404523 105969227242182446748606785)
      ·
        refine ⟨79476920431636835061455089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105969227242182446748606785 79476920431636835061455089)
        ·
          refine ⟨59607690323727626296091317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79476920431636835061455089 59607690323727626296091317)
          ·
            refine ⟨5588220967849464965258561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 59607690323727626296091317 5588220967849464965258561)
            ·
              refine ⟨4191165725887098723943921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5588220967849464965258561 4191165725887098723943921)
              ·
                refine ⟨3143374294415324042957941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4191165725887098723943921 3143374294415324042957941)
                ·
                  refine ⟨294691340101436629027307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3143374294415324042957941 294691340101436629027307)
                  ·
                    rfl

theorem cell22_2582592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 2, 2, 5].length) (baseStart_2582592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2582592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2582592 prefixEnd_2582592 := by exact prefixLift 2582592
  have htrace : WordTrace (prefixWord ++ tailWord_2582592) baseStart_2582592 baseEnd_2582592 := by
    simpa [prefixWord, tailWord_2582592, baseEnd_2582592] using wordTrace_append hprefix tailTrace_2582592
  have hstable : (prefixWord ++ tailWord_2582592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2582592).length < 2 ^ (prefixWord ++ tailWord_2582592).sum := by decide
  have hdescent : baseEnd_2582592 < baseStart_2582592 := by decide
  rcases family_descends (prefixWord ++ tailWord_2582592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2582639 : List Nat := [1, 1, 2, 1, 3, 4, 4, 1, 1, 4]
def baseStart_2582639 : Nat := 118140960795 + 2582639 * 2 ^ 59
def prefixEnd_2582639 : Nat := 4983230072969 + 3 ^ 40 * 2582639 * 2
def baseEnd_2582639 : Nat := 884090109364817431156777

theorem tailTrace_2582639 : CollatzResearch.WordTrace tailWord_2582639 prefixEnd_2582639 884090109364817431156777 := by
  unfold tailWord_2582639
  simp only [CollatzResearch.WordTrace]
  refine ⟨94196582890547457470166971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62797721927031638313444647 94196582890547457470166971)
  ·
    refine ⟨141294874335821186205250457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94196582890547457470166971 141294874335821186205250457)
    ·
      refine ⟨105971155751865889653937843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141294874335821186205250457 105971155751865889653937843)
      ·
        refine ⟨158956733627798834480906765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105971155751865889653937843 158956733627798834480906765)
        ·
          refine ⟨59608775110424562930340037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 158956733627798834480906765 59608775110424562930340037)
          ·
            refine ⟨11176645333204605549438757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59608775110424562930340037 11176645333204605549438757)
            ·
              refine ⟨2095620999975863540519767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11176645333204605549438757 2095620999975863540519767)
              ·
                refine ⟨3143431499963795310779651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2095620999975863540519767 3143431499963795310779651)
                ·
                  refine ⟨4715147249945692966169477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3143431499963795310779651 4715147249945692966169477)
                  ·
                    refine ⟨884090109364817431156777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4715147249945692966169477 884090109364817431156777)
                    ·
                      rfl

theorem cell22_2582639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 4, 1, 1, 4].length) (baseStart_2582639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2582639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2582639 prefixEnd_2582639 := by exact prefixLift 2582639
  have htrace : WordTrace (prefixWord ++ tailWord_2582639) baseStart_2582639 baseEnd_2582639 := by
    simpa [prefixWord, tailWord_2582639, baseEnd_2582639] using wordTrace_append hprefix tailTrace_2582639
  have hstable : (prefixWord ++ tailWord_2582639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2582639).length < 2 ^ (prefixWord ++ tailWord_2582639).sum := by decide
  have hdescent : baseEnd_2582639 < baseStart_2582639 := by decide
  rcases family_descends (prefixWord ++ tailWord_2582639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2582665 : List Nat := [1, 2, 1, 1, 4, 2, 2, 9]
def baseStart_2582665 : Nat := 118140960795 + 2582665 * 2 ^ 59
def prefixEnd_2582665 : Nat := 4983230072969 + 3 ^ 40 * 2582665 * 2
def baseEnd_2582665 : Nat := 98233223299573558889633

theorem tailTrace_2582665 : CollatzResearch.WordTrace tailWord_2582665 prefixEnd_2582665 98233223299573558889633 := by
  unfold tailWord_2582665
  simp only [CollatzResearch.WordTrace]
  refine ⟨94197531188453263910613449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62798354125635509273742299 94197531188453263910613449)
  ·
    refine ⟨70648148391339947932960087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94197531188453263910613449 70648148391339947932960087)
    ·
      refine ⟨105972222587009921899440131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70648148391339947932960087 105972222587009921899440131)
      ·
        refine ⟨158958333880514882849160197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105972222587009921899440131 158958333880514882849160197)
        ·
          refine ⟨29804687602596540534217537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 158958333880514882849160197 29804687602596540534217537)
          ·
            refine ⟨22353515701947405400663153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29804687602596540534217537 22353515701947405400663153)
            ·
              refine ⟨16765136776460554050497365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22353515701947405400663153 16765136776460554050497365)
              ·
                refine ⟨98233223299573558889633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16765136776460554050497365 98233223299573558889633)
                ·
                  rfl

theorem cell22_2582665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 9].length) (baseStart_2582665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2582665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2582665 prefixEnd_2582665 := by exact prefixLift 2582665
  have htrace : WordTrace (prefixWord ++ tailWord_2582665) baseStart_2582665 baseEnd_2582665 := by
    simpa [prefixWord, tailWord_2582665, baseEnd_2582665] using wordTrace_append hprefix tailTrace_2582665
  have hstable : (prefixWord ++ tailWord_2582665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2582665).length < 2 ^ (prefixWord ++ tailWord_2582665).sum := by decide
  have hdescent : baseEnd_2582665 < baseStart_2582665 := by decide
  rcases family_descends (prefixWord ++ tailWord_2582665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2582714 : List Nat := [3, 1, 1, 1, 2, 2, 5, 1, 3, 3]
def baseStart_2582714 : Nat := 118140960795 + 2582714 * 2 ^ 59
def prefixEnd_2582714 : Nat := 4983230072969 + 3 ^ 40 * 2582714 * 2
def baseEnd_2582714 : Nat := 884115783397542235531547

theorem tailTrace_2582714 : CollatzResearch.WordTrace tailWord_2582714 prefixEnd_2582714 884115783397542235531547 := by
  unfold tailWord_2582714
  simp only [CollatzResearch.WordTrace]
  refine ⟨23549829591318936319786799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62799545576850496852764797 23549829591318936319786799)
  ·
    refine ⟨35324744386978404479680199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23549829591318936319786799 35324744386978404479680199)
    ·
      refine ⟨52987116580467606719520299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35324744386978404479680199 52987116580467606719520299)
      ·
        refine ⟨79480674870701410079280449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52987116580467606719520299 79480674870701410079280449)
        ·
          refine ⟨59610506153026057559460337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79480674870701410079280449 59610506153026057559460337)
          ·
            refine ⟨44707879614769543169595253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59610506153026057559460337 44707879614769543169595253)
            ·
              refine ⟨4191363713884644672149555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44707879614769543169595253 4191363713884644672149555)
              ·
                refine ⟨6287045570826967008224333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4191363713884644672149555 6287045570826967008224333)
                ·
                  refine ⟨2357642089060112628084125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6287045570826967008224333 2357642089060112628084125)
                  ·
                    refine ⟨884115783397542235531547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2357642089060112628084125 884115783397542235531547)
                    ·
                      rfl

theorem cell22_2582714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 5, 1, 3, 3].length) (baseStart_2582714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2582714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2582714 prefixEnd_2582714 := by exact prefixLift 2582714
  have htrace : WordTrace (prefixWord ++ tailWord_2582714) baseStart_2582714 baseEnd_2582714 := by
    simpa [prefixWord, tailWord_2582714, baseEnd_2582714] using wordTrace_append hprefix tailTrace_2582714
  have hstable : (prefixWord ++ tailWord_2582714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2582714).length < 2 ^ (prefixWord ++ tailWord_2582714).sum := by decide
  have hdescent : baseEnd_2582714 < baseStart_2582714 := by decide
  rcases family_descends (prefixWord ++ tailWord_2582714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2582774 : List Nat := [5, 1, 1, 1, 1, 1, 3, 2, 3, 4]
def baseStart_2582774 : Nat := 118140960795 + 2582774 * 2 ^ 59
def prefixEnd_2582774 : Nat := 4983230072969 + 3 ^ 40 * 2582774 * 2
def baseEnd_2582774 : Nat := 884136322623722079031363

theorem tailTrace_2582774 : CollatzResearch.WordTrace tailWord_2582774 prefixEnd_2582774 884136322623722079031363 := by
  unfold tailWord_2582774
  simp only [CollatzResearch.WordTrace]
  refine ⟨5887594171566148470395711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 62801004496705583684220917 5887594171566148470395711)
  ·
    refine ⟨8831391257349222705593567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5887594171566148470395711 8831391257349222705593567)
    ·
      refine ⟨13247086886023834058390351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8831391257349222705593567 13247086886023834058390351)
      ·
        refine ⟨19870630329035751087585527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13247086886023834058390351 19870630329035751087585527)
        ·
          refine ⟨29805945493553626631378291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19870630329035751087585527 29805945493553626631378291)
          ·
            refine ⟨44708918240330439947067437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29805945493553626631378291 44708918240330439947067437)
            ·
              refine ⟨16765844340123914980150289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44708918240330439947067437 16765844340123914980150289)
              ·
                refine ⟨12574383255092936235112717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16765844340123914980150289 12574383255092936235112717)
                ·
                  refine ⟨4715393720659851088167269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12574383255092936235112717 4715393720659851088167269)
                  ·
                    refine ⟨884136322623722079031363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4715393720659851088167269 884136322623722079031363)
                    ·
                      rfl

theorem cell22_2582774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 2, 3, 4].length) (baseStart_2582774 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2582774 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2582774 prefixEnd_2582774 := by exact prefixLift 2582774
  have htrace : WordTrace (prefixWord ++ tailWord_2582774) baseStart_2582774 baseEnd_2582774 := by
    simpa [prefixWord, tailWord_2582774, baseEnd_2582774] using wordTrace_append hprefix tailTrace_2582774
  have hstable : (prefixWord ++ tailWord_2582774).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2582774).length < 2 ^ (prefixWord ++ tailWord_2582774).sum := by decide
  have hdescent : baseEnd_2582774 < baseStart_2582774 := by decide
  rcases family_descends (prefixWord ++ tailWord_2582774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2582821 : List Nat := [1, 3, 1, 2, 5, 1, 1, 1, 4, 3]
def baseStart_2582821 : Nat := 118140960795 + 2582821 * 2 ^ 59
def prefixEnd_2582821 : Nat := 4983230072969 + 3 ^ 40 * 2582821 * 2
def baseEnd_2582821 : Nat := 884152411684229623106219

theorem tailTrace_2582821 : CollatzResearch.WordTrace tailWord_2582821 prefixEnd_2582821 884152411684229623106219 := by
  unfold tailWord_2582821
  simp only [CollatzResearch.WordTrace]
  refine ⟨94203220975888102553292317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62802147317258735035528211 94203220975888102553292317)
  ·
    refine ⟨35326207865958038457484619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94203220975888102553292317 35326207865958038457484619)
    ·
      refine ⟨52989311798937057686226929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35326207865958038457484619 52989311798937057686226929)
      ·
        refine ⟨39741983849202793264670197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52989311798937057686226929 39741983849202793264670197)
        ·
          refine ⟨3725810985862761868562831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 39741983849202793264670197 3725810985862761868562831)
          ·
            refine ⟨5588716478794142802844247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3725810985862761868562831 5588716478794142802844247)
            ·
              refine ⟨8383074718191214204266371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5588716478794142802844247 8383074718191214204266371)
              ·
                refine ⟨12574612077286821306399557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8383074718191214204266371 12574612077286821306399557)
                ·
                  refine ⟨2357739764491278994949917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12574612077286821306399557 2357739764491278994949917)
                  ·
                    refine ⟨884152411684229623106219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2357739764491278994949917 884152411684229623106219)
                    ·
                      rfl

theorem cell22_2582821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 1, 4, 3].length) (baseStart_2582821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2582821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2582821 prefixEnd_2582821 := by exact prefixLift 2582821
  have htrace : WordTrace (prefixWord ++ tailWord_2582821) baseStart_2582821 baseEnd_2582821 := by
    simpa [prefixWord, tailWord_2582821, baseEnd_2582821] using wordTrace_append hprefix tailTrace_2582821
  have hstable : (prefixWord ++ tailWord_2582821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2582821).length < 2 ^ (prefixWord ++ tailWord_2582821).sum := by decide
  have hdescent : baseEnd_2582821 < baseStart_2582821 := by decide
  rcases family_descends (prefixWord ++ tailWord_2582821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2582896 : List Nat := [2, 1, 1, 1, 4, 3, 4, 1, 5]
def baseStart_2582896 : Nat := 118140960795 + 2582896 * 2 ^ 59
def prefixEnd_2582896 : Nat := 4983230072969 + 3 ^ 40 * 2582896 * 2
def baseEnd_2582896 : Nat := 294726028572318142493663

theorem tailTrace_2582896 : CollatzResearch.WordTrace tailWord_2582896 prefixEnd_2582896 294726028572318142493663 := by
  unfold tailWord_2582896
  simp only [CollatzResearch.WordTrace]
  refine ⟨47102978225308195181136271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62803970967077593574848361 47102978225308195181136271)
  ·
    refine ⟨70654467337962292771704407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47102978225308195181136271 70654467337962292771704407)
    ·
      refine ⟨105981701006943439157556611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70654467337962292771704407 105981701006943439157556611)
      ·
        refine ⟨158972551510415158736334917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105981701006943439157556611 158972551510415158736334917)
        ·
          refine ⟨29807353408202842263062797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 158972551510415158736334917 29807353408202842263062797)
          ·
            refine ⟨11177757528076065848648549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29807353408202842263062797 11177757528076065848648549)
            ·
              refine ⟨2095829536514262346621603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11177757528076065848648549 2095829536514262346621603)
              ·
                refine ⟨3143744304771393519932405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2095829536514262346621603 3143744304771393519932405)
                ·
                  refine ⟨294726028572318142493663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3143744304771393519932405 294726028572318142493663)
                  ·
                    rfl

theorem cell22_2582896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 4, 1, 5].length) (baseStart_2582896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2582896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2582896 prefixEnd_2582896 := by exact prefixLift 2582896
  have htrace : WordTrace (prefixWord ++ tailWord_2582896) baseStart_2582896 baseEnd_2582896 := by
    simpa [prefixWord, tailWord_2582896, baseEnd_2582896] using wordTrace_append hprefix tailTrace_2582896
  have hstable : (prefixWord ++ tailWord_2582896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2582896).length < 2 ^ (prefixWord ++ tailWord_2582896).sum := by decide
  have hdescent : baseEnd_2582896 < baseStart_2582896 := by decide
  rcases family_descends (prefixWord ++ tailWord_2582896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2582977 : List Nat := [1, 2, 7, 1, 1, 1, 1, 3, 1, 4]
def baseStart_2582977 : Nat := 118140960795 + 2582977 * 2 ^ 59
def prefixEnd_2582977 : Nat := 4983230072969 + 3 ^ 40 * 2582977 * 2
def baseEnd_2582977 : Nat := 884205813672297216205741

theorem tailTrace_2582977 : CollatzResearch.WordTrace tailWord_2582977 prefixEnd_2582977 884205813672297216205741 := by
  unfold tailWord_2582977
  simp only [CollatzResearch.WordTrace]
  refine ⟨94208910763322941195971185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62805940508881960797314123 94208910763322941195971185)
  ·
    refine ⟨70656683072492205896978389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94208910763322941195971185 70656683072492205896978389)
    ·
      refine ⟨1656016009511536075710431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 70656683072492205896978389 1656016009511536075710431)
      ·
        refine ⟨2484024014267304113565647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1656016009511536075710431 2484024014267304113565647)
        ·
          refine ⟨3726036021400956170348471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2484024014267304113565647 3726036021400956170348471)
          ·
            refine ⟨5589054032101434255522707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3726036021400956170348471 5589054032101434255522707)
            ·
              refine ⟨8383581048152151383284061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5589054032101434255522707 8383581048152151383284061)
              ·
                refine ⟨3143842893057056768731523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8383581048152151383284061 3143842893057056768731523)
                ·
                  refine ⟨4715764339585585153097285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3143842893057056768731523 4715764339585585153097285)
                  ·
                    refine ⟨884205813672297216205741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4715764339585585153097285 884205813672297216205741)
                    ·
                      rfl

theorem cell22_2582977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_2582977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2582977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2582977 prefixEnd_2582977 := by exact prefixLift 2582977
  have htrace : WordTrace (prefixWord ++ tailWord_2582977) baseStart_2582977 baseEnd_2582977 := by
    simpa [prefixWord, tailWord_2582977, baseEnd_2582977] using wordTrace_append hprefix tailTrace_2582977
  have hstable : (prefixWord ++ tailWord_2582977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2582977).length < 2 ^ (prefixWord ++ tailWord_2582977).sum := by decide
  have hdescent : baseEnd_2582977 < baseStart_2582977 := by decide
  rcases family_descends (prefixWord ++ tailWord_2582977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2583018 : List Nat := [3, 1, 3, 1, 3, 1, 2, 2, 3, 3]
def baseStart_2583018 : Nat := 118140960795 + 2583018 * 2 ^ 59
def prefixEnd_2583018 : Nat := 4983230072969 + 3 ^ 40 * 2583018 * 2
def baseEnd_2583018 : Nat := 884219848810186775930615

theorem tailTrace_2583018 : CollatzResearch.WordTrace tailWord_2583018 prefixEnd_2583018 884219848810186775930615 := by
  unfold tailWord_2583018
  simp only [CollatzResearch.WordTrace]
  refine ⟨23552601539043601299553427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62806937437449603465475805 23552601539043601299553427)
  ·
    refine ⟨35328902308565401949330141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23552601539043601299553427 35328902308565401949330141)
    ·
      refine ⟨13248338365712025730998803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35328902308565401949330141 13248338365712025730998803)
      ·
        refine ⟨19872507548568038596498205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13248338365712025730998803 19872507548568038596498205)
        ·
          refine ⟨7452190330713014473686827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19872507548568038596498205 7452190330713014473686827)
          ·
            refine ⟨11178285496069521710530241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7452190330713014473686827 11178285496069521710530241)
            ·
              refine ⟨8383714122052141282897681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11178285496069521710530241 8383714122052141282897681)
              ·
                refine ⟨6287785591539105962173261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8383714122052141282897681 6287785591539105962173261)
                ·
                  refine ⟨2357919596827164735814973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6287785591539105962173261 2357919596827164735814973)
                  ·
                    refine ⟨884219848810186775930615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2357919596827164735814973 884219848810186775930615)
                    ·
                      rfl

theorem cell22_2583018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 2, 3, 3].length) (baseStart_2583018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2583018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2583018 prefixEnd_2583018 := by exact prefixLift 2583018
  have htrace : WordTrace (prefixWord ++ tailWord_2583018) baseStart_2583018 baseEnd_2583018 := by
    simpa [prefixWord, tailWord_2583018, baseEnd_2583018] using wordTrace_append hprefix tailTrace_2583018
  have hstable : (prefixWord ++ tailWord_2583018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2583018).length < 2 ^ (prefixWord ++ tailWord_2583018).sum := by decide
  have hdescent : baseEnd_2583018 < baseStart_2583018 := by decide
  rcases family_descends (prefixWord ++ tailWord_2583018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2583052 : List Nat := [2, 2, 1, 2, 4, 2, 3, 2, 1, 3]
def baseStart_2583052 : Nat := 118140960795 + 2583052 * 2 ^ 59
def prefixEnd_2583052 : Nat := 4983230072969 + 3 ^ 40 * 2583052 * 2
def baseEnd_2583052 : Nat := 884231487705022020580511

theorem tailTrace_2583052 : CollatzResearch.WordTrace tailWord_2583052 prefixEnd_2583052 884231487705022020580511 := by
  unfold tailWord_2583052
  simp only [CollatzResearch.WordTrace]
  refine ⟨47105823119025614502475705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62807764158700819336634273 47105823119025614502475705)
  ·
    refine ⟨35329367339269210876856779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47105823119025614502475705 35329367339269210876856779)
    ·
      refine ⟨52994051008903816315285169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35329367339269210876856779 52994051008903816315285169)
      ·
        refine ⟨39745538256677862236463877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52994051008903816315285169 39745538256677862236463877)
        ·
          refine ⟨7452288423127099169336977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39745538256677862236463877 7452288423127099169336977)
          ·
            refine ⟨5589216317345324377002733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7452288423127099169336977 5589216317345324377002733)
            ·
              refine ⟨2095956119004496641376025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5589216317345324377002733 2095956119004496641376025)
              ·
                refine ⟨1571967089253372481032019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2095956119004496641376025 1571967089253372481032019)
                ·
                  refine ⟨2357950633880058721548029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1571967089253372481032019 2357950633880058721548029)
                  ·
                    refine ⟨884231487705022020580511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2357950633880058721548029 884231487705022020580511)
                    ·
                      rfl

theorem cell22_2583052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 3, 2, 1, 3].length) (baseStart_2583052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2583052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2583052 prefixEnd_2583052 := by exact prefixLift 2583052
  have htrace : WordTrace (prefixWord ++ tailWord_2583052) baseStart_2583052 baseEnd_2583052 := by
    simpa [prefixWord, tailWord_2583052, baseEnd_2583052] using wordTrace_append hprefix tailTrace_2583052
  have hstable : (prefixWord ++ tailWord_2583052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2583052).length < 2 ^ (prefixWord ++ tailWord_2583052).sum := by decide
  have hdescent : baseEnd_2583052 < baseStart_2583052 := by decide
  rcases family_descends (prefixWord ++ tailWord_2583052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2583061 : List Nat := [1, 3, 2, 1, 3, 1, 2, 2, 3, 4]
def baseStart_2583061 : Nat := 118140960795 + 2583061 * 2 ^ 59
def prefixEnd_2583061 : Nat := 4983230072969 + 3 ^ 40 * 2583061 * 2
def baseEnd_2583061 : Nat := 884234568588948997105483

theorem tailTrace_2583061 : CollatzResearch.WordTrace tailWord_2583061 prefixEnd_2583061 884234568588948997105483 := by
  unfold tailWord_2583061
  simp only [CollatzResearch.WordTrace]
  refine ⟨94211974495018623542029037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62807982996679082361352691 94211974495018623542029037)
  ·
    refine ⟨35329490435631983828260889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94211974495018623542029037 35329490435631983828260889)
    ·
      refine ⟨26497117826723987871195667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35329490435631983828260889 26497117826723987871195667)
      ·
        refine ⟨39745676740085981806793501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26497117826723987871195667 39745676740085981806793501)
        ·
          refine ⟨14904628777532243177547563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39745676740085981806793501 14904628777532243177547563)
          ·
            refine ⟨22356943166298364766321345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14904628777532243177547563 22356943166298364766321345)
            ·
              refine ⟨16767707374723773574741009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22356943166298364766321345 16767707374723773574741009)
              ·
                refine ⟨12575780531042830181055757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16767707374723773574741009 12575780531042830181055757)
                ·
                  refine ⟨4715917699141061317895909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12575780531042830181055757 4715917699141061317895909)
                  ·
                    refine ⟨884234568588948997105483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4715917699141061317895909 884234568588948997105483)
                    ·
                      rfl

theorem cell22_2583061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 2, 3, 4].length) (baseStart_2583061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2583061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2583061 prefixEnd_2583061 := by exact prefixLift 2583061
  have htrace : WordTrace (prefixWord ++ tailWord_2583061) baseStart_2583061 baseEnd_2583061 := by
    simpa [prefixWord, tailWord_2583061, baseEnd_2583061] using wordTrace_append hprefix tailTrace_2583061
  have hstable : (prefixWord ++ tailWord_2583061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2583061).length < 2 ^ (prefixWord ++ tailWord_2583061).sum := by decide
  have hdescent : baseEnd_2583061 < baseStart_2583061 := by decide
  rcases family_descends (prefixWord ++ tailWord_2583061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2583091 : List Nat := [1, 1, 1, 2, 4, 2, 3, 2, 1, 5]
def baseStart_2583091 : Nat := 118140960795 + 2583091 * 2 ^ 59
def prefixEnd_2583091 : Nat := 4983230072969 + 3 ^ 40 * 2583091 * 2
def baseEnd_2583091 : Nat := 884244838202038918855391

theorem tailTrace_2583091 : CollatzResearch.WordTrace tailWord_2583091 prefixEnd_2583091 884244838202038918855391 := by
  unfold tailWord_2583091
  simp only [CollatzResearch.WordTrace]
  refine ⟨94213068684909938665621127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62808712456606625777080751 94213068684909938665621127)
  ·
    refine ⟨141319603027364907998431691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94213068684909938665621127 141319603027364907998431691)
    ·
      refine ⟨211979404541047361997647537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141319603027364907998431691 211979404541047361997647537)
      ·
        refine ⟨158984553405785521498235653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 211979404541047361997647537 158984553405785521498235653)
        ·
          refine ⟨29809603763584785280919185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 158984553405785521498235653 29809603763584785280919185)
          ·
            refine ⟨22357202822688588960689389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29809603763584785280919185 22357202822688588960689389)
            ·
              refine ⟨8383951058508220860258521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22357202822688588960689389 8383951058508220860258521)
              ·
                refine ⟨6287963293881165645193891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8383951058508220860258521 6287963293881165645193891)
                ·
                  refine ⟨9431944940821748467790837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6287963293881165645193891 9431944940821748467790837)
                  ·
                    refine ⟨884244838202038918855391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9431944940821748467790837 884244838202038918855391)
                    ·
                      rfl

theorem cell22_2583091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 2, 1, 5].length) (baseStart_2583091 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2583091 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2583091 prefixEnd_2583091 := by exact prefixLift 2583091
  have htrace : WordTrace (prefixWord ++ tailWord_2583091) baseStart_2583091 baseEnd_2583091 := by
    simpa [prefixWord, tailWord_2583091, baseEnd_2583091] using wordTrace_append hprefix tailTrace_2583091
  have hstable : (prefixWord ++ tailWord_2583091).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2583091).length < 2 ^ (prefixWord ++ tailWord_2583091).sum := by decide
  have hdescent : baseEnd_2583091 < baseStart_2583091 := by decide
  rcases family_descends (prefixWord ++ tailWord_2583091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2583093 : List Nat := [1, 3, 3, 1, 1, 2, 2, 5, 4]
def baseStart_2583093 : Nat := 118140960795 + 2583093 * 2 ^ 59
def prefixEnd_2583093 : Nat := 4983230072969 + 3 ^ 40 * 2583093 * 2
def baseEnd_2583093 : Nat := 294748507614303860101795

theorem tailTrace_2583093 : CollatzResearch.WordTrace tailWord_2583093 prefixEnd_2583093 294748507614303860101795 := by
  unfold tailWord_2583093
  simp only [CollatzResearch.WordTrace]
  refine ⟨94213141630902693007193933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62808761087268462004795955 94213141630902693007193933)
  ·
    refine ⟨35329928111588509877697725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94213141630902693007193933 35329928111588509877697725)
    ·
      refine ⟨13248723041845691204136647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35329928111588509877697725 13248723041845691204136647)
      ·
        refine ⟨19873084562768536806204971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13248723041845691204136647 19873084562768536806204971)
        ·
          refine ⟨29809626844152805209307457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19873084562768536806204971 29809626844152805209307457)
          ·
            refine ⟨22357220133114603906980593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29809626844152805209307457 22357220133114603906980593)
            ·
              refine ⟨16767915099835952930235445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22357220133114603906980593 16767915099835952930235445)
              ·
                refine ⟨1571992040609620587209573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16767915099835952930235445 1571992040609620587209573)
                ·
                  refine ⟨294748507614303860101795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1571992040609620587209573 294748507614303860101795)
                  ·
                    rfl

theorem cell22_2583093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 5, 4].length) (baseStart_2583093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2583093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2583093 prefixEnd_2583093 := by exact prefixLift 2583093
  have htrace : WordTrace (prefixWord ++ tailWord_2583093) baseStart_2583093 baseEnd_2583093 := by
    simpa [prefixWord, tailWord_2583093, baseEnd_2583093] using wordTrace_append hprefix tailTrace_2583093
  have hstable : (prefixWord ++ tailWord_2583093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2583093).length < 2 ^ (prefixWord ++ tailWord_2583093).sum := by decide
  have hdescent : baseEnd_2583093 < baseStart_2583093 := by decide
  rcases family_descends (prefixWord ++ tailWord_2583093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2583121 : List Nat := [1, 2, 2, 1, 3, 3, 3, 7]
def baseStart_2583121 : Nat := 118140960795 + 2583121 * 2 ^ 59
def prefixEnd_2583121 : Nat := 4983230072969 + 3 ^ 40 * 2583121 * 2
def baseEnd_2583121 : Nat := 98250567535014315622811

theorem tailTrace_2583121 : CollatzResearch.WordTrace tailWord_2583121 prefixEnd_2583121 98250567535014315622811 := by
  unfold tailWord_2583121
  simp only [CollatzResearch.WordTrace]
  refine ⟨94214162874801253789213217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62809441916534169192808811 94214162874801253789213217)
  ·
    refine ⟨70660622156100940341909913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94214162874801253789213217 70660622156100940341909913)
    ·
      refine ⟨52995466617075705256432435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70660622156100940341909913 52995466617075705256432435)
      ·
        refine ⟨79493199925613557884648653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52995466617075705256432435 79493199925613557884648653)
        ·
          refine ⟨29809949972105084206743245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79493199925613557884648653 29809949972105084206743245)
          ·
            refine ⟨11178731239539406577528717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29809949972105084206743245 11178731239539406577528717)
            ·
              refine ⟨4192024214827277466573269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11178731239539406577528717 4192024214827277466573269)
              ·
                refine ⟨98250567535014315622811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4192024214827277466573269 98250567535014315622811)
                ·
                  rfl

theorem cell22_2583121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 3, 7].length) (baseStart_2583121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2583121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2583121 prefixEnd_2583121 := by exact prefixLift 2583121
  have htrace : WordTrace (prefixWord ++ tailWord_2583121) baseStart_2583121 baseEnd_2583121 := by
    simpa [prefixWord, tailWord_2583121, baseEnd_2583121] using wordTrace_append hprefix tailTrace_2583121
  have hstable : (prefixWord ++ tailWord_2583121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2583121).length < 2 ^ (prefixWord ++ tailWord_2583121).sum := by decide
  have hdescent : baseEnd_2583121 < baseStart_2583121 := by decide
  rcases family_descends (prefixWord ++ tailWord_2583121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2583260 : List Nat := [2, 2, 5, 1, 1, 1, 1, 1, 3, 5]
def baseStart_2583260 : Nat := 118140960795 + 2583260 * 2 ^ 59
def prefixEnd_2583260 : Nat := 4983230072969 + 3 ^ 40 * 2583260 * 2
def baseEnd_2583260 : Nat := 884302690355778811379873

theorem tailTrace_2583260 : CollatzResearch.WordTrace tailWord_2583260 prefixEnd_2583260 884302690355778811379873 := by
  unfold tailWord_2583260
  simp only [CollatzResearch.WordTrace]
  refine ⟨47109616310648840264261617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62812821747531787019015489 47109616310648840264261617)
  ·
    refine ⟨35332212232986630198196213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47109616310648840264261617 35332212232986630198196213)
    ·
      refine ⟨3312394896842496581080895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 35332212232986630198196213 3312394896842496581080895)
      ·
        refine ⟨4968592345263744871621343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3312394896842496581080895 4968592345263744871621343)
        ·
          refine ⟨7452888517895617307432015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4968592345263744871621343 7452888517895617307432015)
          ·
            refine ⟨11179332776843425961148023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7452888517895617307432015 11179332776843425961148023)
            ·
              refine ⟨16768999165265138941722035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11179332776843425961148023 16768999165265138941722035)
              ·
                refine ⟨25153498747897708412583053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16768999165265138941722035 25153498747897708412583053)
                ·
                  refine ⟨9432562030461640654718645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25153498747897708412583053 9432562030461640654718645)
                  ·
                    refine ⟨884302690355778811379873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9432562030461640654718645 884302690355778811379873)
                    ·
                      rfl

theorem cell22_2583260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_2583260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2583260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2583260 prefixEnd_2583260 := by exact prefixLift 2583260
  have htrace : WordTrace (prefixWord ++ tailWord_2583260) baseStart_2583260 baseEnd_2583260 := by
    simpa [prefixWord, tailWord_2583260, baseEnd_2583260] using wordTrace_append hprefix tailTrace_2583260
  have hstable : (prefixWord ++ tailWord_2583260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2583260).length < 2 ^ (prefixWord ++ tailWord_2583260).sum := by decide
  have hdescent : baseEnd_2583260 < baseStart_2583260 := by decide
  rcases family_descends (prefixWord ++ tailWord_2583260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2583277 : List Nat := [1, 5, 1, 2, 1, 1, 4, 2, 2, 3]
def baseStart_2583277 : Nat := 118140960795 + 2583277 * 2 ^ 59
def prefixEnd_2583277 : Nat := 4983230072969 + 3 ^ 40 * 2583277 * 2
def baseEnd_2583277 : Nat := 884308509803196433704821

theorem tailTrace_2583277 : CollatzResearch.WordTrace tailWord_2583277 prefixEnd_2583277 884308509803196433704821 := by
  unfold tailWord_2583277
  simp only [CollatzResearch.WordTrace]
  refine ⟨94219852662236092431892085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62813235108157394954594723 94219852662236092431892085)
  ·
    refine ⟨8833111187084633665489883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 94219852662236092431892085 8833111187084633665489883)
    ·
      refine ⟨13249666780626950498234825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8833111187084633665489883 13249666780626950498234825)
      ·
        refine ⟨9937250085470212873676119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13249666780626950498234825 9937250085470212873676119)
        ·
          refine ⟨14905875128205319310514179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9937250085470212873676119 14905875128205319310514179)
          ·
            refine ⟨22358812692307978965771269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14905875128205319310514179 22358812692307978965771269)
            ·
              refine ⟨4192277379807746056082113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22358812692307978965771269 4192277379807746056082113)
              ·
                refine ⟨3144208034855809542061585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4192277379807746056082113 3144208034855809542061585)
                ·
                  refine ⟨2358156026141857156546189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3144208034855809542061585 2358156026141857156546189)
                  ·
                    refine ⟨884308509803196433704821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2358156026141857156546189 884308509803196433704821)
                    ·
                      rfl

theorem cell22_2583277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 4, 2, 2, 3].length) (baseStart_2583277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2583277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2583277 prefixEnd_2583277 := by exact prefixLift 2583277
  have htrace : WordTrace (prefixWord ++ tailWord_2583277) baseStart_2583277 baseEnd_2583277 := by
    simpa [prefixWord, tailWord_2583277, baseEnd_2583277] using wordTrace_append hprefix tailTrace_2583277
  have hstable : (prefixWord ++ tailWord_2583277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2583277).length < 2 ^ (prefixWord ++ tailWord_2583277).sum := by decide
  have hdescent : baseEnd_2583277 < baseStart_2583277 := by decide
  rcases family_descends (prefixWord ++ tailWord_2583277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2583333 : List Nat := [1, 3, 1, 2, 3, 1, 1, 1, 4, 5]
def baseStart_2583333 : Nat := 118140960795 + 2583333 * 2 ^ 59
def prefixEnd_2583333 : Nat := 4983230072969 + 3 ^ 40 * 2583333 * 2
def baseEnd_2583333 : Nat := 884327679747630954304649

theorem tailTrace_2583333 : CollatzResearch.WordTrace tailWord_2583333 prefixEnd_2583333 884327679747630954304649 := by
  unfold tailWord_2583333
  simp only [CollatzResearch.WordTrace]
  refine ⟨94221895150033213995930653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62814596766688809330620435 94221895150033213995930653)
  ·
    refine ⟨35333210681262455248473995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94221895150033213995930653 35333210681262455248473995)
    ·
      refine ⟨52999816021893682872710993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35333210681262455248473995 52999816021893682872710993)
      ·
        refine ⟨39749862016420262154533245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52999816021893682872710993 39749862016420262154533245)
        ·
          refine ⟨14906198256157598307949967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39749862016420262154533245 14906198256157598307949967)
          ·
            refine ⟨22359297384236397461924951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14906198256157598307949967 22359297384236397461924951)
            ·
              refine ⟨33538946076354596192887427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22359297384236397461924951 33538946076354596192887427)
              ·
                refine ⟨50308419114531894289331141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33538946076354596192887427 50308419114531894289331141)
                ·
                  refine ⟨9432828583974730179249589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50308419114531894289331141 9432828583974730179249589)
                  ·
                    refine ⟨884327679747630954304649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9432828583974730179249589 884327679747630954304649)
                    ·
                      rfl

theorem cell22_2583333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 4, 5].length) (baseStart_2583333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2583333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2583333 prefixEnd_2583333 := by exact prefixLift 2583333
  have htrace : WordTrace (prefixWord ++ tailWord_2583333) baseStart_2583333 baseEnd_2583333 := by
    simpa [prefixWord, tailWord_2583333, baseEnd_2583333] using wordTrace_append hprefix tailTrace_2583333
  have hstable : (prefixWord ++ tailWord_2583333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2583333).length < 2 ^ (prefixWord ++ tailWord_2583333).sum := by decide
  have hdescent : baseEnd_2583333 < baseStart_2583333 := by decide
  rcases family_descends (prefixWord ++ tailWord_2583333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2583363 : List Nat := [1, 1, 1, 3, 1, 4, 1, 4, 6]
def baseStart_2583363 : Nat := 118140960795 + 2583363 * 2 ^ 59
def prefixEnd_2583363 : Nat := 4983230072969 + 3 ^ 40 * 2583363 * 2
def baseEnd_2583363 : Nat := 294779316453573625351519

theorem tailTrace_2583363 : CollatzResearch.WordTrace tailWord_2583363 prefixEnd_2583363 294779316453573625351519 := by
  unfold tailWord_2583363
  simp only [CollatzResearch.WordTrace]
  refine ⟨94222989339924529119522743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62815326226616352746348495 94222989339924529119522743)
  ·
    refine ⟨141334484009886793679284115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94222989339924529119522743 141334484009886793679284115)
    ·
      refine ⟨212001726014830190518926173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141334484009886793679284115 212001726014830190518926173)
      ·
        refine ⟨79500647255561321444597315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 212001726014830190518926173 79500647255561321444597315)
        ·
          refine ⟨119250970883341982166895973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79500647255561321444597315 119250970883341982166895973)
          ·
            refine ⟨22359557040626621656292995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 119250970883341982166895973 22359557040626621656292995)
            ·
              refine ⟨33539335560939932484439493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22359557040626621656292995 33539335560939932484439493)
              ·
                refine ⟨6288625417676237340832405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33539335560939932484439493 6288625417676237340832405)
                ·
                  refine ⟨294779316453573625351519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6288625417676237340832405 294779316453573625351519)
                  ·
                    rfl

theorem cell22_2583363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 4, 6].length) (baseStart_2583363 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2583363 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2583363 prefixEnd_2583363 := by exact prefixLift 2583363
  have htrace : WordTrace (prefixWord ++ tailWord_2583363) baseStart_2583363 baseEnd_2583363 := by
    simpa [prefixWord, tailWord_2583363, baseEnd_2583363] using wordTrace_append hprefix tailTrace_2583363
  have hstable : (prefixWord ++ tailWord_2583363).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2583363).length < 2 ^ (prefixWord ++ tailWord_2583363).sum := by decide
  have hdescent : baseEnd_2583363 < baseStart_2583363 := by decide
  rcases family_descends (prefixWord ++ tailWord_2583363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2583373 : List Nat := [1, 6, 1, 2, 2, 2, 1, 3, 1, 3]
def baseStart_2583373 : Nat := 118140960795 + 2583373 * 2 ^ 59
def prefixEnd_2583373 : Nat := 4983230072969 + 3 ^ 40 * 2583373 * 2
def baseEnd_2583373 : Nat := 884341372565084183304527

theorem tailTrace_2583373 : CollatzResearch.WordTrace tailWord_2583373 prefixEnd_2583373 884341372565084183304527 := by
  unfold tailWord_2583373
  simp only [CollatzResearch.WordTrace]
  refine ⟨94223354069888300827386773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62815569379925533884924515 94223354069888300827386773)
  ·
    refine ⟨4416719722026014101283755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 94223354069888300827386773 4416719722026014101283755)
    ·
      refine ⟨6625079583039021151925633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4416719722026014101283755 6625079583039021151925633)
      ·
        refine ⟨4968809687279265863944225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6625079583039021151925633 4968809687279265863944225)
        ·
          refine ⟨3726607265459449397958169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4968809687279265863944225 3726607265459449397958169)
          ·
            refine ⟨2794955449094587048468627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3726607265459449397958169 2794955449094587048468627)
            ·
              refine ⟨4192433173641880572702941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2794955449094587048468627 4192433173641880572702941)
              ·
                refine ⟨1572162440115705214763603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4192433173641880572702941 1572162440115705214763603)
                ·
                  refine ⟨2358243660173557822145405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1572162440115705214763603 2358243660173557822145405)
                  ·
                    refine ⟨884341372565084183304527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2358243660173557822145405 884341372565084183304527)
                    ·
                      rfl

theorem cell22_2583373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 1, 3, 1, 3].length) (baseStart_2583373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2583373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2583373 prefixEnd_2583373 := by exact prefixLift 2583373
  have htrace : WordTrace (prefixWord ++ tailWord_2583373) baseStart_2583373 baseEnd_2583373 := by
    simpa [prefixWord, tailWord_2583373, baseEnd_2583373] using wordTrace_append hprefix tailTrace_2583373
  have hstable : (prefixWord ++ tailWord_2583373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2583373).length < 2 ^ (prefixWord ++ tailWord_2583373).sum := by decide
  have hdescent : baseEnd_2583373 < baseStart_2583373 := by decide
  rcases family_descends (prefixWord ++ tailWord_2583373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2583393 : List Nat := [1, 2, 3, 1, 1, 1, 2, 2, 3, 6]
def baseStart_2583393 : Nat := 118140960795 + 2583393 * 2 ^ 59
def prefixEnd_2583393 : Nat := 4983230072969 + 3 ^ 40 * 2583393 * 2
def baseEnd_2583393 : Nat := 884348218973810797804465

theorem tailTrace_2583393 : CollatzResearch.WordTrace tailWord_2583393 prefixEnd_2583393 884348218973810797804465 := by
  unfold tailWord_2583393
  simp only [CollatzResearch.WordTrace]
  refine ⟨94224083529815844243114833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62816055686543896162076555 94224083529815844243114833)
  ·
    refine ⟨70668062647361883182336125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94224083529815844243114833 70668062647361883182336125)
    ·
      refine ⟨26500523492760706193376047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70668062647361883182336125 26500523492760706193376047)
      ·
        refine ⟨39750785239141059290064071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26500523492760706193376047 39750785239141059290064071)
        ·
          refine ⟨59626177858711588935096107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39750785239141059290064071 59626177858711588935096107)
          ·
            refine ⟨89439266788067383402644161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59626177858711588935096107 89439266788067383402644161)
            ·
              refine ⟨67079450091050537551983121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89439266788067383402644161 67079450091050537551983121)
              ·
                refine ⟨50309587568287903163987341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67079450091050537551983121 50309587568287903163987341)
                ·
                  refine ⟨18866095338107963686495253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50309587568287903163987341 18866095338107963686495253)
                  ·
                    refine ⟨884348218973810797804465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18866095338107963686495253 884348218973810797804465)
                    ·
                      rfl

theorem cell22_2583393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 3, 6].length) (baseStart_2583393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2583393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2583393 prefixEnd_2583393 := by exact prefixLift 2583393
  have htrace : WordTrace (prefixWord ++ tailWord_2583393) baseStart_2583393 baseEnd_2583393 := by
    simpa [prefixWord, tailWord_2583393, baseEnd_2583393] using wordTrace_append hprefix tailTrace_2583393
  have hstable : (prefixWord ++ tailWord_2583393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2583393).length < 2 ^ (prefixWord ++ tailWord_2583393).sum := by decide
  have hdescent : baseEnd_2583393 < baseStart_2583393 := by decide
  rcases family_descends (prefixWord ++ tailWord_2583393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2583408 : List Nat := [2, 1, 1, 1, 4, 1, 3, 9]
def baseStart_2583408 : Nat := 118140960795 + 2583408 * 2 ^ 59
def prefixEnd_2583408 : Nat := 4983230072969 + 3 ^ 40 * 2583408 * 2
def baseEnd_2583408 : Nat := 98261483753372862075491

theorem tailTrace_2583408 : CollatzResearch.WordTrace tailWord_2583408 prefixEnd_2583408 98261483753372862075491 := by
  unfold tailWord_2583408
  simp only [CollatzResearch.WordTrace]
  refine ⟨47112315312380750902455439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62816420416507667869940585 47112315312380750902455439)
  ·
    refine ⟨70668472968571126353683159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47112315312380750902455439 70668472968571126353683159)
    ·
      refine ⟨106002709452856689530524739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70668472968571126353683159 106002709452856689530524739)
      ·
        refine ⟨159004064179285034295787109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106002709452856689530524739 159004064179285034295787109)
        ·
          refine ⟨29813262033615943930460083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 159004064179285034295787109 29813262033615943930460083)
          ·
            refine ⟨44719893050423915895690125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29813262033615943930460083 44719893050423915895690125)
            ·
              refine ⟨16769959893908968460883797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44719893050423915895690125 16769959893908968460883797)
              ·
                refine ⟨98261483753372862075491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16769959893908968460883797 98261483753372862075491)
                ·
                  rfl

theorem cell22_2583408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 9].length) (baseStart_2583408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2583408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2583408 prefixEnd_2583408 := by exact prefixLift 2583408
  have htrace : WordTrace (prefixWord ++ tailWord_2583408) baseStart_2583408 baseEnd_2583408 := by
    simpa [prefixWord, tailWord_2583408, baseEnd_2583408] using wordTrace_append hprefix tailTrace_2583408
  have hstable : (prefixWord ++ tailWord_2583408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2583408).length < 2 ^ (prefixWord ++ tailWord_2583408).sum := by decide
  have hdescent : baseEnd_2583408 < baseStart_2583408 := by decide
  rcases family_descends (prefixWord ++ tailWord_2583408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2583423 : List Nat := [1, 1, 2, 2, 1, 1, 4, 1, 2, 7]
def baseStart_2583423 : Nat := 118140960795 + 2583423 * 2 ^ 59
def prefixEnd_2583423 : Nat := 4983230072969 + 3 ^ 40 * 2583423 * 2
def baseEnd_2583423 : Nat := 884358488586900719554373

theorem tailTrace_2583423 : CollatzResearch.WordTrace tailWord_2583423 prefixEnd_2583423 884358488586900719554373 := by
  unfold tailWord_2583423
  simp only [CollatzResearch.WordTrace]
  refine ⟨94225177719707159366706923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62816785146471439577804615 94225177719707159366706923)
  ·
    refine ⟨141337766579560739050060385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94225177719707159366706923 141337766579560739050060385)
    ·
      refine ⟨106003324934670554287545289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141337766579560739050060385 106003324934670554287545289)
      ·
        refine ⟨79502493701002915715658967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106003324934670554287545289 79502493701002915715658967)
        ·
          refine ⟨119253740551504373573488451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79502493701002915715658967 119253740551504373573488451)
          ·
            refine ⟨178880610827256560360232677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119253740551504373573488451 178880610827256560360232677)
            ·
              refine ⟨33540114530110605067543627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 178880610827256560360232677 33540114530110605067543627)
              ·
                refine ⟨50310171795165907601315441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33540114530110605067543627 50310171795165907601315441)
                ·
                  refine ⟨37732628846374430700986581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50310171795165907601315441 37732628846374430700986581)
                  ·
                    refine ⟨884358488586900719554373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37732628846374430700986581 884358488586900719554373)
                    ·
                      rfl

theorem cell22_2583423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 2, 7].length) (baseStart_2583423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2583423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2583423 prefixEnd_2583423 := by exact prefixLift 2583423
  have htrace : WordTrace (prefixWord ++ tailWord_2583423) baseStart_2583423 baseEnd_2583423 := by
    simpa [prefixWord, tailWord_2583423, baseEnd_2583423] using wordTrace_append hprefix tailTrace_2583423
  have hstable : (prefixWord ++ tailWord_2583423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2583423).length < 2 ^ (prefixWord ++ tailWord_2583423).sum := by decide
  have hdescent : baseEnd_2583423 < baseStart_2583423 := by decide
  rcases family_descends (prefixWord ++ tailWord_2583423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2583442 : List Nat := [3, 2, 3, 2, 3, 9]
def baseStart_2583442 : Nat := 118140960795 + 2583442 * 2 ^ 59
def prefixEnd_2583442 : Nat := 4983230072969 + 3 ^ 40 * 2583442 * 2
def baseEnd_2583442 : Nat := 10918086329323345720115

theorem tailTrace_2583442 : CollatzResearch.WordTrace tailWord_2583442 prefixEnd_2583442 10918086329323345720115 := by
  unfold tailWord_2583442
  simp only [CollatzResearch.WordTrace]
  refine ⟨23556467676659581402912145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62817247137758883741099053 23556467676659581402912145)
  ·
    refine ⟨17667350757494686052184109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23556467676659581402912145 17667350757494686052184109)
    ·
      refine ⟨6625256534060507269569041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17667350757494686052184109 6625256534060507269569041)
      ·
        refine ⟨4968942400545380452176781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6625256534060507269569041 4968942400545380452176781)
        ·
          refine ⟨1863353400204517669566293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4968942400545380452176781 1863353400204517669566293)
          ·
            refine ⟨10918086329323345720115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1863353400204517669566293 10918086329323345720115)
            ·
              rfl

theorem cell22_2583442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 9].length) (baseStart_2583442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2583442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2583442 prefixEnd_2583442 := by exact prefixLift 2583442
  have htrace : WordTrace (prefixWord ++ tailWord_2583442) baseStart_2583442 baseEnd_2583442 := by
    simpa [prefixWord, tailWord_2583442, baseEnd_2583442] using wordTrace_append hprefix tailTrace_2583442
  have hstable : (prefixWord ++ tailWord_2583442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2583442).length < 2 ^ (prefixWord ++ tailWord_2583442).sum := by decide
  have hdescent : baseEnd_2583442 < baseStart_2583442 := by decide
  rcases family_descends (prefixWord ++ tailWord_2583442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2583455 : List Nat := [1, 1, 2, 5, 2, 1, 1, 1, 2, 6]
def baseStart_2583455 : Nat := 118140960795 + 2583455 * 2 ^ 59
def prefixEnd_2583455 : Nat := 4983230072969 + 3 ^ 40 * 2583455 * 2
def baseEnd_2583455 : Nat := 884369442840863302754275

theorem tailTrace_2583455 : CollatzResearch.WordTrace tailWord_2583455 prefixEnd_2583455 884369442840863302754275 := by
  unfold tailWord_2583455
  simp only [CollatzResearch.WordTrace]
  refine ⟨94226344855591228831871819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62817563237060819221247879 94226344855591228831871819)
  ·
    refine ⟨141339517283386843247807729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94226344855591228831871819 141339517283386843247807729)
    ·
      refine ⟨106004637962540132435855797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141339517283386843247807729 106004637962540132435855797)
      ·
        refine ⟨9937934808988137415861481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 106004637962540132435855797 9937934808988137415861481)
        ·
          refine ⟨7453451106741103061896111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9937934808988137415861481 7453451106741103061896111)
          ·
            refine ⟨11180176660111654592844167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7453451106741103061896111 11180176660111654592844167)
            ·
              refine ⟨16770264990167481889266251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11180176660111654592844167 16770264990167481889266251)
              ·
                refine ⟨25155397485251222833899377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16770264990167481889266251 25155397485251222833899377)
                ·
                  refine ⟨18866548113938417125424533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25155397485251222833899377 18866548113938417125424533)
                  ·
                    refine ⟨884369442840863302754275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18866548113938417125424533 884369442840863302754275)
                    ·
                      rfl

theorem cell22_2583455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 1, 2, 6].length) (baseStart_2583455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2583455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2583455 prefixEnd_2583455 := by exact prefixLift 2583455
  have htrace : WordTrace (prefixWord ++ tailWord_2583455) baseStart_2583455 baseEnd_2583455 := by
    simpa [prefixWord, tailWord_2583455, baseEnd_2583455] using wordTrace_append hprefix tailTrace_2583455
  have hstable : (prefixWord ++ tailWord_2583455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2583455).length < 2 ^ (prefixWord ++ tailWord_2583455).sum := by decide
  have hdescent : baseEnd_2583455 < baseStart_2583455 := by decide
  rcases family_descends (prefixWord ++ tailWord_2583455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2583545 : List Nat := [1, 2, 1, 3, 1, 3, 1, 3, 1, 6]
def baseStart_2583545 : Nat := 118140960795 + 2583545 * 2 ^ 59
def prefixEnd_2583545 : Nat := 4983230072969 + 3 ^ 40 * 2583545 * 2
def baseEnd_2583545 : Nat := 884400251680133068003999

theorem tailTrace_2583545 : CollatzResearch.WordTrace tailWord_2583545 prefixEnd_2583545 884400251680133068003999 := by
  unfold tailWord_2583545
  simp only [CollatzResearch.WordTrace]
  refine ⟨94229627425265174202648089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62819751616843449468432059 94229627425265174202648089)
  ·
    refine ⟨70672220568948880651986067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94229627425265174202648089 70672220568948880651986067)
    ·
      refine ⟨106008330853423320977979101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70672220568948880651986067 106008330853423320977979101)
      ·
        refine ⟨39753124070033745366742163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106008330853423320977979101 39753124070033745366742163)
        ·
          refine ⟨59629686105050618050113245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39753124070033745366742163 59629686105050618050113245)
          ·
            refine ⟨22361132289393981768792467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59629686105050618050113245 22361132289393981768792467)
            ·
              refine ⟨33541698434090972653188701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22361132289393981768792467 33541698434090972653188701)
              ·
                refine ⟨12578136912784114744945763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33541698434090972653188701 12578136912784114744945763)
                ·
                  refine ⟨18867205369176172117418645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12578136912784114744945763 18867205369176172117418645)
                  ·
                    refine ⟨884400251680133068003999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18867205369176172117418645 884400251680133068003999)
                    ·
                      rfl

theorem cell22_2583545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 3, 1, 6].length) (baseStart_2583545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2583545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2583545 prefixEnd_2583545 := by exact prefixLift 2583545
  have htrace : WordTrace (prefixWord ++ tailWord_2583545) baseStart_2583545 baseEnd_2583545 := by
    simpa [prefixWord, tailWord_2583545, baseEnd_2583545] using wordTrace_append hprefix tailTrace_2583545
  have hstable : (prefixWord ++ tailWord_2583545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2583545).length < 2 ^ (prefixWord ++ tailWord_2583545).sum := by decide
  have hdescent : baseEnd_2583545 < baseStart_2583545 := by decide
  rcases family_descends (prefixWord ++ tailWord_2583545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2583560 : List Nat := [2, 1, 3, 2, 1, 3, 10]
def baseStart_2583560 : Nat := 118140960795 + 2583560 * 2 ^ 59
def prefixEnd_2583560 : Nat := 4983230072969 + 3 ^ 40 * 2583560 * 2
def baseEnd_2583560 : Nat := 32755755055062149217739

theorem tailTrace_2583560 : CollatzResearch.WordTrace tailWord_2583560 prefixEnd_2583560 32755755055062149217739 := by
  unfold tailWord_2583560
  simp only [CollatzResearch.WordTrace]
  refine ⟨47115087260105415882222067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62820116346807221176296089 47115087260105415882222067)
  ·
    refine ⟨70672630890158123823333101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47115087260105415882222067 70672630890158123823333101)
    ·
      refine ⟨26502236583809296433749913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70672630890158123823333101 26502236583809296433749913)
      ·
        refine ⟨19876677437856972325312435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26502236583809296433749913 19876677437856972325312435)
        ·
          refine ⟨29815016156785458487968653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19876677437856972325312435 29815016156785458487968653)
          ·
            refine ⟨11180631058794546932988245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29815016156785458487968653 11180631058794546932988245)
            ·
              refine ⟨32755755055062149217739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 11180631058794546932988245 32755755055062149217739)
              ·
                rfl

theorem cell22_2583560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 10].length) (baseStart_2583560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2583560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2583560 prefixEnd_2583560 := by exact prefixLift 2583560
  have htrace : WordTrace (prefixWord ++ tailWord_2583560) baseStart_2583560 baseEnd_2583560 := by
    simpa [prefixWord, tailWord_2583560, baseEnd_2583560] using wordTrace_append hprefix tailTrace_2583560
  have hstable : (prefixWord ++ tailWord_2583560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2583560).length < 2 ^ (prefixWord ++ tailWord_2583560).sum := by decide
  have hdescent : baseEnd_2583560 < baseStart_2583560 := by decide
  rcases family_descends (prefixWord ++ tailWord_2583560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2583562 : List Nat := [3, 1, 2, 2, 3, 1, 1, 1, 4, 4]
def baseStart_2583562 : Nat := 118140960795 + 2583562 * 2 ^ 59
def prefixEnd_2583562 : Nat := 4983230072969 + 3 ^ 40 * 2583562 * 2
def baseEnd_2583562 : Nat := 884406071127550690328947

theorem tailTrace_2583562 : CollatzResearch.WordTrace tailWord_2583562 prefixEnd_2583562 884406071127550690328947 := by
  unfold tailWord_2583562
  simp only [CollatzResearch.WordTrace]
  refine ⟨23557561866550896526504235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62820164977469057404011293 23557561866550896526504235)
  ·
    refine ⟨35336342799826344789756353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23557561866550896526504235 35336342799826344789756353)
    ·
      refine ⟨26502257099869758592317265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35336342799826344789756353 26502257099869758592317265)
      ·
        refine ⟨19876692824902318944237949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26502257099869758592317265 19876692824902318944237949)
        ·
          refine ⟨7453759809338369604089231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19876692824902318944237949 7453759809338369604089231)
          ·
            refine ⟨11180639714007554406133847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7453759809338369604089231 11180639714007554406133847)
            ·
              refine ⟨16770959571011331609200771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11180639714007554406133847 16770959571011331609200771)
              ·
                refine ⟨25156439356516997413801157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16770959571011331609200771 25156439356516997413801157)
                ·
                  refine ⟨4716832379346937015087717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25156439356516997413801157 4716832379346937015087717)
                  ·
                    refine ⟨884406071127550690328947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4716832379346937015087717 884406071127550690328947)
                    ·
                      rfl

theorem cell22_2583562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 1, 4, 4].length) (baseStart_2583562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2583562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2583562 prefixEnd_2583562 := by exact prefixLift 2583562
  have htrace : WordTrace (prefixWord ++ tailWord_2583562) baseStart_2583562 baseEnd_2583562 := by
    simpa [prefixWord, tailWord_2583562, baseEnd_2583562] using wordTrace_append hprefix tailTrace_2583562
  have hstable : (prefixWord ++ tailWord_2583562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2583562).length < 2 ^ (prefixWord ++ tailWord_2583562).sum := by decide
  have hdescent : baseEnd_2583562 < baseStart_2583562 := by decide
  rcases family_descends (prefixWord ++ tailWord_2583562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2583566 : List Nat := [4, 1, 1, 2, 2, 3, 3, 2, 4]
def baseStart_2583566 : Nat := 118140960795 + 2583566 * 2 ^ 59
def prefixEnd_2583566 : Nat := 4983230072969 + 3 ^ 40 * 2583566 * 2
def baseEnd_2583566 : Nat := 294802480136432004409645

theorem tailTrace_2583566 : CollatzResearch.WordTrace tailWord_2583566 prefixEnd_2583566 294802480136432004409645 := by
  unfold tailWord_2583566
  simp only [CollatzResearch.WordTrace]
  refine ⟨11778799169773636848645319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62820262238792729859441701 11778799169773636848645319)
  ·
    refine ⟨17668198754660455272967979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11778799169773636848645319 17668198754660455272967979)
    ·
      refine ⟨26502298131990682909451969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17668198754660455272967979 26502298131990682909451969)
      ·
        refine ⟨19876723598993012182088977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26502298131990682909451969 19876723598993012182088977)
        ·
          refine ⟨14907542699244759136566733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19876723598993012182088977 14907542699244759136566733)
          ·
            refine ⟨5590328512216784676212525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14907542699244759136566733 5590328512216784676212525)
            ·
              refine ⟨2096373192081294253579697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5590328512216784676212525 2096373192081294253579697)
              ·
                refine ⟨1572279894060970690184773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2096373192081294253579697 1572279894060970690184773)
                ·
                  refine ⟨294802480136432004409645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1572279894060970690184773 294802480136432004409645)
                  ·
                    rfl

theorem cell22_2583566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 3, 2, 4].length) (baseStart_2583566 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2583566 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2583566 prefixEnd_2583566 := by exact prefixLift 2583566
  have htrace : WordTrace (prefixWord ++ tailWord_2583566) baseStart_2583566 baseEnd_2583566 := by
    simpa [prefixWord, tailWord_2583566, baseEnd_2583566] using wordTrace_append hprefix tailTrace_2583566
  have hstable : (prefixWord ++ tailWord_2583566).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2583566).length < 2 ^ (prefixWord ++ tailWord_2583566).sum := by decide
  have hdescent : baseEnd_2583566 < baseStart_2583566 := by decide
  rcases family_descends (prefixWord ++ tailWord_2583566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2583581 : List Nat := [1, 4, 2, 2, 3, 1, 1, 3, 2, 3]
def baseStart_2583581 : Nat := 118140960795 + 2583581 * 2 ^ 59
def prefixEnd_2583581 : Nat := 4983230072969 + 3 ^ 40 * 2583581 * 2
def baseEnd_2583581 : Nat := 884412575215840974103889

theorem tailTrace_2583581 : CollatzResearch.WordTrace tailWord_2583581 prefixEnd_2583581 884412575215840974103889 := by
  unfold tailWord_2583581
  simp only [CollatzResearch.WordTrace]
  refine ⟨94230940453134752350958597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62820626968756501567305731 94230940453134752350958597)
  ·
    refine ⟨17668301334962766065804737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94230940453134752350958597 17668301334962766065804737)
    ·
      refine ⟨13251226001222074549353553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17668301334962766065804737 13251226001222074549353553)
      ·
        refine ⟨9938419500916555912015165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13251226001222074549353553 9938419500916555912015165)
        ·
          refine ⟨3726907312843708467005687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9938419500916555912015165 3726907312843708467005687)
          ·
            refine ⟨5590360969265562700508531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3726907312843708467005687 5590360969265562700508531)
            ·
              refine ⟨8385541453898344050762797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5590360969265562700508531 8385541453898344050762797)
              ·
                refine ⟨3144578045211879019036049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8385541453898344050762797 3144578045211879019036049)
                ·
                  refine ⟨2358433533908909264277037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3144578045211879019036049 2358433533908909264277037)
                  ·
                    refine ⟨884412575215840974103889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2358433533908909264277037 884412575215840974103889)
                    ·
                      rfl

theorem cell22_2583581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 3, 2, 3].length) (baseStart_2583581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2583581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2583581 prefixEnd_2583581 := by exact prefixLift 2583581
  have htrace : WordTrace (prefixWord ++ tailWord_2583581) baseStart_2583581 baseEnd_2583581 := by
    simpa [prefixWord, tailWord_2583581, baseEnd_2583581] using wordTrace_append hprefix tailTrace_2583581
  have hstable : (prefixWord ++ tailWord_2583581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2583581).length < 2 ^ (prefixWord ++ tailWord_2583581).sum := by decide
  have hdescent : baseEnd_2583581 < baseStart_2583581 := by decide
  rcases family_descends (prefixWord ++ tailWord_2583581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2583635 : List Nat := [1, 1, 1, 2, 1, 1, 2, 3, 2, 8]
def baseStart_2583635 : Nat := 118140960795 + 2583635 * 2 ^ 59
def prefixEnd_2583635 : Nat := 4983230072969 + 3 ^ 40 * 2583635 * 2
def baseEnd_2583635 : Nat := 884431060519402833253723

theorem tailTrace_2583635 : CollatzResearch.WordTrace tailWord_2583635 prefixEnd_2583635 884431060519402833253723 := by
  unfold tailWord_2583635
  simp only [CollatzResearch.WordTrace]
  refine ⟨94232909994939119573424359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62821939996626079715616239 94232909994939119573424359)
  ·
    refine ⟨141349364992408679360136539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94232909994939119573424359 141349364992408679360136539)
    ·
      refine ⟨212024047488613019040204809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141349364992408679360136539 212024047488613019040204809)
      ·
        refine ⟨159018035616459764280153607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 212024047488613019040204809 159018035616459764280153607)
        ·
          refine ⟨238527053424689646420230411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159018035616459764280153607 238527053424689646420230411)
          ·
            refine ⟨357790580137034469630345617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 238527053424689646420230411 357790580137034469630345617)
            ·
              refine ⟨268342935102775852222759213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 357790580137034469630345617 268342935102775852222759213)
              ·
                refine ⟨100628600663540944583534705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 268342935102775852222759213 100628600663540944583534705)
                ·
                  refine ⟨75471450497655708437651029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 100628600663540944583534705 75471450497655708437651029)
                  ·
                    refine ⟨884431060519402833253723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 75471450497655708437651029 884431060519402833253723)
                    ·
                      rfl

theorem cell22_2583635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 8].length) (baseStart_2583635 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2583635 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2583635 prefixEnd_2583635 := by exact prefixLift 2583635
  have htrace : WordTrace (prefixWord ++ tailWord_2583635) baseStart_2583635 baseEnd_2583635 := by
    simpa [prefixWord, tailWord_2583635, baseEnd_2583635] using wordTrace_append hprefix tailTrace_2583635
  have hstable : (prefixWord ++ tailWord_2583635).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2583635).length < 2 ^ (prefixWord ++ tailWord_2583635).sum := by decide
  have hdescent : baseEnd_2583635 < baseStart_2583635 := by decide
  rcases family_descends (prefixWord ++ tailWord_2583635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2583637 : List Nat := [1, 3, 2, 2, 1, 2, 3, 1, 2, 5]
def baseStart_2583637 : Nat := 118140960795 + 2583637 * 2 ^ 59
def prefixEnd_2583637 : Nat := 4983230072969 + 3 ^ 40 * 2583637 * 2
def baseEnd_2583637 : Nat := 884431745160275494703717

theorem tailTrace_2583637 : CollatzResearch.WordTrace tailWord_2583637 prefixEnd_2583637 884431745160275494703717 := by
  unfold tailWord_2583637
  simp only [CollatzResearch.WordTrace]
  refine ⟨94232982940931873914997165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62821988627287915943331443 94232982940931873914997165)
  ·
    refine ⟨35337368602849452718123937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94232982940931873914997165 35337368602849452718123937)
    ·
      refine ⟨26503026452137089538592953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35337368602849452718123937 26503026452137089538592953)
      ·
        refine ⟨19877269839102817153944715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26503026452137089538592953 19877269839102817153944715)
        ·
          refine ⟨29815904758654225730917073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19877269839102817153944715 29815904758654225730917073)
          ·
            refine ⟨22361928568990669298187805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29815904758654225730917073 22361928568990669298187805)
            ·
              refine ⟨8385723213371500986820427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22361928568990669298187805 8385723213371500986820427)
              ·
                refine ⟨12578584820057251480230641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8385723213371500986820427 12578584820057251480230641)
                ·
                  refine ⟨9433938615042938610172981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12578584820057251480230641 9433938615042938610172981)
                  ·
                    refine ⟨884431745160275494703717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9433938615042938610172981 884431745160275494703717)
                    ·
                      rfl

theorem cell22_2583637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 1, 2, 5].length) (baseStart_2583637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2583637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2583637 prefixEnd_2583637 := by exact prefixLift 2583637
  have htrace : WordTrace (prefixWord ++ tailWord_2583637) baseStart_2583637 baseEnd_2583637 := by
    simpa [prefixWord, tailWord_2583637, baseEnd_2583637] using wordTrace_append hprefix tailTrace_2583637
  have hstable : (prefixWord ++ tailWord_2583637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2583637).length < 2 ^ (prefixWord ++ tailWord_2583637).sum := by decide
  have hdescent : baseEnd_2583637 < baseStart_2583637 := by decide
  rcases family_descends (prefixWord ++ tailWord_2583637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2583684 : List Nat := [2, 3, 2, 1, 2, 3, 2, 1, 6]
def baseStart_2583684 : Nat := 118140960795 + 2583684 * 2 ^ 59
def prefixEnd_2583684 : Nat := 4983230072969 + 3 ^ 40 * 2583684 * 2
def baseEnd_2583684 : Nat := 294815944740261012926191

theorem tailTrace_2583684 : CollatzResearch.WordTrace tailWord_2583684 prefixEnd_2583684 294815944740261012926191 := by
  unfold tailWord_2583684
  simp only [CollatzResearch.WordTrace]
  refine ⟨47117348585880800470979053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62823131447841067294638737 47117348585880800470979053)
  ·
    refine ⟨17669005719705300176617145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47117348585880800470979053 17669005719705300176617145)
    ·
      refine ⟨13251754289778975132462859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17669005719705300176617145 13251754289778975132462859)
      ·
        refine ⟨19877631434668462698694289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13251754289778975132462859 19877631434668462698694289)
        ·
          refine ⟨14908223576001347024020717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19877631434668462698694289 14908223576001347024020717)
          ·
            refine ⟨5590583841000505134007769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14908223576001347024020717 5590583841000505134007769)
            ·
              refine ⟨4192937880750378850505827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5590583841000505134007769 4192937880750378850505827)
              ·
                refine ⟨6289406821125568275758741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4192937880750378850505827 6289406821125568275758741)
                ·
                  refine ⟨294815944740261012926191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6289406821125568275758741 294815944740261012926191)
                  ·
                    rfl

theorem cell22_2583684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 2, 1, 6].length) (baseStart_2583684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2583684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2583684 prefixEnd_2583684 := by exact prefixLift 2583684
  have htrace : WordTrace (prefixWord ++ tailWord_2583684) baseStart_2583684 baseEnd_2583684 := by
    simpa [prefixWord, tailWord_2583684, baseEnd_2583684] using wordTrace_append hprefix tailTrace_2583684
  have hstable : (prefixWord ++ tailWord_2583684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2583684).length < 2 ^ (prefixWord ++ tailWord_2583684).sum := by decide
  have hdescent : baseEnd_2583684 < baseStart_2583684 := by decide
  rcases family_descends (prefixWord ++ tailWord_2583684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2583699 : List Nat := [1, 1, 1, 2, 1, 2, 4, 5, 2, 3]
def baseStart_2583699 : Nat := 118140960795 + 2583699 * 2 ^ 59
def prefixEnd_2583699 : Nat := 4983230072969 + 3 ^ 40 * 2583699 * 2
def baseEnd_2583699 : Nat := 884452969027327999653527

theorem tailTrace_2583699 : CollatzResearch.WordTrace tailWord_2583699 prefixEnd_2583699 884452969027327999653527 := by
  unfold tailWord_2583699
  simp only [CollatzResearch.WordTrace]
  refine ⟨94235244266707258503754151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62823496177804839002502767 94235244266707258503754151)
  ·
    refine ⟨141352866400060887755631227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94235244266707258503754151 141352866400060887755631227)
    ·
      refine ⟨212029299600091331633446841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141352866400060887755631227 212029299600091331633446841)
      ·
        refine ⟨159021974700068498725085131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 212029299600091331633446841 159021974700068498725085131)
        ·
          refine ⟨238532962050102748087627697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159021974700068498725085131 238532962050102748087627697)
          ·
            refine ⟨178899721537577061065720773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 238532962050102748087627697 178899721537577061065720773)
            ·
              refine ⟨33543697788295698949822645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 178899721537577061065720773 33543697788295698949822645)
              ·
                refine ⟨3144721667652721776545873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33543697788295698949822645 3144721667652721776545873)
                ·
                  refine ⟨2358541250739541332409405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3144721667652721776545873 2358541250739541332409405)
                  ·
                    refine ⟨884452969027327999653527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2358541250739541332409405 884452969027327999653527)
                    ·
                      rfl

theorem cell22_2583699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 5, 2, 3].length) (baseStart_2583699 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2583699 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2583699 prefixEnd_2583699 := by exact prefixLift 2583699
  have htrace : WordTrace (prefixWord ++ tailWord_2583699) baseStart_2583699 baseEnd_2583699 := by
    simpa [prefixWord, tailWord_2583699, baseEnd_2583699] using wordTrace_append hprefix tailTrace_2583699
  have hstable : (prefixWord ++ tailWord_2583699).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2583699).length < 2 ^ (prefixWord ++ tailWord_2583699).sum := by decide
  have hdescent : baseEnd_2583699 < baseStart_2583699 := by decide
  rcases family_descends (prefixWord ++ tailWord_2583699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2583712 : List Nat := [2, 1, 1, 4, 2, 1, 3, 8]
def baseStart_2583712 : Nat := 118140960795 + 2583712 * 2 ^ 59
def prefixEnd_2583712 : Nat := 4983230072969 + 3 ^ 40 * 2583712 * 2
def baseEnd_2583712 : Nat := 98273046577000033230943

theorem tailTrace_2583712 : CollatzResearch.WordTrace tailWord_2583712 prefixEnd_2583712 98273046577000033230943 := by
  unfold tailWord_2583712
  simp only [CollatzResearch.WordTrace]
  refine ⟨47117859207830080861988695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62823812277106774482651593 47117859207830080861988695)
  ·
    refine ⟨70676788811745121292983043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47117859207830080861988695 70676788811745121292983043)
    ·
      refine ⟨106015183217617681939474565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70676788811745121292983043 106015183217617681939474565)
      ·
        refine ⟨19877846853303315363651481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 106015183217617681939474565 19877846853303315363651481)
        ·
          refine ⟨14908385139977486522738611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19877846853303315363651481 14908385139977486522738611)
          ·
            refine ⟨22362577709966229784107917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14908385139977486522738611 22362577709966229784107917)
            ·
              refine ⟨8385966641237336169040469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22362577709966229784107917 8385966641237336169040469)
              ·
                refine ⟨98273046577000033230943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8385966641237336169040469 98273046577000033230943)
                ·
                  rfl

theorem cell22_2583712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 8].length) (baseStart_2583712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2583712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2583712 prefixEnd_2583712 := by exact prefixLift 2583712
  have htrace : WordTrace (prefixWord ++ tailWord_2583712) baseStart_2583712 baseEnd_2583712 := by
    simpa [prefixWord, tailWord_2583712, baseEnd_2583712] using wordTrace_append hprefix tailTrace_2583712
  have hstable : (prefixWord ++ tailWord_2583712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2583712).length < 2 ^ (prefixWord ++ tailWord_2583712).sum := by decide
  have hdescent : baseEnd_2583712 < baseStart_2583712 := by decide
  rcases family_descends (prefixWord ++ tailWord_2583712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2583729 : List Nat := [1, 2, 2, 5, 1, 3, 8]
def baseStart_2583729 : Nat := 118140960795 + 2583729 * 2 ^ 59
def prefixEnd_2583729 : Nat := 4983230072969 + 3 ^ 40 * 2583729 * 2
def baseEnd_2583729 : Nat := 32757897727422885977905

theorem tailTrace_2583729 : CollatzResearch.WordTrace tailWord_2583729 prefixEnd_2583729 32757897727422885977905 := by
  unfold tailWord_2583729
  simp only [CollatzResearch.WordTrace]
  refine ⟨94236338456598573627346241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62824225637732382418230827 94236338456598573627346241)
  ·
    refine ⟨70677253842448930220509681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94236338456598573627346241 70677253842448930220509681)
    ·
      refine ⟨53007940381836697665382261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70677253842448930220509681 53007940381836697665382261)
      ·
        refine ⟨4969494410797190406129587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 53007940381836697665382261 4969494410797190406129587)
        ·
          refine ⟨7454241616195785609194381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4969494410797190406129587 7454241616195785609194381)
          ·
            refine ⟨2795340606073419603447893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7454241616195785609194381 2795340606073419603447893)
            ·
              refine ⟨32757897727422885977905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2795340606073419603447893 32757897727422885977905)
              ·
                rfl

theorem cell22_2583729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 8].length) (baseStart_2583729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2583729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2583729 prefixEnd_2583729 := by exact prefixLift 2583729
  have htrace : WordTrace (prefixWord ++ tailWord_2583729) baseStart_2583729 baseEnd_2583729 := by
    simpa [prefixWord, tailWord_2583729, baseEnd_2583729] using wordTrace_append hprefix tailTrace_2583729
  have hstable : (prefixWord ++ tailWord_2583729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2583729).length < 2 ^ (prefixWord ++ tailWord_2583729).sum := by decide
  have hdescent : baseEnd_2583729 < baseStart_2583729 := by decide
  rcases family_descends (prefixWord ++ tailWord_2583729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2583791 : List Nat := [1, 1, 2, 1, 7, 1, 2, 2, 5]
def baseStart_2583791 : Nat := 118140960795 + 2583791 * 2 ^ 59
def prefixEnd_2583791 : Nat := 4983230072969 + 3 ^ 40 * 2583791 * 2
def baseEnd_2583791 : Nat := 294828154169156808784415

theorem tailTrace_2583791 : CollatzResearch.WordTrace tailWord_2583791 prefixEnd_2583791 294828154169156808784415 := by
  unfold tailWord_2583791
  simp only [CollatzResearch.WordTrace]
  refine ⟨94238599782373958216103227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62825733188249305477402151 94238599782373958216103227)
  ·
    refine ⟨141357899673560937324154841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94238599782373958216103227 141357899673560937324154841)
    ·
      refine ⟨106018424755170702993116131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141357899673560937324154841 106018424755170702993116131)
      ·
        refine ⟨159027637132756054489674197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106018424755170702993116131 159027637132756054489674197)
        ·
          refine ⟨3727210245298970027101739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 159027637132756054489674197 3727210245298970027101739)
          ·
            refine ⟨5590815367948455040652609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3727210245298970027101739 5590815367948455040652609)
            ·
              refine ⟨4193111525961341280489457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5590815367948455040652609 4193111525961341280489457)
              ·
                refine ⟨3144833644471005960367093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4193111525961341280489457 3144833644471005960367093)
                ·
                  refine ⟨294828154169156808784415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3144833644471005960367093 294828154169156808784415)
                  ·
                    rfl

theorem cell22_2583791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 2, 2, 5].length) (baseStart_2583791 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2583791 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2583791 prefixEnd_2583791 := by exact prefixLift 2583791
  have htrace : WordTrace (prefixWord ++ tailWord_2583791) baseStart_2583791 baseEnd_2583791 := by
    simpa [prefixWord, tailWord_2583791, baseEnd_2583791] using wordTrace_append hprefix tailTrace_2583791
  have hstable : (prefixWord ++ tailWord_2583791).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2583791).length < 2 ^ (prefixWord ++ tailWord_2583791).sum := by decide
  have hdescent : baseEnd_2583791 < baseStart_2583791 := by decide
  rcases family_descends (prefixWord ++ tailWord_2583791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2583795 : List Nat := [1, 1, 1, 2, 2, 7, 2, 2, 1, 3]
def baseStart_2583795 : Nat := 118140960795 + 2583795 * 2 ^ 59
def prefixEnd_2583795 : Nat := 4983230072969 + 3 ^ 40 * 2583795 * 2
def baseEnd_2583795 : Nat := 884485831789215749253233

theorem tailTrace_2583795 : CollatzResearch.WordTrace tailWord_2583795 prefixEnd_2583795 884485831789215749253233 := by
  unfold tailWord_2583795
  simp only [CollatzResearch.WordTrace]
  refine ⟨94238745674359466899248839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62825830449572977932832559 94238745674359466899248839)
  ·
    refine ⟨141358118511539200348873259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94238745674359466899248839 141358118511539200348873259)
    ·
      refine ⟨212037177767308800523309889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141358118511539200348873259 212037177767308800523309889)
      ·
        refine ⟨159027883325481600392482417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 212037177767308800523309889 159027883325481600392482417)
        ·
          refine ⟨119270912494111200294361813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 159027883325481600392482417 119270912494111200294361813)
          ·
            refine ⟨2795412011580731256899105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 119270912494111200294361813 2795412011580731256899105)
            ·
              refine ⟨2096559008685548442674329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2795412011580731256899105 2096559008685548442674329)
              ·
                refine ⟨1572419256514161332005747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2096559008685548442674329 1572419256514161332005747)
                ·
                  refine ⟨2358628884771241998008621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1572419256514161332005747 2358628884771241998008621)
                  ·
                    refine ⟨884485831789215749253233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2358628884771241998008621 884485831789215749253233)
                    ·
                      rfl

theorem cell22_2583795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 2, 2, 1, 3].length) (baseStart_2583795 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2583795 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2583795 prefixEnd_2583795 := by exact prefixLift 2583795
  have htrace : WordTrace (prefixWord ++ tailWord_2583795) baseStart_2583795 baseEnd_2583795 := by
    simpa [prefixWord, tailWord_2583795, baseEnd_2583795] using wordTrace_append hprefix tailTrace_2583795
  have hstable : (prefixWord ++ tailWord_2583795).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2583795).length < 2 ^ (prefixWord ++ tailWord_2583795).sum := by decide
  have hdescent : baseEnd_2583795 < baseStart_2583795 := by decide
  rcases family_descends (prefixWord ++ tailWord_2583795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2583806 : List Nat := [4, 2, 2, 1, 1, 3, 1, 1, 2, 5]
def baseStart_2583806 : Nat := 118140960795 + 2583806 * 2 ^ 59
def prefixEnd_2583806 : Nat := 4983230072969 + 3 ^ 40 * 2583806 * 2
def baseEnd_2583806 : Nat := 884489597314015387228199

theorem tailTrace_2583806 : CollatzResearch.WordTrace tailWord_2583806 prefixEnd_2583806 884489597314015387228199 := by
  unfold tailWord_2583806
  simp only [CollatzResearch.WordTrace]
  refine ⟨11779893359664951972237409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62826097918213077185266181 11779893359664951972237409)
  ·
    refine ⟨8834920019748713979178057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11779893359664951972237409 8834920019748713979178057)
    ·
      refine ⟨6626190014811535484383543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8834920019748713979178057 6626190014811535484383543)
      ·
        refine ⟨9939285022217303226575315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6626190014811535484383543 9939285022217303226575315)
        ·
          refine ⟨14908927533325954839862973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9939285022217303226575315 14908927533325954839862973)
          ·
            refine ⟨5590847824997233064948615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14908927533325954839862973 5590847824997233064948615)
            ·
              refine ⟨8386271737495849597422923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5590847824997233064948615 8386271737495849597422923)
              ·
                refine ⟨12579407606243774396134385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8386271737495849597422923 12579407606243774396134385)
                ·
                  refine ⟨9434555704682830797100789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12579407606243774396134385 9434555704682830797100789)
                  ·
                    refine ⟨884489597314015387228199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9434555704682830797100789 884489597314015387228199)
                    ·
                      rfl

theorem cell22_2583806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_2583806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2583806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2583806 prefixEnd_2583806 := by exact prefixLift 2583806
  have htrace : WordTrace (prefixWord ++ tailWord_2583806) baseStart_2583806 baseEnd_2583806 := by
    simpa [prefixWord, tailWord_2583806, baseEnd_2583806] using wordTrace_append hprefix tailTrace_2583806
  have hstable : (prefixWord ++ tailWord_2583806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2583806).length < 2 ^ (prefixWord ++ tailWord_2583806).sum := by decide
  have hdescent : baseEnd_2583806 < baseStart_2583806 := by decide
  rcases family_descends (prefixWord ++ tailWord_2583806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2583819 : List Nat := [1, 1, 1, 1, 5, 4, 1, 2, 6]
def baseStart_2583819 : Nat := 118140960795 + 2583819 * 2 ^ 59
def prefixEnd_2583819 : Nat := 4983230072969 + 3 ^ 40 * 2583819 * 2
def baseEnd_2583819 : Nat := 294831349159895895551053

theorem tailTrace_2583819 : CollatzResearch.WordTrace tailWord_2583819 prefixEnd_2583819 294831349159895895551053 := by
  unfold tailWord_2583819
  simp only [CollatzResearch.WordTrace]
  refine ⟨94239621026272518998122511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62826414017515012665415007 94239621026272518998122511)
  ·
    refine ⟨141359431539408778497183767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94239621026272518998122511 141359431539408778497183767)
    ·
      refine ⟨212039147309113167745775651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141359431539408778497183767 212039147309113167745775651)
      ·
        refine ⟨318058720963669751618663477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212039147309113167745775651 318058720963669751618663477)
        ·
          refine ⟨29818005090344039214249701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 318058720963669751618663477 29818005090344039214249701)
          ·
            refine ⟨5590875954439507352671819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29818005090344039214249701 5590875954439507352671819)
            ·
              refine ⟨8386313931659261029007729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5590875954439507352671819 8386313931659261029007729)
              ·
                refine ⟨6289735448744445771755797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8386313931659261029007729 6289735448744445771755797)
                ·
                  refine ⟨294831349159895895551053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6289735448744445771755797 294831349159895895551053)
                  ·
                    rfl

theorem cell22_2583819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 2, 6].length) (baseStart_2583819 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2583819 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2583819 prefixEnd_2583819 := by exact prefixLift 2583819
  have htrace : WordTrace (prefixWord ++ tailWord_2583819) baseStart_2583819 baseEnd_2583819 := by
    simpa [prefixWord, tailWord_2583819, baseEnd_2583819] using wordTrace_append hprefix tailTrace_2583819
  have hstable : (prefixWord ++ tailWord_2583819).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2583819).length < 2 ^ (prefixWord ++ tailWord_2583819).sum := by decide
  have hdescent : baseEnd_2583819 < baseStart_2583819 := by decide
  rcases family_descends (prefixWord ++ tailWord_2583819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2583836 : List Nat := [2, 2, 3, 1, 1, 1, 3, 5, 4]
def baseStart_2583836 : Nat := 118140960795 + 2583836 * 2 ^ 59
def prefixEnd_2583836 : Nat := 4983230072969 + 3 ^ 40 * 2583836 * 2
def baseEnd_2583836 : Nat := 294833288975701769659369

theorem tailTrace_2583836 : CollatzResearch.WordTrace tailWord_2583836 prefixEnd_2583836 294833288975701769659369 := by
  unfold tailWord_2583836
  simp only [CollatzResearch.WordTrace]
  refine ⟨47120120533605465450745681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62826827378140620600994241 47120120533605465450745681)
  ·
    refine ⟨35340090400204099088059261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47120120533605465450745681 35340090400204099088059261)
    ·
      refine ⟨13252533900076537158022223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35340090400204099088059261 13252533900076537158022223)
      ·
        refine ⟨19878800850114805737033335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13252533900076537158022223 19878800850114805737033335)
        ·
          refine ⟨29818201275172208605550003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19878800850114805737033335 29818201275172208605550003)
          ·
            refine ⟨44727301912758312908325005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29818201275172208605550003 44727301912758312908325005)
            ·
              refine ⟨16772738217284367340621877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44727301912758312908325005 16772738217284367340621877)
              ·
                refine ⟨1572444207870409438183301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16772738217284367340621877 1572444207870409438183301)
                ·
                  refine ⟨294833288975701769659369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1572444207870409438183301 294833288975701769659369)
                  ·
                    rfl

theorem cell22_2583836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 5, 4].length) (baseStart_2583836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2583836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2583836 prefixEnd_2583836 := by exact prefixLift 2583836
  have htrace : WordTrace (prefixWord ++ tailWord_2583836) baseStart_2583836 baseEnd_2583836 := by
    simpa [prefixWord, tailWord_2583836, baseEnd_2583836] using wordTrace_append hprefix tailTrace_2583836
  have hstable : (prefixWord ++ tailWord_2583836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2583836).length < 2 ^ (prefixWord ++ tailWord_2583836).sum := by decide
  have hdescent : baseEnd_2583836 < baseStart_2583836 := by decide
  rcases family_descends (prefixWord ++ tailWord_2583836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2583853 : List Nat := [1, 5, 3, 1, 1, 2, 2, 1, 6]
def baseStart_2583853 : Nat := 118140960795 + 2583853 * 2 ^ 59
def prefixEnd_2583853 : Nat := 4983230072969 + 3 ^ 40 * 2583853 * 2
def baseEnd_2583853 : Nat := 294835228791507643767685

theorem tailTrace_2583853 : CollatzResearch.WordTrace tailWord_2583853 prefixEnd_2583853 294835228791507643767685 := by
  unfold tailWord_2583853
  simp only [CollatzResearch.WordTrace]
  refine ⟨94240861108149342804860213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62827240738766228536573475 94240861108149342804860213)
  ·
    refine ⟨8835080728889000887955645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 94240861108149342804860213 8835080728889000887955645)
    ·
      refine ⟨3313155273333375332983367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8835080728889000887955645 3313155273333375332983367)
      ·
        refine ⟨4969732910000062999475051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3313155273333375332983367 4969732910000062999475051)
        ·
          refine ⟨7454599365000094499212577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4969732910000062999475051 7454599365000094499212577)
          ·
            refine ⟨5590949523750070874409433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7454599365000094499212577 5590949523750070874409433)
            ·
              refine ⟨4193212142812553155807075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5590949523750070874409433 4193212142812553155807075)
              ·
                refine ⟨6289818214218829733710613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4193212142812553155807075 6289818214218829733710613)
                ·
                  refine ⟨294835228791507643767685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6289818214218829733710613 294835228791507643767685)
                  ·
                    rfl

theorem cell22_2583853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 2, 1, 6].length) (baseStart_2583853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2583853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2583853 prefixEnd_2583853 := by exact prefixLift 2583853
  have htrace : WordTrace (prefixWord ++ tailWord_2583853) baseStart_2583853 baseEnd_2583853 := by
    simpa [prefixWord, tailWord_2583853, baseEnd_2583853] using wordTrace_append hprefix tailTrace_2583853
  have hstable : (prefixWord ++ tailWord_2583853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2583853).length < 2 ^ (prefixWord ++ tailWord_2583853).sum := by decide
  have hdescent : baseEnd_2583853 < baseStart_2583853 := by decide
  rcases family_descends (prefixWord ++ tailWord_2583853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2583909 : List Nat := [1, 3, 1, 3, 1, 2, 1, 3, 7]
def baseStart_2583909 : Nat := 118140960795 + 2583909 * 2 ^ 59
def prefixEnd_2583909 : Nat := 4983230072969 + 3 ^ 40 * 2583909 * 2
def baseEnd_2583909 : Nat := 294841618772985817300961

theorem tailTrace_2583909 : CollatzResearch.WordTrace tailWord_2583909 prefixEnd_2583909 294841618772985817300961 := by
  unfold tailWord_2583909
  simp only [CollatzResearch.WordTrace]
  refine ⟨94242903595946464368898781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62828602397297642912599187 94242903595946464368898781)
  ·
    refine ⟨35341088848479924138337043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94242903595946464368898781 35341088848479924138337043)
    ·
      refine ⟨53011633272719886207505565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35341088848479924138337043 53011633272719886207505565)
      ·
        refine ⟨19879362477269957327814587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53011633272719886207505565 19879362477269957327814587)
        ·
          refine ⟨29819043715904935991721881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19879362477269957327814587 29819043715904935991721881)
          ·
            refine ⟨22364282786928701993791411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29819043715904935991721881 22364282786928701993791411)
            ·
              refine ⟨33546424180393052990687117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22364282786928701993791411 33546424180393052990687117)
              ·
                refine ⟨12579909067647394871507669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33546424180393052990687117 12579909067647394871507669)
                ·
                  refine ⟨294841618772985817300961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12579909067647394871507669 294841618772985817300961)
                  ·
                    rfl

theorem cell22_2583909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 3, 7].length) (baseStart_2583909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2583909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2583909 prefixEnd_2583909 := by exact prefixLift 2583909
  have htrace : WordTrace (prefixWord ++ tailWord_2583909) baseStart_2583909 baseEnd_2583909 := by
    simpa [prefixWord, tailWord_2583909, baseEnd_2583909] using wordTrace_append hprefix tailTrace_2583909
  have hstable : (prefixWord ++ tailWord_2583909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2583909).length < 2 ^ (prefixWord ++ tailWord_2583909).sum := by decide
  have hdescent : baseEnd_2583909 < baseStart_2583909 := by decide
  rcases family_descends (prefixWord ++ tailWord_2583909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2583999 : List Nat := [1, 1, 2, 2, 2, 1, 1, 12]
def baseStart_2583999 : Nat := 118140960795 + 2583999 * 2 ^ 59
def prefixEnd_2583999 : Nat := 4983230072969 + 3 ^ 40 * 2583999 * 2
def baseEnd_2583999 : Nat := 98283962795358579683623

theorem tailTrace_2583999 : CollatzResearch.WordTrace tailWord_2583999 prefixEnd_2583999 98283962795358579683623 := by
  unfold tailWord_2583999
  simp only [CollatzResearch.WordTrace]
  refine ⟨94246186165620409739675051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62830790777080273159783367 94246186165620409739675051)
  ·
    refine ⟨141369279248430614609512577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94246186165620409739675051 141369279248430614609512577)
    ·
      refine ⟨106026959436322960957134433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141369279248430614609512577 106026959436322960957134433)
      ·
        refine ⟨79520219577242220717850825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106026959436322960957134433 79520219577242220717850825)
        ·
          refine ⟨59640164682931665538388119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79520219577242220717850825 59640164682931665538388119)
          ·
            refine ⟨89460247024397498307582179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59640164682931665538388119 89460247024397498307582179)
            ·
              refine ⟨134190370536596247461373269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89460247024397498307582179 134190370536596247461373269)
              ·
                refine ⟨98283962795358579683623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 134190370536596247461373269 98283962795358579683623)
                ·
                  rfl

theorem cell22_2583999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 12].length) (baseStart_2583999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2583999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2583999 prefixEnd_2583999 := by exact prefixLift 2583999
  have htrace : WordTrace (prefixWord ++ tailWord_2583999) baseStart_2583999 baseEnd_2583999 := by
    simpa [prefixWord, tailWord_2583999, baseEnd_2583999] using wordTrace_append hprefix tailTrace_2583999
  have hstable : (prefixWord ++ tailWord_2583999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2583999).length < 2 ^ (prefixWord ++ tailWord_2583999).sum := by decide
  have hdescent : baseEnd_2583999 < baseStart_2583999 := by decide
  rcases family_descends (prefixWord ++ tailWord_2583999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2584020 : List Nat := [2, 4, 1, 2, 3, 1, 1, 1, 4, 3]
def baseStart_2584020 : Nat := 118140960795 + 2584020 * 2 ^ 59
def prefixEnd_2584020 : Nat := 4983230072969 + 3 ^ 40 * 2584020 * 2
def baseEnd_2584020 : Nat := 884562853887390162377543

theorem tailTrace_2584020 : CollatzResearch.WordTrace tailWord_2584020 prefixEnd_2584020 884562853887390162377543 := by
  unfold tailWord_2584020
  simp only [CollatzResearch.WordTrace]
  refine ⟨47123476049272165163094757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62831301399029553550793009 47123476049272165163094757)
  ·
    refine ⟨8835651759238530968080267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47123476049272165163094757 8835651759238530968080267)
    ·
      refine ⟨13253477638857796452120401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8835651759238530968080267 13253477638857796452120401)
      ·
        refine ⟨9940108229143347339090301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13253477638857796452120401 9940108229143347339090301)
        ·
          refine ⟨3727540585928755252158863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9940108229143347339090301 3727540585928755252158863)
          ·
            refine ⟨5591310878893132878238295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3727540585928755252158863 5591310878893132878238295)
            ·
              refine ⟨8386966318339699317357443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5591310878893132878238295 8386966318339699317357443)
              ·
                refine ⟨12580449477509548976036165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8386966318339699317357443 12580449477509548976036165)
                ·
                  refine ⟨2358834277033040433006781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12580449477509548976036165 2358834277033040433006781)
                  ·
                    refine ⟨884562853887390162377543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2358834277033040433006781 884562853887390162377543)
                    ·
                      rfl

theorem cell22_2584020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 1, 4, 3].length) (baseStart_2584020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2584020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2584020 prefixEnd_2584020 := by exact prefixLift 2584020
  have htrace : WordTrace (prefixWord ++ tailWord_2584020) baseStart_2584020 baseEnd_2584020 := by
    simpa [prefixWord, tailWord_2584020, baseEnd_2584020] using wordTrace_append hprefix tailTrace_2584020
  have hstable : (prefixWord ++ tailWord_2584020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2584020).length < 2 ^ (prefixWord ++ tailWord_2584020).sum := by decide
  have hdescent : baseEnd_2584020 < baseStart_2584020 := by decide
  rcases family_descends (prefixWord ++ tailWord_2584020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2584037 : List Nat := [1, 3, 1, 5, 1, 2, 3, 1, 2, 3]
def baseStart_2584037 : Nat := 118140960795 + 2584037 * 2 ^ 59
def prefixEnd_2584037 : Nat := 4983230072969 + 3 ^ 40 * 2584037 * 2
def baseEnd_2584037 : Nat := 884568673334807784702491

theorem tailTrace_2584037 : CollatzResearch.WordTrace tailWord_2584037 prefixEnd_2584037 884568673334807784702491 := by
  unfold tailWord_2584037
  simp only [CollatzResearch.WordTrace]
  refine ⟨94247572139482742229558365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62831714759655161486372243 94247572139482742229558365)
  ·
    refine ⟨35342839552306028336084387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94247572139482742229558365 35342839552306028336084387)
    ·
      refine ⟨53014259328459042504126581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35342839552306028336084387 53014259328459042504126581)
      ·
        refine ⟨4970086812043035234761867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 53014259328459042504126581 4970086812043035234761867)
        ·
          refine ⟨7455130218064552852142801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4970086812043035234761867 7455130218064552852142801)
          ·
            refine ⟨5591347663548414639107101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7455130218064552852142801 5591347663548414639107101)
            ·
              refine ⟨2096755373830655489665163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5591347663548414639107101 2096755373830655489665163)
              ·
                refine ⟨3145133060745983234497745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2096755373830655489665163 3145133060745983234497745)
                ·
                  refine ⟨2358849795559487425873309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3145133060745983234497745 2358849795559487425873309)
                  ·
                    refine ⟨884568673334807784702491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2358849795559487425873309 884568673334807784702491)
                    ·
                      rfl

theorem cell22_2584037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 3, 1, 2, 3].length) (baseStart_2584037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2584037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2584037 prefixEnd_2584037 := by exact prefixLift 2584037
  have htrace : WordTrace (prefixWord ++ tailWord_2584037) baseStart_2584037 baseEnd_2584037 := by
    simpa [prefixWord, tailWord_2584037, baseEnd_2584037] using wordTrace_append hprefix tailTrace_2584037
  have hstable : (prefixWord ++ tailWord_2584037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2584037).length < 2 ^ (prefixWord ++ tailWord_2584037).sum := by decide
  have hdescent : baseEnd_2584037 < baseStart_2584037 := by decide
  rcases family_descends (prefixWord ++ tailWord_2584037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2584048 : List Nat := [2, 1, 1, 1, 3, 4, 2, 2, 3, 3]
def baseStart_2584048 : Nat := 118140960795 + 2584048 * 2 ^ 59
def prefixEnd_2584048 : Nat := 4983230072969 + 3 ^ 40 * 2584048 * 2
def baseEnd_2584048 : Nat := 884572438859607422677457

theorem tailTrace_2584048 : CollatzResearch.WordTrace tailWord_2584048 prefixEnd_2584048 884572438859607422677457 := by
  unfold tailWord_2584048
  simp only [CollatzResearch.WordTrace]
  refine ⟨47123986671221445554104399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62831982228295260738805865 47123986671221445554104399)
  ·
    refine ⟨70685980006832168331156599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47123986671221445554104399 70685980006832168331156599)
    ·
      refine ⟨106028970010248252496734899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70685980006832168331156599 106028970010248252496734899)
      ·
        refine ⟨159043455015372378745102349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106028970010248252496734899 159043455015372378745102349)
        ·
          refine ⟨59641295630764642029413381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 159043455015372378745102349 59641295630764642029413381)
          ·
            refine ⟨11182742930768370380515009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59641295630764642029413381 11182742930768370380515009)
            ·
              refine ⟨8387057198076277785386257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11182742930768370380515009 8387057198076277785386257)
              ·
                refine ⟨6290292898557208339039693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8387057198076277785386257 6290292898557208339039693)
                ·
                  refine ⟨2358859836958953127139885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6290292898557208339039693 2358859836958953127139885)
                  ·
                    refine ⟨884572438859607422677457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2358859836958953127139885 884572438859607422677457)
                    ·
                      rfl

theorem cell22_2584048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 2, 3, 3].length) (baseStart_2584048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2584048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2584048 prefixEnd_2584048 := by exact prefixLift 2584048
  have htrace : WordTrace (prefixWord ++ tailWord_2584048) baseStart_2584048 baseEnd_2584048 := by
    simpa [prefixWord, tailWord_2584048, baseEnd_2584048] using wordTrace_append hprefix tailTrace_2584048
  have hstable : (prefixWord ++ tailWord_2584048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2584048).length < 2 ^ (prefixWord ++ tailWord_2584048).sum := by decide
  have hdescent : baseEnd_2584048 < baseStart_2584048 := by decide
  rcases family_descends (prefixWord ++ tailWord_2584048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2584050 : List Nat := [3, 2, 1, 4, 1, 3, 2, 6]
def baseStart_2584050 : Nat := 118140960795 + 2584050 * 2 ^ 59
def prefixEnd_2584050 : Nat := 4983230072969 + 3 ^ 40 * 2584050 * 2
def baseEnd_2584050 : Nat := 98285902611164453791939

theorem tailTrace_2584050 : CollatzResearch.WordTrace tailWord_2584050 prefixEnd_2584050 98285902611164453791939 := by
  unfold tailWord_2584050
  simp only [CollatzResearch.WordTrace]
  refine ⟨23562011572108911362445401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62832030858957096966521069 23562011572108911362445401)
  ·
    refine ⟨17671508679081683521834051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23562011572108911362445401 17671508679081683521834051)
    ·
      refine ⟨26507263018622525282751077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17671508679081683521834051 26507263018622525282751077)
      ·
        refine ⟨4970111815991723490515827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26507263018622525282751077 4970111815991723490515827)
        ·
          refine ⟨7455167723987585235773741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4970111815991723490515827 7455167723987585235773741)
          ·
            refine ⟨2795687896495344463415153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7455167723987585235773741 2795687896495344463415153)
            ·
              refine ⟨2096765922371508347561365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2795687896495344463415153 2096765922371508347561365)
              ·
                refine ⟨98285902611164453791939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2096765922371508347561365 98285902611164453791939)
                ·
                  rfl

theorem cell22_2584050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 2, 6].length) (baseStart_2584050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2584050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2584050 prefixEnd_2584050 := by exact prefixLift 2584050
  have htrace : WordTrace (prefixWord ++ tailWord_2584050) baseStart_2584050 baseEnd_2584050 := by
    simpa [prefixWord, tailWord_2584050, baseEnd_2584050] using wordTrace_append hprefix tailTrace_2584050
  have hstable : (prefixWord ++ tailWord_2584050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2584050).length < 2 ^ (prefixWord ++ tailWord_2584050).sum := by decide
  have hdescent : baseEnd_2584050 < baseStart_2584050 := by decide
  rcases family_descends (prefixWord ++ tailWord_2584050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2584061 : List Nat := [1, 4, 1, 1, 1, 4, 1, 2, 7]
def baseStart_2584061 : Nat := 118140960795 + 2584061 * 2 ^ 59
def prefixEnd_2584061 : Nat := 4983230072969 + 3 ^ 40 * 2584061 * 2
def baseEnd_2584061 : Nat := 294858963008426574034139

theorem tailTrace_2584061 : CollatzResearch.WordTrace tailWord_2584061 prefixEnd_2584061 294858963008426574034139 := by
  unfold tailWord_2584061
  simp only [CollatzResearch.WordTrace]
  refine ⟨94248447491395794328432037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62832298327597196218954691 94248447491395794328432037)
  ·
    refine ⟨17671583904636711436581007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94248447491395794328432037 17671583904636711436581007)
    ·
      refine ⟨26507375856955067154871511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17671583904636711436581007 26507375856955067154871511)
      ·
        refine ⟨39761063785432600732307267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26507375856955067154871511 39761063785432600732307267)
        ·
          refine ⟨59641595678148901098460901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39761063785432600732307267 59641595678148901098460901)
          ·
            refine ⟨11182799189652918955961419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59641595678148901098460901 11182799189652918955961419)
            ·
              refine ⟨16774198784479378433942129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11182799189652918955961419 16774198784479378433942129)
              ·
                refine ⟨12580649088359533825456597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16774198784479378433942129 12580649088359533825456597)
                ·
                  refine ⟨294858963008426574034139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12580649088359533825456597 294858963008426574034139)
                  ·
                    rfl

theorem cell22_2584061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 2, 7].length) (baseStart_2584061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2584061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2584061 prefixEnd_2584061 := by exact prefixLift 2584061
  have htrace : WordTrace (prefixWord ++ tailWord_2584061) baseStart_2584061 baseEnd_2584061 := by
    simpa [prefixWord, tailWord_2584061, baseEnd_2584061] using wordTrace_append hprefix tailTrace_2584061
  have hstable : (prefixWord ++ tailWord_2584061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2584061).length < 2 ^ (prefixWord ++ tailWord_2584061).sum := by decide
  have hdescent : baseEnd_2584061 < baseStart_2584061 := by decide
  rcases family_descends (prefixWord ++ tailWord_2584061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2584136 : List Nat := [2, 1, 3, 1, 1, 1, 1, 1, 5, 6]
def baseStart_2584136 : Nat := 118140960795 + 2584136 * 2 ^ 59
def prefixEnd_2584136 : Nat := 4983230072969 + 3 ^ 40 * 2584136 * 2
def baseEnd_2584136 : Nat := 884602563058004526477187

theorem tailTrace_2584136 : CollatzResearch.WordTrace tailWord_2584136 prefixEnd_2584136 884602563058004526477187 := by
  unfold tailWord_2584136
  simp only [CollatzResearch.WordTrace]
  refine ⟨47125591483062041068706131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62834121977416054758274841 47125591483062041068706131)
  ·
    refine ⟨70688387224593061603059197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47125591483062041068706131 70688387224593061603059197)
    ·
      refine ⟨26508145209222398101147199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70688387224593061603059197 26508145209222398101147199)
      ·
        refine ⟨39762217813833597151720799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26508145209222398101147199 39762217813833597151720799)
        ·
          refine ⟨59643326720750395727581199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39762217813833597151720799 59643326720750395727581199)
          ·
            refine ⟨89464990081125593591371799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59643326720750395727581199 89464990081125593591371799)
            ·
              refine ⟨134197485121688390387057699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89464990081125593591371799 134197485121688390387057699)
              ·
                refine ⟨201296227682532585580586549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 134197485121688390387057699 201296227682532585580586549)
                ·
                  refine ⟨18871521345237429898179989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 201296227682532585580586549 18871521345237429898179989)
                  ·
                    refine ⟨884602563058004526477187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18871521345237429898179989 884602563058004526477187)
                    ·
                      rfl

theorem cell22_2584136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 5, 6].length) (baseStart_2584136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2584136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2584136 prefixEnd_2584136 := by exact prefixLift 2584136
  have htrace : WordTrace (prefixWord ++ tailWord_2584136) baseStart_2584136 baseEnd_2584136 := by
    simpa [prefixWord, tailWord_2584136, baseEnd_2584136] using wordTrace_append hprefix tailTrace_2584136
  have hstable : (prefixWord ++ tailWord_2584136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2584136).length < 2 ^ (prefixWord ++ tailWord_2584136).sum := by decide
  have hdescent : baseEnd_2584136 < baseStart_2584136 := by decide
  rcases family_descends (prefixWord ++ tailWord_2584136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2584140 : List Nat := [2, 2, 1, 3, 1, 4, 1, 4, 4]
def baseStart_2584140 : Nat := 118140960795 + 2584140 * 2 ^ 59
def prefixEnd_2584140 : Nat := 4983230072969 + 3 ^ 40 * 2584140 * 2
def baseEnd_2584140 : Nat := 294867977446583283125725

theorem tailTrace_2584140 : CollatzResearch.WordTrace tailWord_2584140 prefixEnd_2584140 294867977446583283125725 := by
  unfold tailWord_2584140
  simp only [CollatzResearch.WordTrace]
  refine ⟨47125664429054795410278937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62834219238739727213705249 47125664429054795410278937)
  ·
    refine ⟨35344248321791096557709203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47125664429054795410278937 35344248321791096557709203)
    ·
      refine ⟨53016372482686644836563805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35344248321791096557709203 53016372482686644836563805)
      ·
        refine ⟨19881139681007491813711427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53016372482686644836563805 19881139681007491813711427)
        ·
          refine ⟨29821709521511237720567141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19881139681007491813711427 29821709521511237720567141)
          ·
            refine ⟨5591570535283357072606339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29821709521511237720567141 5591570535283357072606339)
            ·
              refine ⟨8387355802925035608909509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5591570535283357072606339 8387355802925035608909509)
              ·
                refine ⟨1572629213048444176670533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8387355802925035608909509 1572629213048444176670533)
                ·
                  refine ⟨294867977446583283125725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1572629213048444176670533 294867977446583283125725)
                  ·
                    rfl

theorem cell22_2584140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 4, 4].length) (baseStart_2584140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2584140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2584140 prefixEnd_2584140 := by exact prefixLift 2584140
  have htrace : WordTrace (prefixWord ++ tailWord_2584140) baseStart_2584140 baseEnd_2584140 := by
    simpa [prefixWord, tailWord_2584140, baseEnd_2584140] using wordTrace_append hprefix tailTrace_2584140
  have hstable : (prefixWord ++ tailWord_2584140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2584140).length < 2 ^ (prefixWord ++ tailWord_2584140).sum := by decide
  have hdescent : baseEnd_2584140 < baseStart_2584140 := by decide
  rcases family_descends (prefixWord ++ tailWord_2584140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2584157 : List Nat := [1, 4, 4, 2, 1, 1, 1, 2, 6]
def baseStart_2584157 : Nat := 118140960795 + 2584157 * 2 ^ 59
def prefixEnd_2584157 : Nat := 4983230072969 + 3 ^ 40 * 2584157 * 2
def baseEnd_2584157 : Nat := 294869917262389157234041

theorem tailTrace_2584157 : CollatzResearch.WordTrace tailWord_2584157 prefixEnd_2584157 294869917262389157234041 := by
  unfold tailWord_2584157
  simp only [CollatzResearch.WordTrace]
  refine ⟨94251948899048002723926725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62834632599365335149284483 94251948899048002723926725)
  ·
    refine ⟨17672240418571500510736261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94251948899048002723926725 17672240418571500510736261)
    ·
      refine ⟨3313545078482156345763049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17672240418571500510736261 3313545078482156345763049)
      ·
        refine ⟨2485158808861617259322287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3313545078482156345763049 2485158808861617259322287)
        ·
          refine ⟨3727738213292425888983431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2485158808861617259322287 3727738213292425888983431)
          ·
            refine ⟨5591607319938638833475147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3727738213292425888983431 5591607319938638833475147)
            ·
              refine ⟨8387410979907958250212721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5591607319938638833475147 8387410979907958250212721)
              ·
                refine ⟨6290558234930968687659541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8387410979907958250212721 6290558234930968687659541)
                ·
                  refine ⟨294869917262389157234041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6290558234930968687659541 294869917262389157234041)
                  ·
                    rfl

theorem cell22_2584157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 2, 6].length) (baseStart_2584157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2584157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2584157 prefixEnd_2584157 := by exact prefixLift 2584157
  have htrace : WordTrace (prefixWord ++ tailWord_2584157) baseStart_2584157 baseEnd_2584157 := by
    simpa [prefixWord, tailWord_2584157, baseEnd_2584157] using wordTrace_append hprefix tailTrace_2584157
  have hstable : (prefixWord ++ tailWord_2584157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2584157).length < 2 ^ (prefixWord ++ tailWord_2584157).sum := by decide
  have hdescent : baseEnd_2584157 < baseStart_2584157 := by decide
  rcases family_descends (prefixWord ++ tailWord_2584157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2584170 : List Nat := [3, 1, 3, 2, 1, 2, 3, 1, 2, 4]
def baseStart_2584170 : Nat := 118140960795 + 2584170 * 2 ^ 59
def prefixEnd_2584170 : Nat := 4983230072969 + 3 ^ 40 * 2584170 * 2
def baseEnd_2584170 : Nat := 884614201952839771127083

theorem tailTrace_2584170 : CollatzResearch.WordTrace tailWord_2584170 prefixEnd_2584170 884614201952839771127083 := by
  unfold tailWord_2584170
  simp only [CollatzResearch.WordTrace]
  refine ⟨23563105762000226486037491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62834948698667270629433309 23563105762000226486037491)
  ·
    refine ⟨35344658643000339729056237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23563105762000226486037491 35344658643000339729056237)
    ·
      refine ⟨13254246991125127398396089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35344658643000339729056237 13254246991125127398396089)
      ·
        refine ⟨9940685243343845548797067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13254246991125127398396089 9940685243343845548797067)
        ·
          refine ⟨14911027865015768323195601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9940685243343845548797067 14911027865015768323195601)
          ·
            refine ⟨11183270898761826242396701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14911027865015768323195601 11183270898761826242396701)
            ·
              refine ⟨4193726587035684840898763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11183270898761826242396701 4193726587035684840898763)
              ·
                refine ⟨6290589880553527261348145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4193726587035684840898763 6290589880553527261348145)
                ·
                  refine ⟨4717942410415145446011109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6290589880553527261348145 4717942410415145446011109)
                  ·
                    refine ⟨884614201952839771127083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4717942410415145446011109 884614201952839771127083)
                    ·
                      rfl

theorem cell22_2584170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 3, 1, 2, 4].length) (baseStart_2584170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2584170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2584170 prefixEnd_2584170 := by exact prefixLift 2584170
  have htrace : WordTrace (prefixWord ++ tailWord_2584170) baseStart_2584170 baseEnd_2584170 := by
    simpa [prefixWord, tailWord_2584170, baseEnd_2584170] using wordTrace_append hprefix tailTrace_2584170
  have hstable : (prefixWord ++ tailWord_2584170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2584170).length < 2 ^ (prefixWord ++ tailWord_2584170).sum := by decide
  have hdescent : baseEnd_2584170 < baseStart_2584170 := by decide
  rcases family_descends (prefixWord ++ tailWord_2584170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2584183 : List Nat := [1, 1, 3, 1, 1, 3, 1, 1, 7, 3]
def baseStart_2584183 : Nat := 118140960795 + 2584183 * 2 ^ 59
def prefixEnd_2584183 : Nat := 4983230072969 + 3 ^ 40 * 2584183 * 2
def baseEnd_2584183 : Nat := 884618652118512070552043

theorem tailTrace_2584183 : CollatzResearch.WordTrace tailWord_2584183 prefixEnd_2584183 884618652118512070552043 := by
  unfold tailWord_2584183
  simp only [CollatzResearch.WordTrace]
  refine ⟨94252897196953809164373203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62835264797969206109582135 94252897196953809164373203)
  ·
    refine ⟨141379345795430713746559805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94252897196953809164373203 141379345795430713746559805)
    ·
      refine ⟨53017254673286517654959927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141379345795430713746559805 53017254673286517654959927)
      ·
        refine ⟨79525882009929776482439891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53017254673286517654959927 79525882009929776482439891)
        ·
          refine ⟨119288823014894664723659837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79525882009929776482439891 119288823014894664723659837)
          ·
            refine ⟨44733308630585499271372439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 119288823014894664723659837 44733308630585499271372439)
            ·
              refine ⟨67099962945878248907058659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44733308630585499271372439 67099962945878248907058659)
              ·
                refine ⟨100649944418817373360587989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67099962945878248907058659 100649944418817373360587989)
                ·
                  refine ⟨2358983072316032188138781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 100649944418817373360587989 2358983072316032188138781)
                  ·
                    refine ⟨884618652118512070552043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2358983072316032188138781 884618652118512070552043)
                    ·
                      rfl

theorem cell22_2584183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 7, 3].length) (baseStart_2584183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2584183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2584183 prefixEnd_2584183 := by exact prefixLift 2584183
  have htrace : WordTrace (prefixWord ++ tailWord_2584183) baseStart_2584183 baseEnd_2584183 := by
    simpa [prefixWord, tailWord_2584183, baseEnd_2584183] using wordTrace_append hprefix tailTrace_2584183
  have hstable : (prefixWord ++ tailWord_2584183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2584183).length < 2 ^ (prefixWord ++ tailWord_2584183).sum := by decide
  have hdescent : baseEnd_2584183 < baseStart_2584183 := by decide
  rcases family_descends (prefixWord ++ tailWord_2584183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2584213 : List Nat := [1, 3, 2, 1, 1, 1, 1, 7, 5]
def baseStart_2584213 : Nat := 118140960795 + 2584213 * 2 ^ 59
def prefixEnd_2584213 : Nat := 4983230072969 + 3 ^ 40 * 2584213 * 2
def baseEnd_2584213 : Nat := 294876307243867330767317

theorem tailTrace_2584213 : CollatzResearch.WordTrace tailWord_2584213 prefixEnd_2584213 294876307243867330767317 := by
  unfold tailWord_2584213
  simp only [CollatzResearch.WordTrace]
  refine ⟨94253991386845124287965293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62835994257896749525310195 94253991386845124287965293)
  ·
    refine ⟨35345246770066921607986985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94253991386845124287965293 35345246770066921607986985)
    ·
      refine ⟨26508935077550191205990239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35345246770066921607986985 26508935077550191205990239)
      ·
        refine ⟨39763402616325286808985359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26508935077550191205990239 39763402616325286808985359)
        ·
          refine ⟨59645103924487930213478039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39763402616325286808985359 59645103924487930213478039)
          ·
            refine ⟨89467655886731895320217059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59645103924487930213478039 89467655886731895320217059)
            ·
              refine ⟨134201483830097842980325589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89467655886731895320217059 134201483830097842980325589)
              ·
                refine ⟨3145347277267918194851381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 134201483830097842980325589 3145347277267918194851381)
                ·
                  refine ⟨294876307243867330767317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3145347277267918194851381 294876307243867330767317)
                  ·
                    rfl

theorem cell22_2584213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 7, 5].length) (baseStart_2584213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2584213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2584213 prefixEnd_2584213 := by exact prefixLift 2584213
  have htrace : WordTrace (prefixWord ++ tailWord_2584213) baseStart_2584213 baseEnd_2584213 := by
    simpa [prefixWord, tailWord_2584213, baseEnd_2584213] using wordTrace_append hprefix tailTrace_2584213
  have hstable : (prefixWord ++ tailWord_2584213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2584213).length < 2 ^ (prefixWord ++ tailWord_2584213).sum := by decide
  have hdescent : baseEnd_2584213 < baseStart_2584213 := by decide
  rcases family_descends (prefixWord ++ tailWord_2584213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2584260 : List Nat := [2, 3, 3, 1, 1, 1, 2, 2, 3, 4]
def baseStart_2584260 : Nat := 118140960795 + 2584260 * 2 ^ 59
def prefixEnd_2584260 : Nat := 4983230072969 + 3 ^ 40 * 2584260 * 2
def baseEnd_2584260 : Nat := 884645010792109536376807

theorem tailTrace_2584260 : CollatzResearch.WordTrace tailWord_2584260 prefixEnd_2584260 884645010792109536376807 := by
  unfold tailWord_2584260
  simp only [CollatzResearch.WordTrace]
  refine ⟨47127852808837425657463117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62837137078449900876617489 47127852808837425657463117)
  ·
    refine ⟨17672944803314034621548669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47127852808837425657463117 17672944803314034621548669)
    ·
      refine ⟨6627354301242762983080751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17672944803314034621548669 6627354301242762983080751)
      ·
        refine ⟨9941031451864144474621127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6627354301242762983080751 9941031451864144474621127)
        ·
          refine ⟨14911547177796216711931691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9941031451864144474621127 14911547177796216711931691)
          ·
            refine ⟨22367320766694325067897537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14911547177796216711931691 22367320766694325067897537)
            ·
              refine ⟨16775490575020743800923153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22367320766694325067897537 16775490575020743800923153)
              ·
                refine ⟨12581617931265557850692365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16775490575020743800923153 12581617931265557850692365)
                ·
                  refine ⟨4718106724224584194009637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12581617931265557850692365 4718106724224584194009637)
                  ·
                    refine ⟨884645010792109536376807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4718106724224584194009637 884645010792109536376807)
                    ·
                      rfl

theorem cell22_2584260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_2584260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2584260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2584260 prefixEnd_2584260 := by exact prefixLift 2584260
  have htrace : WordTrace (prefixWord ++ tailWord_2584260) baseStart_2584260 baseEnd_2584260 := by
    simpa [prefixWord, tailWord_2584260, baseEnd_2584260] using wordTrace_append hprefix tailTrace_2584260
  have hstable : (prefixWord ++ tailWord_2584260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2584260).length < 2 ^ (prefixWord ++ tailWord_2584260).sum := by decide
  have hdescent : baseEnd_2584260 < baseStart_2584260 := by decide
  rcases family_descends (prefixWord ++ tailWord_2584260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2584288 : List Nat := [2, 1, 1, 3, 1, 2, 2, 3, 1, 6]
def baseStart_2584288 : Nat := 118140960795 + 2584288 * 2 ^ 59
def prefixEnd_2584288 : Nat := 4983230072969 + 3 ^ 40 * 2584288 * 2
def baseEnd_2584288 : Nat := 884654595764326796676721

theorem tailTrace_2584288 : CollatzResearch.WordTrace tailWord_2584288 prefixEnd_2584288 884654595764326796676721 := by
  unfold tailWord_2584288
  simp only [CollatzResearch.WordTrace]
  refine ⟨47128363430786706048472759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62837817907715608064630345 47128363430786706048472759)
  ·
    refine ⟨70692545146180059072709139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47128363430786706048472759 70692545146180059072709139)
    ·
      refine ⟨106038817719270088609063709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70692545146180059072709139 106038817719270088609063709)
      ·
        refine ⟨39764556644726283228398891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106038817719270088609063709 39764556644726283228398891)
        ·
          refine ⟨59646834967089424842598337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39764556644726283228398891 59646834967089424842598337)
          ·
            refine ⟨44735126225317068631948753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59646834967089424842598337 44735126225317068631948753)
            ·
              refine ⟨33551344668987801473961565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44735126225317068631948753 33551344668987801473961565)
              ·
                refine ⟨12581754250870425552735587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33551344668987801473961565 12581754250870425552735587)
                ·
                  refine ⟨18872631376305638329103381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12581754250870425552735587 18872631376305638329103381)
                  ·
                    refine ⟨884654595764326796676721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18872631376305638329103381 884654595764326796676721)
                    ·
                      rfl

theorem cell22_2584288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 3, 1, 6].length) (baseStart_2584288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2584288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2584288 prefixEnd_2584288 := by exact prefixLift 2584288
  have htrace : WordTrace (prefixWord ++ tailWord_2584288) baseStart_2584288 baseEnd_2584288 := by
    simpa [prefixWord, tailWord_2584288, baseEnd_2584288] using wordTrace_append hprefix tailTrace_2584288
  have hstable : (prefixWord ++ tailWord_2584288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2584288).length < 2 ^ (prefixWord ++ tailWord_2584288).sum := by decide
  have hdescent : baseEnd_2584288 < baseStart_2584288 := by decide
  rcases family_descends (prefixWord ++ tailWord_2584288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2584305 : List Nat := [1, 2, 2, 2, 2, 3, 2, 2, 2, 4]
def baseStart_2584305 : Nat := 118140960795 + 2584305 * 2 ^ 59
def prefixEnd_2584305 : Nat := 4983230072969 + 3 ^ 40 * 2584305 * 2
def baseEnd_2584305 : Nat := 884660415211744419001669

theorem tailTrace_2584305 : CollatzResearch.WordTrace tailWord_2584305 prefixEnd_2584305 884660415211744419001669 := by
  unfold tailWord_2584305
  simp only [CollatzResearch.WordTrace]
  refine ⟨94257346902511824000314369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62838231268341216000209579 94257346902511824000314369)
  ·
    refine ⟨70693010176883868000235777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94257346902511824000314369 70693010176883868000235777)
    ·
      refine ⟨53019757632662901000176833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70693010176883868000235777 53019757632662901000176833)
      ·
        refine ⟨39764818224497175750132625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53019757632662901000176833 39764818224497175750132625)
        ·
          refine ⟨29823613668372881812599469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39764818224497175750132625 29823613668372881812599469)
          ·
            refine ⟨11183855125639830679724801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29823613668372881812599469 11183855125639830679724801)
            ·
              refine ⟨8387891344229873009793601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11183855125639830679724801 8387891344229873009793601)
              ·
                refine ⟨6290918508172404757345201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8387891344229873009793601 6290918508172404757345201)
                ·
                  refine ⟨4718188881129303568008901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6290918508172404757345201 4718188881129303568008901)
                  ·
                    refine ⟨884660415211744419001669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4718188881129303568008901 884660415211744419001669)
                    ·
                      rfl

theorem cell22_2584305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 2, 2, 4].length) (baseStart_2584305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2584305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2584305 prefixEnd_2584305 := by exact prefixLift 2584305
  have htrace : WordTrace (prefixWord ++ tailWord_2584305) baseStart_2584305 baseEnd_2584305 := by
    simpa [prefixWord, tailWord_2584305, baseEnd_2584305] using wordTrace_append hprefix tailTrace_2584305
  have hstable : (prefixWord ++ tailWord_2584305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2584305).length < 2 ^ (prefixWord ++ tailWord_2584305).sum := by decide
  have hdescent : baseEnd_2584305 < baseStart_2584305 := by decide
  rcases family_descends (prefixWord ++ tailWord_2584305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2584369 : List Nat := [1, 2, 2, 3, 2, 2, 2, 4, 1, 3]
def baseStart_2584369 : Nat := 118140960795 + 2584369 * 2 ^ 59
def prefixEnd_2584369 : Nat := 4983230072969 + 3 ^ 40 * 2584369 * 2
def baseEnd_2584369 : Nat := 884682323719669585401473

theorem tailTrace_2584369 : CollatzResearch.WordTrace tailWord_2584369 prefixEnd_2584369 884682323719669585401473 := by
  unfold tailWord_2584369
  simp only [CollatzResearch.WordTrace]
  refine ⟨94259681174279962930644161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62839787449519975287096107 94259681174279962930644161)
  ·
    refine ⟨70694760880709972197983121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94259681174279962930644161 70694760880709972197983121)
    ·
      refine ⟨53021070660532479148487341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70694760880709972197983121 53021070660532479148487341)
      ·
        refine ⟨19882901497699679680682753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53021070660532479148487341 19882901497699679680682753)
        ·
          refine ⟨14912176123274759760512065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19882901497699679680682753 14912176123274759760512065)
          ·
            refine ⟨11184132092456069820384049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14912176123274759760512065 11184132092456069820384049)
            ·
              refine ⟨8388099069342052365288037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11184132092456069820384049 8388099069342052365288037)
              ·
                refine ⟨1572768575501634818491507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8388099069342052365288037 1572768575501634818491507)
                ·
                  refine ⟨2359152863252452227737261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1572768575501634818491507 2359152863252452227737261)
                  ·
                    refine ⟨884682323719669585401473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2359152863252452227737261 884682323719669585401473)
                    ·
                      rfl

theorem cell22_2584369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 4, 1, 3].length) (baseStart_2584369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2584369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2584369 prefixEnd_2584369 := by exact prefixLift 2584369
  have htrace : WordTrace (prefixWord ++ tailWord_2584369) baseStart_2584369 baseEnd_2584369 := by
    simpa [prefixWord, tailWord_2584369, baseEnd_2584369] using wordTrace_append hprefix tailTrace_2584369
  have hstable : (prefixWord ++ tailWord_2584369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2584369).length < 2 ^ (prefixWord ++ tailWord_2584369).sum := by decide
  have hdescent : baseEnd_2584369 < baseStart_2584369 := by decide
  rcases family_descends (prefixWord ++ tailWord_2584369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2584380 : List Nat := [2, 2, 2, 2, 1, 1, 4, 1, 2, 5]
def baseStart_2584380 : Nat := 118140960795 + 2584380 * 2 ^ 59
def prefixEnd_2584380 : Nat := 4983230072969 + 3 ^ 40 * 2584380 * 2
def baseEnd_2584380 : Nat := 884686089244469223376439

theorem tailTrace_2584380 : CollatzResearch.WordTrace tailWord_2584380 prefixEnd_2584380 884686089244469223376439 := by
  unfold tailWord_2584380
  simp only [CollatzResearch.WordTrace]
  refine ⟨47130041188620055904647297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62840054918160074539529729 47130041188620055904647297)
  ·
    refine ⟨35347530891465041928485473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47130041188620055904647297 35347530891465041928485473)
    ·
      refine ⟨26510648168598781446364105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35347530891465041928485473 26510648168598781446364105)
      ·
        refine ⟨19882986126449086084773079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26510648168598781446364105 19882986126449086084773079)
        ·
          refine ⟨29824479189673629127159619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19882986126449086084773079 29824479189673629127159619)
          ·
            refine ⟨44736718784510443690739429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29824479189673629127159619 44736718784510443690739429)
            ·
              refine ⟨8388134772095708192013643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44736718784510443690739429 8388134772095708192013643)
              ·
                refine ⟨12582202158143562288020465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8388134772095708192013643 12582202158143562288020465)
                ·
                  refine ⟨9436651618607671716015349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12582202158143562288020465 9436651618607671716015349)
                  ·
                    refine ⟨884686089244469223376439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9436651618607671716015349 884686089244469223376439)
                    ·
                      rfl

theorem cell22_2584380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 1, 2, 5].length) (baseStart_2584380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2584380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2584380 prefixEnd_2584380 := by exact prefixLift 2584380
  have htrace : WordTrace (prefixWord ++ tailWord_2584380) baseStart_2584380 baseEnd_2584380 := by
    simpa [prefixWord, tailWord_2584380, baseEnd_2584380] using wordTrace_append hprefix tailTrace_2584380
  have hstable : (prefixWord ++ tailWord_2584380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2584380).length < 2 ^ (prefixWord ++ tailWord_2584380).sum := by decide
  have hdescent : baseEnd_2584380 < baseStart_2584380 := by decide
  rcases family_descends (prefixWord ++ tailWord_2584380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2584446 : List Nat := [4, 2, 3, 1, 1, 1, 3, 2, 1, 4]
def baseStart_2584446 : Nat := 118140960795 + 2584446 * 2 ^ 59
def prefixEnd_2584446 : Nat := 4983230072969 + 3 ^ 40 * 2584446 * 2
def baseEnd_2584446 : Nat := 884708682393267051226237

theorem tailTrace_2584446 : CollatzResearch.WordTrace tailWord_2584446 prefixEnd_2584446 884708682393267051226237 := by
  unfold tailWord_2584446
  simp only [CollatzResearch.WordTrace]
  refine ⟨11782811199375125635149649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62841659730000670054131461 11782811199375125635149649)
  ·
    refine ⟨8837108399531344226362237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11782811199375125635149649 8837108399531344226362237)
    ·
      refine ⟨3313915649824254084885839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8837108399531344226362237 3313915649824254084885839)
      ·
        refine ⟨4970873474736381127328759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3313915649824254084885839 4970873474736381127328759)
        ·
          refine ⟨7456310212104571690993139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4970873474736381127328759 7456310212104571690993139)
          ·
            refine ⟨11184465318156857536489709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7456310212104571690993139 11184465318156857536489709)
            ·
              refine ⟨4194174494308821576183641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11184465318156857536489709 4194174494308821576183641)
              ·
                refine ⟨3145630870731616182137731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4194174494308821576183641 3145630870731616182137731)
                ·
                  refine ⟨4718446306097424273206597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3145630870731616182137731 4718446306097424273206597)
                  ·
                    refine ⟨884708682393267051226237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4718446306097424273206597 884708682393267051226237)
                    ·
                      rfl

theorem cell22_2584446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_2584446 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2584446 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2584446 prefixEnd_2584446 := by exact prefixLift 2584446
  have htrace : WordTrace (prefixWord ++ tailWord_2584446) baseStart_2584446 baseEnd_2584446 := by
    simpa [prefixWord, tailWord_2584446, baseEnd_2584446] using wordTrace_append hprefix tailTrace_2584446
  have hstable : (prefixWord ++ tailWord_2584446).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2584446).length < 2 ^ (prefixWord ++ tailWord_2584446).sum := by decide
  have hdescent : baseEnd_2584446 < baseStart_2584446 := by decide
  rcases family_descends (prefixWord ++ tailWord_2584446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2584457 : List Nat := [1, 2, 1, 1, 5, 1, 4, 1, 2, 4]
def baseStart_2584457 : Nat := 118140960795 + 2584457 * 2 ^ 59
def prefixEnd_2584457 : Nat := 4983230072969 + 3 ^ 40 * 2584457 * 2
def baseEnd_2584457 : Nat := 884712447918066689201203

theorem tailTrace_2584457 : CollatzResearch.WordTrace tailWord_2584457 prefixEnd_2584457 884712447918066689201203 := by
  unfold tailWord_2584457
  simp only [CollatzResearch.WordTrace]
  refine ⟨94262890797961153959847625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62841927198640769306565083 94262890797961153959847625)
  ·
    refine ⟨70697168098470865469885719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94262890797961153959847625 70697168098470865469885719)
    ·
      refine ⟨106045752147706298204828579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70697168098470865469885719 106045752147706298204828579)
      ·
        refine ⟨159068628221559447307242869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106045752147706298204828579 159068628221559447307242869)
        ·
          refine ⟨14912683895771198185054019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 159068628221559447307242869 14912683895771198185054019)
          ·
            refine ⟨22369025843656797277581029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14912683895771198185054019 22369025843656797277581029)
            ·
              refine ⟨4194192345685649489546443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22369025843656797277581029 4194192345685649489546443)
              ·
                refine ⟨6291288518528474234319665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4194192345685649489546443 6291288518528474234319665)
                ·
                  refine ⟨4718466388896355675739749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6291288518528474234319665 4718466388896355675739749)
                  ·
                    refine ⟨884712447918066689201203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4718466388896355675739749 884712447918066689201203)
                    ·
                      rfl

theorem cell22_2584457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 4, 1, 2, 4].length) (baseStart_2584457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2584457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2584457 prefixEnd_2584457 := by exact prefixLift 2584457
  have htrace : WordTrace (prefixWord ++ tailWord_2584457) baseStart_2584457 baseEnd_2584457 := by
    simpa [prefixWord, tailWord_2584457, baseEnd_2584457] using wordTrace_append hprefix tailTrace_2584457
  have hstable : (prefixWord ++ tailWord_2584457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2584457).length < 2 ^ (prefixWord ++ tailWord_2584457).sum := by decide
  have hdescent : baseEnd_2584457 < baseStart_2584457 := by decide
  rcases family_descends (prefixWord ++ tailWord_2584457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2584472 : List Nat := [2, 1, 2, 6, 1, 10]
def baseStart_2584472 : Nat := 118140960795 + 2584472 * 2 ^ 59
def prefixEnd_2584472 : Nat := 4983230072969 + 3 ^ 40 * 2584472 * 2
def baseEnd_2584472 : Nat := 10922439292896440124397

theorem tailTrace_2584472 : CollatzResearch.WordTrace tailWord_2584472 prefixEnd_2584472 10922439292896440124397 := by
  unfold tailWord_2584472
  simp only [CollatzResearch.WordTrace]
  refine ⟨47131718946453405760821835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62842291928604541014429113 47131718946453405760821835)
  ·
    refine ⟨70697578419680108641232753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47131718946453405760821835 70697578419680108641232753)
    ·
      refine ⟨53023183814760081480924565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70697578419680108641232753 53023183814760081480924565)
      ·
        refine ⟨2485461741316878819418339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 53023183814760081480924565 2485461741316878819418339)
        ·
          refine ⟨3728192611975318229127509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2485461741316878819418339 3728192611975318229127509)
          ·
            refine ⟨10922439292896440124397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3728192611975318229127509 10922439292896440124397)
            ·
              rfl

theorem cell22_2584472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 10].length) (baseStart_2584472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2584472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2584472 prefixEnd_2584472 := by exact prefixLift 2584472
  have htrace : WordTrace (prefixWord ++ tailWord_2584472) baseStart_2584472 baseEnd_2584472 := by
    simpa [prefixWord, tailWord_2584472, baseEnd_2584472] using wordTrace_append hprefix tailTrace_2584472
  have hstable : (prefixWord ++ tailWord_2584472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2584472).length < 2 ^ (prefixWord ++ tailWord_2584472).sum := by decide
  have hdescent : baseEnd_2584472 < baseStart_2584472 := by decide
  rcases family_descends (prefixWord ++ tailWord_2584472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2584476 : List Nat := [2, 2, 3, 3, 1, 2, 2, 2, 2, 3]
def baseStart_2584476 : Nat := 118140960795 + 2584476 * 2 ^ 59
def prefixEnd_2584476 : Nat := 4983230072969 + 3 ^ 40 * 2584476 * 2
def baseEnd_2584476 : Nat := 884718952006356972976145

theorem tailTrace_2584476 : CollatzResearch.WordTrace tailWord_2584476 prefixEnd_2584476 884718952006356972976145 := by
  unfold tailWord_2584476
  simp only [CollatzResearch.WordTrace]
  refine ⟨47131791892446160102394641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62842389189928213469859521 47131791892446160102394641)
  ·
    refine ⟨35348843919334620076795981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47131791892446160102394641 35348843919334620076795981)
    ·
      refine ⟨13255816469750482528798493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35348843919334620076795981 13255816469750482528798493)
      ·
        refine ⟨4970931176156430948299435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13255816469750482528798493 4970931176156430948299435)
        ·
          refine ⟨7456396764234646422449153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4970931176156430948299435 7456396764234646422449153)
          ·
            refine ⟨5592297573175984816836865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7456396764234646422449153 5592297573175984816836865)
            ·
              refine ⟨4194223179881988612627649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5592297573175984816836865 4194223179881988612627649)
              ·
                refine ⟨3145667384911491459470737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4194223179881988612627649 3145667384911491459470737)
                ·
                  refine ⟨2359250538683618594603053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3145667384911491459470737 2359250538683618594603053)
                  ·
                    refine ⟨884718952006356972976145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2359250538683618594603053 884718952006356972976145)
                    ·
                      rfl

theorem cell22_2584476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 2, 2, 2, 3].length) (baseStart_2584476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2584476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2584476 prefixEnd_2584476 := by exact prefixLift 2584476
  have htrace : WordTrace (prefixWord ++ tailWord_2584476) baseStart_2584476 baseEnd_2584476 := by
    simpa [prefixWord, tailWord_2584476, baseEnd_2584476] using wordTrace_append hprefix tailTrace_2584476
  have hstable : (prefixWord ++ tailWord_2584476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2584476).length < 2 ^ (prefixWord ++ tailWord_2584476).sum := by decide
  have hdescent : baseEnd_2584476 < baseStart_2584476 := by decide
  rcases family_descends (prefixWord ++ tailWord_2584476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2584478 : List Nat := [4, 3, 1, 3, 1, 1, 1, 4, 4]
def baseStart_2584478 : Nat := 118140960795 + 2584478 * 2 ^ 59
def prefixEnd_2584478 : Nat := 4983230072969 + 3 ^ 40 * 2584478 * 2
def baseEnd_2584478 : Nat := 294906545549076544808713

theorem tailTrace_2584478 : CollatzResearch.WordTrace tailWord_2584478 prefixEnd_2584478 294906545549076544808713 := by
  unfold tailWord_2584478
  simp only [CollatzResearch.WordTrace]
  refine ⟨11782957091360634318295261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62842437820590049697574725 11782957091360634318295261)
  ·
    refine ⟨4418608909260237869360723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11782957091360634318295261 4418608909260237869360723)
    ·
      refine ⟨6627913363890356804041085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4418608909260237869360723 6627913363890356804041085)
      ·
        refine ⟨2485467511458883801515407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6627913363890356804041085 2485467511458883801515407)
        ·
          refine ⟨3728201267188325702273111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2485467511458883801515407 3728201267188325702273111)
          ·
            refine ⟨5592301900782488553409667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3728201267188325702273111 5592301900782488553409667)
            ·
              refine ⟨8388452851173732830114501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5592301900782488553409667 8388452851173732830114501)
              ·
                refine ⟨1572834909595074905646469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8388452851173732830114501 1572834909595074905646469)
                ·
                  refine ⟨294906545549076544808713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1572834909595074905646469 294906545549076544808713)
                  ·
                    rfl

theorem cell22_2584478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 4, 4].length) (baseStart_2584478 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2584478 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2584478 prefixEnd_2584478 := by exact prefixLift 2584478
  have htrace : WordTrace (prefixWord ++ tailWord_2584478) baseStart_2584478 baseEnd_2584478 := by
    simpa [prefixWord, tailWord_2584478, baseEnd_2584478] using wordTrace_append hprefix tailTrace_2584478
  have hstable : (prefixWord ++ tailWord_2584478).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2584478).length < 2 ^ (prefixWord ++ tailWord_2584478).sum := by decide
  have hdescent : baseEnd_2584478 < baseStart_2584478 := by decide
  rcases family_descends (prefixWord ++ tailWord_2584478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2584508 : List Nat := [2, 2, 2, 5, 2, 1, 1, 1, 2, 4]
def baseStart_2584508 : Nat := 118140960795 + 2584508 * 2 ^ 59
def prefixEnd_2584508 : Nat := 4983230072969 + 3 ^ 40 * 2584508 * 2
def baseEnd_2584508 : Nat := 884729906260319556176047

theorem tailTrace_2584508 : CollatzResearch.WordTrace tailWord_2584508 prefixEnd_2584508 884729906260319556176047 := by
  unfold tailWord_2584508
  simp only [CollatzResearch.WordTrace]
  refine ⟨47132375460388194834977089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62843167280517593113302785 47132375460388194834977089)
  ·
    refine ⟨35349281595291146126232817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47132375460388194834977089 35349281595291146126232817)
    ·
      refine ⟨26511961196468359594674613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35349281595291146126232817 26511961196468359594674613)
      ·
        refine ⟨2485496362168908712000745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26511961196468359594674613 2485496362168908712000745)
        ·
          refine ⟨1864122271626681534000559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2485496362168908712000745 1864122271626681534000559)
          ·
            refine ⟨2796183407440022301000839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1864122271626681534000559 2796183407440022301000839)
            ·
              refine ⟨4194275111160033451501259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2796183407440022301000839 4194275111160033451501259)
              ·
                refine ⟨6291412666740050177251889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4194275111160033451501259 6291412666740050177251889)
                ·
                  refine ⟨4718559500055037632938917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6291412666740050177251889 4718559500055037632938917)
                  ·
                    refine ⟨884729906260319556176047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4718559500055037632938917 884729906260319556176047)
                    ·
                      rfl

theorem cell22_2584508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 1, 1, 2, 4].length) (baseStart_2584508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2584508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2584508 prefixEnd_2584508 := by exact prefixLift 2584508
  have htrace : WordTrace (prefixWord ++ tailWord_2584508) baseStart_2584508 baseEnd_2584508 := by
    simpa [prefixWord, tailWord_2584508, baseEnd_2584508] using wordTrace_append hprefix tailTrace_2584508
  have hstable : (prefixWord ++ tailWord_2584508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2584508).length < 2 ^ (prefixWord ++ tailWord_2584508).sum := by decide
  have hdescent : baseEnd_2584508 < baseStart_2584508 := by decide
  rcases family_descends (prefixWord ++ tailWord_2584508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2584515 : List Nat := [1, 1, 1, 3, 1, 1, 2, 1, 6, 5]
def baseStart_2584515 : Nat := 118140960795 + 2584515 * 2 ^ 59
def prefixEnd_2584515 : Nat := 4983230072969 + 3 ^ 40 * 2584515 * 2
def baseEnd_2584515 : Nat := 884732302503373871251025

theorem tailTrace_2584515 : CollatzResearch.WordTrace tailWord_2584515 prefixEnd_2584515 884732302503373871251025 := by
  unfold tailWord_2584515
  simp only [CollatzResearch.WordTrace]
  refine ⟨94265006231751029865458999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62843337487834019910305999 94265006231751029865458999)
  ·
    refine ⟨141397509347626544798188499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94265006231751029865458999 141397509347626544798188499)
    ·
      refine ⟨212096264021439817197282749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141397509347626544798188499 212096264021439817197282749)
      ·
        refine ⟨79536099008039931448981031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 212096264021439817197282749 79536099008039931448981031)
        ·
          refine ⟨119304148512059897173471547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79536099008039931448981031 119304148512059897173471547)
          ·
            refine ⟨178956222768089845760207321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119304148512059897173471547 178956222768089845760207321)
            ·
              refine ⟨134217167076067384320155491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 178956222768089845760207321 134217167076067384320155491)
              ·
                refine ⟨201325750614101076480233237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 134217167076067384320155491 201325750614101076480233237)
                ·
                  refine ⟨9437144560035987960010933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 201325750614101076480233237 9437144560035987960010933)
                  ·
                    refine ⟨884732302503373871251025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9437144560035987960010933 884732302503373871251025)
                    ·
                      rfl

theorem cell22_2584515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 6, 5].length) (baseStart_2584515 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2584515 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2584515 prefixEnd_2584515 := by exact prefixLift 2584515
  have htrace : WordTrace (prefixWord ++ tailWord_2584515) baseStart_2584515 baseEnd_2584515 := by
    simpa [prefixWord, tailWord_2584515, baseEnd_2584515] using wordTrace_append hprefix tailTrace_2584515
  have hstable : (prefixWord ++ tailWord_2584515).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2584515).length < 2 ^ (prefixWord ++ tailWord_2584515).sum := by decide
  have hdescent : baseEnd_2584515 < baseStart_2584515 := by decide
  rcases family_descends (prefixWord ++ tailWord_2584515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2584532 : List Nat := [2, 4, 1, 2, 1, 1, 1, 1, 4, 5]
def baseStart_2584532 : Nat := 118140960795 + 2584532 * 2 ^ 59
def prefixEnd_2584532 : Nat := 4983230072969 + 3 ^ 40 * 2584532 * 2
def baseEnd_2584532 : Nat := 884738121950791493575973

theorem tailTrace_2584532 : CollatzResearch.WordTrace tailWord_2584532 prefixEnd_2584532 884738121950791493575973 := by
  unfold tailWord_2584532
  simp only [CollatzResearch.WordTrace]
  refine ⟨47132813136344720884413925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62843750848459627845885233 47132813136344720884413925)
  ·
    refine ⟨8837402463064635165827611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47132813136344720884413925 8837402463064635165827611)
    ·
      refine ⟨13256103694596952748741417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8837402463064635165827611 13256103694596952748741417)
      ·
        refine ⟨9942077770947714561556063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13256103694596952748741417 9942077770947714561556063)
        ·
          refine ⟨14913116656421571842334095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9942077770947714561556063 14913116656421571842334095)
          ·
            refine ⟨22369674984632357763501143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14913116656421571842334095 22369674984632357763501143)
            ·
              refine ⟨33554512476948536645251715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22369674984632357763501143 33554512476948536645251715)
              ·
                refine ⟨50331768715422804967877573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33554512476948536645251715 50331768715422804967877573)
                ·
                  refine ⟨9437206634141775931477045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50331768715422804967877573 9437206634141775931477045)
                  ·
                    refine ⟨884738121950791493575973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9437206634141775931477045 884738121950791493575973)
                    ·
                      rfl

theorem cell22_2584532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 4, 5].length) (baseStart_2584532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2584532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2584532 prefixEnd_2584532 := by exact prefixLift 2584532
  have htrace : WordTrace (prefixWord ++ tailWord_2584532) baseStart_2584532 baseEnd_2584532 := by
    simpa [prefixWord, tailWord_2584532, baseEnd_2584532] using wordTrace_append hprefix tailTrace_2584532
  have hstable : (prefixWord ++ tailWord_2584532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2584532).length < 2 ^ (prefixWord ++ tailWord_2584532).sum := by decide
  have hdescent : baseEnd_2584532 < baseStart_2584532 := by decide
  rcases family_descends (prefixWord ++ tailWord_2584532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2584551 : List Nat := [1, 1, 5, 2, 3, 1, 3, 1, 5]
def baseStart_2584551 : Nat := 118140960795 + 2584551 * 2 ^ 59
def prefixEnd_2584551 : Nat := 4983230072969 + 3 ^ 40 * 2584551 * 2
def baseEnd_2584551 : Nat := 294914875346360592450305

theorem tailTrace_2584551 : CollatzResearch.WordTrace tailWord_2584551 prefixEnd_2584551 294914875346360592450305 := by
  unfold tailWord_2584551
  simp only [CollatzResearch.WordTrace]
  refine ⟨94266319259620608013769507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62844212839747072009179671 94266319259620608013769507)
  ·
    refine ⟨141399478889430912020654261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94266319259620608013769507 141399478889430912020654261)
    ·
      refine ⟨13256201145884148001936337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 141399478889430912020654261 13256201145884148001936337)
      ·
        refine ⟨9942150859413111001452253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13256201145884148001936337 9942150859413111001452253)
        ·
          refine ⟨3728306572279916625544595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9942150859413111001452253 3728306572279916625544595)
          ·
            refine ⟨5592459858419874938316893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3728306572279916625544595 5592459858419874938316893)
            ·
              refine ⟨2097172446907453101868835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5592459858419874938316893 2097172446907453101868835)
              ·
                refine ⟨3145758670361179652803253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2097172446907453101868835 3145758670361179652803253)
                ·
                  refine ⟨294914875346360592450305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3145758670361179652803253 294914875346360592450305)
                  ·
                    rfl

theorem cell22_2584551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 3, 1, 5].length) (baseStart_2584551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2584551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2584551 prefixEnd_2584551 := by exact prefixLift 2584551
  have htrace : WordTrace (prefixWord ++ tailWord_2584551) baseStart_2584551 baseEnd_2584551 := by
    simpa [prefixWord, tailWord_2584551, baseEnd_2584551] using wordTrace_append hprefix tailTrace_2584551
  have hstable : (prefixWord ++ tailWord_2584551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2584551).length < 2 ^ (prefixWord ++ tailWord_2584551).sum := by decide
  have hdescent : baseEnd_2584551 < baseStart_2584551 := by decide
  rcases family_descends (prefixWord ++ tailWord_2584551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2584577 : List Nat := [1, 2, 4, 1, 2, 1, 2, 1, 3, 5]
def baseStart_2584577 : Nat := 118140960795 + 2584577 * 2 ^ 59
def prefixEnd_2584577 : Nat := 4983230072969 + 3 ^ 40 * 2584577 * 2
def baseEnd_2584577 : Nat := 884753526370426376200835

theorem tailTrace_2584577 : CollatzResearch.WordTrace tailWord_2584577 prefixEnd_2584577 884753526370426376200835 := by
  unfold tailWord_2584577
  simp only [CollatzResearch.WordTrace]
  refine ⟨94267267557526414454215985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62844845038350942969477323 94267267557526414454215985)
  ·
    refine ⟨70700450668144810840661989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94267267557526414454215985 70700450668144810840661989)
    ·
      refine ⟨13256334500277152032624123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70700450668144810840661989 13256334500277152032624123)
      ·
        refine ⟨19884501750415728048936185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13256334500277152032624123 19884501750415728048936185)
        ·
          refine ⟨14913376312811796036702139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19884501750415728048936185 14913376312811796036702139)
          ·
            refine ⟨22370064469217694055053209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14913376312811796036702139 22370064469217694055053209)
            ·
              refine ⟨16777548351913270541289907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22370064469217694055053209 16777548351913270541289907)
              ·
                refine ⟨25166322527869905811934861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16777548351913270541289907 25166322527869905811934861)
                ·
                  refine ⟨9437370947951214679475573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25166322527869905811934861 9437370947951214679475573)
                  ·
                    refine ⟨884753526370426376200835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9437370947951214679475573 884753526370426376200835)
                    ·
                      rfl

theorem cell22_2584577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 1, 3, 5].length) (baseStart_2584577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2584577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2584577 prefixEnd_2584577 := by exact prefixLift 2584577
  have htrace : WordTrace (prefixWord ++ tailWord_2584577) baseStart_2584577 baseEnd_2584577 := by
    simpa [prefixWord, tailWord_2584577, baseEnd_2584577] using wordTrace_append hprefix tailTrace_2584577
  have hstable : (prefixWord ++ tailWord_2584577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2584577).length < 2 ^ (prefixWord ++ tailWord_2584577).sum := by decide
  have hdescent : baseEnd_2584577 < baseStart_2584577 := by decide
  rcases family_descends (prefixWord ++ tailWord_2584577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2584589 : List Nat := [1, 7, 1, 2, 1, 1, 3, 2, 1, 3]
def baseStart_2584589 : Nat := 118140960795 + 2584589 * 2 ^ 59
def prefixEnd_2584589 : Nat := 4983230072969 + 3 ^ 40 * 2584589 * 2
def baseEnd_2584589 : Nat := 884757634215662344900799

theorem tailTrace_2584589 : CollatzResearch.WordTrace tailWord_2584589 prefixEnd_2584589 884757634215662344900799 := by
  unfold tailWord_2584589
  simp only [CollatzResearch.WordTrace]
  refine ⟨94267705233482940503652821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62845136822321960335768547 94267705233482940503652821)
  ·
    refine ⟨2209399341409756418054363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 94267705233482940503652821 2209399341409756418054363)
    ·
      refine ⟨3314099012114634627081545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2209399341409756418054363 3314099012114634627081545)
      ·
        refine ⟨2485574259085975970311159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3314099012114634627081545 2485574259085975970311159)
        ·
          refine ⟨3728361388628963955466739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2485574259085975970311159 3728361388628963955466739)
          ·
            refine ⟨5592542082943445933200109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3728361388628963955466739 5592542082943445933200109)
            ·
              refine ⟨2097203281103792224950041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5592542082943445933200109 2097203281103792224950041)
              ·
                refine ⟨1572902460827844168712531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2097203281103792224950041 1572902460827844168712531)
                ·
                  refine ⟨2359353691241766253068797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1572902460827844168712531 2359353691241766253068797)
                  ·
                    refine ⟨884757634215662344900799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2359353691241766253068797 884757634215662344900799)
                    ·
                      rfl

theorem cell22_2584589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_2584589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2584589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2584589 prefixEnd_2584589 := by exact prefixLift 2584589
  have htrace : WordTrace (prefixWord ++ tailWord_2584589) baseStart_2584589 baseEnd_2584589 := by
    simpa [prefixWord, tailWord_2584589, baseEnd_2584589] using wordTrace_append hprefix tailTrace_2584589
  have hstable : (prefixWord ++ tailWord_2584589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2584589).length < 2 ^ (prefixWord ++ tailWord_2584589).sum := by decide
  have hdescent : baseEnd_2584589 < baseStart_2584589 := by decide
  rcases family_descends (prefixWord ++ tailWord_2584589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2584592 : List Nat := [2, 1, 1, 1, 1, 1, 1, 8, 2, 4]
def baseStart_2584592 : Nat := 118140960795 + 2584592 * 2 ^ 59
def prefixEnd_2584592 : Nat := 4983230072969 + 3 ^ 40 * 2584592 * 2
def baseEnd_2584592 : Nat := 884758661176971337075789

theorem tailTrace_2584592 : CollatzResearch.WordTrace tailWord_2584592 prefixEnd_2584592 884758661176971337075789 := by
  unfold tailWord_2584592
  simp only [CollatzResearch.WordTrace]
  refine ⟨47133907326236036008006015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62845209768314714677341353 47133907326236036008006015)
  ·
    refine ⟨70700860989354054012009023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47133907326236036008006015 70700860989354054012009023)
    ·
      refine ⟨106051291484031081018013535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70700860989354054012009023 106051291484031081018013535)
      ·
        refine ⟨159076937226046621527020303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106051291484031081018013535 159076937226046621527020303)
        ·
          refine ⟨238615405839069932290530455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159076937226046621527020303 238615405839069932290530455)
          ·
            refine ⟨357923108758604898435795683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 238615405839069932290530455 357923108758604898435795683)
            ·
              refine ⟨536884663137907347653693525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 357923108758604898435795683 536884663137907347653693525)
              ·
                refine ⟨6291617146147351730316721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 536884663137907347653693525 6291617146147351730316721)
                ·
                  refine ⟨4718712859610513797737541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6291617146147351730316721 4718712859610513797737541)
                  ·
                    refine ⟨884758661176971337075789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4718712859610513797737541 884758661176971337075789)
                    ·
                      rfl

theorem cell22_2584592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 8, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 8, 2, 4].length) (baseStart_2584592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2584592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2584592 prefixEnd_2584592 := by exact prefixLift 2584592
  have htrace : WordTrace (prefixWord ++ tailWord_2584592) baseStart_2584592 baseEnd_2584592 := by
    simpa [prefixWord, tailWord_2584592, baseEnd_2584592] using wordTrace_append hprefix tailTrace_2584592
  have hstable : (prefixWord ++ tailWord_2584592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2584592).length < 2 ^ (prefixWord ++ tailWord_2584592).sum := by decide
  have hdescent : baseEnd_2584592 < baseStart_2584592 := by decide
  rcases family_descends (prefixWord ++ tailWord_2584592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2584607 : List Nat := [1, 1, 2, 4, 1, 2, 4, 7]
def baseStart_2584607 : Nat := 118140960795 + 2584607 * 2 ^ 59
def prefixEnd_2584607 : Nat := 4983230072969 + 3 ^ 40 * 2584607 * 2
def baseEnd_2584607 : Nat := 98307088442612921994527

theorem tailTrace_2584607 : CollatzResearch.WordTrace tailWord_2584607 prefixEnd_2584607 98307088442612921994527 := by
  unfold tailWord_2584607
  simp only [CollatzResearch.WordTrace]
  refine ⟨94268361747417729577808075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62845574498278486385205383 94268361747417729577808075)
  ·
    refine ⟨141402542621126594366712113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94268361747417729577808075 141402542621126594366712113)
    ·
      refine ⟨106051906965844945775034085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141402542621126594366712113 106051906965844945775034085)
      ·
        refine ⟨19884732556095927332818891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 106051906965844945775034085 19884732556095927332818891)
        ·
          refine ⟨29827098834143890999228337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19884732556095927332818891 29827098834143890999228337)
          ·
            refine ⟨22370324125607918249421253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29827098834143890999228337 22370324125607918249421253)
            ·
              refine ⟨4194435773551484671766485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22370324125607918249421253 4194435773551484671766485)
              ·
                refine ⟨98307088442612921994527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4194435773551484671766485 98307088442612921994527)
                ·
                  rfl

theorem cell22_2584607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 4, 7].length) (baseStart_2584607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2584607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2584607 prefixEnd_2584607 := by exact prefixLift 2584607
  have htrace : WordTrace (prefixWord ++ tailWord_2584607) baseStart_2584607 baseEnd_2584607 := by
    simpa [prefixWord, tailWord_2584607, baseEnd_2584607] using wordTrace_append hprefix tailTrace_2584607
  have hstable : (prefixWord ++ tailWord_2584607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2584607).length < 2 ^ (prefixWord ++ tailWord_2584607).sum := by decide
  have hdescent : baseEnd_2584607 < baseStart_2584607 := by decide
  rcases family_descends (prefixWord ++ tailWord_2584607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2584615 : List Nat := [1, 1, 7, 1, 3, 1, 1, 2, 1, 4]
def baseStart_2584615 : Nat := 118140960795 + 2584615 * 2 ^ 59
def prefixEnd_2584615 : Nat := 4983230072969 + 3 ^ 40 * 2584615 * 2
def baseEnd_2584615 : Nat := 884766534547006943750719

theorem tailTrace_2584615 : CollatzResearch.WordTrace tailWord_2584615 prefixEnd_2584615 884766534547006943750719 := by
  unfold tailWord_2584615
  simp only [CollatzResearch.WordTrace]
  refine ⟨94268653531388746944099299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62845769020925831296066199 94268653531388746944099299)
  ·
    refine ⟨141402980297083120416148949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94268653531388746944099299 141402980297083120416148949)
    ·
      refine ⟨3314132350712885634753491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 141402980297083120416148949 3314132350712885634753491)
      ·
        refine ⟨4971198526069328452130237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3314132350712885634753491 4971198526069328452130237)
        ·
          refine ⟨1864199447275998169548839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4971198526069328452130237 1864199447275998169548839)
          ·
            refine ⟨2796299170913997254323259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1864199447275998169548839 2796299170913997254323259)
            ·
              refine ⟨4194448756370995881484889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2796299170913997254323259 4194448756370995881484889)
              ·
                refine ⟨3145836567278246911113667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4194448756370995881484889 3145836567278246911113667)
                ·
                  refine ⟨4718754850917370366670501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3145836567278246911113667 4718754850917370366670501)
                  ·
                    refine ⟨884766534547006943750719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4718754850917370366670501 884766534547006943750719)
                    ·
                      rfl

theorem cell22_2584615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_2584615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2584615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2584615 prefixEnd_2584615 := by exact prefixLift 2584615
  have htrace : WordTrace (prefixWord ++ tailWord_2584615) baseStart_2584615 baseEnd_2584615 := by
    simpa [prefixWord, tailWord_2584615, baseEnd_2584615] using wordTrace_append hprefix tailTrace_2584615
  have hstable : (prefixWord ++ tailWord_2584615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2584615).length < 2 ^ (prefixWord ++ tailWord_2584615).sum := by decide
  have hdescent : baseEnd_2584615 < baseStart_2584615 := by decide
  rcases family_descends (prefixWord ++ tailWord_2584615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2584652 : List Nat := [2, 2, 1, 3, 1, 1, 2, 3, 7]
def baseStart_2584652 : Nat := 118140960795 + 2584652 * 2 ^ 59
def prefixEnd_2584652 : Nat := 4983230072969 + 3 ^ 40 * 2584652 * 2
def baseEnd_2584652 : Nat := 294926400134383726858535

theorem tailTrace_2584652 : CollatzResearch.WordTrace tailWord_2584652 prefixEnd_2584652 294926400134383726858535 := by
  unfold tailWord_2584652
  simp only [CollatzResearch.WordTrace]
  refine ⟨47135001516127351131598105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62846668688169801508797473 47135001516127351131598105)
  ·
    refine ⟨35351251137095513348698579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47135001516127351131598105 35351251137095513348698579)
    ·
      refine ⟨53026876705643270023047869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35351251137095513348698579 53026876705643270023047869)
      ·
        refine ⟨19885078764616226258642951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53026876705643270023047869 19885078764616226258642951)
        ·
          refine ⟨29827618146924339387964427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19885078764616226258642951 29827618146924339387964427)
          ·
            refine ⟨44741427220386509081946641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29827618146924339387964427 44741427220386509081946641)
            ·
              refine ⟨33556070415289881811459981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44741427220386509081946641 33556070415289881811459981)
              ·
                refine ⟨12583526405733705679297493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33556070415289881811459981 12583526405733705679297493)
                ·
                  refine ⟨294926400134383726858535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12583526405733705679297493 294926400134383726858535)
                  ·
                    rfl

theorem cell22_2584652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 3, 7].length) (baseStart_2584652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2584652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2584652 prefixEnd_2584652 := by exact prefixLift 2584652
  have htrace : WordTrace (prefixWord ++ tailWord_2584652) baseStart_2584652 baseEnd_2584652 := by
    simpa [prefixWord, tailWord_2584652, baseEnd_2584652] using wordTrace_append hprefix tailTrace_2584652
  have hstable : (prefixWord ++ tailWord_2584652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2584652).length < 2 ^ (prefixWord ++ tailWord_2584652).sum := by decide
  have hdescent : baseEnd_2584652 < baseStart_2584652 := by decide
  rcases family_descends (prefixWord ++ tailWord_2584652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2584714 : List Nat := [3, 1, 2, 3, 1, 2, 1, 3, 6]
def baseStart_2584714 : Nat := 118140960795 + 2584714 * 2 ^ 59
def prefixEnd_2584714 : Nat := 4983230072969 + 3 ^ 40 * 2584714 * 2
def baseEnd_2584714 : Nat := 294933474756734561841805

theorem tailTrace_2584714 : CollatzResearch.WordTrace tailWord_2584714 prefixEnd_2584714 294933474756734561841805 := by
  unfold tailWord_2584714
  simp only [CollatzResearch.WordTrace]
  refine ⟨23568066089507521712988299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62848176238686724567968797 23568066089507521712988299)
  ·
    refine ⟨35352099134261282569482449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23568066089507521712988299 35352099134261282569482449)
    ·
      refine ⟨26514074350695961927111837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35352099134261282569482449 26514074350695961927111837)
      ·
        refine ⟨9942777881510985722666939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26514074350695961927111837 9942777881510985722666939)
        ·
          refine ⟨14914166822266478584000409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9942777881510985722666939 14914166822266478584000409)
          ·
            refine ⟨11185625116699858938000307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14914166822266478584000409 11185625116699858938000307)
            ·
              refine ⟨16778437675049788407000461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11185625116699858938000307 16778437675049788407000461)
              ·
                refine ⟨6291914128143670652625173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16778437675049788407000461 6291914128143670652625173)
                ·
                  refine ⟨294933474756734561841805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6291914128143670652625173 294933474756734561841805)
                  ·
                    rfl

theorem cell22_2584714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 3, 6].length) (baseStart_2584714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2584714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2584714 prefixEnd_2584714 := by exact prefixLift 2584714
  have htrace : WordTrace (prefixWord ++ tailWord_2584714) baseStart_2584714 baseEnd_2584714 := by
    simpa [prefixWord, tailWord_2584714, baseEnd_2584714] using wordTrace_append hprefix tailTrace_2584714
  have hstable : (prefixWord ++ tailWord_2584714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2584714).length < 2 ^ (prefixWord ++ tailWord_2584714).sum := by decide
  have hdescent : baseEnd_2584714 < baseStart_2584714 := by decide
  rcases family_descends (prefixWord ++ tailWord_2584714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2584759 : List Nat := [1, 1, 3, 1, 4, 4, 8]
def baseStart_2584759 : Nat := 118140960795 + 2584759 * 2 ^ 59
def prefixEnd_2584759 : Nat := 4983230072969 + 3 ^ 40 * 2584759 * 2
def baseEnd_2584759 : Nat := 32770956618142169190751

theorem tailTrace_2584759 : CollatzResearch.WordTrace tailWord_2584759 prefixEnd_2584759 32770956618142169190751 := by
  unfold tailWord_2584759
  simp only [CollatzResearch.WordTrace]
  refine ⟨94273905642867059537341331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62849270428578039691560887 94273905642867059537341331)
  ·
    refine ⟨141410858464300589306011997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94273905642867059537341331 141410858464300589306011997)
    ·
      refine ⟨53029071924112720989754499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141410858464300589306011997 53029071924112720989754499)
      ·
        refine ⟨79543607886169081484631749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53029071924112720989754499 79543607886169081484631749)
        ·
          refine ⟨14914426478656702778368453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 79543607886169081484631749 14914426478656702778368453)
          ·
            refine ⟨2796454964748131770944085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14914426478656702778368453 2796454964748131770944085)
            ·
              refine ⟨32770956618142169190751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2796454964748131770944085 32770956618142169190751)
              ·
                rfl

theorem cell22_2584759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 8].length) (baseStart_2584759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2584759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2584759 prefixEnd_2584759 := by exact prefixLift 2584759
  have htrace : WordTrace (prefixWord ++ tailWord_2584759) baseStart_2584759 baseEnd_2584759 := by
    simpa [prefixWord, tailWord_2584759, baseEnd_2584759] using wordTrace_append hprefix tailTrace_2584759
  have hstable : (prefixWord ++ tailWord_2584759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2584759).length < 2 ^ (prefixWord ++ tailWord_2584759).sum := by decide
  have hdescent : baseEnd_2584759 < baseStart_2584759 := by decide
  rcases family_descends (prefixWord ++ tailWord_2584759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2584780 : List Nat := [2, 2, 1, 6, 1, 1, 1, 3, 2, 3]
def baseStart_2584780 : Nat := 118140960795 + 2584780 * 2 ^ 59
def prefixEnd_2584780 : Nat := 4983230072969 + 3 ^ 40 * 2584780 * 2
def baseEnd_2584780 : Nat := 884823017419001513375213

theorem tailTrace_2584780 : CollatzResearch.WordTrace tailWord_2584780 prefixEnd_2584780 884823017419001513375213 := by
  unfold tailWord_2584780
  simp only [CollatzResearch.WordTrace]
  refine ⟨47137335787895490061927897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62849781050527320082570529 47137335787895490061927897)
  ·
    refine ⟨35353001840921617546445923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47137335787895490061927897 35353001840921617546445923)
    ·
      refine ⟨53029502761382426319668885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35353001840921617546445923 53029502761382426319668885)
      ·
        refine ⟨2485757941939801233734479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 53029502761382426319668885 2485757941939801233734479)
        ·
          refine ⟨3728636912909701850601719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2485757941939801233734479 3728636912909701850601719)
          ·
            refine ⟨5592955369364552775902579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3728636912909701850601719 5592955369364552775902579)
            ·
              refine ⟨8389433054046829163853869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5592955369364552775902579 8389433054046829163853869)
              ·
                refine ⟨3146037395267560936445201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8389433054046829163853869 3146037395267560936445201)
                ·
                  refine ⟨2359528046450670702333901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3146037395267560936445201 2359528046450670702333901)
                  ·
                    refine ⟨884823017419001513375213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2359528046450670702333901 884823017419001513375213)
                    ·
                      rfl

theorem cell22_2584780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 3, 2, 3].length) (baseStart_2584780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2584780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2584780 prefixEnd_2584780 := by exact prefixLift 2584780
  have htrace : WordTrace (prefixWord ++ tailWord_2584780) baseStart_2584780 baseEnd_2584780 := by
    simpa [prefixWord, tailWord_2584780, baseEnd_2584780] using wordTrace_append hprefix tailTrace_2584780
  have hstable : (prefixWord ++ tailWord_2584780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2584780).length < 2 ^ (prefixWord ++ tailWord_2584780).sum := by decide
  have hdescent : baseEnd_2584780 < baseStart_2584780 := by decide
  rcases family_descends (prefixWord ++ tailWord_2584780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2584819 : List Nat := [1, 1, 1, 2, 2, 4, 2, 2, 2, 5]
def baseStart_2584819 : Nat := 118140960795 + 2584819 * 2 ^ 59
def prefixEnd_2584819 : Nat := 4983230072969 + 3 ^ 40 * 2584819 * 2
def baseEnd_2584819 : Nat := 884836367916018411650093

theorem tailTrace_2584819 : CollatzResearch.WordTrace tailWord_2584819 prefixEnd_2584819 884836367916018411650093 := by
  unfold tailWord_2584819
  simp only [CollatzResearch.WordTrace]
  refine ⟨94276094022649689784525511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62850729348433126523017007 94276094022649689784525511)
  ·
    refine ⟨141414141033974534676788267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94276094022649689784525511 141414141033974534676788267)
    ·
      refine ⟨212121211550961802015182401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141414141033974534676788267 212121211550961802015182401)
      ·
        refine ⟨159090908663221351511386801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 212121211550961802015182401 159090908663221351511386801)
        ·
          refine ⟨119318181497416013633540101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 159090908663221351511386801 119318181497416013633540101)
          ·
            refine ⟨22372159030765502556288769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 119318181497416013633540101 22372159030765502556288769)
            ·
              refine ⟨16779119273074126917216577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22372159030765502556288769 16779119273074126917216577)
              ·
                refine ⟨12584339454805595187912433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16779119273074126917216577 12584339454805595187912433)
                ·
                  refine ⟨9438254591104196390934325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12584339454805595187912433 9438254591104196390934325)
                  ·
                    refine ⟨884836367916018411650093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9438254591104196390934325 884836367916018411650093)
                    ·
                      rfl

theorem cell22_2584819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 2, 2, 5].length) (baseStart_2584819 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2584819 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2584819 prefixEnd_2584819 := by exact prefixLift 2584819
  have htrace : WordTrace (prefixWord ++ tailWord_2584819) baseStart_2584819 baseEnd_2584819 := by
    simpa [prefixWord, tailWord_2584819, baseEnd_2584819] using wordTrace_append hprefix tailTrace_2584819
  have hstable : (prefixWord ++ tailWord_2584819).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2584819).length < 2 ^ (prefixWord ++ tailWord_2584819).sum := by decide
  have hdescent : baseEnd_2584819 < baseStart_2584819 := by decide
  rcases family_descends (prefixWord ++ tailWord_2584819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2584849 : List Nat := [1, 2, 2, 1, 1, 5, 1, 1, 8]
def baseStart_2584849 : Nat := 118140960795 + 2584849 * 2 ^ 59
def prefixEnd_2584849 : Nat := 4983230072969 + 3 ^ 40 * 2584849 * 2
def baseEnd_2584849 : Nat := 294948879176369444466667

theorem tailTrace_2584849 : CollatzResearch.WordTrace tailWord_2584849 prefixEnd_2584849 294948879176369444466667 := by
  unfold tailWord_2584849
  simp only [CollatzResearch.WordTrace]
  refine ⟨94277188212541004908117601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62851458808360669938745067 94277188212541004908117601)
  ·
    refine ⟨70707891159405753681088201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94277188212541004908117601 70707891159405753681088201)
    ·
      refine ⟨53030918369554315260816151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70707891159405753681088201 53030918369554315260816151)
      ·
        refine ⟨79546377554331472891224227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53030918369554315260816151 79546377554331472891224227)
        ·
          refine ⟨119319566331497209336836341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79546377554331472891224227 119319566331497209336836341)
          ·
            refine ⟨11186209343577863375328407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 119319566331497209336836341 11186209343577863375328407)
            ·
              refine ⟨16779314015366795062992611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11186209343577863375328407 16779314015366795062992611)
              ·
                refine ⟨25168971023050192594488917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16779314015366795062992611 25168971023050192594488917)
                ·
                  refine ⟨294948879176369444466667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25168971023050192594488917 294948879176369444466667)
                  ·
                    rfl

theorem cell22_2584849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 1, 8].length) (baseStart_2584849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2584849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2584849 prefixEnd_2584849 := by exact prefixLift 2584849
  have htrace : WordTrace (prefixWord ++ tailWord_2584849) baseStart_2584849 baseEnd_2584849 := by
    simpa [prefixWord, tailWord_2584849, baseEnd_2584849] using wordTrace_append hprefix tailTrace_2584849
  have hstable : (prefixWord ++ tailWord_2584849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2584849).length < 2 ^ (prefixWord ++ tailWord_2584849).sum := by decide
  have hdescent : baseEnd_2584849 < baseStart_2584849 := by decide
  rcases family_descends (prefixWord ++ tailWord_2584849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2584868 : List Nat := [2, 3, 1, 3, 1, 3, 1, 3, 1, 4]
def baseStart_2584868 : Nat := 118140960795 + 2584868 * 2 ^ 59
def prefixEnd_2584868 : Nat := 4983230072969 + 3 ^ 40 * 2584868 * 2
def baseEnd_2584868 : Nat := 884853141617398617174943

theorem tailTrace_2584868 : CollatzResearch.WordTrace tailWord_2584868 prefixEnd_2584868 884853141617398617174943 := by
  unfold tailWord_2584868
  simp only [CollatzResearch.WordTrace]
  refine ⟨47138940599736085576529629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62851920799648114102039505 47138940599736085576529629)
  ·
    refine ⟨17677102724901032091198611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47138940599736085576529629 17677102724901032091198611)
    ·
      refine ⟨26515654087351548136797917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17677102724901032091198611 26515654087351548136797917)
      ·
        refine ⟨9943370282756830551299219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26515654087351548136797917 9943370282756830551299219)
        ·
          refine ⟨14915055424135245826948829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9943370282756830551299219 14915055424135245826948829)
          ·
            refine ⟨5593145784050717185105811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14915055424135245826948829 5593145784050717185105811)
            ·
              refine ⟨8389718676076075777658717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5593145784050717185105811 8389718676076075777658717)
              ·
                refine ⟨3146144503528528416622019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8389718676076075777658717 3146144503528528416622019)
                ·
                  refine ⟨4719216755292792624933029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3146144503528528416622019 4719216755292792624933029)
                  ·
                    refine ⟨884853141617398617174943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4719216755292792624933029 884853141617398617174943)
                    ·
                      rfl

theorem cell22_2584868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 3, 1, 4].length) (baseStart_2584868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2584868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2584868 prefixEnd_2584868 := by exact prefixLift 2584868
  have htrace : WordTrace (prefixWord ++ tailWord_2584868) baseStart_2584868 baseEnd_2584868 := by
    simpa [prefixWord, tailWord_2584868, baseEnd_2584868] using wordTrace_append hprefix tailTrace_2584868
  have hstable : (prefixWord ++ tailWord_2584868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2584868).length < 2 ^ (prefixWord ++ tailWord_2584868).sum := by decide
  have hdescent : baseEnd_2584868 < baseStart_2584868 := by decide
  rcases family_descends (prefixWord ++ tailWord_2584868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2584917 : List Nat := [1, 3, 2, 2, 5, 1, 1, 3, 4]
def baseStart_2584917 : Nat := 118140960795 + 2584917 * 2 ^ 59
def prefixEnd_2584917 : Nat := 4983230072969 + 3 ^ 40 * 2584917 * 2
def baseEnd_2584917 : Nat := 294956638439592940899931

theorem tailTrace_2584917 : CollatzResearch.WordTrace tailWord_2584917 prefixEnd_2584917 294956638439592940899931 := by
  unfold tailWord_2584917
  simp only [CollatzResearch.WordTrace]
  refine ⟨94279668376294652521593005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62853112250863101681062003 94279668376294652521593005)
  ·
    refine ⟨35354875641110494695597377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94279668376294652521593005 35354875641110494695597377)
    ·
      refine ⟨26516156730832871021698033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35354875641110494695597377 26516156730832871021698033)
      ·
        refine ⟨19887117548124653266273525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26516156730832871021698033 19887117548124653266273525)
        ·
          refine ⟨1864417270136686243713143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19887117548124653266273525 1864417270136686243713143)
          ·
            refine ⟨2796625905205029365569715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1864417270136686243713143 2796625905205029365569715)
            ·
              refine ⟨4194938857807544048354573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2796625905205029365569715 4194938857807544048354573)
              ·
                refine ⟨1573102071677829018132965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4194938857807544048354573 1573102071677829018132965)
                ·
                  refine ⟨294956638439592940899931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1573102071677829018132965 294956638439592940899931)
                  ·
                    rfl

theorem cell22_2584917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 1, 3, 4].length) (baseStart_2584917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2584917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2584917 prefixEnd_2584917 := by exact prefixLift 2584917
  have htrace : WordTrace (prefixWord ++ tailWord_2584917) baseStart_2584917 baseEnd_2584917 := by
    simpa [prefixWord, tailWord_2584917, baseEnd_2584917] using wordTrace_append hprefix tailTrace_2584917
  have hstable : (prefixWord ++ tailWord_2584917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2584917).length < 2 ^ (prefixWord ++ tailWord_2584917).sum := by decide
  have hdescent : baseEnd_2584917 < baseStart_2584917 := by decide
  rcases family_descends (prefixWord ++ tailWord_2584917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2584928 : List Nat := [2, 1, 1, 3, 6, 1, 8]
def baseStart_2584928 : Nat := 118140960795 + 2584928 * 2 ^ 59
def prefixEnd_2584928 : Nat := 4983230072969 + 3 ^ 40 * 2584928 * 2
def baseEnd_2584928 : Nat := 32773099290502905950917

theorem tailTrace_2584928 : CollatzResearch.WordTrace tailWord_2584928 prefixEnd_2584928 32773099290502905950917 := by
  unfold tailWord_2584928
  simp only [CollatzResearch.WordTrace]
  refine ⟨47140034789627400700121719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62853379719503200933495625 47140034789627400700121719)
  ·
    refine ⟨70710052184441101050182579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47140034789627400700121719 70710052184441101050182579)
    ·
      refine ⟨106065078276661651575273869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70710052184441101050182579 106065078276661651575273869)
      ·
        refine ⟨39774404353748119340727701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106065078276661651575273869 39774404353748119340727701)
        ·
          refine ⟨1864425204081943094096611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 39774404353748119340727701 1864425204081943094096611)
          ·
            refine ⟨2796637806122914641144917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1864425204081943094096611 2796637806122914641144917)
            ·
              refine ⟨32773099290502905950917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2796637806122914641144917 32773099290502905950917)
              ·
                rfl

theorem cell22_2584928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 8].length) (baseStart_2584928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2584928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2584928 prefixEnd_2584928 := by exact prefixLift 2584928
  have htrace : WordTrace (prefixWord ++ tailWord_2584928) baseStart_2584928 baseEnd_2584928 := by
    simpa [prefixWord, tailWord_2584928, baseEnd_2584928] using wordTrace_append hprefix tailTrace_2584928
  have hstable : (prefixWord ++ tailWord_2584928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2584928).length < 2 ^ (prefixWord ++ tailWord_2584928).sum := by decide
  have hdescent : baseEnd_2584928 < baseStart_2584928 := by decide
  rcases family_descends (prefixWord ++ tailWord_2584928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2584941 : List Nat := [1, 5, 1, 1, 1, 2, 2, 1, 2, 6]
def baseStart_2584941 : Nat := 118140960795 + 2584941 * 2 ^ 59
def prefixEnd_2584941 : Nat := 4983230072969 + 3 ^ 40 * 2584941 * 2
def baseEnd_2584941 : Nat := 884878131009250760099719

theorem tailTrace_2584941 : CollatzResearch.WordTrace tailWord_2584941 prefixEnd_2584941 884878131009250760099719 := by
  unfold tailWord_2584941
  simp only [CollatzResearch.WordTrace]
  refine ⟨94280543728207704620466677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62853695818805136413644451 94280543728207704620466677)
  ·
    refine ⟨8838800974519472308168751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 94280543728207704620466677 8838800974519472308168751)
    ·
      refine ⟨13258201461779208462253127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8838800974519472308168751 13258201461779208462253127)
      ·
        refine ⟨19887302192668812693379691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13258201461779208462253127 19887302192668812693379691)
        ·
          refine ⟨29830953289003219040069537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19887302192668812693379691 29830953289003219040069537)
          ·
            refine ⟨22373214966752414280052153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29830953289003219040069537 22373214966752414280052153)
            ·
              refine ⟨16779911225064310710039115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22373214966752414280052153 16779911225064310710039115)
              ·
                refine ⟨25169866837596466065058673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16779911225064310710039115 25169866837596466065058673)
                ·
                  refine ⟨18877400128197349548794005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25169866837596466065058673 18877400128197349548794005)
                  ·
                    refine ⟨884878131009250760099719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18877400128197349548794005 884878131009250760099719)
                    ·
                      rfl

theorem cell22_2584941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 1, 2, 6].length) (baseStart_2584941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2584941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2584941 prefixEnd_2584941 := by exact prefixLift 2584941
  have htrace : WordTrace (prefixWord ++ tailWord_2584941) baseStart_2584941 baseEnd_2584941 := by
    simpa [prefixWord, tailWord_2584941, baseEnd_2584941] using wordTrace_append hprefix tailTrace_2584941
  have hstable : (prefixWord ++ tailWord_2584941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2584941).length < 2 ^ (prefixWord ++ tailWord_2584941).sum := by decide
  have hdescent : baseEnd_2584941 < baseStart_2584941 := by decide
  rcases family_descends (prefixWord ++ tailWord_2584941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2584990 : List Nat := [4, 3, 1, 2, 1, 1, 1, 4, 5]
def baseStart_2584990 : Nat := 118140960795 + 2584990 * 2 ^ 59
def prefixEnd_2584990 : Nat := 4983230072969 + 3 ^ 40 * 2584990 * 2
def baseEnd_2584990 : Nat := 294964968236876988541523

theorem tailTrace_2584990 : CollatzResearch.WordTrace tailWord_2584990 prefixEnd_2584990 294964968236876988541523 := by
  unfold tailWord_2584990
  simp only [CollatzResearch.WordTrace]
  refine ⟨11785291363128773248625053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62854887270020123992666949 11785291363128773248625053)
  ·
    refine ⟨4419484261173289968234395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11785291363128773248625053 4419484261173289968234395)
    ·
      refine ⟨6629226391759934952351593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4419484261173289968234395 6629226391759934952351593)
      ·
        refine ⟨4971919793819951214263695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6629226391759934952351593 4971919793819951214263695)
        ·
          refine ⟨7457879690729926821395543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4971919793819951214263695 7457879690729926821395543)
          ·
            refine ⟨11186819536094890232093315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7457879690729926821395543 11186819536094890232093315)
            ·
              refine ⟨16780229304142335348139973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11186819536094890232093315 16780229304142335348139973)
              ·
                refine ⟨3146292994526687877776245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16780229304142335348139973 3146292994526687877776245)
                ·
                  refine ⟨294964968236876988541523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3146292994526687877776245 294964968236876988541523)
                  ·
                    rfl

theorem cell22_2584990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 4, 5].length) (baseStart_2584990 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2584990 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2584990 prefixEnd_2584990 := by exact prefixLift 2584990
  have htrace : WordTrace (prefixWord ++ tailWord_2584990) baseStart_2584990 baseEnd_2584990 := by
    simpa [prefixWord, tailWord_2584990, baseEnd_2584990] using wordTrace_append hprefix tailTrace_2584990
  have hstable : (prefixWord ++ tailWord_2584990).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2584990).length < 2 ^ (prefixWord ++ tailWord_2584990).sum := by decide
  have hdescent : baseEnd_2584990 < baseStart_2584990 := by decide
  rcases family_descends (prefixWord ++ tailWord_2584990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2585005 : List Nat := [1, 5, 2, 2, 2, 1, 1, 1, 2, 5]
def baseStart_2585005 : Nat := 118140960795 + 2585005 * 2 ^ 59
def prefixEnd_2585005 : Nat := 4983230072969 + 3 ^ 40 * 2585005 * 2
def baseEnd_2585005 : Nat := 884900039517175926499523

theorem tailTrace_2585005 : CollatzResearch.WordTrace tailWord_2585005 prefixEnd_2585005 884900039517175926499523 := by
  unfold tailWord_2585005
  simp only [CollatzResearch.WordTrace]
  refine ⟨94282877999975843550796469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62855251999983895700530979 94282877999975843550796469)
  ·
    refine ⟨8839019812497735332887169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 94282877999975843550796469 8839019812497735332887169)
    ·
      refine ⟨6629264859373301499665377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8839019812497735332887169 6629264859373301499665377)
      ·
        refine ⟨4971948644529976124749033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6629264859373301499665377 4971948644529976124749033)
        ·
          refine ⟨3728961483397482093561775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4971948644529976124749033 3728961483397482093561775)
          ·
            refine ⟨5593442225096223140342663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3728961483397482093561775 5593442225096223140342663)
            ·
              refine ⟨8390163337644334710513995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5593442225096223140342663 8390163337644334710513995)
              ·
                refine ⟨12585245006466502065770993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8390163337644334710513995 12585245006466502065770993)
                ·
                  refine ⟨9438933754849876549328245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12585245006466502065770993 9438933754849876549328245)
                  ·
                    refine ⟨884900039517175926499523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9438933754849876549328245 884900039517175926499523)
                    ·
                      rfl

theorem cell22_2585005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_2585005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2585005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2585005 prefixEnd_2585005 := by exact prefixLift 2585005
  have htrace : WordTrace (prefixWord ++ tailWord_2585005) baseStart_2585005 baseEnd_2585005 := by
    simpa [prefixWord, tailWord_2585005, baseEnd_2585005] using wordTrace_append hprefix tailTrace_2585005
  have hstable : (prefixWord ++ tailWord_2585005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2585005).length < 2 ^ (prefixWord ++ tailWord_2585005).sum := by decide
  have hdescent : baseEnd_2585005 < baseStart_2585005 := by decide
  rcases family_descends (prefixWord ++ tailWord_2585005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2585078 : List Nat := [5, 1, 1, 1, 2, 1, 1, 1, 2, 7]
def baseStart_2585078 : Nat := 118140960795 + 2585078 * 2 ^ 59
def prefixEnd_2585078 : Nat := 4983230072969 + 3 ^ 40 * 2585078 * 2
def baseEnd_2585078 : Nat := 884925028909028069424299

theorem tailTrace_2585078 : CollatzResearch.WordTrace tailWord_2585078 prefixEnd_2585078 884925028909028069424299 := by
  unfold tailWord_2585078
  simp only [CollatzResearch.WordTrace]
  refine ⟨5892846283044461063637743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 62857027019140918012135925 5892846283044461063637743)
  ·
    refine ⟨8839269424566691595456615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5892846283044461063637743 8839269424566691595456615)
    ·
      refine ⟨13258904136850037393184923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8839269424566691595456615 13258904136850037393184923)
      ·
        refine ⟨19888356205275056089777385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13258904136850037393184923 19888356205275056089777385)
        ·
          refine ⟨14916267153956292067333039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19888356205275056089777385 14916267153956292067333039)
          ·
            refine ⟨22374400730934438100999559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14916267153956292067333039 22374400730934438100999559)
            ·
              refine ⟨33561601096401657151499339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22374400730934438100999559 33561601096401657151499339)
              ·
                refine ⟨50342401644602485727249009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33561601096401657151499339 50342401644602485727249009)
                ·
                  refine ⟨37756801233451864295436757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50342401644602485727249009 37756801233451864295436757)
                  ·
                    refine ⟨884925028909028069424299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37756801233451864295436757 884925028909028069424299)
                    ·
                      rfl

theorem cell22_2585078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 2, 7].length) (baseStart_2585078 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2585078 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2585078 prefixEnd_2585078 := by exact prefixLift 2585078
  have htrace : WordTrace (prefixWord ++ tailWord_2585078) baseStart_2585078 baseEnd_2585078 := by
    simpa [prefixWord, tailWord_2585078, baseEnd_2585078] using wordTrace_append hprefix tailTrace_2585078
  have hstable : (prefixWord ++ tailWord_2585078).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2585078).length < 2 ^ (prefixWord ++ tailWord_2585078).sum := by decide
  have hdescent : baseEnd_2585078 < baseStart_2585078 := by decide
  rcases family_descends (prefixWord ++ tailWord_2585078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2585091 : List Nat := [1, 1, 1, 3, 2, 1, 3, 1, 9]
def baseStart_2585091 : Nat := 118140960795 + 2585091 * 2 ^ 59
def prefixEnd_2585091 : Nat := 4983230072969 + 3 ^ 40 * 2585091 * 2
def baseEnd_2585091 : Nat := 294976493024900122949753

theorem tailTrace_2585091 : CollatzResearch.WordTrace tailWord_2585091 prefixEnd_2585091 294976493024900122949753 := by
  unfold tailWord_2585091
  simp only [CollatzResearch.WordTrace]
  refine ⟨94286014677664280238427127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62857343118442853492284751 94286014677664280238427127)
  ·
    refine ⟨141429022016496420357640691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94286014677664280238427127 141429022016496420357640691)
    ·
      refine ⟨212143533024744630536461037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141429022016496420357640691 212143533024744630536461037)
      ·
        refine ⟨79553824884279236451172889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 212143533024744630536461037 79553824884279236451172889)
        ·
          refine ⟨59665368663209427338379667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79553824884279236451172889 59665368663209427338379667)
          ·
            refine ⟨89498052994814141007569501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59665368663209427338379667 89498052994814141007569501)
            ·
              refine ⟨33561769873055302877838563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89498052994814141007569501 33561769873055302877838563)
              ·
                refine ⟨50342654809582954316757845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33561769873055302877838563 50342654809582954316757845)
                ·
                  refine ⟨294976493024900122949753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 50342654809582954316757845 294976493024900122949753)
                  ·
                    rfl

theorem cell22_2585091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 9].length) (baseStart_2585091 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2585091 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2585091 prefixEnd_2585091 := by exact prefixLift 2585091
  have htrace : WordTrace (prefixWord ++ tailWord_2585091) baseStart_2585091 baseEnd_2585091 := by
    simpa [prefixWord, tailWord_2585091, baseEnd_2585091] using wordTrace_append hprefix tailTrace_2585091
  have hstable : (prefixWord ++ tailWord_2585091).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2585091).length < 2 ^ (prefixWord ++ tailWord_2585091).sum := by decide
  have hdescent : baseEnd_2585091 < baseStart_2585091 := by decide
  rcases family_descends (prefixWord ++ tailWord_2585091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2585112 : List Nat := [2, 1, 2, 3, 3, 3, 1, 1, 3, 3]
def baseStart_2585112 : Nat := 118140960795 + 2585112 * 2 ^ 59
def prefixEnd_2585112 : Nat := 4983230072969 + 3 ^ 40 * 2585112 * 2
def baseEnd_2585112 : Nat := 884936667803863314074195

theorem tailTrace_2585112 : CollatzResearch.WordTrace tailWord_2585112 prefixEnd_2585112 884936667803863314074195 := by
  unfold tailWord_2585112
  simp only [CollatzResearch.WordTrace]
  refine ⟨47143390305294100412470795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62857853740392133883294393 47143390305294100412470795)
  ·
    refine ⟨70715085457941150618706193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47143390305294100412470795 70715085457941150618706193)
    ·
      refine ⟨53036314093455862964029645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70715085457941150618706193 53036314093455862964029645)
      ·
        refine ⟨19888617785045948611511117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53036314093455862964029645 19888617785045948611511117)
        ·
          refine ⟨7458231669392230729316669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19888617785045948611511117 7458231669392230729316669)
          ·
            refine ⟨2796836876022086523493751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7458231669392230729316669 2796836876022086523493751)
            ·
              refine ⟨4195255314033129785240627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2796836876022086523493751 4195255314033129785240627)
              ·
                refine ⟨6292882971049694677860941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4195255314033129785240627 6292882971049694677860941)
                ·
                  refine ⟨2359831114143635504197853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6292882971049694677860941 2359831114143635504197853)
                  ·
                    refine ⟨884936667803863314074195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2359831114143635504197853 884936667803863314074195)
                    ·
                      rfl

theorem cell22_2585112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 1, 1, 3, 3].length) (baseStart_2585112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2585112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2585112 prefixEnd_2585112 := by exact prefixLift 2585112
  have htrace : WordTrace (prefixWord ++ tailWord_2585112) baseStart_2585112 baseEnd_2585112 := by
    simpa [prefixWord, tailWord_2585112, baseEnd_2585112] using wordTrace_append hprefix tailTrace_2585112
  have hstable : (prefixWord ++ tailWord_2585112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2585112).length < 2 ^ (prefixWord ++ tailWord_2585112).sum := by decide
  have hdescent : baseEnd_2585112 < baseStart_2585112 := by decide
  rcases family_descends (prefixWord ++ tailWord_2585112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2585125 : List Nat := [1, 3, 1, 2, 2, 1, 6, 1, 5]
def baseStart_2585125 : Nat := 118140960795 + 2585125 * 2 ^ 59
def prefixEnd_2585125 : Nat := 4983230072969 + 3 ^ 40 * 2585125 * 2
def baseEnd_2585125 : Nat := 294980372656511871166385

theorem tailTrace_2585125 : CollatzResearch.WordTrace tailWord_2585125 prefixEnd_2585125 294980372656511871166385 := by
  unfold tailWord_2585125
  simp only [CollatzResearch.WordTrace]
  refine ⟨94287254759541104045164829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62858169839694069363443219 94287254759541104045164829)
  ·
    refine ⟨35357720534827914016936811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94287254759541104045164829 35357720534827914016936811)
    ·
      refine ⟨53036580802241871025405217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35357720534827914016936811 53036580802241871025405217)
      ·
        refine ⟨39777435601681403269053913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53036580802241871025405217 39777435601681403269053913)
        ·
          refine ⟨29833076701261052451790435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39777435601681403269053913 29833076701261052451790435)
          ·
            refine ⟨44749615051891578677685653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29833076701261052451790435 44749615051891578677685653)
            ·
              refine ⟨2097638205557417750516515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 44749615051891578677685653 2097638205557417750516515)
              ·
                refine ⟨3146457308336126625774773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2097638205557417750516515 3146457308336126625774773)
                ·
                  refine ⟨294980372656511871166385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3146457308336126625774773 294980372656511871166385)
                  ·
                    rfl

theorem cell22_2585125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 6, 1, 5].length) (baseStart_2585125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2585125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2585125 prefixEnd_2585125 := by exact prefixLift 2585125
  have htrace : WordTrace (prefixWord ++ tailWord_2585125) baseStart_2585125 baseEnd_2585125 := by
    simpa [prefixWord, tailWord_2585125, baseEnd_2585125] using wordTrace_append hprefix tailTrace_2585125
  have hstable : (prefixWord ++ tailWord_2585125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2585125).length < 2 ^ (prefixWord ++ tailWord_2585125).sum := by decide
  have hdescent : baseEnd_2585125 < baseStart_2585125 := by decide
  rcases family_descends (prefixWord ++ tailWord_2585125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2585183 : List Nat := [1, 1, 2, 3, 1, 1, 1, 4, 4, 4]
def baseStart_2585183 : Nat := 118140960795 + 2585183 * 2 ^ 59
def prefixEnd_2585183 : Nat := 4983230072969 + 3 ^ 40 * 2585183 * 2
def baseEnd_2585183 : Nat := 884960972554842795548977

theorem tailTrace_2585183 : CollatzResearch.WordTrace tailWord_2585183 prefixEnd_2585183 884960972554842795548977 := by
  unfold tailWord_2585183
  simp only [CollatzResearch.WordTrace]
  refine ⟨94289370193330979950776203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62859580128887319967184135 94289370193330979950776203)
  ·
    refine ⟨141434055289996469926164305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94289370193330979950776203 141434055289996469926164305)
    ·
      refine ⟨106075541467497352444623229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141434055289996469926164305 106075541467497352444623229)
      ·
        refine ⟨39778328050311507166733711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106075541467497352444623229 39778328050311507166733711)
        ·
          refine ⟨59667492075467260750100567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39778328050311507166733711 59667492075467260750100567)
          ·
            refine ⟨89501238113200891125150851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59667492075467260750100567 89501238113200891125150851)
            ·
              refine ⟨134251857169801336687726277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89501238113200891125150851 134251857169801336687726277)
              ·
                refine ⟨25172223219337750628948677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 134251857169801336687726277 25172223219337750628948677)
                ·
                  refine ⟨4719791853625828242927877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25172223219337750628948677 4719791853625828242927877)
                  ·
                    refine ⟨884960972554842795548977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4719791853625828242927877 884960972554842795548977)
                    ·
                      rfl

theorem cell22_2585183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 4, 4, 4].length) (baseStart_2585183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2585183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2585183 prefixEnd_2585183 := by exact prefixLift 2585183
  have htrace : WordTrace (prefixWord ++ tailWord_2585183) baseStart_2585183 baseEnd_2585183 := by
    simpa [prefixWord, tailWord_2585183, baseEnd_2585183] using wordTrace_append hprefix tailTrace_2585183
  have hstable : (prefixWord ++ tailWord_2585183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2585183).length < 2 ^ (prefixWord ++ tailWord_2585183).sum := by decide
  have hdescent : baseEnd_2585183 < baseStart_2585183 := by decide
  rcases family_descends (prefixWord ++ tailWord_2585183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2585185 : List Nat := [1, 2, 3, 1, 1, 5, 2, 1, 1, 5]
def baseStart_2585185 : Nat := 118140960795 + 2585185 * 2 ^ 59
def prefixEnd_2585185 : Nat := 4983230072969 + 3 ^ 40 * 2585185 * 2
def baseEnd_2585185 : Nat := 884961657195715456998971

theorem tailTrace_2585185 : CollatzResearch.WordTrace tailWord_2585185 prefixEnd_2585185 884961657195715456998971 := by
  unfold tailWord_2585185
  simp only [CollatzResearch.WordTrace]
  refine ⟨94289443139323734292349009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62859628759549156194899339 94289443139323734292349009)
  ·
    refine ⟨70717082354492800719261757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94289443139323734292349009 70717082354492800719261757)
    ·
      refine ⟨26518905882934800269723159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70717082354492800719261757 26518905882934800269723159)
      ·
        refine ⟨39778358824402200404584739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26518905882934800269723159 39778358824402200404584739)
        ·
          refine ⟨59667538236603300606877109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39778358824402200404584739 59667538236603300606877109)
          ·
            refine ⟨5593831709681559431894729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 59667538236603300606877109 5593831709681559431894729)
            ·
              refine ⟨4195373782261169573921047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5593831709681559431894729 4195373782261169573921047)
              ·
                refine ⟨6293060673391754360881571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4195373782261169573921047 6293060673391754360881571)
                ·
                  refine ⟨9439591010087631541322357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6293060673391754360881571 9439591010087631541322357)
                  ·
                    refine ⟨884961657195715456998971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9439591010087631541322357 884961657195715456998971)
                    ·
                      rfl

theorem cell22_2585185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 2, 1, 1, 5].length) (baseStart_2585185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2585185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2585185 prefixEnd_2585185 := by exact prefixLift 2585185
  have htrace : WordTrace (prefixWord ++ tailWord_2585185) baseStart_2585185 baseEnd_2585185 := by
    simpa [prefixWord, tailWord_2585185, baseEnd_2585185] using wordTrace_append hprefix tailTrace_2585185
  have hstable : (prefixWord ++ tailWord_2585185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2585185).length < 2 ^ (prefixWord ++ tailWord_2585185).sum := by decide
  have hdescent : baseEnd_2585185 < baseStart_2585185 := by decide
  rcases family_descends (prefixWord ++ tailWord_2585185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2585200 : List Nat := [2, 1, 1, 1, 7, 1, 1, 1, 1, 6]
def baseStart_2585200 : Nat := 118140960795 + 2585200 * 2 ^ 59
def prefixEnd_2585200 : Nat := 4983230072969 + 3 ^ 40 * 2585200 * 2
def baseEnd_2585200 : Nat := 884966792002260417873925

theorem tailTrace_2585200 : CollatzResearch.WordTrace tailWord_2585200 prefixEnd_2585200 884966792002260417873925 := by
  unfold tailWord_2585200
  simp only [CollatzResearch.WordTrace]
  refine ⟨47144995117134695927072527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62859993489512927902763369 47144995117134695927072527)
  ·
    refine ⟨70717492675702043890608791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47144995117134695927072527 70717492675702043890608791)
    ·
      refine ⟨106076239013553065835913187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70717492675702043890608791 106076239013553065835913187)
      ·
        refine ⟨159114358520329598753869781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106076239013553065835913187 159114358520329598753869781)
        ·
          refine ⟨3729242777820224970793823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 159114358520329598753869781 3729242777820224970793823)
          ·
            refine ⟨5593864166730337456190735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3729242777820224970793823 5593864166730337456190735)
            ·
              refine ⟨8390796250095506184286103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5593864166730337456190735 8390796250095506184286103)
              ·
                refine ⟨12586194375143259276429155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8390796250095506184286103 12586194375143259276429155)
                ·
                  refine ⟨18879291562714888914643733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12586194375143259276429155 18879291562714888914643733)
                  ·
                    refine ⟨884966792002260417873925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18879291562714888914643733 884966792002260417873925)
                    ·
                      rfl

theorem cell22_2585200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 1, 1, 6].length) (baseStart_2585200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2585200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2585200 prefixEnd_2585200 := by exact prefixLift 2585200
  have htrace : WordTrace (prefixWord ++ tailWord_2585200) baseStart_2585200 baseEnd_2585200 := by
    simpa [prefixWord, tailWord_2585200, baseEnd_2585200] using wordTrace_append hprefix tailTrace_2585200
  have hstable : (prefixWord ++ tailWord_2585200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2585200).length < 2 ^ (prefixWord ++ tailWord_2585200).sum := by decide
  have hdescent : baseEnd_2585200 < baseStart_2585200 := by decide
  rcases family_descends (prefixWord ++ tailWord_2585200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2585206 : List Nat := [5, 1, 1, 2, 3, 2, 2, 1, 1, 4]
def baseStart_2585206 : Nat := 118140960795 + 2585206 * 2 ^ 59
def prefixEnd_2585206 : Nat := 4983230072969 + 3 ^ 40 * 2585206 * 2
def baseEnd_2585206 : Nat := 884968845924878402223907

theorem tailTrace_2585206 : CollatzResearch.WordTrace tailWord_2585206 prefixEnd_2585206 884968845924878402223907 := by
  unfold tailWord_2585206
  simp only [CollatzResearch.WordTrace]
  refine ⟨5893138067015478429928967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 62860139381498436585908981 5893138067015478429928967)
  ·
    refine ⟨8839707100523217644893451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5893138067015478429928967 8839707100523217644893451)
    ·
      refine ⟨13259560650784826467340177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8839707100523217644893451 13259560650784826467340177)
      ·
        refine ⟨9944670488088619850505133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13259560650784826467340177 9944670488088619850505133)
        ·
          refine ⟨3729251433033232443939425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9944670488088619850505133 3729251433033232443939425)
          ·
            refine ⟨2796938574774924332954569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3729251433033232443939425 2796938574774924332954569)
            ·
              refine ⟨2097703931081193249715927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2796938574774924332954569 2097703931081193249715927)
              ·
                refine ⟨3146555896621789874573891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2097703931081193249715927 3146555896621789874573891)
                ·
                  refine ⟨4719833844932684811860837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3146555896621789874573891 4719833844932684811860837)
                  ·
                    refine ⟨884968845924878402223907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4719833844932684811860837 884968845924878402223907)
                    ·
                      rfl

theorem cell22_2585206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 2, 1, 1, 4].length) (baseStart_2585206 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2585206 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2585206 prefixEnd_2585206 := by exact prefixLift 2585206
  have htrace : WordTrace (prefixWord ++ tailWord_2585206) baseStart_2585206 baseEnd_2585206 := by
    simpa [prefixWord, tailWord_2585206, baseEnd_2585206] using wordTrace_append hprefix tailTrace_2585206
  have hstable : (prefixWord ++ tailWord_2585206).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2585206).length < 2 ^ (prefixWord ++ tailWord_2585206).sum := by decide
  have hdescent : baseEnd_2585206 < baseStart_2585206 := by decide
  rcases family_descends (prefixWord ++ tailWord_2585206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2585228 : List Nat := [2, 2, 1, 2, 1, 1, 2, 3, 2, 6]
def baseStart_2585228 : Nat := 118140960795 + 2585228 * 2 ^ 59
def prefixEnd_2585228 : Nat := 4983230072969 + 3 ^ 40 * 2585228 * 2
def baseEnd_2585228 : Nat := 884976376974477678173839

theorem tailTrace_2585228 : CollatzResearch.WordTrace tailWord_2585228 prefixEnd_2585228 884976376974477678173839 := by
  unfold tailWord_2585228
  simp only [CollatzResearch.WordTrace]
  refine ⟨47145505739083976318082169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62860674318778635090776225 47145505739083976318082169)
  ·
    refine ⟨35359129304312982238561627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47145505739083976318082169 35359129304312982238561627)
    ·
      refine ⟨53038693956469473357842441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35359129304312982238561627 53038693956469473357842441)
      ·
        refine ⟨39779020467352105018381831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53038693956469473357842441 39779020467352105018381831)
        ·
          refine ⟨59668530701028157527572747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39779020467352105018381831 59668530701028157527572747)
          ·
            refine ⟨89502796051542236291359121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59668530701028157527572747 89502796051542236291359121)
            ·
              refine ⟨67127097038656677218519341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89502796051542236291359121 67127097038656677218519341)
              ·
                refine ⟨25172661389496253956944753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67127097038656677218519341 25172661389496253956944753)
                ·
                  refine ⟨18879496042122190467708565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25172661389496253956944753 18879496042122190467708565)
                  ·
                    refine ⟨884976376974477678173839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18879496042122190467708565 884976376974477678173839)
                    ·
                      rfl

theorem cell22_2585228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 2, 6].length) (baseStart_2585228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2585228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2585228 prefixEnd_2585228 := by exact prefixLift 2585228
  have htrace : WordTrace (prefixWord ++ tailWord_2585228) baseStart_2585228 baseEnd_2585228 := by
    simpa [prefixWord, tailWord_2585228, baseEnd_2585228] using wordTrace_append hprefix tailTrace_2585228
  have hstable : (prefixWord ++ tailWord_2585228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2585228).length < 2 ^ (prefixWord ++ tailWord_2585228).sum := by decide
  have hdescent : baseEnd_2585228 < baseStart_2585228 := by decide
  rcases family_descends (prefixWord ++ tailWord_2585228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2585236 : List Nat := [2, 4, 2, 2, 1, 2, 3, 1, 2, 3]
def baseStart_2585236 : Nat := 118140960795 + 2585236 * 2 ^ 59
def prefixEnd_2585236 : Nat := 4983230072969 + 3 ^ 40 * 2585236 * 2
def baseEnd_2585236 : Nat := 884979115537968323973815

theorem tailTrace_2585236 : CollatzResearch.WordTrace tailWord_2585236 prefixEnd_2585236 884979115537968323973815 := by
  unfold tailWord_2585236
  simp only [CollatzResearch.WordTrace]
  refine ⟨47145651631069485001227781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62860868841425980001637041 47145651631069485001227781)
  ·
    refine ⟨8839809680825528437730209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47145651631069485001227781 8839809680825528437730209)
    ·
      refine ⟨6629857260619146328297657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8839809680825528437730209 6629857260619146328297657)
      ·
        refine ⟨4972392945464359746223243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6629857260619146328297657 4972392945464359746223243)
        ·
          refine ⟨7458589418196539619334865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4972392945464359746223243 7458589418196539619334865)
          ·
            refine ⟨5593942063647404714501149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7458589418196539619334865 5593942063647404714501149)
            ·
              refine ⟨2097728273867776767937931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5593942063647404714501149 2097728273867776767937931)
              ·
                refine ⟨3146592410801665151906897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2097728273867776767937931 3146592410801665151906897)
                ·
                  refine ⟨2359944308101248863930173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3146592410801665151906897 2359944308101248863930173)
                  ·
                    refine ⟨884979115537968323973815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2359944308101248863930173 884979115537968323973815)
                    ·
                      rfl

theorem cell22_2585236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 3, 1, 2, 3].length) (baseStart_2585236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2585236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2585236 prefixEnd_2585236 := by exact prefixLift 2585236
  have htrace : WordTrace (prefixWord ++ tailWord_2585236) baseStart_2585236 baseEnd_2585236 := by
    simpa [prefixWord, tailWord_2585236, baseEnd_2585236] using wordTrace_append hprefix tailTrace_2585236
  have hstable : (prefixWord ++ tailWord_2585236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2585236).length < 2 ^ (prefixWord ++ tailWord_2585236).sum := by decide
  have hdescent : baseEnd_2585236 < baseStart_2585236 := by decide
  rcases family_descends (prefixWord ++ tailWord_2585236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2585249 : List Nat := [1, 2, 3, 3, 4, 1, 2, 6]
def baseStart_2585249 : Nat := 118140960795 + 2585249 * 2 ^ 59
def prefixEnd_2585249 : Nat := 4983230072969 + 3 ^ 40 * 2585249 * 2
def baseEnd_2585249 : Nat := 98331507300404513710975

theorem tailTrace_2585249 : CollatzResearch.WordTrace tailWord_2585249 prefixEnd_2585249 98331507300404513710975 := by
  unfold tailWord_2585249
  simp only [CollatzResearch.WordTrace]
  refine ⟨94291777411091873222678801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62861184940727915481785867 94291777411091873222678801)
  ·
    refine ⟨70718833058318904917009101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94291777411091873222678801 70718833058318904917009101)
    ·
      refine ⟨26519562396869589343878413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70718833058318904917009101 26519562396869589343878413)
      ·
        refine ⟨9944835898826096003954405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26519562396869589343878413 9944835898826096003954405)
        ·
          refine ⟨1864656731029893000741451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9944835898826096003954405 1864656731029893000741451)
          ·
            refine ⟨2796985096544839501112177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1864656731029893000741451 2796985096544839501112177)
            ·
              refine ⟨2097738822408629625834133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2796985096544839501112177 2097738822408629625834133)
              ·
                refine ⟨98331507300404513710975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2097738822408629625834133 98331507300404513710975)
                ·
                  rfl

theorem cell22_2585249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 2, 6].length) (baseStart_2585249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2585249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2585249 prefixEnd_2585249 := by exact prefixLift 2585249
  have htrace : WordTrace (prefixWord ++ tailWord_2585249) baseStart_2585249 baseEnd_2585249 := by
    simpa [prefixWord, tailWord_2585249, baseEnd_2585249] using wordTrace_append hprefix tailTrace_2585249
  have hstable : (prefixWord ++ tailWord_2585249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2585249).length < 2 ^ (prefixWord ++ tailWord_2585249).sum := by decide
  have hdescent : baseEnd_2585249 < baseStart_2585249 := by decide
  rcases family_descends (prefixWord ++ tailWord_2585249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2585294 : List Nat := [4, 1, 1, 1, 3, 4, 2, 1, 5]
def baseStart_2585294 : Nat := 118140960795 + 2585294 * 2 ^ 59
def prefixEnd_2585294 : Nat := 4983230072969 + 3 ^ 40 * 2585294 * 2
def baseEnd_2585294 : Nat := 294999656707758502007879

theorem tailTrace_2585294 : CollatzResearch.WordTrace tailWord_2585294 prefixEnd_2585294 294999656707758502007879 := by
  unfold tailWord_2585294
  simp only [CollatzResearch.WordTrace]
  refine ⟨11786677336991105738508367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62862279130619230605377957 11786677336991105738508367)
  ·
    refine ⟨17680016005486658607762551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11786677336991105738508367 17680016005486658607762551)
    ·
      refine ⟨26520024008229987911643827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17680016005486658607762551 26520024008229987911643827)
      ·
        refine ⟨39780036012344981867465741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26520024008229987911643827 39780036012344981867465741)
        ·
          refine ⟨14917513504629368200299653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39780036012344981867465741 14917513504629368200299653)
          ·
            refine ⟨2797033782118006537556185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14917513504629368200299653 2797033782118006537556185)
            ·
              refine ⟨2097775336588504903167139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2797033782118006537556185 2097775336588504903167139)
              ·
                refine ⟨3146663004882757354750709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2097775336588504903167139 3146663004882757354750709)
                ·
                  refine ⟨294999656707758502007879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3146663004882757354750709 294999656707758502007879)
                  ·
                    rfl

theorem cell22_2585294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 2, 1, 5].length) (baseStart_2585294 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2585294 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2585294 prefixEnd_2585294 := by exact prefixLift 2585294
  have htrace : WordTrace (prefixWord ++ tailWord_2585294) baseStart_2585294 baseEnd_2585294 := by
    simpa [prefixWord, tailWord_2585294, baseEnd_2585294] using wordTrace_append hprefix tailTrace_2585294
  have hstable : (prefixWord ++ tailWord_2585294).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2585294).length < 2 ^ (prefixWord ++ tailWord_2585294).sum := by decide
  have hdescent : baseEnd_2585294 < baseStart_2585294 := by decide
  rcases family_descends (prefixWord ++ tailWord_2585294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2585322 : List Nat := [3, 1, 3, 1, 1, 1, 1, 7, 4]
def baseStart_2585322 : Nat := 118140960795 + 2585322 * 2 ^ 59
def prefixEnd_2585322 : Nat := 4983230072969 + 3 ^ 40 * 2585322 * 2
def baseEnd_2585322 : Nat := 295002851698497588774517

theorem tailTrace_2585322 : CollatzResearch.WordTrace tailWord_2585322 prefixEnd_2585322 295002851698497588774517 := by
  unfold tailWord_2585322
  simp only [CollatzResearch.WordTrace]
  refine ⟨23573609984956851672521555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62862959959884937793390813 23573609984956851672521555)
  ·
    refine ⟨35360414977435277508782333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23573609984956851672521555 35360414977435277508782333)
    ·
      refine ⟨13260155616538229065793375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35360414977435277508782333 13260155616538229065793375)
      ·
        refine ⟨19890233424807343598690063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13260155616538229065793375 19890233424807343598690063)
        ·
          refine ⟨29835350137211015398035095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19890233424807343598690063 29835350137211015398035095)
          ·
            refine ⟨44753025205816523097052643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29835350137211015398035095 44753025205816523097052643)
            ·
              refine ⟨67129537808724784645578965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44753025205816523097052643 67129537808724784645578965)
              ·
                refine ⟨1573348542391987140130757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 67129537808724784645578965 1573348542391987140130757)
                ·
                  refine ⟨295002851698497588774517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1573348542391987140130757 295002851698497588774517)
                  ·
                    rfl

theorem cell22_2585322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 7, 4].length) (baseStart_2585322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2585322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2585322 prefixEnd_2585322 := by exact prefixLift 2585322
  have htrace : WordTrace (prefixWord ++ tailWord_2585322) baseStart_2585322 baseEnd_2585322 := by
    simpa [prefixWord, tailWord_2585322, baseEnd_2585322] using wordTrace_append hprefix tailTrace_2585322
  have hstable : (prefixWord ++ tailWord_2585322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2585322).length < 2 ^ (prefixWord ++ tailWord_2585322).sum := by decide
  have hdescent : baseEnd_2585322 < baseStart_2585322 := by decide
  rcases family_descends (prefixWord ++ tailWord_2585322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2585332 : List Nat := [2, 6, 1, 1, 2, 2, 2, 2, 1, 3]
def baseStart_2585332 : Nat := 118140960795 + 2585332 * 2 ^ 59
def prefixEnd_2585332 : Nat := 4983230072969 + 3 ^ 40 * 2585332 * 2
def baseEnd_2585332 : Nat := 885011978299856073573521

theorem tailTrace_2585332 : CollatzResearch.WordTrace tailWord_2585332 prefixEnd_2585332 885011978299856073573521 := by
  unfold tailWord_2585332
  simp only [CollatzResearch.WordTrace]
  refine ⟨47147402334895589198975125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62863203113194118931966833 47147402334895589198975125)
  ·
    refine ⟨2210034484448230743701959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 47147402334895589198975125 2210034484448230743701959)
    ·
      refine ⟨3315051726672346115552939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2210034484448230743701959 3315051726672346115552939)
      ·
        refine ⟨4972577590008519173329409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3315051726672346115552939 4972577590008519173329409)
        ·
          refine ⟨3729433192506389379997057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4972577590008519173329409 3729433192506389379997057)
          ·
            refine ⟨2797074894379792034997793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3729433192506389379997057 2797074894379792034997793)
            ·
              refine ⟨2097806170784844026248345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2797074894379792034997793 2097806170784844026248345)
              ·
                refine ⟨1573354628088633019686259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2097806170784844026248345 1573354628088633019686259)
                ·
                  refine ⟨2360031942132949529529389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1573354628088633019686259 2360031942132949529529389)
                  ·
                    refine ⟨885011978299856073573521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2360031942132949529529389 885011978299856073573521)
                    ·
                      rfl

theorem cell22_2585332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_2585332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2585332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2585332 prefixEnd_2585332 := by exact prefixLift 2585332
  have htrace : WordTrace (prefixWord ++ tailWord_2585332) baseStart_2585332 baseEnd_2585332 := by
    simpa [prefixWord, tailWord_2585332, baseEnd_2585332] using wordTrace_append hprefix tailTrace_2585332
  have hstable : (prefixWord ++ tailWord_2585332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2585332).length < 2 ^ (prefixWord ++ tailWord_2585332).sum := by decide
  have hdescent : baseEnd_2585332 < baseStart_2585332 := by decide
  rcases family_descends (prefixWord ++ tailWord_2585332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2585399 : List Nat := [1, 1, 3, 1, 2, 1, 3, 6, 1, 3]
def baseStart_2585399 : Nat := 118140960795 + 2585399 * 2 ^ 59
def prefixEnd_2585399 : Nat := 4983230072969 + 3 ^ 40 * 2585399 * 2
def baseEnd_2585399 : Nat := 885034913769090232148315

theorem tailTrace_2585399 : CollatzResearch.WordTrace tailWord_2585399 prefixEnd_2585399 885034913769090232148315 := by
  unfold tailWord_2585399
  simp only [CollatzResearch.WordTrace]
  refine ⟨94297248360548448840639251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62864832240365632560426167 94297248360548448840639251)
  ·
    refine ⟨141445872540822673260958877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94297248360548448840639251 141445872540822673260958877)
    ·
      refine ⟨53042202202808502472859579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141445872540822673260958877 53042202202808502472859579)
      ·
        refine ⟨79563303304212753709289369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53042202202808502472859579 79563303304212753709289369)
        ·
          refine ⟨59672477478159565281967027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79563303304212753709289369 59672477478159565281967027)
          ·
            refine ⟨89508716217239347922950541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59672477478159565281967027 89508716217239347922950541)
            ·
              refine ⟨33565768581464755471106453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89508716217239347922950541 33565768581464755471106453)
              ·
                refine ⟨1573395402256160412708115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 33565768581464755471106453 1573395402256160412708115)
                ·
                  refine ⟨2360093103384240619062173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1573395402256160412708115 2360093103384240619062173)
                  ·
                    refine ⟨885034913769090232148315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2360093103384240619062173 885034913769090232148315)
                    ·
                      rfl

theorem cell22_2585399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 6, 1, 3].length) (baseStart_2585399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2585399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2585399 prefixEnd_2585399 := by exact prefixLift 2585399
  have htrace : WordTrace (prefixWord ++ tailWord_2585399) baseStart_2585399 baseEnd_2585399 := by
    simpa [prefixWord, tailWord_2585399, baseEnd_2585399] using wordTrace_append hprefix tailTrace_2585399
  have hstable : (prefixWord ++ tailWord_2585399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2585399).length < 2 ^ (prefixWord ++ tailWord_2585399).sum := by decide
  have hdescent : baseEnd_2585399 < baseStart_2585399 := by decide
  rcases family_descends (prefixWord ++ tailWord_2585399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2585457 : List Nat := [1, 2, 2, 2, 1, 4, 3, 1, 6]
def baseStart_2585457 : Nat := 118140960795 + 2585457 * 2 ^ 59
def prefixEnd_2585457 : Nat := 4983230072969 + 3 ^ 40 * 2585457 * 2
def baseEnd_2585457 : Nat := 295018256118132471399379

theorem tailTrace_2585457 : CollatzResearch.WordTrace tailWord_2585457 prefixEnd_2585457 295018256118132471399379 := by
  unfold tailWord_2585457
  simp only [CollatzResearch.WordTrace]
  refine ⟨94299363794338324746250625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62866242529558883164167083 94299363794338324746250625)
  ·
    refine ⟨70724522845753743559687969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94299363794338324746250625 70724522845753743559687969)
    ·
      refine ⟨53043392134315307669765977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70724522845753743559687969 53043392134315307669765977)
      ·
        refine ⟨39782544100736480752324483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53043392134315307669765977 39782544100736480752324483)
        ·
          refine ⟨59673816151104721128486725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39782544100736480752324483 59673816151104721128486725)
          ·
            refine ⟨11188840528332135211591261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59673816151104721128486725 11188840528332135211591261)
            ·
              refine ⟨4195815198124550704346723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11188840528332135211591261 4195815198124550704346723)
              ·
                refine ⟨6293722797186826056520085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4195815198124550704346723 6293722797186826056520085)
                ·
                  refine ⟨295018256118132471399379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6293722797186826056520085 295018256118132471399379)
                  ·
                    rfl

theorem cell22_2585457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 3, 1, 6].length) (baseStart_2585457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2585457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2585457 prefixEnd_2585457 := by exact prefixLift 2585457
  have htrace : WordTrace (prefixWord ++ tailWord_2585457) baseStart_2585457 baseEnd_2585457 := by
    simpa [prefixWord, tailWord_2585457, baseEnd_2585457] using wordTrace_append hprefix tailTrace_2585457
  have hstable : (prefixWord ++ tailWord_2585457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2585457).length < 2 ^ (prefixWord ++ tailWord_2585457).sum := by decide
  have hdescent : baseEnd_2585457 < baseStart_2585457 := by decide
  rcases family_descends (prefixWord ++ tailWord_2585457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2585472 : List Nat := [2, 1, 1, 2, 1, 2, 2, 2, 6, 3]
def baseStart_2585472 : Nat := 118140960795 + 2585472 * 2 ^ 59
def prefixEnd_2585472 : Nat := 4983230072969 + 3 ^ 40 * 2585472 * 2
def baseEnd_2585472 : Nat := 885059903160942375073091

theorem tailTrace_2585472 : CollatzResearch.WordTrace tailWord_2585472 prefixEnd_2585472 885059903160942375073091 := by
  unfold tailWord_2585472
  simp only [CollatzResearch.WordTrace]
  refine ⟨47149955444641991154023335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62866607259522654872031113 47149955444641991154023335)
  ·
    refine ⟨70724933166962986731035003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47149955444641991154023335 70724933166962986731035003)
    ·
      refine ⟨106087399750444480096552505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70724933166962986731035003 106087399750444480096552505)
      ·
        refine ⟨79565549812833360072414379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106087399750444480096552505 79565549812833360072414379)
        ·
          refine ⟨119348324719250040108621569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79565549812833360072414379 119348324719250040108621569)
          ·
            refine ⟨89511243539437530081466177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119348324719250040108621569 89511243539437530081466177)
            ·
              refine ⟨67133432654578147561099633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89511243539437530081466177 67133432654578147561099633)
              ·
                refine ⟨50350074490933610670824725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67133432654578147561099633 50350074490933610670824725)
                ·
                  refine ⟨2360159741762513000194909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 50350074490933610670824725 2360159741762513000194909)
                  ·
                    refine ⟨885059903160942375073091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2360159741762513000194909 885059903160942375073091)
                    ·
                      rfl

theorem cell22_2585472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 6, 3].length) (baseStart_2585472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2585472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2585472 prefixEnd_2585472 := by exact prefixLift 2585472
  have htrace : WordTrace (prefixWord ++ tailWord_2585472) baseStart_2585472 baseEnd_2585472 := by
    simpa [prefixWord, tailWord_2585472, baseEnd_2585472] using wordTrace_append hprefix tailTrace_2585472
  have hstable : (prefixWord ++ tailWord_2585472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2585472).length < 2 ^ (prefixWord ++ tailWord_2585472).sum := by decide
  have hdescent : baseEnd_2585472 < baseStart_2585472 := by decide
  rcases family_descends (prefixWord ++ tailWord_2585472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2585502 : List Nat := [4, 3, 1, 14]
def baseStart_2585502 : Nat := 118140960795 + 2585502 * 2 ^ 59
def prefixEnd_2585502 : Nat := 4983230072969 + 3 ^ 40 * 2585502 * 2
def baseEnd_2585502 : Nat := 1214088028496614947631

theorem tailTrace_2585502 : CollatzResearch.WordTrace tailWord_2585502 prefixEnd_2585502 1214088028496614947631 := by
  unfold tailWord_2585502
  simp only [CollatzResearch.WordTrace]
  refine ⟨11787625634896912178954845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62867336719450198287759173 11787625634896912178954845)
  ·
    refine ⟨4420359613086342067108067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11787625634896912178954845 4420359613086342067108067)
    ·
      refine ⟨6630539419629513100662101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4420359613086342067108067 6630539419629513100662101)
      ·
        refine ⟨1214088028496614947631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 14 6630539419629513100662101 1214088028496614947631)
        ·
          rfl

theorem cell22_2585502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 14].length) (baseStart_2585502 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2585502 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2585502 prefixEnd_2585502 := by exact prefixLift 2585502
  have htrace : WordTrace (prefixWord ++ tailWord_2585502) baseStart_2585502 baseEnd_2585502 := by
    simpa [prefixWord, tailWord_2585502, baseEnd_2585502] using wordTrace_append hprefix tailTrace_2585502
  have hstable : (prefixWord ++ tailWord_2585502).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2585502).length < 2 ^ (prefixWord ++ tailWord_2585502).sum := by decide
  have hdescent : baseEnd_2585502 < baseStart_2585502 := by decide
  rcases family_descends (prefixWord ++ tailWord_2585502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2585506 : List Nat := [3, 3, 1, 2, 2, 1, 1, 4, 2, 3]
def baseStart_2585506 : Nat := 118140960795 + 2585506 * 2 ^ 59
def prefixEnd_2585506 : Nat := 4983230072969 + 3 ^ 40 * 2585506 * 2
def baseEnd_2585506 : Nat := 885071542055777619722987

theorem tailTrace_2585506 : CollatzResearch.WordTrace tailWord_2585506 prefixEnd_2585506 885071542055777619722987 := by
  unfold tailWord_2585506
  simp only [CollatzResearch.WordTrace]
  refine ⟨23575287742790201528696093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62867433980773870743189581 23575287742790201528696093)
  ·
    refine ⟨8840732903546325573261035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23575287742790201528696093 8840732903546325573261035)
    ·
      refine ⟨13261099355319488359891553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8840732903546325573261035 13261099355319488359891553)
      ·
        refine ⟨9945824516489616269918665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13261099355319488359891553 9945824516489616269918665)
        ·
          refine ⟨7459368387367212202438999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9945824516489616269918665 7459368387367212202438999)
          ·
            refine ⟨11189052581050818303658499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7459368387367212202438999 11189052581050818303658499)
            ·
              refine ⟨16783578871576227455487749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11189052581050818303658499 16783578871576227455487749)
              ·
                refine ⟨3146921038420542647903953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16783578871576227455487749 3146921038420542647903953)
                ·
                  refine ⟨2360190778815406985927965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3146921038420542647903953 2360190778815406985927965)
                  ·
                    refine ⟨885071542055777619722987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2360190778815406985927965 885071542055777619722987)
                    ·
                      rfl

theorem cell22_2585506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 4, 2, 3].length) (baseStart_2585506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2585506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2585506 prefixEnd_2585506 := by exact prefixLift 2585506
  have htrace : WordTrace (prefixWord ++ tailWord_2585506) baseStart_2585506 baseEnd_2585506 := by
    simpa [prefixWord, tailWord_2585506, baseEnd_2585506] using wordTrace_append hprefix tailTrace_2585506
  have hstable : (prefixWord ++ tailWord_2585506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2585506).length < 2 ^ (prefixWord ++ tailWord_2585506).sum := by decide
  have hdescent : baseEnd_2585506 < baseStart_2585506 := by decide
  rcases family_descends (prefixWord ++ tailWord_2585506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2585551 : List Nat := [1, 1, 2, 1, 1, 6, 1, 5, 1, 3]
def baseStart_2585551 : Nat := 118140960795 + 2585551 * 2 ^ 59
def prefixEnd_2585551 : Nat := 4983230072969 + 3 ^ 40 * 2585551 * 2
def baseEnd_2585551 : Nat := 885086946475412502347849

theorem tailTrace_2585551 : CollatzResearch.WordTrace tailWord_2585551 prefixEnd_2585551 885086946475412502347849 := by
  unfold tailWord_2585551
  simp only [CollatzResearch.WordTrace]
  refine ⟨94302792255997778800172507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62868528170665185866781671 94302792255997778800172507)
  ·
    refine ⟨141454188383996668200258761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94302792255997778800172507 141454188383996668200258761)
    ·
      refine ⟨106090641287997501150194071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141454188383996668200258761 106090641287997501150194071)
      ·
        refine ⟨159135961931996251725291107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106090641287997501150194071 159135961931996251725291107)
        ·
          refine ⟨238703942897994377587936661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159135961931996251725291107 238703942897994377587936661)
          ·
            refine ⟨11189247323343486449434531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 238703942897994377587936661 11189247323343486449434531)
            ·
              refine ⟨16783870985015229674151797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11189247323343486449434531 16783870985015229674151797)
              ·
                refine ⟨1573487904845177781951731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16783870985015229674151797 1573487904845177781951731)
                ·
                  refine ⟨2360231857267766672927597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1573487904845177781951731 2360231857267766672927597)
                  ·
                    refine ⟨885086946475412502347849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2360231857267766672927597 885086946475412502347849)
                    ·
                      rfl

theorem cell22_2585551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 5, 1, 3].length) (baseStart_2585551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2585551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2585551 prefixEnd_2585551 := by exact prefixLift 2585551
  have htrace : WordTrace (prefixWord ++ tailWord_2585551) baseStart_2585551 baseEnd_2585551 := by
    simpa [prefixWord, tailWord_2585551, baseEnd_2585551] using wordTrace_append hprefix tailTrace_2585551
  have hstable : (prefixWord ++ tailWord_2585551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2585551).length < 2 ^ (prefixWord ++ tailWord_2585551).sum := by decide
  have hdescent : baseEnd_2585551 < baseStart_2585551 := by decide
  rcases family_descends (prefixWord ++ tailWord_2585551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
