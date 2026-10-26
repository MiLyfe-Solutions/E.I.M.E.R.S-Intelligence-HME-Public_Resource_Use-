import V185TrunkScan22Chunk397

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3549472 : List Nat := [2, 1, 1, 5, 2, 2, 2, 2, 1, 4]
def baseStart_3549472 : Nat := 118140960795 + 3549472 * 2 ^ 59
def prefixEnd_3549472 : Nat := 4983230072969 + 3 ^ 40 * 3549472 * 2
def baseEnd_3549472 : Nat := 1215056803783761272117521

theorem tailTrace_3549472 : CollatzResearch.WordTrace tailWord_3549472 prefixEnd_3549472 1215056803783761272117521 := by
  unfold tailWord_3549472
  simp only [CollatzResearch.WordTrace]
  refine ⟨64729939698438310200269335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86306586264584413600359113 64729939698438310200269335)
  ·
    refine ⟨97094909547657465300404003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64729939698438310200269335 97094909547657465300404003)
    ·
      refine ⟨145642364321486197950606005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97094909547657465300404003 145642364321486197950606005)
      ·
        refine ⟨13653971655139331057869313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 145642364321486197950606005 13653971655139331057869313)
        ·
          refine ⟨10240478741354498293401985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13653971655139331057869313 10240478741354498293401985)
          ·
            refine ⟨7680359056015873720051489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10240478741354498293401985 7680359056015873720051489)
            ·
              refine ⟨5760269292011905290038617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7680359056015873720051489 5760269292011905290038617)
              ·
                refine ⟨4320201969008928967528963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5760269292011905290038617 4320201969008928967528963)
                ·
                  refine ⟨6480302953513393451293445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4320201969008928967528963 6480302953513393451293445)
                  ·
                    refine ⟨1215056803783761272117521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6480302953513393451293445 1215056803783761272117521)
                    ·
                      rfl

theorem cell22_3549472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 2, 2, 1, 4].length) (baseStart_3549472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3549472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3549472 prefixEnd_3549472 := by exact prefixLift 3549472
  have htrace : WordTrace (prefixWord ++ tailWord_3549472) baseStart_3549472 baseEnd_3549472 := by
    simpa [prefixWord, tailWord_3549472, baseEnd_3549472] using wordTrace_append hprefix tailTrace_3549472
  have hstable : (prefixWord ++ tailWord_3549472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3549472).length < 2 ^ (prefixWord ++ tailWord_3549472).sum := by decide
  have hdescent : baseEnd_3549472 < baseStart_3549472 := by decide
  rcases family_descends (prefixWord ++ tailWord_3549472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3549498 : List Nat := [3, 1, 1, 1, 4, 2, 10]
def baseStart_3549498 : Nat := 118140960795 + 3549498 * 2 ^ 59
def prefixEnd_3549498 : Nat := 4983230072969 + 3 ^ 40 * 3549498 * 2
def baseEnd_3549498 : Nat := 45002433485744661887683

theorem tailTrace_3549498 : CollatzResearch.WordTrace tailWord_3549498 prefixEnd_3549498 45002433485744661887683 := by
  unfold tailWord_3549498
  simp only [CollatzResearch.WordTrace]
  refine ⟨32365206923695606710246287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86307218463188284560656765 32365206923695606710246287)
  ·
    refine ⟨48547810385543410065369431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32365206923695606710246287 48547810385543410065369431)
    ·
      refine ⟨72821715578315115098054147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48547810385543410065369431 72821715578315115098054147)
      ·
        refine ⟨109232573367472672647081221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72821715578315115098054147 109232573367472672647081221)
        ·
          refine ⟨20481107506401126121327729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 109232573367472672647081221 20481107506401126121327729)
          ·
            refine ⟨15360830629800844590995797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20481107506401126121327729 15360830629800844590995797)
            ·
              refine ⟨45002433485744661887683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 15360830629800844590995797 45002433485744661887683)
              ·
                rfl

theorem cell22_3549498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 10].length) (baseStart_3549498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3549498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3549498 prefixEnd_3549498 := by exact prefixLift 3549498
  have htrace : WordTrace (prefixWord ++ tailWord_3549498) baseStart_3549498 baseEnd_3549498 := by
    simpa [prefixWord, tailWord_3549498, baseEnd_3549498] using wordTrace_append hprefix tailTrace_3549498
  have hstable : (prefixWord ++ tailWord_3549498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3549498).length < 2 ^ (prefixWord ++ tailWord_3549498).sum := by decide
  have hdescent : baseEnd_3549498 < baseStart_3549498 := by decide
  rcases family_descends (prefixWord ++ tailWord_3549498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3549500 : List Nat := [2, 2, 2, 2, 1, 2, 3, 2, 2, 4]
def baseStart_3549500 : Nat := 118140960795 + 3549500 * 2 ^ 59
def prefixEnd_3549500 : Nat := 4983230072969 + 3 ^ 40 * 3549500 * 2
def baseEnd_3549500 : Nat := 1215066388755978532417435

theorem tailTrace_3549500 : CollatzResearch.WordTrace tailWord_3549500 prefixEnd_3549500 1215066388755978532417435 := by
  unfold tailWord_3549500
  simp only [CollatzResearch.WordTrace]
  refine ⟨64730450320387590591278977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86307267093850120788371969 64730450320387590591278977)
  ·
    refine ⟨48547837740290692943459233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64730450320387590591278977 48547837740290692943459233)
    ·
      refine ⟨36410878305218019707594425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48547837740290692943459233 36410878305218019707594425)
      ·
        refine ⟨27308158728913514780695819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36410878305218019707594425 27308158728913514780695819)
        ·
          refine ⟨40962238093370272171043729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27308158728913514780695819 40962238093370272171043729)
          ·
            refine ⟨30721678570027704128282797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40962238093370272171043729 30721678570027704128282797)
            ·
              refine ⟨11520629463760389048106049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30721678570027704128282797 11520629463760389048106049)
              ·
                refine ⟨8640472097820291786079537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11520629463760389048106049 8640472097820291786079537)
                ·
                  refine ⟨6480354073365218839559653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8640472097820291786079537 6480354073365218839559653)
                  ·
                    refine ⟨1215066388755978532417435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6480354073365218839559653 1215066388755978532417435)
                    ·
                      rfl

theorem cell22_3549500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 2, 2, 4].length) (baseStart_3549500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3549500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3549500 prefixEnd_3549500 := by exact prefixLift 3549500
  have htrace : WordTrace (prefixWord ++ tailWord_3549500) baseStart_3549500 baseEnd_3549500 := by
    simpa [prefixWord, tailWord_3549500, baseEnd_3549500] using wordTrace_append hprefix tailTrace_3549500
  have hstable : (prefixWord ++ tailWord_3549500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3549500).length < 2 ^ (prefixWord ++ tailWord_3549500).sum := by decide
  have hdescent : baseEnd_3549500 < baseStart_3549500 := by decide
  rcases family_descends (prefixWord ++ tailWord_3549500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3549502 : List Nat := [4, 2, 1, 2, 1, 2, 2, 1, 4, 3]
def baseStart_3549502 : Nat := 118140960795 + 3549502 * 2 ^ 59
def prefixEnd_3549502 : Nat := 4983230072969 + 3 ^ 40 * 3549502 * 2
def baseEnd_3549502 : Nat := 1215067073396851193867429

theorem tailTrace_3549502 : CollatzResearch.WordTrace tailWord_3549502 prefixEnd_3549502 1215067073396851193867429 := by
  unfold tailWord_3549502
  simp only [CollatzResearch.WordTrace]
  refine ⟨16182621698345991940516345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86307315724511957016087173 16182621698345991940516345)
  ·
    refine ⟨12136966273759493955387259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16182621698345991940516345 12136966273759493955387259)
    ·
      refine ⟨18205449410639240933080889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12136966273759493955387259 18205449410639240933080889)
      ·
        refine ⟨13654087057979430699810667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18205449410639240933080889 13654087057979430699810667)
        ·
          refine ⟨20481130586969146049716001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13654087057979430699810667 20481130586969146049716001)
          ·
            refine ⟨15360847940226859537287001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20481130586969146049716001 15360847940226859537287001)
            ·
              refine ⟨11520635955170144652965251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15360847940226859537287001 11520635955170144652965251)
              ·
                refine ⟨17280953932755216979447877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11520635955170144652965251 17280953932755216979447877)
                ·
                  refine ⟨3240178862391603183646477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17280953932755216979447877 3240178862391603183646477)
                  ·
                    refine ⟨1215067073396851193867429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3240178862391603183646477 1215067073396851193867429)
                    ·
                      rfl

theorem cell22_3549502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 1, 4, 3].length) (baseStart_3549502 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3549502 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3549502 prefixEnd_3549502 := by exact prefixLift 3549502
  have htrace : WordTrace (prefixWord ++ tailWord_3549502) baseStart_3549502 baseEnd_3549502 := by
    simpa [prefixWord, tailWord_3549502, baseEnd_3549502] using wordTrace_append hprefix tailTrace_3549502
  have hstable : (prefixWord ++ tailWord_3549502).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3549502).length < 2 ^ (prefixWord ++ tailWord_3549502).sum := by decide
  have hdescent : baseEnd_3549502 < baseStart_3549502 := by decide
  rcases family_descends (prefixWord ++ tailWord_3549502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3549528 : List Nat := [2, 1, 2, 2, 1, 1, 2, 1, 4, 6]
def baseStart_3549528 : Nat := 118140960795 + 3549528 * 2 ^ 59
def prefixEnd_3549528 : Nat := 4983230072969 + 3 ^ 40 * 3549528 * 2
def baseEnd_3549528 : Nat := 1215075973728195792717349

theorem tailTrace_3549528 : CollatzResearch.WordTrace tailWord_3549528 prefixEnd_3549528 1215075973728195792717349 := by
  unfold tailWord_3549528
  simp only [CollatzResearch.WordTrace]
  refine ⟨64730960942336870982288619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86307947923115827976384825 64730960942336870982288619)
  ·
    refine ⟨97096441413505306473432929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64730960942336870982288619 97096441413505306473432929)
    ·
      refine ⟨72822331060128979855074697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97096441413505306473432929 72822331060128979855074697)
      ·
        refine ⟨54616748295096734891306023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72822331060128979855074697 54616748295096734891306023)
        ·
          refine ⟨81925122442645102336959035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54616748295096734891306023 81925122442645102336959035)
          ·
            refine ⟨122887683663967653505438553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81925122442645102336959035 122887683663967653505438553)
            ·
              refine ⟨92165762747975740129078915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122887683663967653505438553 92165762747975740129078915)
              ·
                refine ⟨138248644121963610193618373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92165762747975740129078915 138248644121963610193618373)
                ·
                  refine ⟨25921620772868176911303445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 138248644121963610193618373 25921620772868176911303445)
                  ·
                    refine ⟨1215075973728195792717349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25921620772868176911303445 1215075973728195792717349)
                    ·
                      rfl

theorem cell22_3549528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 4, 6].length) (baseStart_3549528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3549528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3549528 prefixEnd_3549528 := by exact prefixLift 3549528
  have htrace : WordTrace (prefixWord ++ tailWord_3549528) baseStart_3549528 baseEnd_3549528 := by
    simpa [prefixWord, tailWord_3549528, baseEnd_3549528] using wordTrace_append hprefix tailTrace_3549528
  have hstable : (prefixWord ++ tailWord_3549528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3549528).length < 2 ^ (prefixWord ++ tailWord_3549528).sum := by decide
  have hdescent : baseEnd_3549528 < baseStart_3549528 := by decide
  rcases family_descends (prefixWord ++ tailWord_3549528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3549530 : List Nat := [3, 1, 1, 2, 1, 2, 1, 3, 5, 3]
def baseStart_3549530 : Nat := 118140960795 + 3549530 * 2 ^ 59
def prefixEnd_3549530 : Nat := 4983230072969 + 3 ^ 40 * 3549530 * 2
def baseEnd_3549530 : Nat := 1215076658369068454167343

theorem tailTrace_3549530 : CollatzResearch.WordTrace tailWord_3549530 prefixEnd_3549530 1215076658369068454167343 := by
  unfold tailWord_3549530
  simp only [CollatzResearch.WordTrace]
  refine ⟨32365498707666624076537511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86307996553777664204100029 32365498707666624076537511)
  ·
    refine ⟨48548248061499936114806267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32365498707666624076537511 48548248061499936114806267)
    ·
      refine ⟨72822372092249904172209401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48548248061499936114806267 72822372092249904172209401)
      ·
        refine ⟨54616779069187428129157051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72822372092249904172209401 54616779069187428129157051)
        ·
          refine ⟨81925168603781142193735577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54616779069187428129157051 81925168603781142193735577)
          ·
            refine ⟨61443876452835856645301683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81925168603781142193735577 61443876452835856645301683)
            ·
              refine ⟨92165814679253784967952525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61443876452835856645301683 92165814679253784967952525)
              ·
                refine ⟨34562180504720169362982197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92165814679253784967952525 34562180504720169362982197)
                ·
                  refine ⟨3240204422317515877779581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34562180504720169362982197 3240204422317515877779581)
                  ·
                    refine ⟨1215076658369068454167343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3240204422317515877779581 1215076658369068454167343)
                    ·
                      rfl

theorem cell22_3549530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 3, 5, 3].length) (baseStart_3549530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3549530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3549530 prefixEnd_3549530 := by exact prefixLift 3549530
  have htrace : WordTrace (prefixWord ++ tailWord_3549530) baseStart_3549530 baseEnd_3549530 := by
    simpa [prefixWord, tailWord_3549530, baseEnd_3549530] using wordTrace_append hprefix tailTrace_3549530
  have hstable : (prefixWord ++ tailWord_3549530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3549530).length < 2 ^ (prefixWord ++ tailWord_3549530).sum := by decide
  have hdescent : baseEnd_3549530 < baseStart_3549530 := by decide
  rcases family_descends (prefixWord ++ tailWord_3549530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3549575 : List Nat := [1, 1, 4, 2, 2, 1, 3, 1, 2, 5]
def baseStart_3549575 : Nat := 118140960795 + 3549575 * 2 ^ 59
def prefixEnd_3549575 : Nat := 4983230072969 + 3 ^ 40 * 3549575 * 2
def baseEnd_3549575 : Nat := 1215092062788703336792205

theorem tailTrace_3549575 : CollatzResearch.WordTrace tailWord_3549575 prefixEnd_3549575 1215092062788703336792205 := by
  unfold tailWord_3549575
  simp only [CollatzResearch.WordTrace]
  refine ⟨129463636115503468991538179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86309090743668979327692119 129463636115503468991538179)
  ·
    refine ⟨194195454173255203487307269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129463636115503468991538179 194195454173255203487307269)
    ·
      refine ⟨36411647657485350653870113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 194195454173255203487307269 36411647657485350653870113)
      ·
        refine ⟨27308735743114012990402585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36411647657485350653870113 27308735743114012990402585)
        ·
          refine ⟨20481551807335509742801939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27308735743114012990402585 20481551807335509742801939)
          ·
            refine ⟨30722327711003264614202909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20481551807335509742801939 30722327711003264614202909)
            ·
              refine ⟨11520872891626224230326091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30722327711003264614202909 11520872891626224230326091)
              ·
                refine ⟨17281309337439336345489137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11520872891626224230326091 17281309337439336345489137)
                ·
                  refine ⟨12960982003079502259116853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17281309337439336345489137 12960982003079502259116853)
                  ·
                    refine ⟨1215092062788703336792205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12960982003079502259116853 1215092062788703336792205)
                    ·
                      rfl

theorem cell22_3549575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 1, 2, 5].length) (baseStart_3549575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3549575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3549575 prefixEnd_3549575 := by exact prefixLift 3549575
  have htrace : WordTrace (prefixWord ++ tailWord_3549575) baseStart_3549575 baseEnd_3549575 := by
    simpa [prefixWord, tailWord_3549575, baseEnd_3549575] using wordTrace_append hprefix tailTrace_3549575
  have hstable : (prefixWord ++ tailWord_3549575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3549575).length < 2 ^ (prefixWord ++ tailWord_3549575).sum := by decide
  have hdescent : baseEnd_3549575 < baseStart_3549575 := by decide
  rcases family_descends (prefixWord ++ tailWord_3549575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3549598 : List Nat := [4, 3, 1, 2, 1, 2, 2, 3, 1, 3]
def baseStart_3549598 : Nat := 118140960795 + 3549598 * 2 ^ 59
def prefixEnd_3549598 : Nat := 4983230072969 + 3 ^ 40 * 3549598 * 2
def baseEnd_3549598 : Nat := 1215099936158738943467135

theorem tailTrace_3549598 : CollatzResearch.WordTrace tailWord_3549598 prefixEnd_3549598 1215099936158738943467135 := by
  unfold tailWord_3549598
  simp only [CollatzResearch.WordTrace]
  refine ⟨16183059374302517989953181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86309649996280095946416965 16183059374302517989953181)
  ·
    refine ⟨6068647265363444246232443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16183059374302517989953181 6068647265363444246232443)
    ·
      refine ⟨9102970898045166369348665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6068647265363444246232443 9102970898045166369348665)
      ·
        refine ⟨6827228173533874777011499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9102970898045166369348665 6827228173533874777011499)
        ·
          refine ⟨10240842260300812165517249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6827228173533874777011499 10240842260300812165517249)
          ·
            refine ⟨7680631695225609124137937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10240842260300812165517249 7680631695225609124137937)
            ·
              refine ⟨5760473771419206843103453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7680631695225609124137937 5760473771419206843103453)
              ·
                refine ⟨2160177664282202566163795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5760473771419206843103453 2160177664282202566163795)
                ·
                  refine ⟨3240266496423303849245693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2160177664282202566163795 3240266496423303849245693)
                  ·
                    refine ⟨1215099936158738943467135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3240266496423303849245693 1215099936158738943467135)
                    ·
                      rfl

theorem cell22_3549598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 2, 3, 1, 3].length) (baseStart_3549598 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3549598 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3549598 prefixEnd_3549598 := by exact prefixLift 3549598
  have htrace : WordTrace (prefixWord ++ tailWord_3549598) baseStart_3549598 baseEnd_3549598 := by
    simpa [prefixWord, tailWord_3549598, baseEnd_3549598] using wordTrace_append hprefix tailTrace_3549598
  have hstable : (prefixWord ++ tailWord_3549598).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3549598).length < 2 ^ (prefixWord ++ tailWord_3549598).sum := by decide
  have hdescent : baseEnd_3549598 < baseStart_3549598 := by decide
  rcases family_descends (prefixWord ++ tailWord_3549598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3549652 : List Nat := [2, 4, 1, 2, 2, 1, 2, 1, 1, 6]
def baseStart_3549652 : Nat := 118140960795 + 3549652 * 2 ^ 59
def prefixEnd_3549652 : Nat := 4983230072969 + 3 ^ 40 * 3549652 * 2
def baseEnd_3549652 : Nat := 1215118421462300802616969

theorem tailTrace_3549652 : CollatzResearch.WordTrace tailWord_3549652 prefixEnd_3549652 1215118421462300802616969 := by
  unfold tailWord_3549652
  simp only [CollatzResearch.WordTrace]
  refine ⟨64733222268112255571045605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86310963024149674094727473 64733222268112255571045605)
  ·
    refine ⟨12137479175271047919571051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64733222268112255571045605 12137479175271047919571051)
    ·
      refine ⟨18206218762906571879356577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12137479175271047919571051 18206218762906571879356577)
      ·
        refine ⟨13654664072179928909517433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18206218762906571879356577 13654664072179928909517433)
        ·
          refine ⟨10240998054134946682138075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13654664072179928909517433 10240998054134946682138075)
          ·
            refine ⟨15361497081202420023207113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10240998054134946682138075 15361497081202420023207113)
            ·
              refine ⟨11521122810901815017405335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15361497081202420023207113 11521122810901815017405335)
              ·
                refine ⟨17281684216352722526108003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11521122810901815017405335 17281684216352722526108003)
                ·
                  refine ⟨25922526324529083789162005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17281684216352722526108003 25922526324529083789162005)
                  ·
                    refine ⟨1215118421462300802616969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25922526324529083789162005 1215118421462300802616969)
                    ·
                      rfl

theorem cell22_3549652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 1, 1, 6].length) (baseStart_3549652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3549652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3549652 prefixEnd_3549652 := by exact prefixLift 3549652
  have htrace : WordTrace (prefixWord ++ tailWord_3549652) baseStart_3549652 baseEnd_3549652 := by
    simpa [prefixWord, tailWord_3549652, baseEnd_3549652] using wordTrace_append hprefix tailTrace_3549652
  have hstable : (prefixWord ++ tailWord_3549652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3549652).length < 2 ^ (prefixWord ++ tailWord_3549652).sum := by decide
  have hdescent : baseEnd_3549652 < baseStart_3549652 := by decide
  rcases family_descends (prefixWord ++ tailWord_3549652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3549654 : List Nat := [5, 2, 1, 1, 1, 1, 1, 1, 6, 3]
def baseStart_3549654 : Nat := 118140960795 + 3549654 * 2 ^ 59
def prefixEnd_3549654 : Nat := 4983230072969 + 3 ^ 40 * 3549654 * 2
def baseEnd_3549654 : Nat := 1215119106103173464066963

theorem tailTrace_3549654 : CollatzResearch.WordTrace tailWord_3549654 prefixEnd_3549654 1215119106103173464066963 := by
  unfold tailWord_3549654
  simp only [CollatzResearch.WordTrace]
  refine ⟨8091657342638579092729001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 86311011654811510322442677 8091657342638579092729001)
  ·
    refine ⟨6068743006978934319546751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8091657342638579092729001 6068743006978934319546751)
    ·
      refine ⟨9103114510468401479320127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6068743006978934319546751 9103114510468401479320127)
      ·
        refine ⟨13654671765702602218980191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9103114510468401479320127 13654671765702602218980191)
        ·
          refine ⟨20482007648553903328470287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13654671765702602218980191 20482007648553903328470287)
          ·
            refine ⟨30723011472830854992705431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20482007648553903328470287 30723011472830854992705431)
            ·
              refine ⟨46084517209246282489058147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30723011472830854992705431 46084517209246282489058147)
              ·
                refine ⟨69126775813869423733587221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46084517209246282489058147 69126775813869423733587221)
                ·
                  refine ⟨3240317616275129237511901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 69126775813869423733587221 3240317616275129237511901)
                  ·
                    refine ⟨1215119106103173464066963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3240317616275129237511901 1215119106103173464066963)
                    ·
                      rfl

theorem cell22_3549654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 6, 3].length) (baseStart_3549654 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3549654 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3549654 prefixEnd_3549654 := by exact prefixLift 3549654
  have htrace : WordTrace (prefixWord ++ tailWord_3549654) baseStart_3549654 baseEnd_3549654 := by
    simpa [prefixWord, tailWord_3549654, baseEnd_3549654] using wordTrace_append hprefix tailTrace_3549654
  have hstable : (prefixWord ++ tailWord_3549654).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3549654).length < 2 ^ (prefixWord ++ tailWord_3549654).sum := by decide
  have hdescent : baseEnd_3549654 < baseStart_3549654 := by decide
  rcases family_descends (prefixWord ++ tailWord_3549654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3549667 : List Nat := [1, 1, 1, 6, 3, 2, 8]
def baseStart_3549667 : Nat := 118140960795 + 3549667 * 2 ^ 59
def prefixEnd_3549667 : Nat := 4983230072969 + 3 ^ 40 * 3549667 * 2
def baseEnd_3549667 : Nat := 45004576158105398647849

theorem tailTrace_3549667 : CollatzResearch.WordTrace tailWord_3549667 prefixEnd_3549667 45004576158105398647849 := by
  unfold tailWord_3549667
  simp only [CollatzResearch.WordTrace]
  refine ⟨129466991631170168703887255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86311327754113445802591503 129466991631170168703887255)
  ·
    refine ⟨194200487446755253055830883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129466991631170168703887255 194200487446755253055830883)
    ·
      refine ⟨291300731170132879583746325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194200487446755253055830883 291300731170132879583746325)
      ·
        refine ⟨13654721773599978730488109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 291300731170132879583746325 13654721773599978730488109)
        ·
          refine ⟨5120520665099992023933041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13654721773599978730488109 5120520665099992023933041)
          ·
            refine ⟨3840390498824994017949781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5120520665099992023933041 3840390498824994017949781)
            ·
              refine ⟨45004576158105398647849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3840390498824994017949781 45004576158105398647849)
              ·
                rfl

theorem cell22_3549667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 8].length) (baseStart_3549667 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3549667 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3549667 prefixEnd_3549667 := by exact prefixLift 3549667
  have htrace : WordTrace (prefixWord ++ tailWord_3549667) baseStart_3549667 baseEnd_3549667 := by
    simpa [prefixWord, tailWord_3549667, baseEnd_3549667] using wordTrace_append hprefix tailTrace_3549667
  have hstable : (prefixWord ++ tailWord_3549667).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3549667).length < 2 ^ (prefixWord ++ tailWord_3549667).sum := by decide
  have hdescent : baseEnd_3549667 < baseStart_3549667 := by decide
  rcases family_descends (prefixWord ++ tailWord_3549667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3549669 : List Nat := [1, 3, 1, 5, 2, 1, 1, 2, 2, 4]
def baseStart_3549669 : Nat := 118140960795 + 3549669 * 2 ^ 59
def prefixEnd_3549669 : Nat := 4983230072969 + 3 ^ 40 * 3549669 * 2
def baseEnd_3549669 : Nat := 1215124240909718424941917

theorem tailTrace_3549669 : CollatzResearch.WordTrace tailWord_3549669 prefixEnd_3549669 1215124240909718424941917 := by
  unfold tailWord_3549669
  simp only [CollatzResearch.WordTrace]
  refine ⟨129467064577162923045460061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86311376384775282030306707 129467064577162923045460061)
  ·
    refine ⟨48550149216436096142047523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129467064577162923045460061 48550149216436096142047523)
    ·
      refine ⟨72825223824654144213071285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48550149216436096142047523 72825223824654144213071285)
      ·
        refine ⟨6827364733561326019975433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 72825223824654144213071285 6827364733561326019975433)
        ·
          refine ⟨5120523550170994514981575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6827364733561326019975433 5120523550170994514981575)
          ·
            refine ⟨7680785325256491772472363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5120523550170994514981575 7680785325256491772472363)
            ·
              refine ⟨11521177987884737658708545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7680785325256491772472363 11521177987884737658708545)
              ·
                refine ⟨8640883490913553244031409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11521177987884737658708545 8640883490913553244031409)
                ·
                  refine ⟨6480662618185164933023557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8640883490913553244031409 6480662618185164933023557)
                  ·
                    refine ⟨1215124240909718424941917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6480662618185164933023557 1215124240909718424941917)
                    ·
                      rfl

theorem cell22_3549669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 2, 2, 4].length) (baseStart_3549669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3549669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3549669 prefixEnd_3549669 := by exact prefixLift 3549669
  have htrace : WordTrace (prefixWord ++ tailWord_3549669) baseStart_3549669 baseEnd_3549669 := by
    simpa [prefixWord, tailWord_3549669, baseEnd_3549669] using wordTrace_append hprefix tailTrace_3549669
  have hstable : (prefixWord ++ tailWord_3549669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3549669).length < 2 ^ (prefixWord ++ tailWord_3549669).sum := by decide
  have hdescent : baseEnd_3549669 < baseStart_3549669 := by decide
  rcases family_descends (prefixWord ++ tailWord_3549669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3549680 : List Nat := [2, 1, 1, 1, 3, 3, 2, 1, 2, 6]
def baseStart_3549680 : Nat := 118140960795 + 3549680 * 2 ^ 59
def prefixEnd_3549680 : Nat := 4983230072969 + 3 ^ 40 * 3549680 * 2
def baseEnd_3549680 : Nat := 1215128006434518062916883

theorem tailTrace_3549680 : CollatzResearch.WordTrace tailWord_3549680 prefixEnd_3549680 1215128006434518062916883 := by
  unfold tailWord_3549680
  simp only [CollatzResearch.WordTrace]
  refine ⟨64733732890061535962055247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86311643853415381282740329 64733732890061535962055247)
  ·
    refine ⟨97100599335092303943082871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64733732890061535962055247 97100599335092303943082871)
    ·
      refine ⟨145650899002638455914624307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97100599335092303943082871 145650899002638455914624307)
      ·
        refine ⟨218476348503957683871936461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145650899002638455914624307 218476348503957683871936461)
        ·
          refine ⟨81928630688984131451976173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 218476348503957683871936461 81928630688984131451976173)
          ·
            refine ⟨30723236508369049294491065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81928630688984131451976173 30723236508369049294491065)
            ·
              refine ⟨23042427381276786970868299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30723236508369049294491065 23042427381276786970868299)
              ·
                refine ⟨34563641071915180456302449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23042427381276786970868299 34563641071915180456302449)
                ·
                  refine ⟨25922730803936385342226837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34563641071915180456302449 25922730803936385342226837)
                  ·
                    refine ⟨1215128006434518062916883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25922730803936385342226837 1215128006434518062916883)
                    ·
                      rfl

theorem cell22_3549680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 1, 2, 6].length) (baseStart_3549680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3549680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3549680 prefixEnd_3549680 := by exact prefixLift 3549680
  have htrace : WordTrace (prefixWord ++ tailWord_3549680) baseStart_3549680 baseEnd_3549680 := by
    simpa [prefixWord, tailWord_3549680, baseEnd_3549680] using wordTrace_append hprefix tailTrace_3549680
  have hstable : (prefixWord ++ tailWord_3549680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3549680).length < 2 ^ (prefixWord ++ tailWord_3549680).sum := by decide
  have hdescent : baseEnd_3549680 < baseStart_3549680 := by decide
  rcases family_descends (prefixWord ++ tailWord_3549680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3549740 : List Nat := [2, 2, 1, 1, 1, 2, 1, 2, 10]
def baseStart_3549740 : Nat := 118140960795 + 3549740 * 2 ^ 59
def prefixEnd_3549740 : Nat := 4983230072969 + 3 ^ 40 * 3549740 * 2
def baseEnd_3549740 : Nat := 405049515220232635472233

theorem tailTrace_3549740 : CollatzResearch.WordTrace tailWord_3549740 prefixEnd_3549740 405049515220232635472233 := by
  unfold tailWord_3549740
  simp only [CollatzResearch.WordTrace]
  refine ⟨64734827079952851085647337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86313102773270468114196449 64734827079952851085647337)
  ·
    refine ⟨48551120309964638314235503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64734827079952851085647337 48551120309964638314235503)
    ·
      refine ⟨72826680464946957471353255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48551120309964638314235503 72826680464946957471353255)
      ·
        refine ⟨109240020697420436207029883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72826680464946957471353255 109240020697420436207029883)
        ·
          refine ⟨163860031046130654310544825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109240020697420436207029883 163860031046130654310544825)
          ·
            refine ⟨122895023284597990732908619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163860031046130654310544825 122895023284597990732908619)
            ·
              refine ⟨184342534926896986099362929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122895023284597990732908619 184342534926896986099362929)
              ·
                refine ⟨138256901195172739574522197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 184342534926896986099362929 138256901195172739574522197)
                ·
                  refine ⟨405049515220232635472233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 138256901195172739574522197 405049515220232635472233)
                  ·
                    rfl

theorem cell22_3549740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 10].length) (baseStart_3549740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3549740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3549740 prefixEnd_3549740 := by exact prefixLift 3549740
  have htrace : WordTrace (prefixWord ++ tailWord_3549740) baseStart_3549740 baseEnd_3549740 := by
    simpa [prefixWord, tailWord_3549740, baseEnd_3549740] using wordTrace_append hprefix tailTrace_3549740
  have hstable : (prefixWord ++ tailWord_3549740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3549740).length < 2 ^ (prefixWord ++ tailWord_3549740).sum := by decide
  have hdescent : baseEnd_3549740 < baseStart_3549740 := by decide
  rcases family_descends (prefixWord ++ tailWord_3549740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3549757 : List Nat := [1, 4, 1, 3, 2, 1, 1, 1, 8]
def baseStart_3549757 : Nat := 118140960795 + 3549757 * 2 ^ 59
def prefixEnd_3549757 : Nat := 4983230072969 + 3 ^ 40 * 3549757 * 2
def baseEnd_3549757 : Nat := 405051455036038509580549

theorem tailTrace_3549757 : CollatzResearch.WordTrace tailWord_3549757 prefixEnd_3549757 405051455036038509580549 := by
  unfold tailWord_3549757
  simp only [CollatzResearch.WordTrace]
  refine ⟨129470274200844114074663525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86313516133896076049775683 129470274200844114074663525)
  ·
    refine ⟨24275676412658271388999411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129470274200844114074663525 24275676412658271388999411)
    ·
      refine ⟨36413514618987407083499117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24275676412658271388999411 36413514618987407083499117)
      ·
        refine ⟨13655067982120277656312169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36413514618987407083499117 13655067982120277656312169)
        ·
          refine ⟨10241300986590208242234127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13655067982120277656312169 10241300986590208242234127)
          ·
            refine ⟨15361951479885312363351191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10241300986590208242234127 15361951479885312363351191)
            ·
              refine ⟨23042927219827968545026787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15361951479885312363351191 23042927219827968545026787)
              ·
                refine ⟨34564390829741952817540181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23042927219827968545026787 34564390829741952817540181)
                ·
                  refine ⟨405051455036038509580549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34564390829741952817540181 405051455036038509580549)
                  ·
                    rfl

theorem cell22_3549757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 1, 8].length) (baseStart_3549757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3549757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3549757 prefixEnd_3549757 := by exact prefixLift 3549757
  have htrace : WordTrace (prefixWord ++ tailWord_3549757) baseStart_3549757 baseEnd_3549757 := by
    simpa [prefixWord, tailWord_3549757, baseEnd_3549757] using wordTrace_append hprefix tailTrace_3549757
  have hstable : (prefixWord ++ tailWord_3549757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3549757).length < 2 ^ (prefixWord ++ tailWord_3549757).sum := by decide
  have hdescent : baseEnd_3549757 < baseStart_3549757 := by decide
  rcases family_descends (prefixWord ++ tailWord_3549757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3549772 : List Nat := [2, 2, 1, 3, 1, 2, 1, 4, 1, 5]
def baseStart_3549772 : Nat := 118140960795 + 3549772 * 2 ^ 59
def prefixEnd_3549772 : Nat := 4983230072969 + 3 ^ 40 * 3549772 * 2
def baseEnd_3549772 : Nat := 1215159499914660489616601

theorem tailTrace_3549772 : CollatzResearch.WordTrace tailWord_3549772 prefixEnd_3549772 1215159499914660489616601 := by
  unfold tailWord_3549772
  simp only [CollatzResearch.WordTrace]
  refine ⟨64735410647894885818229785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86313880863859847757639713 64735410647894885818229785)
  ·
    refine ⟨48551557985921164363672339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64735410647894885818229785 48551557985921164363672339)
    ·
      refine ⟨72827336978881746545508509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48551557985921164363672339 72827336978881746545508509)
      ·
        refine ⟨27310251367080654954565691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72827336978881746545508509 27310251367080654954565691)
        ·
          refine ⟨40965377050620982431848537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27310251367080654954565691 40965377050620982431848537)
          ·
            refine ⟨30724032787965736823886403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40965377050620982431848537 30724032787965736823886403)
            ·
              refine ⟨46086049181948605235829605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30724032787965736823886403 46086049181948605235829605)
              ·
                refine ⟨8641134221615363481718051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46086049181948605235829605 8641134221615363481718051)
                ·
                  refine ⟨12961701332423045222577077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8641134221615363481718051 12961701332423045222577077)
                  ·
                    refine ⟨1215159499914660489616601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12961701332423045222577077 1215159499914660489616601)
                    ·
                      rfl

theorem cell22_3549772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 4, 1, 5].length) (baseStart_3549772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3549772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3549772 prefixEnd_3549772 := by exact prefixLift 3549772
  have htrace : WordTrace (prefixWord ++ tailWord_3549772) baseStart_3549772 baseEnd_3549772 := by
    simpa [prefixWord, tailWord_3549772, baseEnd_3549772] using wordTrace_append hprefix tailTrace_3549772
  have hstable : (prefixWord ++ tailWord_3549772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3549772).length < 2 ^ (prefixWord ++ tailWord_3549772).sum := by decide
  have hdescent : baseEnd_3549772 < baseStart_3549772 := by decide
  rcases family_descends (prefixWord ++ tailWord_3549772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3549774 : List Nat := [4, 1, 1, 1, 1, 2, 3, 5, 4]
def baseStart_3549774 : Nat := 118140960795 + 3549774 * 2 ^ 59
def prefixEnd_3549774 : Nat := 4983230072969 + 3 ^ 40 * 3549774 * 2
def baseEnd_3549774 : Nat := 405053394851844383688865

theorem tailTrace_3549774 : CollatzResearch.WordTrace tailWord_3549774 prefixEnd_3549774 405053394851844383688865 := by
  unfold tailWord_3549774
  simp only [CollatzResearch.WordTrace]
  refine ⟨16183861780222815747254047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86313929494521683985354917 16183861780222815747254047)
  ·
    refine ⟨24275792670334223620881071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16183861780222815747254047 24275792670334223620881071)
    ·
      refine ⟨36413689005501335431321607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24275792670334223620881071 36413689005501335431321607)
      ·
        refine ⟨54620533508252003146982411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36413689005501335431321607 54620533508252003146982411)
        ·
          refine ⟨81930800262378004720473617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54620533508252003146982411 81930800262378004720473617)
          ·
            refine ⟨61448100196783503540355213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81930800262378004720473617 61448100196783503540355213)
            ·
              refine ⟨23043037573793813827633205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61448100196783503540355213 23043037573793813827633205)
              ·
                refine ⟨2160284772543170046340613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23043037573793813827633205 2160284772543170046340613)
                ·
                  refine ⟨405053394851844383688865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2160284772543170046340613 405053394851844383688865)
                  ·
                    rfl

theorem cell22_3549774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 5, 4].length) (baseStart_3549774 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3549774 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3549774 prefixEnd_3549774 := by exact prefixLift 3549774
  have htrace : WordTrace (prefixWord ++ tailWord_3549774) baseStart_3549774 baseEnd_3549774 := by
    simpa [prefixWord, tailWord_3549774, baseEnd_3549774] using wordTrace_append hprefix tailTrace_3549774
  have hstable : (prefixWord ++ tailWord_3549774).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3549774).length < 2 ^ (prefixWord ++ tailWord_3549774).sum := by decide
  have hdescent : baseEnd_3549774 < baseStart_3549774 := by decide
  rcases family_descends (prefixWord ++ tailWord_3549774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3549802 : List Nat := [3, 1, 3, 2, 1, 1, 2, 9]
def baseStart_3549802 : Nat := 118140960795 + 3549802 * 2 ^ 59
def prefixEnd_3549802 : Nat := 4983230072969 + 3 ^ 40 * 3549802 * 2
def baseEnd_3549802 : Nat := 135018863280861156818501

theorem tailTrace_3549802 : CollatzResearch.WordTrace tailWord_3549802 prefixEnd_3549802 135018863280861156818501 := by
  unfold tailWord_3549802
  simp only [CollatzResearch.WordTrace]
  refine ⟨32367978871420271690012915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86314610323787391173367773 32367978871420271690012915)
  ·
    refine ⟨48551968307130407535019373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32367978871420271690012915 48551968307130407535019373)
    ·
      refine ⟨18206988115173902825632265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48551968307130407535019373 18206988115173902825632265)
      ·
        refine ⟨13655241086380427119224199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18206988115173902825632265 13655241086380427119224199)
        ·
          refine ⟨20482861629570640678836299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13655241086380427119224199 20482861629570640678836299)
          ·
            refine ⟨30724292444355961018254449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20482861629570640678836299 30724292444355961018254449)
            ·
              refine ⟨23043219333266970763690837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30724292444355961018254449 23043219333266970763690837)
              ·
                refine ⟨135018863280861156818501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23043219333266970763690837 135018863280861156818501)
                ·
                  rfl

theorem cell22_3549802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 9].length) (baseStart_3549802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3549802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3549802 prefixEnd_3549802 := by exact prefixLift 3549802
  have htrace : WordTrace (prefixWord ++ tailWord_3549802) baseStart_3549802 baseEnd_3549802 := by
    simpa [prefixWord, tailWord_3549802, baseEnd_3549802] using wordTrace_append hprefix tailTrace_3549802
  have hstable : (prefixWord ++ tailWord_3549802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3549802).length < 2 ^ (prefixWord ++ tailWord_3549802).sum := by decide
  have hdescent : baseEnd_3549802 < baseStart_3549802 := by decide
  rcases family_descends (prefixWord ++ tailWord_3549802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3549806 : List Nat := [4, 1, 2, 2, 2, 3, 1, 1, 1, 5]
def baseStart_3549806 : Nat := 118140960795 + 3549806 * 2 ^ 59
def prefixEnd_3549806 : Nat := 4983230072969 + 3 ^ 40 * 3549806 * 2
def baseEnd_3549806 : Nat := 1215171138809495734266497

theorem tailTrace_3549806 : CollatzResearch.WordTrace tailWord_3549806 prefixEnd_3549806 1215171138809495734266497 := by
  unfold tailWord_3549806
  simp only [CollatzResearch.WordTrace]
  refine ⟨16184007672208324430399659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86314707585111063628798181 16184007672208324430399659)
  ·
    refine ⟨24276011508312486645599489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16184007672208324430399659 24276011508312486645599489)
    ·
      refine ⟨18207008631234364984199617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24276011508312486645599489 18207008631234364984199617)
      ·
        refine ⟨13655256473425773738149713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18207008631234364984199617 13655256473425773738149713)
        ·
          refine ⟨10241442355069330303612285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13655256473425773738149713 10241442355069330303612285)
          ·
            refine ⟨3840540883150998863854607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10241442355069330303612285 3840540883150998863854607)
            ·
              refine ⟨5760811324726498295781911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3840540883150998863854607 5760811324726498295781911)
              ·
                refine ⟨8641216987089747443672867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5760811324726498295781911 8641216987089747443672867)
                ·
                  refine ⟨12961825480634621165509301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8641216987089747443672867 12961825480634621165509301)
                  ·
                    refine ⟨1215171138809495734266497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12961825480634621165509301 1215171138809495734266497)
                    ·
                      rfl

theorem cell22_3549806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 1, 1, 1, 5].length) (baseStart_3549806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3549806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3549806 prefixEnd_3549806 := by exact prefixLift 3549806
  have htrace : WordTrace (prefixWord ++ tailWord_3549806) baseStart_3549806 baseEnd_3549806 := by
    simpa [prefixWord, tailWord_3549806, baseEnd_3549806] using wordTrace_append hprefix tailTrace_3549806
  have hstable : (prefixWord ++ tailWord_3549806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3549806).length < 2 ^ (prefixWord ++ tailWord_3549806).sum := by decide
  have hdescent : baseEnd_3549806 < baseStart_3549806 := by decide
  rcases family_descends (prefixWord ++ tailWord_3549806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3549847 : List Nat := [1, 1, 3, 3, 2, 1, 1, 3, 7]
def baseStart_3549847 : Nat := 118140960795 + 3549847 * 2 ^ 59
def prefixEnd_3549847 : Nat := 4983230072969 + 3 ^ 40 * 3549847 * 2
def baseEnd_3549847 : Nat := 405061724649128431330457

theorem tailTrace_3549847 : CollatzResearch.WordTrace tailWord_3549847 prefixEnd_3549847 405061724649128431330457 := by
  unfold tailWord_3549847
  simp only [CollatzResearch.WordTrace]
  refine ⟨129473556770518059445439795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86315704513678706296959863 129473556770518059445439795)
  ·
    refine ⟨194210335155777089168159693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129473556770518059445439795 194210335155777089168159693)
    ·
      refine ⟨72828875683416408438059885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 194210335155777089168159693 72828875683416408438059885)
      ·
        refine ⟨27310828381281153164272457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72828875683416408438059885 27310828381281153164272457)
        ·
          refine ⟨20483121285960864873204343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27310828381281153164272457 20483121285960864873204343)
          ·
            refine ⟨30724681928941297309806515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20483121285960864873204343 30724681928941297309806515)
            ·
              refine ⟨46087022893411945964709773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30724681928941297309806515 46087022893411945964709773)
              ·
                refine ⟨17282633585029479736766165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46087022893411945964709773 17282633585029479736766165)
                ·
                  refine ⟨405061724649128431330457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17282633585029479736766165 405061724649128431330457)
                  ·
                    rfl

theorem cell22_3549847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 3, 7].length) (baseStart_3549847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3549847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3549847 prefixEnd_3549847 := by exact prefixLift 3549847
  have htrace : WordTrace (prefixWord ++ tailWord_3549847) baseStart_3549847 baseEnd_3549847 := by
    simpa [prefixWord, tailWord_3549847, baseEnd_3549847] using wordTrace_append hprefix tailTrace_3549847
  have hstable : (prefixWord ++ tailWord_3549847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3549847).length < 2 ^ (prefixWord ++ tailWord_3549847).sum := by decide
  have hdescent : baseEnd_3549847 < baseStart_3549847 := by decide
  rcases family_descends (prefixWord ++ tailWord_3549847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3549924 : List Nat := [2, 3, 1, 1, 1, 4, 1, 3, 1, 5]
def baseStart_3549924 : Nat := 118140960795 + 3549924 * 2 ^ 59
def prefixEnd_3549924 : Nat := 4983230072969 + 3 ^ 40 * 3549924 * 2
def baseEnd_3549924 : Nat := 1215211532620982759816135

theorem tailTrace_3549924 : CollatzResearch.WordTrace tailWord_3549924 prefixEnd_3549924 1215211532620982759816135 := by
  unfold tailWord_3549924
  simp only [CollatzResearch.WordTrace]
  refine ⟨64738182595619550797996413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86317576794159401063995217 64738182595619550797996413)
  ·
    refine ⟨24276818473357331549248655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64738182595619550797996413 24276818473357331549248655)
    ·
      refine ⟨36415227710035997323872983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24276818473357331549248655 36415227710035997323872983)
      ·
        refine ⟨54622841565053995985809475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36415227710035997323872983 54622841565053995985809475)
        ·
          refine ⟨81934262347580993978714213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54622841565053995985809475 81934262347580993978714213)
          ·
            refine ⟨15362674190171436371008915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81934262347580993978714213 15362674190171436371008915)
            ·
              refine ⟨23044011285257154556513373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15362674190171436371008915 23044011285257154556513373)
              ·
                refine ⟨8641504231971432958692515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23044011285257154556513373 8641504231971432958692515)
                ·
                  refine ⟨12962256347957149438038773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8641504231971432958692515 12962256347957149438038773)
                  ·
                    refine ⟨1215211532620982759816135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12962256347957149438038773 1215211532620982759816135)
                    ·
                      rfl

theorem cell22_3549924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 3, 1, 5].length) (baseStart_3549924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3549924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3549924 prefixEnd_3549924 := by exact prefixLift 3549924
  have htrace : WordTrace (prefixWord ++ tailWord_3549924) baseStart_3549924 baseEnd_3549924 := by
    simpa [prefixWord, tailWord_3549924, baseEnd_3549924] using wordTrace_append hprefix tailTrace_3549924
  have hstable : (prefixWord ++ tailWord_3549924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3549924).length < 2 ^ (prefixWord ++ tailWord_3549924).sum := by decide
  have hdescent : baseEnd_3549924 < baseStart_3549924 := by decide
  rcases family_descends (prefixWord ++ tailWord_3549924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3549975 : List Nat := [1, 1, 3, 4, 3, 1, 3, 1, 2, 3]
def baseStart_3549975 : Nat := 118140960795 + 3549975 * 2 ^ 59
def prefixEnd_3549975 : Nat := 4983230072969 + 3 ^ 40 * 3549975 * 2
def baseEnd_3549975 : Nat := 1215228990963235626790979

theorem tailTrace_3549975 : CollatzResearch.WordTrace tailWord_3549975 prefixEnd_3549975 1215228990963235626790979 := by
  unfold tailWord_3549975
  simp only [CollatzResearch.WordTrace]
  refine ⟨129478225314054337306099379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86318816876036224870732919 129478225314054337306099379)
  ·
    refine ⟨194217337971081505959149069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129478225314054337306099379 194217337971081505959149069)
    ·
      refine ⟨72831501739155564734680901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 194217337971081505959149069 72831501739155564734680901)
      ·
        refine ⟨13655906576091668387752669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72831501739155564734680901 13655906576091668387752669)
        ·
          refine ⟨5120964966034375645407251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13655906576091668387752669 5120964966034375645407251)
          ·
            refine ⟨7681447449051563468110877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5120964966034375645407251 7681447449051563468110877)
            ·
              refine ⟨2880542793394336300541579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7681447449051563468110877 2880542793394336300541579)
              ·
                refine ⟨4320814190091504450812369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2880542793394336300541579 4320814190091504450812369)
                ·
                  refine ⟨3240610642568628338109277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4320814190091504450812369 3240610642568628338109277)
                  ·
                    refine ⟨1215228990963235626790979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3240610642568628338109277 1215228990963235626790979)
                    ·
                      rfl

theorem cell22_3549975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 3, 1, 2, 3].length) (baseStart_3549975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3549975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3549975 prefixEnd_3549975 := by exact prefixLift 3549975
  have htrace : WordTrace (prefixWord ++ tailWord_3549975) baseStart_3549975 baseEnd_3549975 := by
    simpa [prefixWord, tailWord_3549975, baseEnd_3549975] using wordTrace_append hprefix tailTrace_3549975
  have hstable : (prefixWord ++ tailWord_3549975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3549975).length < 2 ^ (prefixWord ++ tailWord_3549975).sum := by decide
  have hdescent : baseEnd_3549975 < baseStart_3549975 := by decide
  rcases family_descends (prefixWord ++ tailWord_3549975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3549988 : List Nat := [2, 3, 1, 3, 3, 2, 2, 6]
def baseStart_3549988 : Nat := 118140960795 + 3549988 * 2 ^ 59
def prefixEnd_3549988 : Nat := 4983230072969 + 3 ^ 40 * 3549988 * 2
def baseEnd_3549988 : Nat := 135025937903211991801771

theorem tailTrace_3549988 : CollatzResearch.WordTrace tailWord_3549988 prefixEnd_3549988 135025937903211991801771 := by
  unfold tailWord_3549988
  simp only [CollatzResearch.WordTrace]
  refine ⟨64739349731503620263161309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86319132975338160350881745 64739349731503620263161309)
  ·
    refine ⟨24277256149313857598685491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64739349731503620263161309 24277256149313857598685491)
    ·
      refine ⟨36415884223970786398028237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24277256149313857598685491 36415884223970786398028237)
      ·
        refine ⟨13655956583989044899260589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36415884223970786398028237 13655956583989044899260589)
        ·
          refine ⟨5120983718995891837222721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13655956583989044899260589 5120983718995891837222721)
          ·
            refine ⟨3840737789246918877917041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5120983718995891837222721 3840737789246918877917041)
            ·
              refine ⟨2880553341935189158437781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3840737789246918877917041 2880553341935189158437781)
              ·
                refine ⟨135025937903211991801771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2880553341935189158437781 135025937903211991801771)
                ·
                  rfl

theorem cell22_3549988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 2, 6].length) (baseStart_3549988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3549988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3549988 prefixEnd_3549988 := by exact prefixLift 3549988
  have htrace : WordTrace (prefixWord ++ tailWord_3549988) baseStart_3549988 baseEnd_3549988 := by
    simpa [prefixWord, tailWord_3549988, baseEnd_3549988] using wordTrace_append hprefix tailTrace_3549988
  have hstable : (prefixWord ++ tailWord_3549988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3549988).length < 2 ^ (prefixWord ++ tailWord_3549988).sum := by decide
  have hdescent : baseEnd_3549988 < baseStart_3549988 := by decide
  rcases family_descends (prefixWord ++ tailWord_3549988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3550059 : List Nat := [1, 1, 1, 1, 2, 2, 5, 1, 3, 5]
def baseStart_3550059 : Nat := 118140960795 + 3550059 * 2 ^ 59
def prefixEnd_3550059 : Nat := 4983230072969 + 3 ^ 40 * 3550059 * 2
def baseEnd_3550059 : Nat := 1215257745879887407690721

theorem tailTrace_3550059 : CollatzResearch.WordTrace tailWord_3550059 prefixEnd_3550059 1215257745879887407690721 := by
  unfold tailWord_3550059
  simp only [CollatzResearch.WordTrace]
  refine ⟨129481289045750019652157231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86320859363833346434771487 129481289045750019652157231)
  ·
    refine ⟨194221933568625029478235847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129481289045750019652157231 194221933568625029478235847)
    ·
      refine ⟨291332900352937544217353771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194221933568625029478235847 291332900352937544217353771)
      ·
        refine ⟨436999350529406316326030657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291332900352937544217353771 436999350529406316326030657)
        ·
          refine ⟨327749512897054737244522993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 436999350529406316326030657 327749512897054737244522993)
          ·
            refine ⟨245812134672791052933392245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 327749512897054737244522993 245812134672791052933392245)
            ·
              refine ⟨23044887625574161212505523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 245812134672791052933392245 23044887625574161212505523)
              ·
                refine ⟨34567331438361241818758285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23044887625574161212505523 34567331438361241818758285)
                ·
                  refine ⟨12962749289385465682034357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34567331438361241818758285 12962749289385465682034357)
                  ·
                    refine ⟨1215257745879887407690721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12962749289385465682034357 1215257745879887407690721)
                    ·
                      rfl

theorem cell22_3550059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 1, 3, 5].length) (baseStart_3550059 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3550059 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3550059 prefixEnd_3550059 := by exact prefixLift 3550059
  have htrace : WordTrace (prefixWord ++ tailWord_3550059) baseStart_3550059 baseEnd_3550059 := by
    simpa [prefixWord, tailWord_3550059, baseEnd_3550059] using wordTrace_append hprefix tailTrace_3550059
  have hstable : (prefixWord ++ tailWord_3550059).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3550059).length < 2 ^ (prefixWord ++ tailWord_3550059).sum := by decide
  have hdescent : baseEnd_3550059 < baseStart_3550059 := by decide
  rcases family_descends (prefixWord ++ tailWord_3550059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3550074 : List Nat := [3, 1, 1, 1, 1, 1, 3, 2, 3, 6]
def baseStart_3550074 : Nat := 118140960795 + 3550074 * 2 ^ 59
def prefixEnd_3550074 : Nat := 4983230072969 + 3 ^ 40 * 3550074 * 2
def baseEnd_3550074 : Nat := 1215262880686432368565675

theorem tailTrace_3550074 : CollatzResearch.WordTrace tailWord_3550074 prefixEnd_3550074 1215262880686432368565675 := by
  unfold tailWord_3550074
  simp only [CollatzResearch.WordTrace]
  refine ⟨32370459035173919303488319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86321224093797118142635517 32370459035173919303488319)
  ·
    refine ⟨48555688552760878955232479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32370459035173919303488319 48555688552760878955232479)
    ·
      refine ⟨72833532829141318432848719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48555688552760878955232479 72833532829141318432848719)
      ·
        refine ⟨109250299243711977649273079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72833532829141318432848719 109250299243711977649273079)
        ·
          refine ⟨163875448865567966473909619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109250299243711977649273079 163875448865567966473909619)
          ·
            refine ⟨245813173298351949710864429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163875448865567966473909619 245813173298351949710864429)
            ·
              refine ⟨92179939986881981141574161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 245813173298351949710864429 92179939986881981141574161)
              ·
                refine ⟨69134954990161485856180621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92179939986881981141574161 69134954990161485856180621)
                ·
                  refine ⟨25925608121310557196067733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69134954990161485856180621 25925608121310557196067733)
                  ·
                    refine ⟨1215262880686432368565675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25925608121310557196067733 1215262880686432368565675)
                    ·
                      rfl

theorem cell22_3550074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 3, 6].length) (baseStart_3550074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3550074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3550074 prefixEnd_3550074 := by exact prefixLift 3550074
  have htrace : WordTrace (prefixWord ++ tailWord_3550074) baseStart_3550074 baseEnd_3550074 := by
    simpa [prefixWord, tailWord_3550074, baseEnd_3550074] using wordTrace_append hprefix tailTrace_3550074
  have hstable : (prefixWord ++ tailWord_3550074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3550074).length < 2 ^ (prefixWord ++ tailWord_3550074).sum := by decide
  have hdescent : baseEnd_3550074 < baseStart_3550074 := by decide
  rcases family_descends (prefixWord ++ tailWord_3550074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3550076 : List Nat := [2, 2, 2, 1, 1, 1, 1, 5, 4, 3]
def baseStart_3550076 : Nat := 118140960795 + 3550076 * 2 ^ 59
def prefixEnd_3550076 : Nat := 4983230072969 + 3 ^ 40 * 3550076 * 2
def baseEnd_3550076 : Nat := 1215263565327305030015669

theorem tailTrace_3550076 : CollatzResearch.WordTrace tailWord_3550076 prefixEnd_3550076 1215263565327305030015669 := by
  unfold tailWord_3550076
  simp only [CollatzResearch.WordTrace]
  refine ⟨64740954543344215777763041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86321272724458954370350721 64740954543344215777763041)
  ·
    refine ⟨48555715907508161833322281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64740954543344215777763041 48555715907508161833322281)
    ·
      refine ⟨36416786930631121374991711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48555715907508161833322281 36416786930631121374991711)
      ·
        refine ⟨54625180395946682062487567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36416786930631121374991711 54625180395946682062487567)
        ·
          refine ⟨81937770593920023093731351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54625180395946682062487567 81937770593920023093731351)
          ·
            refine ⟨122906655890880034640597027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81937770593920023093731351 122906655890880034640597027)
            ·
              refine ⟨184359983836320051960895541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122906655890880034640597027 184359983836320051960895541)
              ·
                refine ⟨17283748484655004871333957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 184359983836320051960895541 17283748484655004871333957)
                ·
                  refine ⟨3240702840872813413375117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17283748484655004871333957 3240702840872813413375117)
                  ·
                    refine ⟨1215263565327305030015669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3240702840872813413375117 1215263565327305030015669)
                    ·
                      rfl

theorem cell22_3550076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 5, 4, 3].length) (baseStart_3550076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3550076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3550076 prefixEnd_3550076 := by exact prefixLift 3550076
  have htrace : WordTrace (prefixWord ++ tailWord_3550076) baseStart_3550076 baseEnd_3550076 := by
    simpa [prefixWord, tailWord_3550076, baseEnd_3550076] using wordTrace_append hprefix tailTrace_3550076
  have hstable : (prefixWord ++ tailWord_3550076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3550076).length < 2 ^ (prefixWord ++ tailWord_3550076).sum := by decide
  have hdescent : baseEnd_3550076 < baseStart_3550076 := by decide
  rcases family_descends (prefixWord ++ tailWord_3550076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3550108 : List Nat := [2, 2, 3, 3, 2, 1, 1, 1, 1, 6]
def baseStart_3550108 : Nat := 118140960795 + 3550108 * 2 ^ 59
def prefixEnd_3550108 : Nat := 4983230072969 + 3 ^ 40 * 3550108 * 2
def baseEnd_3550108 : Nat := 1215274519581267613215571

theorem tailTrace_3550108 : CollatzResearch.WordTrace tailWord_3550108 prefixEnd_3550108 1215274519581267613215571 := by
  unfold tailWord_3550108
  simp only [CollatzResearch.WordTrace]
  refine ⟨64741538111286250510345489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86322050815048334013793985 64741538111286250510345489)
  ·
    refine ⟨48556153583464687882759117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64741538111286250510345489 48556153583464687882759117)
    ·
      refine ⟨18208557593799257956034669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48556153583464687882759117 18208557593799257956034669)
      ·
        refine ⟨6828209097674721733513001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18208557593799257956034669 6828209097674721733513001)
        ·
          refine ⟨5121156823256041300134751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6828209097674721733513001 5121156823256041300134751)
          ·
            refine ⟨7681735234884061950202127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5121156823256041300134751 7681735234884061950202127)
            ·
              refine ⟨11522602852326092925303191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7681735234884061950202127 11522602852326092925303191)
              ·
                refine ⟨17283904278489139387954787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11522602852326092925303191 17283904278489139387954787)
                ·
                  refine ⟨25925856417733709081932181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17283904278489139387954787 25925856417733709081932181)
                  ·
                    refine ⟨1215274519581267613215571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25925856417733709081932181 1215274519581267613215571)
                    ·
                      rfl

theorem cell22_3550108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 1, 1, 6].length) (baseStart_3550108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3550108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3550108 prefixEnd_3550108 := by exact prefixLift 3550108
  have htrace : WordTrace (prefixWord ++ tailWord_3550108) baseStart_3550108 baseEnd_3550108 := by
    simpa [prefixWord, tailWord_3550108, baseEnd_3550108] using wordTrace_append hprefix tailTrace_3550108
  have hstable : (prefixWord ++ tailWord_3550108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3550108).length < 2 ^ (prefixWord ++ tailWord_3550108).sum := by decide
  have hdescent : baseEnd_3550108 < baseStart_3550108 := by decide
  rcases family_descends (prefixWord ++ tailWord_3550108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3550121 : List Nat := [1, 2, 1, 1, 1, 1, 5, 2, 5, 3]
def baseStart_3550121 : Nat := 118140960795 + 3550121 * 2 ^ 59
def prefixEnd_3550121 : Nat := 4983230072969 + 3 ^ 40 * 3550121 * 2
def baseEnd_3550121 : Nat := 1215278969746939912640531

theorem tailTrace_3550121 : CollatzResearch.WordTrace tailWord_3550121 prefixEnd_3550121 1215278969746939912640531 := by
  unfold tailWord_3550121
  simp only [CollatzResearch.WordTrace]
  refine ⟨129483550371525404240914217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86322366914350269493942811 129483550371525404240914217)
  ·
    refine ⟨97112662778644053180685663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129483550371525404240914217 97112662778644053180685663)
    ·
      refine ⟨145668994167966079771028495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97112662778644053180685663 145668994167966079771028495)
      ·
        refine ⟨218503491251949119656542743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145668994167966079771028495 218503491251949119656542743)
        ·
          refine ⟨327755236877923679484814115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218503491251949119656542743 327755236877923679484814115)
          ·
            refine ⟨491632855316885519227221173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 327755236877923679484814115 491632855316885519227221173)
            ·
              refine ⟨46090580185958017427551985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 491632855316885519227221173 46090580185958017427551985)
              ·
                refine ⟨34567935139468513070663989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46090580185958017427551985 34567935139468513070663989)
                ·
                  refine ⟨3240743919325173100374749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34567935139468513070663989 3240743919325173100374749)
                  ·
                    refine ⟨1215278969746939912640531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3240743919325173100374749 1215278969746939912640531)
                    ·
                      rfl

theorem cell22_3550121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 2, 5, 3].length) (baseStart_3550121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3550121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3550121 prefixEnd_3550121 := by exact prefixLift 3550121
  have htrace : WordTrace (prefixWord ++ tailWord_3550121) baseStart_3550121 baseEnd_3550121 := by
    simpa [prefixWord, tailWord_3550121, baseEnd_3550121] using wordTrace_append hprefix tailTrace_3550121
  have hstable : (prefixWord ++ tailWord_3550121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3550121).length < 2 ^ (prefixWord ++ tailWord_3550121).sum := by decide
  have hdescent : baseEnd_3550121 < baseStart_3550121 := by decide
  rcases family_descends (prefixWord ++ tailWord_3550121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3550138 : List Nat := [3, 1, 1, 1, 2, 1, 6, 1, 3, 3]
def baseStart_3550138 : Nat := 118140960795 + 3550138 * 2 ^ 59
def prefixEnd_3550138 : Nat := 4983230072969 + 3 ^ 40 * 3550138 * 2
def baseEnd_3550138 : Nat := 1215284789194357534965479

theorem tailTrace_3550138 : CollatzResearch.WordTrace tailWord_3550138 prefixEnd_3550138 1215284789194357534965479 := by
  unfold tailWord_3550138
  simp only [CollatzResearch.WordTrace]
  refine ⟨32371042603115954036070767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86322780274975877429522045 32371042603115954036070767)
  ·
    refine ⟨48556563904673931054106151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32371042603115954036070767 48556563904673931054106151)
    ·
      refine ⟨72834845857010896581159227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48556563904673931054106151 72834845857010896581159227)
      ·
        refine ⟨109252268785516344871738841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72834845857010896581159227 109252268785516344871738841)
        ·
          refine ⟨81939201589137258653804131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109252268785516344871738841 81939201589137258653804131)
          ·
            refine ⟨122908802383705887980706197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81939201589137258653804131 122908802383705887980706197)
            ·
              refine ⟨5761350111736213499095603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 122908802383705887980706197 5761350111736213499095603)
              ·
                refine ⟨8642025167604320248643405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5761350111736213499095603 8642025167604320248643405)
                ·
                  refine ⟨3240759437851620093241277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8642025167604320248643405 3240759437851620093241277)
                  ·
                    refine ⟨1215284789194357534965479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3240759437851620093241277 1215284789194357534965479)
                    ·
                      rfl

theorem cell22_3550138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 6, 1, 3, 3].length) (baseStart_3550138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3550138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3550138 prefixEnd_3550138 := by exact prefixLift 3550138
  have htrace : WordTrace (prefixWord ++ tailWord_3550138) baseStart_3550138 baseEnd_3550138 := by
    simpa [prefixWord, tailWord_3550138, baseEnd_3550138] using wordTrace_append hprefix tailTrace_3550138
  have hstable : (prefixWord ++ tailWord_3550138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3550138).length < 2 ^ (prefixWord ++ tailWord_3550138).sum := by decide
  have hdescent : baseEnd_3550138 < baseStart_3550138 := by decide
  rcases family_descends (prefixWord ++ tailWord_3550138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3550151 : List Nat := [1, 1, 4, 1, 1, 2, 2, 5, 5]
def baseStart_3550151 : Nat := 118140960795 + 3550151 * 2 ^ 59
def prefixEnd_3550151 : Nat := 4983230072969 + 3 ^ 40 * 3550151 * 2
def baseEnd_3550151 : Nat := 405096413120009944796813

theorem tailTrace_3550151 : CollatzResearch.WordTrace tailWord_3550151 prefixEnd_3550151 405096413120009944796813 := by
  unfold tailWord_3550151
  simp only [CollatzResearch.WordTrace]
  refine ⟨129484644561416719364506307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86323096374277812909670871 129484644561416719364506307)
  ·
    refine ⟨194226966842125079046759461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129484644561416719364506307 194226966842125079046759461)
    ·
      refine ⟨36417556282898452321267399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 194226966842125079046759461 36417556282898452321267399)
      ·
        refine ⟨54626334424347678481901099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36417556282898452321267399 54626334424347678481901099)
        ·
          refine ⟨81939501636521517722851649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54626334424347678481901099 81939501636521517722851649)
          ·
            refine ⟨61454626227391138292138737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81939501636521517722851649 61454626227391138292138737)
            ·
              refine ⟨46090969670543353719104053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61454626227391138292138737 46090969670543353719104053)
              ·
                refine ⟨4321028406613439411166005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46090969670543353719104053 4321028406613439411166005)
                ·
                  refine ⟨405096413120009944796813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4321028406613439411166005 405096413120009944796813)
                  ·
                    rfl

theorem cell22_3550151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 5, 5].length) (baseStart_3550151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3550151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3550151 prefixEnd_3550151 := by exact prefixLift 3550151
  have htrace : WordTrace (prefixWord ++ tailWord_3550151) baseStart_3550151 baseEnd_3550151 := by
    simpa [prefixWord, tailWord_3550151, baseEnd_3550151] using wordTrace_append hprefix tailTrace_3550151
  have hstable : (prefixWord ++ tailWord_3550151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3550151).length < 2 ^ (prefixWord ++ tailWord_3550151).sum := by decide
  have hdescent : baseEnd_3550151 < baseStart_3550151 := by decide
  rcases family_descends (prefixWord ++ tailWord_3550151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3550157 : List Nat := [1, 6, 3, 1, 1, 1, 1, 8]
def baseStart_3550157 : Nat := 118140960795 + 3550157 * 2 ^ 59
def prefixEnd_3550157 : Nat := 4983230072969 + 3 ^ 40 * 3550157 * 2
def baseEnd_3550157 : Nat := 135032365920294202082269

theorem tailTrace_3550157 : CollatzResearch.WordTrace tailWord_3550157 prefixEnd_3550157 135032365920294202082269 := by
  unfold tailWord_3550157
  simp only [CollatzResearch.WordTrace]
  refine ⟨129484863399394982389224725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86323242266263321592816483 129484863399394982389224725)
  ·
    refine ⟨6069602971846639799494909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 129484863399394982389224725 6069602971846639799494909)
    ·
      refine ⟨2276101114442489924810591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6069602971846639799494909 2276101114442489924810591)
      ·
        refine ⟨3414151671663734887215887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2276101114442489924810591 3414151671663734887215887)
        ·
          refine ⟨5121227507495602330823831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3414151671663734887215887 5121227507495602330823831)
          ·
            refine ⟨7681841261243403496235747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5121227507495602330823831 7681841261243403496235747)
            ·
              refine ⟨11522761891865105244353621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7681841261243403496235747 11522761891865105244353621)
              ·
                refine ⟨135032365920294202082269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11522761891865105244353621 135032365920294202082269)
                ·
                  rfl

theorem cell22_3550157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 8].length) (baseStart_3550157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3550157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3550157 prefixEnd_3550157 := by exact prefixLift 3550157
  have htrace : WordTrace (prefixWord ++ tailWord_3550157) baseStart_3550157 baseEnd_3550157 := by
    simpa [prefixWord, tailWord_3550157, baseEnd_3550157] using wordTrace_append hprefix tailTrace_3550157
  have hstable : (prefixWord ++ tailWord_3550157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3550157).length < 2 ^ (prefixWord ++ tailWord_3550157).sum := by decide
  have hdescent : baseEnd_3550157 < baseStart_3550157 := by decide
  rcases family_descends (prefixWord ++ tailWord_3550157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3550241 : List Nat := [1, 2, 3, 2, 3, 11]
def baseStart_3550241 : Nat := 118140960795 + 3550241 * 2 ^ 59
def prefixEnd_3550241 : Nat := 4983230072969 + 3 ^ 40 * 3550241 * 2
def baseEnd_3550241 : Nat := 15003951212337032094323

theorem tailTrace_3550241 : CollatzResearch.WordTrace tailWord_3550241 prefixEnd_3550241 15003951212337032094323 := by
  unfold tailWord_3550241
  simp only [CollatzResearch.WordTrace]
  refine ⟨129487927131090664735282577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86325284754060443156855051 129487927131090664735282577)
  ·
    refine ⟨97115945348317998551461933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129487927131090664735282577 97115945348317998551461933)
    ·
      refine ⟨36418479505619249456798225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97115945348317998551461933 36418479505619249456798225)
      ·
        refine ⟨27313859629214437092598669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36418479505619249456798225 27313859629214437092598669)
        ·
          refine ⟨10242697360955413909724501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27313859629214437092598669 10242697360955413909724501)
          ·
            refine ⟨15003951212337032094323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 10242697360955413909724501 15003951212337032094323)
            ·
              rfl

theorem cell22_3550241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 11].length) (baseStart_3550241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3550241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3550241 prefixEnd_3550241 := by exact prefixLift 3550241
  have htrace : WordTrace (prefixWord ++ tailWord_3550241) baseStart_3550241 baseEnd_3550241 := by
    simpa [prefixWord, tailWord_3550241, baseEnd_3550241] using wordTrace_append hprefix tailTrace_3550241
  have hstable : (prefixWord ++ tailWord_3550241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3550241).length < 2 ^ (prefixWord ++ tailWord_3550241).sum := by decide
  have hdescent : baseEnd_3550241 < baseStart_3550241 := by decide
  rcases family_descends (prefixWord ++ tailWord_3550241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3550243 : List Nat := [1, 1, 1, 4, 3, 2, 2, 2, 2, 4]
def baseStart_3550243 : Nat := 118140960795 + 3550243 * 2 ^ 59
def prefixEnd_3550243 : Nat := 4983230072969 + 3 ^ 40 * 3550243 * 2
def baseEnd_3550243 : Nat := 1215320732840172261090157

theorem tailTrace_3550243 : CollatzResearch.WordTrace tailWord_3550243 prefixEnd_3550243 1215320732840172261090157 := by
  unfold tailWord_3550243
  simp only [CollatzResearch.WordTrace]
  refine ⟨129488000077083419076855383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86325333384722279384570255 129488000077083419076855383)
  ·
    refine ⟨194232000115625128615283075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129488000077083419076855383 194232000115625128615283075)
    ·
      refine ⟨291348000173437692922924613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194232000115625128615283075 291348000173437692922924613)
      ·
        refine ⟨54627750032519567423048365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 291348000173437692922924613 54627750032519567423048365)
        ·
          refine ⟨20485406262194837783643137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54627750032519567423048365 20485406262194837783643137)
          ·
            refine ⟨15364054696646128337732353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20485406262194837783643137 15364054696646128337732353)
            ·
              refine ⟨11523041022484596253299265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15364054696646128337732353 11523041022484596253299265)
              ·
                refine ⟨8642280766863447189974449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11523041022484596253299265 8642280766863447189974449)
                ·
                  refine ⟨6481710575147585392480837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8642280766863447189974449 6481710575147585392480837)
                  ·
                    refine ⟨1215320732840172261090157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6481710575147585392480837 1215320732840172261090157)
                    ·
                      rfl

theorem cell22_3550243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 2, 2, 4].length) (baseStart_3550243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3550243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3550243 prefixEnd_3550243 := by exact prefixLift 3550243
  have htrace : WordTrace (prefixWord ++ tailWord_3550243) baseStart_3550243 baseEnd_3550243 := by
    simpa [prefixWord, tailWord_3550243, baseEnd_3550243] using wordTrace_append hprefix tailTrace_3550243
  have hstable : (prefixWord ++ tailWord_3550243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3550243).length < 2 ^ (prefixWord ++ tailWord_3550243).sum := by decide
  have hdescent : baseEnd_3550243 < baseStart_3550243 := by decide
  rcases family_descends (prefixWord ++ tailWord_3550243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3550245 : List Nat := [1, 3, 1, 2, 2, 2, 4, 2, 2, 3]
def baseStart_3550245 : Nat := 118140960795 + 3550245 * 2 ^ 59
def prefixEnd_3550245 : Nat := 4983230072969 + 3 ^ 40 * 3550245 * 2
def baseEnd_3550245 : Nat := 1215321417481044922540151

theorem tailTrace_3550245 : CollatzResearch.WordTrace tailWord_3550245 prefixEnd_3550245 1215321417481044922540151 := by
  unfold tailWord_3550245
  simp only [CollatzResearch.WordTrace]
  refine ⟨129488073023076173418428189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86325382015384115612285459 129488073023076173418428189)
  ·
    refine ⟨48558027383653565031910571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129488073023076173418428189 48558027383653565031910571)
    ·
      refine ⟨72837041075480347547865857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48558027383653565031910571 72837041075480347547865857)
      ·
        refine ⟨54627780806610260660899393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72837041075480347547865857 54627780806610260660899393)
        ·
          refine ⟨40970835604957695495674545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54627780806610260660899393 40970835604957695495674545)
          ·
            refine ⟨30728126703718271621755909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40970835604957695495674545 30728126703718271621755909)
            ·
              refine ⟨5761523756947175929079233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30728126703718271621755909 5761523756947175929079233)
              ·
                refine ⟨4321142817710381946809425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5761523756947175929079233 4321142817710381946809425)
                ·
                  refine ⟨3240857113282786460107069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4321142817710381946809425 3240857113282786460107069)
                  ·
                    refine ⟨1215321417481044922540151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3240857113282786460107069 1215321417481044922540151)
                    ·
                      rfl

theorem cell22_3550245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 4, 2, 2, 3].length) (baseStart_3550245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3550245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3550245 prefixEnd_3550245 := by exact prefixLift 3550245
  have htrace : WordTrace (prefixWord ++ tailWord_3550245) baseStart_3550245 baseEnd_3550245 := by
    simpa [prefixWord, tailWord_3550245, baseEnd_3550245] using wordTrace_append hprefix tailTrace_3550245
  have hstable : (prefixWord ++ tailWord_3550245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3550245).length < 2 ^ (prefixWord ++ tailWord_3550245).sum := by decide
  have hdescent : baseEnd_3550245 < baseStart_3550245 := by decide
  rcases family_descends (prefixWord ++ tailWord_3550245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3550247 : List Nat := [1, 1, 7, 1, 1, 2, 1, 4, 4]
def baseStart_3550247 : Nat := 118140960795 + 3550247 * 2 ^ 59
def prefixEnd_3550247 : Nat := 4983230072969 + 3 ^ 40 * 3550247 * 2
def baseEnd_3550247 : Nat := 405107367373972527996715

theorem tailTrace_3550247 : CollatzResearch.WordTrace tailWord_3550247 prefixEnd_3550247 405107367373972527996715 := by
  unfold tailWord_3550247
  simp only [CollatzResearch.WordTrace]
  refine ⟨129488145969068927760000995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86325430646045951840000663 129488145969068927760000995)
  ·
    refine ⟨194232218953603391640001493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129488145969068927760000995 194232218953603391640001493)
    ·
      refine ⟨4552317631725079491562535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 194232218953603391640001493 4552317631725079491562535)
      ·
        refine ⟨6828476447587619237343803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4552317631725079491562535 6828476447587619237343803)
        ·
          refine ⟨10242714671381428856015705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6828476447587619237343803 10242714671381428856015705)
          ·
            refine ⟨7682036003536071642011779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10242714671381428856015705 7682036003536071642011779)
            ·
              refine ⟨11523054005304107463017669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7682036003536071642011779 11523054005304107463017669)
              ·
                refine ⟨2160572625994520149315813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11523054005304107463017669 2160572625994520149315813)
                ·
                  refine ⟨405107367373972527996715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2160572625994520149315813 405107367373972527996715)
                  ·
                    rfl

theorem cell22_3550247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 4, 4].length) (baseStart_3550247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3550247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3550247 prefixEnd_3550247 := by exact prefixLift 3550247
  have htrace : WordTrace (prefixWord ++ tailWord_3550247) baseStart_3550247 baseEnd_3550247 := by
    simpa [prefixWord, tailWord_3550247, baseEnd_3550247] using wordTrace_append hprefix tailTrace_3550247
  have hstable : (prefixWord ++ tailWord_3550247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3550247).length < 2 ^ (prefixWord ++ tailWord_3550247).sum := by decide
  have hdescent : baseEnd_3550247 < baseStart_3550247 := by decide
  rcases family_descends (prefixWord ++ tailWord_3550247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3550262 : List Nat := [5, 1, 2, 1, 1, 2, 2, 3, 2, 3]
def baseStart_3550262 : Nat := 118140960795 + 3550262 * 2 ^ 59
def prefixEnd_3550262 : Nat := 4983230072969 + 3 ^ 40 * 3550262 * 2
def baseEnd_3550262 : Nat := 1215327236928462544865099

theorem tailTrace_3550262 : CollatzResearch.WordTrace tailWord_3550262 prefixEnd_3550262 1215327236928462544865099 := by
  unfold tailWord_3550262
  simp only [CollatzResearch.WordTrace]
  refine ⟨8093043316500911582612315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 86325795376009723547864693 8093043316500911582612315)
  ·
    refine ⟨12139564974751367373918473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8093043316500911582612315 12139564974751367373918473)
    ·
      refine ⟨9104673731063525530438855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12139564974751367373918473 9104673731063525530438855)
      ·
        refine ⟨13657010596595288295658283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9104673731063525530438855 13657010596595288295658283)
        ·
          refine ⟨20485515894892932443487425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13657010596595288295658283 20485515894892932443487425)
          ·
            refine ⟨15364136921169699332615569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20485515894892932443487425 15364136921169699332615569)
            ·
              refine ⟨11523102690877274499461677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15364136921169699332615569 11523102690877274499461677)
              ·
                refine ⟨4321163509078977937298129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11523102690877274499461677 4321163509078977937298129)
                ·
                  refine ⟨3240872631809233452973597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4321163509078977937298129 3240872631809233452973597)
                  ·
                    refine ⟨1215327236928462544865099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3240872631809233452973597 1215327236928462544865099)
                    ·
                      rfl

theorem cell22_3550262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 3, 2, 3].length) (baseStart_3550262 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3550262 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3550262 prefixEnd_3550262 := by exact prefixLift 3550262
  have htrace : WordTrace (prefixWord ++ tailWord_3550262) baseStart_3550262 baseEnd_3550262 := by
    simpa [prefixWord, tailWord_3550262, baseEnd_3550262] using wordTrace_append hprefix tailTrace_3550262
  have hstable : (prefixWord ++ tailWord_3550262).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3550262).length < 2 ^ (prefixWord ++ tailWord_3550262).sum := by decide
  have hdescent : baseEnd_3550262 < baseStart_3550262 := by decide
  rcases family_descends (prefixWord ++ tailWord_3550262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3550271 : List Nat := [1, 1, 2, 2, 3, 1, 1, 1, 4, 6]
def baseStart_3550271 : Nat := 118140960795 + 3550271 * 2 ^ 59
def prefixEnd_3550271 : Nat := 4983230072969 + 3 ^ 40 * 3550271 * 2
def baseEnd_3550271 : Nat := 1215330317812389521390071

theorem tailTrace_3550271 : CollatzResearch.WordTrace tailWord_3550271 prefixEnd_3550271 1215330317812389521390071 := by
  unfold tailWord_3550271
  simp only [CollatzResearch.WordTrace]
  refine ⟨129489021320981979858874667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86326014213987986572583111 129489021320981979858874667)
  ·
    refine ⟨194233531981472969788312001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129489021320981979858874667 194233531981472969788312001)
    ·
      refine ⟨145675148986104727341234001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194233531981472969788312001 145675148986104727341234001)
      ·
        refine ⟨109256361739578545505925501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145675148986104727341234001 109256361739578545505925501)
        ·
          refine ⟨40971135652341954564722063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109256361739578545505925501 40971135652341954564722063)
          ·
            refine ⟨61456703478512931847083095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40971135652341954564722063 61456703478512931847083095)
            ·
              refine ⟨92185055217769397770624643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61456703478512931847083095 92185055217769397770624643)
              ·
                refine ⟨138277582826654096655936965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92185055217769397770624643 138277582826654096655936965)
                ·
                  refine ⟨25927046779997643122988181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 138277582826654096655936965 25927046779997643122988181)
                  ·
                    refine ⟨1215330317812389521390071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25927046779997643122988181 1215330317812389521390071)
                    ·
                      rfl

theorem cell22_3550271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 4, 6].length) (baseStart_3550271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3550271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3550271 prefixEnd_3550271 := by exact prefixLift 3550271
  have htrace : WordTrace (prefixWord ++ tailWord_3550271) baseStart_3550271 baseEnd_3550271 := by
    simpa [prefixWord, tailWord_3550271, baseEnd_3550271] using wordTrace_append hprefix tailTrace_3550271
  have hstable : (prefixWord ++ tailWord_3550271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3550271).length < 2 ^ (prefixWord ++ tailWord_3550271).sum := by decide
  have hdescent : baseEnd_3550271 < baseStart_3550271 := by decide
  rcases family_descends (prefixWord ++ tailWord_3550271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3550320 : List Nat := [2, 1, 1, 1, 5, 1, 5, 1, 5]
def baseStart_3550320 : Nat := 118140960795 + 3550320 * 2 ^ 59
def prefixEnd_3550320 : Nat := 4983230072969 + 3 ^ 40 * 3550320 * 2
def baseEnd_3550320 : Nat := 405115697171256575638307

theorem tailTrace_3550320 : CollatzResearch.WordTrace tailWord_3550320 prefixEnd_3550320 405115697171256575638307 := by
  unfold tailWord_3550320
  simp only [CollatzResearch.WordTrace]
  refine ⟨64745404248902230613704207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86327205665202974151605609 64745404248902230613704207)
  ·
    refine ⟨97118106373353345920556311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64745404248902230613704207 97118106373353345920556311)
    ·
      refine ⟨145677159560030018880834467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97118106373353345920556311 145677159560030018880834467)
      ·
        refine ⟨218515739340045028321251701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145677159560030018880834467 218515739340045028321251701)
        ·
          refine ⟨20485850563129221405117347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 218515739340045028321251701 20485850563129221405117347)
          ·
            refine ⟨30728775844693832107676021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20485850563129221405117347 30728775844693832107676021)
            ·
              refine ⟨2880822735440046760094627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30728775844693832107676021 2880822735440046760094627)
              ·
                refine ⟨4321234103160070140141941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2880822735440046760094627 4321234103160070140141941)
                ·
                  refine ⟨405115697171256575638307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4321234103160070140141941 405115697171256575638307)
                  ·
                    rfl

theorem cell22_3550320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 5, 1, 5].length) (baseStart_3550320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3550320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3550320 prefixEnd_3550320 := by exact prefixLift 3550320
  have htrace : WordTrace (prefixWord ++ tailWord_3550320) baseStart_3550320 baseEnd_3550320 := by
    simpa [prefixWord, tailWord_3550320, baseEnd_3550320] using wordTrace_append hprefix tailTrace_3550320
  have hstable : (prefixWord ++ tailWord_3550320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3550320).length < 2 ^ (prefixWord ++ tailWord_3550320).sum := by decide
  have hdescent : baseEnd_3550320 < baseStart_3550320 := by decide
  rcases family_descends (prefixWord ++ tailWord_3550320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3550341 : List Nat := [1, 3, 1, 1, 7, 1, 1, 3, 1, 3]
def baseStart_3550341 : Nat := 118140960795 + 3550341 * 2 ^ 59
def prefixEnd_3550341 : Nat := 4983230072969 + 3 ^ 40 * 3550341 * 2
def baseEnd_3550341 : Nat := 1215354280242932672139857

theorem tailTrace_3550341 : CollatzResearch.WordTrace tailWord_3550341 prefixEnd_3550341 1215354280242932672139857 := by
  unfold tailWord_3550341
  simp only [CollatzResearch.WordTrace]
  refine ⟨129491574430728381813922877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86327716287152254542615251 129491574430728381813922877)
  ·
    refine ⟨48559340411523143180221079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129491574430728381813922877 48559340411523143180221079)
    ·
      refine ⟨72839010617284714770331619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48559340411523143180221079 72839010617284714770331619)
      ·
        refine ⟨109258515925927072155497429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72839010617284714770331619 109258515925927072155497429)
        ·
          refine ⟨2560746467013915753644471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 109258515925927072155497429 2560746467013915753644471)
          ·
            refine ⟨3841119700520873630466707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2560746467013915753644471 3841119700520873630466707)
            ·
              refine ⟨5761679550781310445700061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3841119700520873630466707 5761679550781310445700061)
              ·
                refine ⟨2160629831542991417137523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5761679550781310445700061 2160629831542991417137523)
                ·
                  refine ⟨3240944747314487125706285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2160629831542991417137523 3240944747314487125706285)
                  ·
                    refine ⟨1215354280242932672139857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3240944747314487125706285 1215354280242932672139857)
                    ·
                      rfl

theorem cell22_3550341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 1, 3, 1, 3].length) (baseStart_3550341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3550341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3550341 prefixEnd_3550341 := by exact prefixLift 3550341
  have htrace : WordTrace (prefixWord ++ tailWord_3550341) baseStart_3550341 baseEnd_3550341 := by
    simpa [prefixWord, tailWord_3550341, baseEnd_3550341] using wordTrace_append hprefix tailTrace_3550341
  have hstable : (prefixWord ++ tailWord_3550341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3550341).length < 2 ^ (prefixWord ++ tailWord_3550341).sum := by decide
  have hdescent : baseEnd_3550341 < baseStart_3550341 := by decide
  rcases family_descends (prefixWord ++ tailWord_3550341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3550393 : List Nat := [1, 2, 1, 4, 1, 3, 2, 8]
def baseStart_3550393 : Nat := 118140960795 + 3550393 * 2 ^ 59
def prefixEnd_3550393 : Nat := 4983230072969 + 3 ^ 40 * 3550393 * 2
def baseEnd_3550393 : Nat := 135041342322846874426633

theorem tailTrace_3550393 : CollatzResearch.WordTrace tailWord_3550393 prefixEnd_3550393 135041342322846874426633 := by
  unfold tailWord_3550393
  simp only [CollatzResearch.WordTrace]
  refine ⟨129493471026539994694815833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86328980684359996463210555 129493471026539994694815833)
  ·
    refine ⟨97120103269904996021111875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129493471026539994694815833 97120103269904996021111875)
    ·
      refine ⟨145680154904857494031667813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97120103269904996021111875 145680154904857494031667813)
      ·
        refine ⟨27315029044660780130937715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 145680154904857494031667813 27315029044660780130937715)
        ·
          refine ⟨40972543566991170196406573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27315029044660780130937715 40972543566991170196406573)
          ·
            refine ⟨15364703837621688823652465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40972543566991170196406573 15364703837621688823652465)
            ·
              refine ⟨11523527878216266617739349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15364703837621688823652465 11523527878216266617739349)
              ·
                refine ⟨135041342322846874426633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11523527878216266617739349 135041342322846874426633)
                ·
                  rfl

theorem cell22_3550393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 8].length) (baseStart_3550393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3550393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3550393 prefixEnd_3550393 := by exact prefixLift 3550393
  have htrace : WordTrace (prefixWord ++ tailWord_3550393) baseStart_3550393 baseEnd_3550393 := by
    simpa [prefixWord, tailWord_3550393, baseEnd_3550393] using wordTrace_append hprefix tailTrace_3550393
  have hstable : (prefixWord ++ tailWord_3550393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3550393).length < 2 ^ (prefixWord ++ tailWord_3550393).sum := by decide
  have hdescent : baseEnd_3550393 < baseStart_3550393 := by decide
  rcases family_descends (prefixWord ++ tailWord_3550393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3550414 : List Nat := [4, 1, 1, 1, 5, 1, 2, 2, 2, 3]
def baseStart_3550414 : Nat := 118140960795 + 3550414 * 2 ^ 59
def prefixEnd_3550414 : Nat := 4983230072969 + 3 ^ 40 * 3550414 * 2
def baseEnd_3550414 : Nat := 1215379269634784815064633

theorem tailTrace_3550414 : CollatzResearch.WordTrace tailWord_3550414 prefixEnd_3550414 1215379269634784815064633 := by
  unfold tailWord_3550414
  simp only [CollatzResearch.WordTrace]
  refine ⟨16186779619932989410166287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86329491306309276854220197 16186779619932989410166287)
  ·
    refine ⟨24280169429899484115249431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16186779619932989410166287 24280169429899484115249431)
    ·
      refine ⟨36420254144849226172874147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24280169429899484115249431 36420254144849226172874147)
      ·
        refine ⟨54630381217273839259311221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36420254144849226172874147 54630381217273839259311221)
        ·
          refine ⟨5121598239119422430560427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54630381217273839259311221 5121598239119422430560427)
          ·
            refine ⟨7682397358679133645840641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5121598239119422430560427 7682397358679133645840641)
            ·
              refine ⟨5761798019009350234380481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7682397358679133645840641 5761798019009350234380481)
              ·
                refine ⟨4321348514257012675785361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5761798019009350234380481 4321348514257012675785361)
                ·
                  refine ⟨3241011385692759506839021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4321348514257012675785361 3241011385692759506839021)
                  ·
                    refine ⟨1215379269634784815064633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3241011385692759506839021 1215379269634784815064633)
                    ·
                      rfl

theorem cell22_3550414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 2, 2, 2, 3].length) (baseStart_3550414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3550414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3550414 prefixEnd_3550414 := by exact prefixLift 3550414
  have htrace : WordTrace (prefixWord ++ tailWord_3550414) baseStart_3550414 baseEnd_3550414 := by
    simpa [prefixWord, tailWord_3550414, baseEnd_3550414] using wordTrace_append hprefix tailTrace_3550414
  have hstable : (prefixWord ++ tailWord_3550414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3550414).length < 2 ^ (prefixWord ++ tailWord_3550414).sum := by decide
  have hdescent : baseEnd_3550414 < baseStart_3550414 := by decide
  rcases family_descends (prefixWord ++ tailWord_3550414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3550423 : List Nat := [1, 1, 3, 2, 1, 2, 3, 1, 2, 6]
def baseStart_3550423 : Nat := 118140960795 + 3550423 * 2 ^ 59
def prefixEnd_3550423 : Nat := 4983230072969 + 3 ^ 40 * 3550423 * 2
def baseEnd_3550423 : Nat := 1215382350518711791589605

theorem tailTrace_3550423 : CollatzResearch.WordTrace tailWord_3550423 prefixEnd_3550423 1215382350518711791589605 := by
  unfold tailWord_3550423
  simp only [CollatzResearch.WordTrace]
  refine ⟨129494565216431309818407923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86329710144287539878938615 129494565216431309818407923)
  ·
    refine ⟨194241847824646964727611885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129494565216431309818407923 194241847824646964727611885)
    ·
      refine ⟨72840692934242611772854457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 194241847824646964727611885 72840692934242611772854457)
      ·
        refine ⟨54630519700681958829640843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72840692934242611772854457 54630519700681958829640843)
        ·
          refine ⟨81945779551022938244461265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54630519700681958829640843 81945779551022938244461265)
          ·
            refine ⟨61459334663267203683345949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81945779551022938244461265 61459334663267203683345949)
            ·
              refine ⟨23047250498725201381254731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61459334663267203683345949 23047250498725201381254731)
              ·
                refine ⟨34570875748087802071882097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23047250498725201381254731 34570875748087802071882097)
                ·
                  refine ⟨25928156811065851553911573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34570875748087802071882097 25928156811065851553911573)
                  ·
                    refine ⟨1215382350518711791589605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25928156811065851553911573 1215382350518711791589605)
                    ·
                      rfl

theorem cell22_3550423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 1, 2, 6].length) (baseStart_3550423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3550423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3550423 prefixEnd_3550423 := by exact prefixLift 3550423
  have htrace : WordTrace (prefixWord ++ tailWord_3550423) baseStart_3550423 baseEnd_3550423 := by
    simpa [prefixWord, tailWord_3550423, baseEnd_3550423] using wordTrace_append hprefix tailTrace_3550423
  have hstable : (prefixWord ++ tailWord_3550423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3550423).length < 2 ^ (prefixWord ++ tailWord_3550423).sum := by decide
  have hdescent : baseEnd_3550423 < baseStart_3550423 := by decide
  rcases family_descends (prefixWord ++ tailWord_3550423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3550425 : List Nat := [1, 2, 1, 2, 3, 1, 1, 5, 3, 3]
def baseStart_3550425 : Nat := 118140960795 + 3550425 * 2 ^ 59
def prefixEnd_3550425 : Nat := 4983230072969 + 3 ^ 40 * 3550425 * 2
def baseEnd_3550425 : Nat := 1215383035159584453039599

theorem tailTrace_3550425 : CollatzResearch.WordTrace tailWord_3550425 prefixEnd_3550425 1215383035159584453039599 := by
  unfold tailWord_3550425
  simp only [CollatzResearch.WordTrace]
  refine ⟨129494638162424064159980729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86329758774949376106653819 129494638162424064159980729)
  ·
    refine ⟨97120978621818048119985547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129494638162424064159980729 97120978621818048119985547)
    ·
      refine ⟨145681467932727072179978321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97120978621818048119985547 145681467932727072179978321)
      ·
        refine ⟨109261100949545304134983741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145681467932727072179978321 109261100949545304134983741)
        ·
          refine ⟨40972912856079489050618903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109261100949545304134983741 40972912856079489050618903)
          ·
            refine ⟨61459369284119233575928355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40972912856079489050618903 61459369284119233575928355)
            ·
              refine ⟨92189053926178850363892533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61459369284119233575928355 92189053926178850363892533)
              ·
                refine ⟨8642723805579267221614925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 92189053926178850363892533 8642723805579267221614925)
                ·
                  refine ⟨3241021427092225208105597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8642723805579267221614925 3241021427092225208105597)
                  ·
                    refine ⟨1215383035159584453039599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3241021427092225208105597 1215383035159584453039599)
                    ·
                      rfl

theorem cell22_3550425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 5, 3, 3].length) (baseStart_3550425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3550425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3550425 prefixEnd_3550425 := by exact prefixLift 3550425
  have htrace : WordTrace (prefixWord ++ tailWord_3550425) baseStart_3550425 baseEnd_3550425 := by
    simpa [prefixWord, tailWord_3550425, baseEnd_3550425] using wordTrace_append hprefix tailTrace_3550425
  have hstable : (prefixWord ++ tailWord_3550425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3550425).length < 2 ^ (prefixWord ++ tailWord_3550425).sum := by decide
  have hdescent : baseEnd_3550425 < baseStart_3550425 := by decide
  rcases family_descends (prefixWord ++ tailWord_3550425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3550442 : List Nat := [3, 1, 3, 1, 1, 4, 1, 2, 3, 3]
def baseStart_3550442 : Nat := 118140960795 + 3550442 * 2 ^ 59
def prefixEnd_3550442 : Nat := 4983230072969 + 3 ^ 40 * 3550442 * 2
def baseEnd_3550442 : Nat := 1215388854607002075364547

theorem tailTrace_3550442 : CollatzResearch.WordTrace tailWord_3550442 prefixEnd_3550442 1215388854607002075364547 := by
  unfold tailWord_3550442
  simp only [CollatzResearch.WordTrace]
  refine ⟨32373814550840619015837395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86330172135574984042233053 32373814550840619015837395)
  ·
    refine ⟨48560721826260928523756093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32373814550840619015837395 48560721826260928523756093)
    ·
      refine ⟨18210270684847848196408535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48560721826260928523756093 18210270684847848196408535)
      ·
        refine ⟨27315406027271772294612803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18210270684847848196408535 27315406027271772294612803)
        ·
          refine ⟨40973109040907658441919205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27315406027271772294612803 40973109040907658441919205)
          ·
            refine ⟨7682457945170185957859851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40973109040907658441919205 7682457945170185957859851)
            ·
              refine ⟨11523686917755278936789777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7682457945170185957859851 11523686917755278936789777)
              ·
                refine ⟨8642765188316459202592333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11523686917755278936789777 8642765188316459202592333)
                ·
                  refine ⟨3241036945618672200972125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8642765188316459202592333 3241036945618672200972125)
                  ·
                    refine ⟨1215388854607002075364547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3241036945618672200972125 1215388854607002075364547)
                    ·
                      rfl

theorem cell22_3550442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 2, 3, 3].length) (baseStart_3550442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3550442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3550442 prefixEnd_3550442 := by exact prefixLift 3550442
  have htrace : WordTrace (prefixWord ++ tailWord_3550442) baseStart_3550442 baseEnd_3550442 := by
    simpa [prefixWord, tailWord_3550442, baseEnd_3550442] using wordTrace_append hprefix tailTrace_3550442
  have hstable : (prefixWord ++ tailWord_3550442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3550442).length < 2 ^ (prefixWord ++ tailWord_3550442).sum := by decide
  have hdescent : baseEnd_3550442 < baseStart_3550442 := by decide
  rcases family_descends (prefixWord ++ tailWord_3550442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3550500 : List Nat := [2, 3, 1, 3, 1, 1, 1, 4, 6]
def baseStart_3550500 : Nat := 118140960795 + 3550500 * 2 ^ 59
def prefixEnd_3550500 : Nat := 4983230072969 + 3 ^ 40 * 3550500 * 2
def baseEnd_3550500 : Nat := 405136236397436419138123

theorem tailTrace_3550500 : CollatzResearch.WordTrace tailWord_3550500 prefixEnd_3550500 405136236397436419138123 := by
  unfold tailWord_3550500
  simp only [CollatzResearch.WordTrace]
  refine ⟨64748686818576175984480477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86331582424768234645973969 64748686818576175984480477)
  ·
    refine ⟨24280757556966065994180179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64748686818576175984480477 24280757556966065994180179)
    ·
      refine ⟨36421136335449098991270269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24280757556966065994180179 36421136335449098991270269)
      ·
        refine ⟨13657926125793412121726351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36421136335449098991270269 13657926125793412121726351)
        ·
          refine ⟨20486889188690118182589527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13657926125793412121726351 20486889188690118182589527)
          ·
            refine ⟨30730333783035177273884291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20486889188690118182589527 30730333783035177273884291)
            ·
              refine ⟨46095500674552765910826437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30730333783035177273884291 46095500674552765910826437)
              ·
                refine ⟨8642906376478643608279957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46095500674552765910826437 8642906376478643608279957)
                ·
                  refine ⟨405136236397436419138123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8642906376478643608279957 405136236397436419138123)
                  ·
                    rfl

theorem cell22_3550500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 4, 6].length) (baseStart_3550500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3550500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3550500 prefixEnd_3550500 := by exact prefixLift 3550500
  have htrace : WordTrace (prefixWord ++ tailWord_3550500) baseStart_3550500 baseEnd_3550500 := by
    simpa [prefixWord, tailWord_3550500, baseEnd_3550500] using wordTrace_append hprefix tailTrace_3550500
  have hstable : (prefixWord ++ tailWord_3550500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3550500).length < 2 ^ (prefixWord ++ tailWord_3550500).sum := by decide
  have hdescent : baseEnd_3550500 < baseStart_3550500 := by decide
  rcases family_descends (prefixWord ++ tailWord_3550500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3550545 : List Nat := [1, 2, 2, 1, 4, 1, 4, 7]
def baseStart_3550545 : Nat := 118140960795 + 3550545 * 2 ^ 59
def prefixEnd_3550545 : Nat := 4983230072969 + 3 ^ 40 * 3550545 * 2
def baseEnd_3550545 : Nat := 135047123734660460004359

theorem tailTrace_3550545 : CollatzResearch.WordTrace tailWord_3550545 prefixEnd_3550545 135047123734660460004359 := by
  unfold tailWord_3550545
  simp only [CollatzResearch.WordTrace]
  refine ⟨129499014921989324654349089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86332676614659549769566059 129499014921989324654349089)
  ·
    refine ⟨97124261191491993490761817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129499014921989324654349089 97124261191491993490761817)
    ·
      refine ⟨72843195893618995118071363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97124261191491993490761817 72843195893618995118071363)
      ·
        refine ⟨109264793840428492677107045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72843195893618995118071363 109264793840428492677107045)
        ·
          refine ⟨20487148845080342376957571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 109264793840428492677107045 20487148845080342376957571)
          ·
            refine ⟨30730723267620513565436357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20487148845080342376957571 30730723267620513565436357)
            ·
              refine ⟨5762010612678846293519317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30730723267620513565436357 5762010612678846293519317)
              ·
                refine ⟨135047123734660460004359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5762010612678846293519317 135047123734660460004359)
                ·
                  rfl

theorem cell22_3550545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 4, 7].length) (baseStart_3550545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3550545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3550545 prefixEnd_3550545 := by exact prefixLift 3550545
  have htrace : WordTrace (prefixWord ++ tailWord_3550545) baseStart_3550545 baseEnd_3550545 := by
    simpa [prefixWord, tailWord_3550545, baseEnd_3550545] using wordTrace_append hprefix tailTrace_3550545
  have hstable : (prefixWord ++ tailWord_3550545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3550545).length < 2 ^ (prefixWord ++ tailWord_3550545).sum := by decide
  have hdescent : baseEnd_3550545 < baseStart_3550545 := by decide
  rcases family_descends (prefixWord ++ tailWord_3550545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3550549 : List Nat := [1, 3, 2, 2, 3, 2, 1, 3, 2, 3]
def baseStart_3550549 : Nat := 118140960795 + 3550549 * 2 ^ 59
def prefixEnd_3550549 : Nat := 4983230072969 + 3 ^ 40 * 3550549 * 2
def baseEnd_3550549 : Nat := 1215425482893689462939219

theorem tailTrace_3550549 : CollatzResearch.WordTrace tailWord_3550549 prefixEnd_3550549 1215425482893689462939219 := by
  unfold tailWord_3550549
  simp only [CollatzResearch.WordTrace]
  refine ⟨129499160813974833337494701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86332773875983222224996467 129499160813974833337494701)
  ·
    refine ⟨48562185305240562501560513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129499160813974833337494701 48562185305240562501560513)
    ·
      refine ⟨36421638978930421876170385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48562185305240562501560513 36421638978930421876170385)
      ·
        refine ⟨27316229234197816407127789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36421638978930421876170385 27316229234197816407127789)
        ·
          refine ⟨10243585962824181152672921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27316229234197816407127789 10243585962824181152672921)
          ·
            refine ⟨7682689472118135864504691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10243585962824181152672921 7682689472118135864504691)
            ·
              refine ⟨11524034208177203796757037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7682689472118135864504691 11524034208177203796757037)
              ·
                refine ⟨4321512828066451423783889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11524034208177203796757037 4321512828066451423783889)
                ·
                  refine ⟨3241134621049838567837917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4321512828066451423783889 3241134621049838567837917)
                  ·
                    refine ⟨1215425482893689462939219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3241134621049838567837917 1215425482893689462939219)
                    ·
                      rfl

theorem cell22_3550549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 3, 2, 3].length) (baseStart_3550549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3550549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3550549 prefixEnd_3550549 := by exact prefixLift 3550549
  have htrace : WordTrace (prefixWord ++ tailWord_3550549) baseStart_3550549 baseEnd_3550549 := by
    simpa [prefixWord, tailWord_3550549, baseEnd_3550549] using wordTrace_append hprefix tailTrace_3550549
  have hstable : (prefixWord ++ tailWord_3550549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3550549).length < 2 ^ (prefixWord ++ tailWord_3550549).sum := by decide
  have hdescent : baseEnd_3550549 < baseStart_3550549 := by decide
  rcases family_descends (prefixWord ++ tailWord_3550549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3550650 : List Nat := [3, 1, 1, 1, 2, 1, 1, 1, 2, 9]
def baseStart_3550650 : Nat := 118140960795 + 3550650 * 2 ^ 59
def prefixEnd_3550650 : Nat := 4983230072969 + 3 ^ 40 * 3550650 * 2
def baseEnd_3550650 : Nat := 1215460057257758866163909

theorem tailTrace_3550650 : CollatzResearch.WordTrace tailWord_3550650 prefixEnd_3550650 1215460057257758866163909 := by
  unfold tailWord_3550650
  simp only [CollatzResearch.WordTrace]
  refine ⟨32375711146652231896730351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86335229724405951724614269 32375711146652231896730351)
  ·
    refine ⟨48563566719978347845095527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32375711146652231896730351 48563566719978347845095527)
    ·
      refine ⟨72845350079967521767643291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48563566719978347845095527 72845350079967521767643291)
      ·
        refine ⟨109268025119951282651464937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72845350079967521767643291 109268025119951282651464937)
        ·
          refine ⟨81951018839963461988598703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109268025119951282651464937 81951018839963461988598703)
          ·
            refine ⟨122926528259945192982898055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81951018839963461988598703 122926528259945192982898055)
            ·
              refine ⟨184389792389917789474347083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122926528259945192982898055 184389792389917789474347083)
              ·
                refine ⟨276584688584876684211520625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 184389792389917789474347083 276584688584876684211520625)
                ·
                  refine ⟨207438516438657513158640469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 276584688584876684211520625 207438516438657513158640469)
                  ·
                    refine ⟨1215460057257758866163909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 207438516438657513158640469 1215460057257758866163909)
                    ·
                      rfl

theorem cell22_3550650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 2, 9].length) (baseStart_3550650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3550650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3550650 prefixEnd_3550650 := by exact prefixLift 3550650
  have htrace : WordTrace (prefixWord ++ tailWord_3550650) baseStart_3550650 baseEnd_3550650 := by
    simpa [prefixWord, tailWord_3550650, baseEnd_3550650] using wordTrace_append hprefix tailTrace_3550650
  have hstable : (prefixWord ++ tailWord_3550650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3550650).length < 2 ^ (prefixWord ++ tailWord_3550650).sum := by decide
  have hdescent : baseEnd_3550650 < baseStart_3550650 := by decide
  rcases family_descends (prefixWord ++ tailWord_3550650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3550667 : List Nat := [1, 1, 1, 1, 3, 3, 5, 1, 1, 5]
def baseStart_3550667 : Nat := 118140960795 + 3550667 * 2 ^ 59
def prefixEnd_3550667 : Nat := 4983230072969 + 3 ^ 40 * 3550667 * 2
def baseEnd_3550667 : Nat := 1215465876705176488488857

theorem tailTrace_3550667 : CollatzResearch.WordTrace tailWord_3550667 prefixEnd_3550667 1215465876705176488488857 := by
  unfold tailWord_3550667
  simp only [CollatzResearch.WordTrace]
  refine ⟨129503464627547339490290255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86335643085031559660193503 129503464627547339490290255)
  ·
    refine ⟨194255196941321009235435383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129503464627547339490290255 194255196941321009235435383)
    ·
      refine ⟨291382795411981513853153075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194255196941321009235435383 291382795411981513853153075)
      ·
        refine ⟨437074193117972270779729613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291382795411981513853153075 437074193117972270779729613)
        ·
          refine ⟨163902822419239601542398605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 437074193117972270779729613 163902822419239601542398605)
          ·
            refine ⟨61463558407214850578399477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 163902822419239601542398605 61463558407214850578399477)
            ·
              refine ⟨5762208600676392241724951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61463558407214850578399477 5762208600676392241724951)
              ·
                refine ⟨8643312901014588362587427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5762208600676392241724951 8643312901014588362587427)
                ·
                  refine ⟨12964969351521882543881141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8643312901014588362587427 12964969351521882543881141)
                  ·
                    refine ⟨1215465876705176488488857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12964969351521882543881141 1215465876705176488488857)
                    ·
                      rfl

theorem cell22_3550667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 5, 1, 1, 5].length) (baseStart_3550667 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3550667 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3550667 prefixEnd_3550667 := by exact prefixLift 3550667
  have htrace : WordTrace (prefixWord ++ tailWord_3550667) baseStart_3550667 baseEnd_3550667 := by
    simpa [prefixWord, tailWord_3550667, baseEnd_3550667] using wordTrace_append hprefix tailTrace_3550667
  have hstable : (prefixWord ++ tailWord_3550667).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3550667).length < 2 ^ (prefixWord ++ tailWord_3550667).sum := by decide
  have hdescent : baseEnd_3550667 < baseStart_3550667 := by decide
  rcases family_descends (prefixWord ++ tailWord_3550667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3550682 : List Nat := [3, 1, 1, 2, 3, 2, 2, 1, 1, 6]
def baseStart_3550682 : Nat := 118140960795 + 3550682 * 2 ^ 59
def prefixEnd_3550682 : Nat := 4983230072969 + 3 ^ 40 * 3550682 * 2
def baseEnd_3550682 : Nat := 1215471011511721449363811

theorem tailTrace_3550682 : CollatzResearch.WordTrace tailWord_3550682 prefixEnd_3550682 1215471011511721449363811 := by
  unfold tailWord_3550682
  simp only [CollatzResearch.WordTrace]
  refine ⟨32376002930623249263021575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86336007814995331368057533 32376002930623249263021575)
  ·
    refine ⟨48564004395934873894532363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32376002930623249263021575 48564004395934873894532363)
    ·
      refine ⟨72846006593902310841798545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48564004395934873894532363 72846006593902310841798545)
      ·
        refine ⟨54634504945426733131348909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72846006593902310841798545 54634504945426733131348909)
        ·
          refine ⟨20487939354535024924255841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54634504945426733131348909 20487939354535024924255841)
          ·
            refine ⟨15365954515901268693191881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20487939354535024924255841 15365954515901268693191881)
            ·
              refine ⟨11524465886925951519893911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15365954515901268693191881 11524465886925951519893911)
              ·
                refine ⟨17286698830388927279840867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11524465886925951519893911 17286698830388927279840867)
                ·
                  refine ⟨25930048245583390919761301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17286698830388927279840867 25930048245583390919761301)
                  ·
                    refine ⟨1215471011511721449363811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25930048245583390919761301 1215471011511721449363811)
                    ·
                      rfl

theorem cell22_3550682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 1, 1, 6].length) (baseStart_3550682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3550682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3550682 prefixEnd_3550682 := by exact prefixLift 3550682
  have htrace : WordTrace (prefixWord ++ tailWord_3550682) baseStart_3550682 baseEnd_3550682 := by
    simpa [prefixWord, tailWord_3550682, baseEnd_3550682] using wordTrace_append hprefix tailTrace_3550682
  have hstable : (prefixWord ++ tailWord_3550682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3550682).length < 2 ^ (prefixWord ++ tailWord_3550682).sum := by decide
  have hdescent : baseEnd_3550682 < baseStart_3550682 := by decide
  rcases family_descends (prefixWord ++ tailWord_3550682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3550746 : List Nat := [3, 1, 1, 3, 1, 1, 1, 7, 1, 3]
def baseStart_3550746 : Nat := 118140960795 + 3550746 * 2 ^ 59
def prefixEnd_3550746 : Nat := 4983230072969 + 3 ^ 40 * 3550746 * 2
def baseEnd_3550746 : Nat := 1215492920019646615763615

theorem tailTrace_3550746 : CollatzResearch.WordTrace tailWord_3550746 prefixEnd_3550746 1215492920019646615763615 := by
  unfold tailWord_3550746
  simp only [CollatzResearch.WordTrace]
  refine ⟨32376586498565283995604023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86337563996174090654944061 32376586498565283995604023)
  ·
    refine ⟨48564879747847925993406035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32376586498565283995604023 48564879747847925993406035)
    ·
      refine ⟨72847319621771888990109053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48564879747847925993406035 72847319621771888990109053)
      ·
        refine ⟨27317744858164458371290895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72847319621771888990109053 27317744858164458371290895)
        ·
          refine ⟨40976617287246687556936343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27317744858164458371290895 40976617287246687556936343)
          ·
            refine ⟨61464925930870031335404515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40976617287246687556936343 61464925930870031335404515)
            ·
              refine ⟨92197388896305047003106773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61464925930870031335404515 92197388896305047003106773)
              ·
                refine ⟨2160876302257149539135315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 92197388896305047003106773 2160876302257149539135315)
                ·
                  refine ⟨3241314453385724308702973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2160876302257149539135315 3241314453385724308702973)
                  ·
                    refine ⟨1215492920019646615763615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3241314453385724308702973 1215492920019646615763615)
                    ·
                      rfl

theorem cell22_3550746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 7, 1, 3].length) (baseStart_3550746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3550746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3550746 prefixEnd_3550746 := by exact prefixLift 3550746
  have htrace : WordTrace (prefixWord ++ tailWord_3550746) baseStart_3550746 baseEnd_3550746 := by
    simpa [prefixWord, tailWord_3550746, baseEnd_3550746] using wordTrace_append hprefix tailTrace_3550746
  have hstable : (prefixWord ++ tailWord_3550746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3550746).length < 2 ^ (prefixWord ++ tailWord_3550746).sum := by decide
  have hdescent : baseEnd_3550746 < baseStart_3550746 := by decide
  rcases family_descends (prefixWord ++ tailWord_3550746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3550757 : List Nat := [1, 3, 1, 2, 2, 1, 1, 4, 2, 5]
def baseStart_3550757 : Nat := 118140960795 + 3550757 * 2 ^ 59
def prefixEnd_3550757 : Nat := 4983230072969 + 3 ^ 40 * 3550757 * 2
def baseEnd_3550757 : Nat := 1215496685544446253738581

theorem tailTrace_3550757 : CollatzResearch.WordTrace tailWord_3550757 prefixEnd_3550757 1215496685544446253738581 := by
  unfold tailWord_3550757
  simp only [CollatzResearch.WordTrace]
  refine ⟨129506747197221284861066525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86337831464814189907377683 129506747197221284861066525)
  ·
    refine ⟨48565030198957981822899947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129506747197221284861066525 48565030198957981822899947)
    ·
      refine ⟨72847545298436972734349921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48565030198957981822899947 72847545298436972734349921)
      ·
        refine ⟨54635658973827729550762441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72847545298436972734349921 54635658973827729550762441)
        ·
          refine ⟨40976744230370797163071831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54635658973827729550762441 40976744230370797163071831)
          ·
            refine ⟨61465116345556195744607747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40976744230370797163071831 61465116345556195744607747)
            ·
              refine ⟨92197674518334293616911621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61465116345556195744607747 92197674518334293616911621)
              ·
                refine ⟨17287063972187680053170929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 92197674518334293616911621 17287063972187680053170929)
                ·
                  refine ⟨12965297979140760039878197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17287063972187680053170929 12965297979140760039878197)
                  ·
                    refine ⟨1215496685544446253738581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12965297979140760039878197 1215496685544446253738581)
                    ·
                      rfl

theorem cell22_3550757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 4, 2, 5].length) (baseStart_3550757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3550757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3550757 prefixEnd_3550757 := by exact prefixLift 3550757
  have htrace : WordTrace (prefixWord ++ tailWord_3550757) baseStart_3550757 baseEnd_3550757 := by
    simpa [prefixWord, tailWord_3550757, baseEnd_3550757] using wordTrace_append hprefix tailTrace_3550757
  have hstable : (prefixWord ++ tailWord_3550757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3550757).length < 2 ^ (prefixWord ++ tailWord_3550757).sum := by decide
  have hdescent : baseEnd_3550757 < baseStart_3550757 := by decide
  rcases family_descends (prefixWord ++ tailWord_3550757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3550789 : List Nat := [1, 3, 1, 1, 1, 4, 2, 4, 1, 4]
def baseStart_3550789 : Nat := 118140960795 + 3550789 * 2 ^ 59
def prefixEnd_3550789 : Nat := 4983230072969 + 3 ^ 40 * 3550789 * 2
def baseEnd_3550789 : Nat := 1215507639798408836938483

theorem tailTrace_3550789 : CollatzResearch.WordTrace tailWord_3550789 prefixEnd_3550789 1215507639798408836938483 := by
  unfold tailWord_3550789
  simp only [CollatzResearch.WordTrace]
  refine ⟨129507914333105354326231421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86338609555403569550820947 129507914333105354326231421)
  ·
    refine ⟨48565467874914507872336783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129507914333105354326231421 48565467874914507872336783)
    ·
      refine ⟨72848201812371761808505175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48565467874914507872336783 72848201812371761808505175)
      ·
        refine ⟨109272302718557642712757763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72848201812371761808505175 109272302718557642712757763)
        ·
          refine ⟨163908454077836464069136645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109272302718557642712757763 163908454077836464069136645)
          ·
            refine ⟨30732835139594337012963121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 163908454077836464069136645 30732835139594337012963121)
            ·
              refine ⟨23049626354695752759722341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30732835139594337012963121 23049626354695752759722341)
              ·
                refine ⟨4321804941505453642447939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23049626354695752759722341 4321804941505453642447939)
                ·
                  refine ⟨6482707412258180463671909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4321804941505453642447939 6482707412258180463671909)
                  ·
                    refine ⟨1215507639798408836938483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6482707412258180463671909 1215507639798408836938483)
                    ·
                      rfl

theorem cell22_3550789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 4, 1, 4].length) (baseStart_3550789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3550789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3550789 prefixEnd_3550789 := by exact prefixLift 3550789
  have htrace : WordTrace (prefixWord ++ tailWord_3550789) baseStart_3550789 baseEnd_3550789 := by
    simpa [prefixWord, tailWord_3550789, baseEnd_3550789] using wordTrace_append hprefix tailTrace_3550789
  have hstable : (prefixWord ++ tailWord_3550789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3550789).length < 2 ^ (prefixWord ++ tailWord_3550789).sum := by decide
  have hdescent : baseEnd_3550789 < baseStart_3550789 := by decide
  rcases family_descends (prefixWord ++ tailWord_3550789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3550821 : List Nat := [1, 3, 1, 3, 3, 1, 2, 4, 4]
def baseStart_3550821 : Nat := 118140960795 + 3550821 * 2 ^ 59
def prefixEnd_3550821 : Nat := 4983230072969 + 3 ^ 40 * 3550821 * 2
def baseEnd_3550821 : Nat := 405172864684123806712795

theorem tailTrace_3550821 : CollatzResearch.WordTrace tailWord_3550821 prefixEnd_3550821 405172864684123806712795 := by
  unfold tailWord_3550821
  simp only [CollatzResearch.WordTrace]
  refine ⟨129509081468989423791396317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86339387645992949194264211 129509081468989423791396317)
  ·
    refine ⟨48565905550871033921773619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129509081468989423791396317 48565905550871033921773619)
    ·
      refine ⟨72848858326306550882660429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48565905550871033921773619 72848858326306550882660429)
      ·
        refine ⟨27318321872364956580997661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72848858326306550882660429 27318321872364956580997661)
        ·
          refine ⟨10244370702136858717874123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27318321872364956580997661 10244370702136858717874123)
          ·
            refine ⟨15366556053205288076811185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10244370702136858717874123 15366556053205288076811185)
            ·
              refine ⟨11524917039903966057608389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15366556053205288076811185 11524917039903966057608389)
              ·
                refine ⟨2160921944981993635801573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11524917039903966057608389 2160921944981993635801573)
                ·
                  refine ⟨405172864684123806712795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2160921944981993635801573 405172864684123806712795)
                  ·
                    rfl

theorem cell22_3550821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 4, 4].length) (baseStart_3550821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3550821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3550821 prefixEnd_3550821 := by exact prefixLift 3550821
  have htrace : WordTrace (prefixWord ++ tailWord_3550821) baseStart_3550821 baseEnd_3550821 := by
    simpa [prefixWord, tailWord_3550821, baseEnd_3550821] using wordTrace_append hprefix tailTrace_3550821
  have hstable : (prefixWord ++ tailWord_3550821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3550821).length < 2 ^ (prefixWord ++ tailWord_3550821).sum := by decide
  have hdescent : baseEnd_3550821 < baseStart_3550821 := by decide
  rcases family_descends (prefixWord ++ tailWord_3550821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3550834 : List Nat := [3, 2, 1, 2, 3, 1, 1, 2, 1, 6]
def baseStart_3550834 : Nat := 118140960795 + 3550834 * 2 ^ 59
def prefixEnd_3550834 : Nat := 4983230072969 + 3 ^ 40 * 3550834 * 2
def baseEnd_3550834 : Nat := 1215523044218043719563345

theorem tailTrace_3550834 : CollatzResearch.WordTrace tailWord_3550834 prefixEnd_3550834 1215523044218043719563345 := by
  unfold tailWord_3550834
  simp only [CollatzResearch.WordTrace]
  refine ⟨32377388904485581752904889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86339703745294884674413037 32377388904485581752904889)
  ·
    refine ⟨24283041678364186314678667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32377388904485581752904889 24283041678364186314678667)
    ·
      refine ⟨36424562517546279472018001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24283041678364186314678667 36424562517546279472018001)
      ·
        refine ⟨27318421888159709604013501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36424562517546279472018001 27318421888159709604013501)
        ·
          refine ⟨10244408208059891101505063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27318421888159709604013501 10244408208059891101505063)
          ·
            refine ⟨15366612312089836652257595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10244408208059891101505063 15366612312089836652257595)
            ·
              refine ⟨23049918468134754978386393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15366612312089836652257595 23049918468134754978386393)
              ·
                refine ⟨17287438851101066233789795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23049918468134754978386393 17287438851101066233789795)
                ·
                  refine ⟨25931158276651599350684693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17287438851101066233789795 25931158276651599350684693)
                  ·
                    refine ⟨1215523044218043719563345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25931158276651599350684693 1215523044218043719563345)
                    ·
                      rfl

theorem cell22_3550834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 2, 1, 6].length) (baseStart_3550834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3550834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3550834 prefixEnd_3550834 := by exact prefixLift 3550834
  have htrace : WordTrace (prefixWord ++ tailWord_3550834) baseStart_3550834 baseEnd_3550834 := by
    simpa [prefixWord, tailWord_3550834, baseEnd_3550834] using wordTrace_append hprefix tailTrace_3550834
  have hstable : (prefixWord ++ tailWord_3550834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3550834).length < 2 ^ (prefixWord ++ tailWord_3550834).sum := by decide
  have hdescent : baseEnd_3550834 < baseStart_3550834 := by decide
  rcases family_descends (prefixWord ++ tailWord_3550834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3550849 : List Nat := [1, 2, 4, 2, 1, 3, 1, 8]
def baseStart_3550849 : Nat := 118140960795 + 3550849 * 2 ^ 59
def prefixEnd_3550849 : Nat := 4983230072969 + 3 ^ 40 * 3550849 * 2
def baseEnd_3550849 : Nat := 135058686558287631159811

theorem tailTrace_3550849 : CollatzResearch.WordTrace tailWord_3550849 prefixEnd_3550849 135058686558287631159811 := by
  unfold tailWord_3550849
  simp only [CollatzResearch.WordTrace]
  refine ⟨129510102712887984573415601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86340068475258656382277067 129510102712887984573415601)
  ·
    refine ⟨97132577034665988430061701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129510102712887984573415601 97132577034665988430061701)
    ·
      refine ⟨18212358193999872830636569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97132577034665988430061701 18212358193999872830636569)
      ·
        refine ⟨13659268645499904622977427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18212358193999872830636569 13659268645499904622977427)
        ·
          refine ⟨20488902968249856934466141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13659268645499904622977427 20488902968249856934466141)
          ·
            refine ⟨7683338613093696350424803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20488902968249856934466141 7683338613093696350424803)
            ·
              refine ⟨11525007919640544525637205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7683338613093696350424803 11525007919640544525637205)
              ·
                refine ⟨135058686558287631159811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11525007919640544525637205 135058686558287631159811)
                ·
                  rfl

theorem cell22_3550849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 8].length) (baseStart_3550849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3550849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3550849 prefixEnd_3550849 := by exact prefixLift 3550849
  have htrace : WordTrace (prefixWord ++ tailWord_3550849) baseStart_3550849 baseEnd_3550849 := by
    simpa [prefixWord, tailWord_3550849, baseEnd_3550849] using wordTrace_append hprefix tailTrace_3550849
  have hstable : (prefixWord ++ tailWord_3550849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3550849).length < 2 ^ (prefixWord ++ tailWord_3550849).sum := by decide
  have hdescent : baseEnd_3550849 < baseStart_3550849 := by decide
  rcases family_descends (prefixWord ++ tailWord_3550849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3550864 : List Nat := [2, 1, 1, 1, 1, 1, 3, 4, 5, 3]
def baseStart_3550864 : Nat := 118140960795 + 3550864 * 2 ^ 59
def prefixEnd_3550864 : Nat := 4983230072969 + 3 ^ 40 * 3550864 * 2
def baseEnd_3550864 : Nat := 1215533313831133641313253

theorem tailTrace_3550864 : CollatzResearch.WordTrace tailWord_3550864 prefixEnd_3550864 1215533313831133641313253 := by
  unfold tailWord_3550864
  simp only [CollatzResearch.WordTrace]
  refine ⟨64755324903916821067605823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86340433205222428090141097 64755324903916821067605823)
  ·
    refine ⟨97132987355875231601408735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64755324903916821067605823 97132987355875231601408735)
    ·
      refine ⟨145699481033812847402113103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97132987355875231601408735 145699481033812847402113103)
      ·
        refine ⟨218549221550719271103169655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145699481033812847402113103 218549221550719271103169655)
        ·
          refine ⟨327823832326078906654754483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218549221550719271103169655 327823832326078906654754483)
          ·
            refine ⟨491735748489118359982131725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 327823832326078906654754483 491735748489118359982131725)
            ·
              refine ⟨184400905683419384993299397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 491735748489118359982131725 184400905683419384993299397)
              ·
                refine ⟨34575169815641134686243637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 184400905683419384993299397 34575169815641134686243637)
                ·
                  refine ⟨3241422170216356376835341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34575169815641134686243637 3241422170216356376835341)
                  ·
                    refine ⟨1215533313831133641313253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3241422170216356376835341 1215533313831133641313253)
                    ·
                      rfl

theorem cell22_3550864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 4, 5, 3].length) (baseStart_3550864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3550864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3550864 prefixEnd_3550864 := by exact prefixLift 3550864
  have htrace : WordTrace (prefixWord ++ tailWord_3550864) baseStart_3550864 baseEnd_3550864 := by
    simpa [prefixWord, tailWord_3550864, baseEnd_3550864] using wordTrace_append hprefix tailTrace_3550864
  have hstable : (prefixWord ++ tailWord_3550864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3550864).length < 2 ^ (prefixWord ++ tailWord_3550864).sum := by decide
  have hdescent : baseEnd_3550864 < baseStart_3550864 := by decide
  rcases family_descends (prefixWord ++ tailWord_3550864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3550866 : List Nat := [3, 2, 3, 1, 3, 2, 8]
def baseStart_3550866 : Nat := 118140960795 + 3550866 * 2 ^ 59
def prefixEnd_3550866 : Nat := 4983230072969 + 3 ^ 40 * 3550866 * 2
def baseEnd_3550866 : Nat := 45019777721185418620861

theorem tailTrace_3550866 : CollatzResearch.WordTrace tailWord_3550866 prefixEnd_3550866 45019777721185418620861 := by
  unfold tailWord_3550866
  simp only [CollatzResearch.WordTrace]
  refine ⟨32377680688456599119196113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86340481835884264317856301 32377680688456599119196113)
  ·
    refine ⟨24283260516342449339397085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32377680688456599119196113 24283260516342449339397085)
    ·
      refine ⟨9106222693628418502273907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24283260516342449339397085 9106222693628418502273907)
      ·
        refine ⟨13659334040442627753410861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9106222693628418502273907 13659334040442627753410861)
        ·
          refine ⟨5122250265165985407529073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13659334040442627753410861 5122250265165985407529073)
          ·
            refine ⟨3841687698874489055646805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5122250265165985407529073 3841687698874489055646805)
            ·
              refine ⟨45019777721185418620861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3841687698874489055646805 45019777721185418620861)
              ·
                rfl

theorem cell22_3550866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 8].length) (baseStart_3550866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3550866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3550866 prefixEnd_3550866 := by exact prefixLift 3550866
  have htrace : WordTrace (prefixWord ++ tailWord_3550866) baseStart_3550866 baseEnd_3550866 := by
    simpa [prefixWord, tailWord_3550866, baseEnd_3550866] using wordTrace_append hprefix tailTrace_3550866
  have hstable : (prefixWord ++ tailWord_3550866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3550866).length < 2 ^ (prefixWord ++ tailWord_3550866).sum := by decide
  have hdescent : baseEnd_3550866 < baseStart_3550866 := by decide
  rcases family_descends (prefixWord ++ tailWord_3550866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3550868 : List Nat := [2, 4, 2, 2, 2, 1, 1, 2, 2, 4]
def baseStart_3550868 : Nat := 118140960795 + 3550868 * 2 ^ 59
def prefixEnd_3550868 : Nat := 4983230072969 + 3 ^ 40 * 3550868 * 2
def baseEnd_3550868 : Nat := 1215534683112878964213241

theorem tailTrace_3550868 : CollatzResearch.WordTrace tailWord_3550868 prefixEnd_3550868 1215534683112878964213241 := by
  unfold tailWord_3550868
  simp only [CollatzResearch.WordTrace]
  refine ⟨64755397849909575409178629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86340530466546100545571505 64755397849909575409178629)
  ·
    refine ⟨12141637096858045389220993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64755397849909575409178629 12141637096858045389220993)
    ·
      refine ⟨9106227822643534041915745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12141637096858045389220993 9106227822643534041915745)
      ·
        refine ⟨6829670866982650531436809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9106227822643534041915745 6829670866982650531436809)
        ·
          refine ⟨5122253150236987898577607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6829670866982650531436809 5122253150236987898577607)
          ·
            refine ⟨7683379725355481847866411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5122253150236987898577607 7683379725355481847866411)
            ·
              refine ⟨11525069588033222771799617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7683379725355481847866411 11525069588033222771799617)
              ·
                refine ⟨8643802191024917078849713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11525069588033222771799617 8643802191024917078849713)
                ·
                  refine ⟨6482851643268687809137285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8643802191024917078849713 6482851643268687809137285)
                  ·
                    refine ⟨1215534683112878964213241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6482851643268687809137285 1215534683112878964213241)
                    ·
                      rfl

theorem cell22_3550868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_3550868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3550868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3550868 prefixEnd_3550868 := by exact prefixLift 3550868
  have htrace : WordTrace (prefixWord ++ tailWord_3550868) baseStart_3550868 baseEnd_3550868 := by
    simpa [prefixWord, tailWord_3550868, baseEnd_3550868] using wordTrace_append hprefix tailTrace_3550868
  have hstable : (prefixWord ++ tailWord_3550868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3550868).length < 2 ^ (prefixWord ++ tailWord_3550868).sum := by decide
  have hdescent : baseEnd_3550868 < baseStart_3550868 := by decide
  rcases family_descends (prefixWord ++ tailWord_3550868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3550932 : List Nat := [2, 4, 1, 3, 1, 1, 4, 2, 1, 3]
def baseStart_3550932 : Nat := 118140960795 + 3550932 * 2 ^ 59
def prefixEnd_3550932 : Nat := 4983230072969 + 3 ^ 40 * 3550932 * 2
def baseEnd_3550932 : Nat := 1215556591620804130613045

theorem tailTrace_3550932 : CollatzResearch.WordTrace tailWord_3550932 prefixEnd_3550932 1215556591620804130613045 := by
  unfold tailWord_3550932
  simp only [CollatzResearch.WordTrace]
  refine ⟨64756564985793644874343525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86342086647724859832458033 64756564985793644874343525)
  ·
    refine ⟨12141855934836308413939411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64756564985793644874343525 12141855934836308413939411)
    ·
      refine ⟨18212783902254462620909117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12141855934836308413939411 18212783902254462620909117)
      ·
        refine ⟨6829793963345423482840919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18212783902254462620909117 6829793963345423482840919)
        ·
          refine ⟨10244690945018135224261379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6829793963345423482840919 10244690945018135224261379)
          ·
            refine ⟨15367036417527202836392069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10244690945018135224261379 15367036417527202836392069)
            ·
              refine ⟨2881319328286350531823513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15367036417527202836392069 2881319328286350531823513)
              ·
                refine ⟨2160989496214762898867635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2881319328286350531823513 2160989496214762898867635)
                ·
                  refine ⟨3241484244322144348301453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2160989496214762898867635 3241484244322144348301453)
                  ·
                    refine ⟨1215556591620804130613045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3241484244322144348301453 1215556591620804130613045)
                    ·
                      rfl

theorem cell22_3550932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 4, 2, 1, 3].length) (baseStart_3550932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3550932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3550932 prefixEnd_3550932 := by exact prefixLift 3550932
  have htrace : WordTrace (prefixWord ++ tailWord_3550932) baseStart_3550932 baseEnd_3550932 := by
    simpa [prefixWord, tailWord_3550932, baseEnd_3550932] using wordTrace_append hprefix tailTrace_3550932
  have hstable : (prefixWord ++ tailWord_3550932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3550932).length < 2 ^ (prefixWord ++ tailWord_3550932).sum := by decide
  have hdescent : baseEnd_3550932 < baseStart_3550932 := by decide
  rcases family_descends (prefixWord ++ tailWord_3550932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3550984 : List Nat := [2, 1, 3, 2, 2, 1, 11]
def baseStart_3550984 : Nat := 118140960795 + 3550984 * 2 ^ 59
def prefixEnd_3550984 : Nat := 4983230072969 + 3 ^ 40 * 3550984 * 2
def baseEnd_3550984 : Nat := 45021273788277530678255

theorem tailTrace_3550984 : CollatzResearch.WordTrace tailWord_3550984 prefixEnd_3550984 45021273788277530678255 := by
  unfold tailWord_3550984
  simp only [CollatzResearch.WordTrace]
  refine ⟨64757513283699451314790003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86343351044932601753053337 64757513283699451314790003)
  ·
    refine ⟨97136269925549176972185005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64757513283699451314790003 97136269925549176972185005)
    ·
      refine ⟨36426101222080941364569377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97136269925549176972185005 36426101222080941364569377)
      ·
        refine ⟨27319575916560706023427033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36426101222080941364569377 27319575916560706023427033)
        ·
          refine ⟨20489681937420529517570275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27319575916560706023427033 20489681937420529517570275)
          ·
            refine ⟨30734522906130794276355413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20489681937420529517570275 30734522906130794276355413)
            ·
              refine ⟨45021273788277530678255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 30734522906130794276355413 45021273788277530678255)
              ·
                rfl

theorem cell22_3550984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 11].length) (baseStart_3550984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3550984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3550984 prefixEnd_3550984 := by exact prefixLift 3550984
  have htrace : WordTrace (prefixWord ++ tailWord_3550984) baseStart_3550984 baseEnd_3550984 := by
    simpa [prefixWord, tailWord_3550984, baseEnd_3550984] using wordTrace_append hprefix tailTrace_3550984
  have hstable : (prefixWord ++ tailWord_3550984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3550984).length < 2 ^ (prefixWord ++ tailWord_3550984).sum := by decide
  have hdescent : baseEnd_3550984 < baseStart_3550984 := by decide
  rcases family_descends (prefixWord ++ tailWord_3550984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3550988 : List Nat := [2, 2, 1, 2, 2, 1, 5, 2, 2, 3]
def baseStart_3550988 : Nat := 118140960795 + 3550988 * 2 ^ 59
def prefixEnd_3550988 : Nat := 4983230072969 + 3 ^ 40 * 3550988 * 2
def baseEnd_3550988 : Nat := 1215575761565238651212873

theorem tailTrace_3550988 : CollatzResearch.WordTrace tailWord_3550988 prefixEnd_3550988 1215575761565238651212873 := by
  unfold tailWord_3550988
  simp only [CollatzResearch.WordTrace]
  refine ⟨64757586229692205656362809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86343448306256274208483745 64757586229692205656362809)
  ·
    refine ⟨48568189672269154242272107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64757586229692205656362809 48568189672269154242272107)
    ·
      refine ⟨72852284508403731363408161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48568189672269154242272107 72852284508403731363408161)
      ·
        refine ⟨54639213381302798522556121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72852284508403731363408161 54639213381302798522556121)
        ·
          refine ⟨40979410035977098891917091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54639213381302798522556121 40979410035977098891917091)
          ·
            refine ⟨61469115053965648337875637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40979410035977098891917091 61469115053965648337875637)
            ·
              refine ⟨5762729536309279531675841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61469115053965648337875637 5762729536309279531675841)
              ·
                refine ⟨4322047152231959648756881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5762729536309279531675841 4322047152231959648756881)
                ·
                  refine ⟨3241535364173969736567661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4322047152231959648756881 3241535364173969736567661)
                  ·
                    refine ⟨1215575761565238651212873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3241535364173969736567661 1215575761565238651212873)
                    ·
                      rfl

theorem cell22_3550988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 5, 2, 2, 3].length) (baseStart_3550988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3550988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3550988 prefixEnd_3550988 := by exact prefixLift 3550988
  have htrace : WordTrace (prefixWord ++ tailWord_3550988) baseStart_3550988 baseEnd_3550988 := by
    simpa [prefixWord, tailWord_3550988, baseEnd_3550988] using wordTrace_append hprefix tailTrace_3550988
  have hstable : (prefixWord ++ tailWord_3550988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3550988).length < 2 ^ (prefixWord ++ tailWord_3550988).sum := by decide
  have hdescent : baseEnd_3550988 < baseStart_3550988 := by decide
  rcases family_descends (prefixWord ++ tailWord_3550988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3551059 : List Nat := [1, 1, 1, 2, 1, 1, 3, 1, 1, 10]
def baseStart_3551059 : Nat := 118140960795 + 3551059 * 2 ^ 59
def prefixEnd_3551059 : Nat := 4983230072969 + 3 ^ 40 * 3551059 * 2
def baseEnd_3551059 : Nat := 1215600066316218132687655

theorem tailTrace_3551059 : CollatzResearch.WordTrace tailWord_3551059 prefixEnd_3551059 1215600066316218132687655 := by
  unfold tailWord_3551059
  simp only [CollatzResearch.WordTrace]
  refine ⟨129517762042127190438560231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86345174694751460292373487 129517762042127190438560231)
  ·
    refine ⟨194276643063190785657840347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129517762042127190438560231 194276643063190785657840347)
    ·
      refine ⟨291414964594786178486760521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194276643063190785657840347 291414964594786178486760521)
      ·
        refine ⟨218561223446089633865070391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 291414964594786178486760521 218561223446089633865070391)
        ·
          refine ⟨327841835169134450797605587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218561223446089633865070391 327841835169134450797605587)
          ·
            refine ⟨491762752753701676196408381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 327841835169134450797605587 491762752753701676196408381)
            ·
              refine ⟨184411032282638128573653143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 491762752753701676196408381 184411032282638128573653143)
              ·
                refine ⟨276616548423957192860479715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 184411032282638128573653143 276616548423957192860479715)
                ·
                  refine ⟨414924822635935789290719573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 276616548423957192860479715 414924822635935789290719573)
                  ·
                    refine ⟨1215600066316218132687655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 414924822635935789290719573 1215600066316218132687655)
                    ·
                      rfl

theorem cell22_3551059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 10].length) (baseStart_3551059 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3551059 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3551059 prefixEnd_3551059 := by exact prefixLift 3551059
  have htrace : WordTrace (prefixWord ++ tailWord_3551059) baseStart_3551059 baseEnd_3551059 := by
    simpa [prefixWord, tailWord_3551059, baseEnd_3551059] using wordTrace_append hprefix tailTrace_3551059
  have hstable : (prefixWord ++ tailWord_3551059).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3551059).length < 2 ^ (prefixWord ++ tailWord_3551059).sum := by decide
  have hdescent : baseEnd_3551059 < baseStart_3551059 := by decide
  rcases family_descends (prefixWord ++ tailWord_3551059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3551063 : List Nat := [1, 1, 3, 2, 5, 1, 1, 3, 5]
def baseStart_3551063 : Nat := 118140960795 + 3551063 * 2 ^ 59
def prefixEnd_3551063 : Nat := 4983230072969 + 3 ^ 40 * 3551063 * 2
def baseEnd_3551063 : Nat := 405200478532654485195881

theorem tailTrace_3551063 : CollatzResearch.WordTrace tailWord_3551063 prefixEnd_3551063 405200478532654485195881 := by
  unfold tailWord_3551063
  simp only [CollatzResearch.WordTrace]
  refine ⟨129517907934112699121705843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86345271956075132747803895 129517907934112699121705843)
  ·
    refine ⟨194276861901169048682558765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129517907934112699121705843 194276861901169048682558765)
    ·
      refine ⟨72853823212938393255959537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 194276861901169048682558765 72853823212938393255959537)
      ·
        refine ⟨54640367409703794941969653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72853823212938393255959537 54640367409703794941969653)
        ·
          refine ⟨5122534444659730775809655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54640367409703794941969653 5122534444659730775809655)
          ·
            refine ⟨7683801666989596163714483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5122534444659730775809655 7683801666989596163714483)
            ·
              refine ⟨11525702500484394245571725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7683801666989596163714483 11525702500484394245571725)
              ·
                refine ⟨4322138437681647842089397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11525702500484394245571725 4322138437681647842089397)
                ·
                  refine ⟨405200478532654485195881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4322138437681647842089397 405200478532654485195881)
                  ·
                    rfl

theorem cell22_3551063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 3, 5].length) (baseStart_3551063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3551063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3551063 prefixEnd_3551063 := by exact prefixLift 3551063
  have htrace : WordTrace (prefixWord ++ tailWord_3551063) baseStart_3551063 baseEnd_3551063 := by
    simpa [prefixWord, tailWord_3551063, baseEnd_3551063] using wordTrace_append hprefix tailTrace_3551063
  have hstable : (prefixWord ++ tailWord_3551063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3551063).length < 2 ^ (prefixWord ++ tailWord_3551063).sum := by decide
  have hdescent : baseEnd_3551063 < baseStart_3551063 := by decide
  rcases family_descends (prefixWord ++ tailWord_3551063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3551121 : List Nat := [1, 2, 2, 1, 1, 1, 4, 2, 4, 4]
def baseStart_3551121 : Nat := 118140960795 + 3551121 * 2 ^ 59
def prefixEnd_3551121 : Nat := 4983230072969 + 3 ^ 40 * 3551121 * 2
def baseEnd_3551121 : Nat := 1215621290183270637637465

theorem tailTrace_3551121 : CollatzResearch.WordTrace tailWord_3551121 prefixEnd_3551121 1215621290183270637637465 := by
  unfold tailWord_3551121
  simp only [CollatzResearch.WordTrace]
  refine ⟨129520023367902575027317217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86346682245268383351544811 129520023367902575027317217)
  ·
    refine ⟨97140017525926931270487913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129520023367902575027317217 97140017525926931270487913)
    ·
      refine ⟨72855013144445198452865935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97140017525926931270487913 72855013144445198452865935)
      ·
        refine ⟨109282519716667797679298903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72855013144445198452865935 109282519716667797679298903)
        ·
          refine ⟨163923779575001696518948355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109282519716667797679298903 163923779575001696518948355)
          ·
            refine ⟨245885669362502544778422533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163923779575001696518948355 245885669362502544778422533)
            ·
              refine ⟨46103563005469227145954225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 245885669362502544778422533 46103563005469227145954225)
              ·
                refine ⟨34577672254101920359465669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46103563005469227145954225 34577672254101920359465669)
                ·
                  refine ⟨6483313547644110067399813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34577672254101920359465669 6483313547644110067399813)
                  ·
                    refine ⟨1215621290183270637637465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6483313547644110067399813 1215621290183270637637465)
                    ·
                      rfl

theorem cell22_3551121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 4].length) (baseStart_3551121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3551121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3551121 prefixEnd_3551121 := by exact prefixLift 3551121
  have htrace : WordTrace (prefixWord ++ tailWord_3551121) baseStart_3551121 baseEnd_3551121 := by
    simpa [prefixWord, tailWord_3551121, baseEnd_3551121] using wordTrace_append hprefix tailTrace_3551121
  have hstable : (prefixWord ++ tailWord_3551121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3551121).length < 2 ^ (prefixWord ++ tailWord_3551121).sum := by decide
  have hdescent : baseEnd_3551121 < baseStart_3551121 := by decide
  rcases family_descends (prefixWord ++ tailWord_3551121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3551157 : List Nat := [1, 3, 3, 2, 1, 4, 1, 2, 2, 3]
def baseStart_3551157 : Nat := 118140960795 + 3551157 * 2 ^ 59
def prefixEnd_3551157 : Nat := 4983230072969 + 3 ^ 40 * 3551157 * 2
def baseEnd_3551157 : Nat := 1215633613718978543737355

theorem tailTrace_3551157 : CollatzResearch.WordTrace tailWord_3551157 prefixEnd_3551157 1215633613718978543737355 := by
  unfold tailWord_3551157
  simp only [CollatzResearch.WordTrace]
  refine ⟨129521336395772153175627725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86347557597181435450418483 129521336395772153175627725)
  ·
    refine ⟨48570501148414557440860397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129521336395772153175627725 48570501148414557440860397)
    ·
      refine ⟨18213937930655459040322649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48570501148414557440860397 18213937930655459040322649)
      ·
        refine ⟨13660453447991594280241987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18213937930655459040322649 13660453447991594280241987)
        ·
          refine ⟨20490680171987391420362981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13660453447991594280241987 20490680171987391420362981)
          ·
            refine ⟨3842002532247635891318059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20490680171987391420362981 3842002532247635891318059)
            ·
              refine ⟨5763003798371453836977089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3842002532247635891318059 5763003798371453836977089)
              ·
                refine ⟨4322252848778590377732817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5763003798371453836977089 4322252848778590377732817)
                ·
                  refine ⟨3241689636583942783299613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4322252848778590377732817 3241689636583942783299613)
                  ·
                    refine ⟨1215633613718978543737355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3241689636583942783299613 1215633613718978543737355)
                    ·
                      rfl

theorem cell22_3551157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 1, 2, 2, 3].length) (baseStart_3551157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3551157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3551157 prefixEnd_3551157 := by exact prefixLift 3551157
  have htrace : WordTrace (prefixWord ++ tailWord_3551157) baseStart_3551157 baseEnd_3551157 := by
    simpa [prefixWord, tailWord_3551157, baseEnd_3551157] using wordTrace_append hprefix tailTrace_3551157
  have hstable : (prefixWord ++ tailWord_3551157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3551157).length < 2 ^ (prefixWord ++ tailWord_3551157).sum := by decide
  have hdescent : baseEnd_3551157 < baseStart_3551157 := by decide
  rcases family_descends (prefixWord ++ tailWord_3551157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3551228 : List Nat := [2, 2, 2, 1, 2, 2, 2, 2, 3, 4]
def baseStart_3551228 : Nat := 118140960795 + 3551228 * 2 ^ 59
def prefixEnd_3551228 : Nat := 4983230072969 + 3 ^ 40 * 3551228 * 2
def baseEnd_3551228 : Nat := 1215657918469958025212137

theorem tailTrace_3551228 : CollatzResearch.WordTrace tailWord_3551228 prefixEnd_3551228 1215657918469958025212137 := by
  unfold tailWord_3551228
  simp only [CollatzResearch.WordTrace]
  refine ⟨64761962989257466150731169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86349283985676621534308225 64761962989257466150731169)
  ·
    refine ⟨48571472241943099613048377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64761962989257466150731169 48571472241943099613048377)
    ·
      refine ⟨36428604181457324709786283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48571472241943099613048377 36428604181457324709786283)
      ·
        refine ⟨54642906272185987064679425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36428604181457324709786283 54642906272185987064679425)
        ·
          refine ⟨40982179704139490298509569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54642906272185987064679425 40982179704139490298509569)
          ·
            refine ⟨30736634778104617723882177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40982179704139490298509569 30736634778104617723882177)
            ·
              refine ⟨23052476083578463292911633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30736634778104617723882177 23052476083578463292911633)
              ·
                refine ⟨17289357062683847469683725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23052476083578463292911633 17289357062683847469683725)
                ·
                  refine ⟨6483508898506442801131397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17289357062683847469683725 6483508898506442801131397)
                  ·
                    refine ⟨1215657918469958025212137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6483508898506442801131397 1215657918469958025212137)
                    ·
                      rfl

theorem cell22_3551228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 2, 3, 4].length) (baseStart_3551228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3551228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3551228 prefixEnd_3551228 := by exact prefixLift 3551228
  have htrace : WordTrace (prefixWord ++ tailWord_3551228) baseStart_3551228 baseEnd_3551228 := by
    simpa [prefixWord, tailWord_3551228, baseEnd_3551228] using wordTrace_append hprefix tailTrace_3551228
  have hstable : (prefixWord ++ tailWord_3551228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3551228).length < 2 ^ (prefixWord ++ tailWord_3551228).sum := by decide
  have hdescent : baseEnd_3551228 < baseStart_3551228 := by decide
  rcases family_descends (prefixWord ++ tailWord_3551228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3551258 : List Nat := [3, 1, 1, 3, 1, 3, 1, 1, 3, 5]
def baseStart_3551258 : Nat := 118140960795 + 3551258 * 2 ^ 59
def prefixEnd_3551258 : Nat := 4983230072969 + 3 ^ 40 * 3551258 * 2
def baseEnd_3551258 : Nat := 1215668188083047946962045

theorem tailTrace_3551258 : CollatzResearch.WordTrace tailWord_3551258 prefixEnd_3551258 1215668188083047946962045 := by
  unfold tailWord_3551258
  simp only [CollatzResearch.WordTrace]
  refine ⟨32381255042101561856263607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86350013445604164950036285 32381255042101561856263607)
  ·
    refine ⟨48571882563152342784395411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32381255042101561856263607 48571882563152342784395411)
    ·
      refine ⟨72857823844728514176593117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48571882563152342784395411 72857823844728514176593117)
      ·
        refine ⟨27321683941773192816222419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72857823844728514176593117 27321683941773192816222419)
        ·
          refine ⟨40982525912659789224333629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27321683941773192816222419 40982525912659789224333629)
          ·
            refine ⟨15368447217247420959125111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40982525912659789224333629 15368447217247420959125111)
            ·
              refine ⟨23052670825871131438687667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15368447217247420959125111 23052670825871131438687667)
              ·
                refine ⟨34579006238806697158031501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23052670825871131438687667 34579006238806697158031501)
                ·
                  refine ⟨12967127339552511434261813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34579006238806697158031501 12967127339552511434261813)
                  ·
                    refine ⟨1215668188083047946962045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12967127339552511434261813 1215668188083047946962045)
                    ·
                      rfl

theorem cell22_3551258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 1, 3, 5].length) (baseStart_3551258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3551258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3551258 prefixEnd_3551258 := by exact prefixLift 3551258
  have htrace : WordTrace (prefixWord ++ tailWord_3551258) baseStart_3551258 baseEnd_3551258 := by
    simpa [prefixWord, tailWord_3551258, baseEnd_3551258] using wordTrace_append hprefix tailTrace_3551258
  have hstable : (prefixWord ++ tailWord_3551258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3551258).length < 2 ^ (prefixWord ++ tailWord_3551258).sum := by decide
  have hdescent : baseEnd_3551258 < baseStart_3551258 := by decide
  rcases family_descends (prefixWord ++ tailWord_3551258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3551326 : List Nat := [4, 4, 1, 1, 2, 1, 1, 1, 4, 3]
def baseStart_3551326 : Nat := 118140960795 + 3551326 * 2 ^ 59
def prefixEnd_3551326 : Nat := 4983230072969 + 3 ^ 40 * 3551326 * 2
def baseEnd_3551326 : Nat := 1215691465872718436261837

theorem tailTrace_3551326 : CollatzResearch.WordTrace tailWord_3551326 prefixEnd_3551326 1215691465872718436261837 := by
  unfold tailWord_3551326
  simp only [CollatzResearch.WordTrace]
  refine ⟨16190937541519986879816229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86351666888106596692353221 16190937541519986879816229)
  ·
    refine ⟨3035800789034997539965543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16190937541519986879816229 3035800789034997539965543)
    ·
      refine ⟨4553701183552496309948315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3035800789034997539965543 4553701183552496309948315)
      ·
        refine ⟨6830551775328744464922473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4553701183552496309948315 6830551775328744464922473)
        ·
          refine ⟨5122913831496558348691855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6830551775328744464922473 5122913831496558348691855)
          ·
            refine ⟨7684370747244837523037783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5122913831496558348691855 7684370747244837523037783)
            ·
              refine ⟨11526556120867256284556675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7684370747244837523037783 11526556120867256284556675)
              ·
                refine ⟨17289834181300884426835013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11526556120867256284556675 17289834181300884426835013)
                ·
                  refine ⟨3241843908993915830031565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17289834181300884426835013 3241843908993915830031565)
                  ·
                    refine ⟨1215691465872718436261837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3241843908993915830031565 1215691465872718436261837)
                    ·
                      rfl

theorem cell22_3551326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_3551326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3551326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3551326 prefixEnd_3551326 := by exact prefixLift 3551326
  have htrace : WordTrace (prefixWord ++ tailWord_3551326) baseStart_3551326 baseEnd_3551326 := by
    simpa [prefixWord, tailWord_3551326, baseEnd_3551326] using wordTrace_append hprefix tailTrace_3551326
  have hstable : (prefixWord ++ tailWord_3551326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3551326).length < 2 ^ (prefixWord ++ tailWord_3551326).sum := by decide
  have hdescent : baseEnd_3551326 < baseStart_3551326 := by decide
  rcases family_descends (prefixWord ++ tailWord_3551326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3551337 : List Nat := [1, 2, 1, 1, 1, 5, 1, 6, 1, 3]
def baseStart_3551337 : Nat := 118140960795 + 3551337 * 2 ^ 59
def prefixEnd_3551337 : Nat := 4983230072969 + 3 ^ 40 * 3551337 * 2
def baseEnd_3551337 : Nat := 1215695231397518074236803

theorem tailTrace_3551337 : CollatzResearch.WordTrace tailWord_3551337 prefixEnd_3551337 1215695231397518074236803 := by
  unfold tailWord_3551337
  simp only [CollatzResearch.WordTrace]
  refine ⟨129527901535120043917180265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86351934356746695944786843 129527901535120043917180265)
  ·
    refine ⟨97145926151340032937885199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129527901535120043917180265 97145926151340032937885199)
    ·
      refine ⟨145718889227010049406827799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97145926151340032937885199 145718889227010049406827799)
      ·
        refine ⟨218578333840515074110241699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145718889227010049406827799 218578333840515074110241699)
        ·
          refine ⟨327867500760772611165362549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218578333840515074110241699 327867500760772611165362549)
          ·
            refine ⟨30737578196322432296752739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 327867500760772611165362549 30737578196322432296752739)
            ·
              refine ⟨46106367294483648445129109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30737578196322432296752739 46106367294483648445129109)
              ·
                refine ⟨2161235966928921020865427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 46106367294483648445129109 2161235966928921020865427)
                ·
                  refine ⟨3241853950393381531298141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2161235966928921020865427 3241853950393381531298141)
                  ·
                    refine ⟨1215695231397518074236803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3241853950393381531298141 1215695231397518074236803)
                    ·
                      rfl

theorem cell22_3551337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 6, 1, 3].length) (baseStart_3551337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3551337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3551337 prefixEnd_3551337 := by exact prefixLift 3551337
  have htrace : WordTrace (prefixWord ++ tailWord_3551337) baseStart_3551337 baseEnd_3551337 := by
    simpa [prefixWord, tailWord_3551337, baseEnd_3551337] using wordTrace_append hprefix tailTrace_3551337
  have hstable : (prefixWord ++ tailWord_3551337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3551337).length < 2 ^ (prefixWord ++ tailWord_3551337).sum := by decide
  have hdescent : baseEnd_3551337 < baseStart_3551337 := by decide
  rcases family_descends (prefixWord ++ tailWord_3551337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3551410 : List Nat := [3, 2, 1, 1, 1, 3, 2, 3, 1, 5]
def baseStart_3551410 : Nat := 118140960795 + 3551410 * 2 ^ 59
def prefixEnd_3551410 : Nat := 4983230072969 + 3 ^ 40 * 3551410 * 2
def baseEnd_3551410 : Nat := 1215720220789370217161579

theorem tailTrace_3551410 : CollatzResearch.WordTrace tailWord_3551410 prefixEnd_3551410 1215720220789370217161579 := by
  unfold tailWord_3551410
  simp only [CollatzResearch.WordTrace]
  refine ⟨32382641015963894346146921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86353709375903718256391789 32382641015963894346146921)
  ·
    refine ⟨24286980761972920759610191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32382641015963894346146921 24286980761972920759610191)
    ·
      refine ⟨36430471142959381139415287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24286980761972920759610191 36430471142959381139415287)
      ·
        refine ⟨54645706714439071709122931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36430471142959381139415287 54645706714439071709122931)
        ·
          refine ⟨81968560071658607563684397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54645706714439071709122931 81968560071658607563684397)
          ·
            refine ⟨30738210026871977836381649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81968560071658607563684397 30738210026871977836381649)
            ·
              refine ⟨23053657520153983377286237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30738210026871977836381649 23053657520153983377286237)
              ·
                refine ⟨8645121570057743766482339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23053657520153983377286237 8645121570057743766482339)
                ·
                  refine ⟨12967682355086615649723509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8645121570057743766482339 12967682355086615649723509)
                  ·
                    refine ⟨1215720220789370217161579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12967682355086615649723509 1215720220789370217161579)
                    ·
                      rfl

theorem cell22_3551410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 3, 1, 5].length) (baseStart_3551410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3551410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3551410 prefixEnd_3551410 := by exact prefixLift 3551410
  have htrace : WordTrace (prefixWord ++ tailWord_3551410) baseStart_3551410 baseEnd_3551410 := by
    simpa [prefixWord, tailWord_3551410, baseEnd_3551410] using wordTrace_append hprefix tailTrace_3551410
  have hstable : (prefixWord ++ tailWord_3551410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3551410).length < 2 ^ (prefixWord ++ tailWord_3551410).sum := by decide
  have hdescent : baseEnd_3551410 < baseStart_3551410 := by decide
  rcases family_descends (prefixWord ++ tailWord_3551410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3551442 : List Nat := [3, 2, 2, 2, 1, 2, 2, 2, 2, 4]
def baseStart_3551442 : Nat := 118140960795 + 3551442 * 2 ^ 59
def prefixEnd_3551442 : Nat := 4983230072969 + 3 ^ 40 * 3551442 * 2
def baseEnd_3551442 : Nat := 1215731175043332800361481

theorem tailTrace_3551442 : CollatzResearch.WordTrace tailWord_3551442 prefixEnd_3551442 1215731175043332800361481 := by
  unfold tailWord_3551442
  simp only [CollatzResearch.WordTrace]
  refine ⟨32382932799934911712438145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86354487466493097899835053 32382932799934911712438145)
  ·
    refine ⟨24287199599951183784328609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32382932799934911712438145 24287199599951183784328609)
    ·
      refine ⟨18215399699963387838246457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24287199599951183784328609 18215399699963387838246457)
      ·
        refine ⟨13661549774972540878684843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18215399699963387838246457 13661549774972540878684843)
        ·
          refine ⟨20492324662458811318027265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13661549774972540878684843 20492324662458811318027265)
          ·
            refine ⟨15369243496844108488520449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20492324662458811318027265 15369243496844108488520449)
            ·
              refine ⟨11526932622633081366390337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15369243496844108488520449 11526932622633081366390337)
              ·
                refine ⟨8645199466974811024792753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11526932622633081366390337 8645199466974811024792753)
                ·
                  refine ⟨6483899600231108268594565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8645199466974811024792753 6483899600231108268594565)
                  ·
                    refine ⟨1215731175043332800361481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6483899600231108268594565 1215731175043332800361481)
                    ·
                      rfl

theorem cell22_3551442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 2, 2, 4].length) (baseStart_3551442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3551442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3551442 prefixEnd_3551442 := by exact prefixLift 3551442
  have htrace : WordTrace (prefixWord ++ tailWord_3551442) baseStart_3551442 baseEnd_3551442 := by
    simpa [prefixWord, tailWord_3551442, baseEnd_3551442] using wordTrace_append hprefix tailTrace_3551442
  have hstable : (prefixWord ++ tailWord_3551442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3551442).length < 2 ^ (prefixWord ++ tailWord_3551442).sum := by decide
  have hdescent : baseEnd_3551442 < baseStart_3551442 := by decide
  rcases family_descends (prefixWord ++ tailWord_3551442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3551446 : List Nat := [5, 2, 1, 2, 1, 2, 1, 4, 4]
def baseStart_3551446 : Nat := 118140960795 + 3551446 * 2 ^ 59
def prefixEnd_3551446 : Nat := 4983230072969 + 3 ^ 40 * 3551446 * 2
def baseEnd_3551446 : Nat := 405244181441692707753823

theorem tailTrace_3551446 : CollatzResearch.WordTrace tailWord_3551446 prefixEnd_3551446 405244181441692707753823 := by
  unfold tailWord_3551446
  simp only [CollatzResearch.WordTrace]
  refine ⟨8095742318232822220806137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 86354584727816770355265461 8095742318232822220806137)
  ·
    refine ⟨6071806738674616665604603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8095742318232822220806137 6071806738674616665604603)
    ·
      refine ⟨9107710108011924998406905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6071806738674616665604603 9107710108011924998406905)
      ·
        refine ⟨6830782581008943748805179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9107710108011924998406905 6830782581008943748805179)
        ·
          refine ⟨10246173871513415623207769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6830782581008943748805179 10246173871513415623207769)
          ·
            refine ⟨7684630403635061717405827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10246173871513415623207769 7684630403635061717405827)
            ·
              refine ⟨11526945605452592576108741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7684630403635061717405827 11526945605452592576108741)
              ·
                refine ⟨2161302301022361108020389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11526945605452592576108741 2161302301022361108020389)
                ·
                  refine ⟨405244181441692707753823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2161302301022361108020389 405244181441692707753823)
                  ·
                    rfl

theorem cell22_3551446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 4, 4].length) (baseStart_3551446 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3551446 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3551446 prefixEnd_3551446 := by exact prefixLift 3551446
  have htrace : WordTrace (prefixWord ++ tailWord_3551446) baseStart_3551446 baseEnd_3551446 := by
    simpa [prefixWord, tailWord_3551446, baseEnd_3551446] using wordTrace_append hprefix tailTrace_3551446
  have hstable : (prefixWord ++ tailWord_3551446).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3551446).length < 2 ^ (prefixWord ++ tailWord_3551446).sum := by decide
  have hdescent : baseEnd_3551446 < baseStart_3551446 := by decide
  rcases family_descends (prefixWord ++ tailWord_3551446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3551470 : List Nat := [4, 1, 2, 1, 1, 1, 1, 1, 4, 6]
def baseStart_3551470 : Nat := 118140960795 + 3551470 * 2 ^ 59
def prefixEnd_3551470 : Nat := 4983230072969 + 3 ^ 40 * 3551470 * 2
def baseEnd_3551470 : Nat := 1215740760015550060661395

theorem tailTrace_3551470 : CollatzResearch.WordTrace tailWord_3551470 prefixEnd_3551470 1215740760015550060661395 := by
  unfold tailWord_3551470
  simp only [CollatzResearch.WordTrace]
  refine ⟨16191594055454775953971483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86355168295758805087847909 16191594055454775953971483)
  ·
    refine ⟨24287391083182163930957225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16191594055454775953971483 24287391083182163930957225)
    ·
      refine ⟨18215543312386622948217919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24287391083182163930957225 18215543312386622948217919)
      ·
        refine ⟨27323314968579934422326879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18215543312386622948217919 27323314968579934422326879)
        ·
          refine ⟨40984972452869901633490319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27323314968579934422326879 40984972452869901633490319)
          ·
            refine ⟨61477458679304852450235479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40984972452869901633490319 61477458679304852450235479)
            ·
              refine ⟨92216188018957278675353219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61477458679304852450235479 92216188018957278675353219)
              ·
                refine ⟨138324282028435918013029829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92216188018957278675353219 138324282028435918013029829)
                ·
                  refine ⟨25935802880331734627443093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 138324282028435918013029829 25935802880331734627443093)
                  ·
                    refine ⟨1215740760015550060661395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25935802880331734627443093 1215740760015550060661395)
                    ·
                      rfl

theorem cell22_3551470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 4, 6].length) (baseStart_3551470 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3551470 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3551470 prefixEnd_3551470 := by exact prefixLift 3551470
  have htrace : WordTrace (prefixWord ++ tailWord_3551470) baseStart_3551470 baseEnd_3551470 := by
    simpa [prefixWord, tailWord_3551470, baseEnd_3551470] using wordTrace_append hprefix tailTrace_3551470
  have hstable : (prefixWord ++ tailWord_3551470).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3551470).length < 2 ^ (prefixWord ++ tailWord_3551470).sum := by decide
  have hdescent : baseEnd_3551470 < baseStart_3551470 := by decide
  rcases family_descends (prefixWord ++ tailWord_3551470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3551500 : List Nat := [2, 2, 1, 2, 2, 2, 1, 1, 4, 5]
def baseStart_3551500 : Nat := 118140960795 + 3551500 * 2 ^ 59
def prefixEnd_3551500 : Nat := 4983230072969 + 3 ^ 40 * 3551500 * 2
def baseEnd_3551500 : Nat := 1215751029628639982411303

theorem tailTrace_3551500 : CollatzResearch.WordTrace tailWord_3551500 prefixEnd_3551500 1215751029628639982411303 := by
  unfold tailWord_3551500
  simp only [CollatzResearch.WordTrace]
  refine ⟨64766923316764761377681977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86355897755686348503575969 64766923316764761377681977)
  ·
    refine ⟨48575192487573571033261483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64766923316764761377681977 48575192487573571033261483)
    ·
      refine ⟨72862788731360356549892225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48575192487573571033261483 72862788731360356549892225)
      ·
        refine ⟨54647091548520267412419169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72862788731360356549892225 54647091548520267412419169)
        ·
          refine ⟨40985318661390200559314377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54647091548520267412419169 40985318661390200559314377)
          ·
            refine ⟨30738988996042650419485783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40985318661390200559314377 30738988996042650419485783)
            ·
              refine ⟨46108483494063975629228675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30738988996042650419485783 46108483494063975629228675)
              ·
                refine ⟨69162725241095963443843013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46108483494063975629228675 69162725241095963443843013)
                ·
                  refine ⟨12968010982705493145720565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69162725241095963443843013 12968010982705493145720565)
                  ·
                    refine ⟨1215751029628639982411303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12968010982705493145720565 1215751029628639982411303)
                    ·
                      rfl

theorem cell22_3551500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 4, 5].length) (baseStart_3551500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3551500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3551500 prefixEnd_3551500 := by exact prefixLift 3551500
  have htrace : WordTrace (prefixWord ++ tailWord_3551500) baseStart_3551500 baseEnd_3551500 := by
    simpa [prefixWord, tailWord_3551500, baseEnd_3551500] using wordTrace_append hprefix tailTrace_3551500
  have hstable : (prefixWord ++ tailWord_3551500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3551500).length < 2 ^ (prefixWord ++ tailWord_3551500).sum := by decide
  have hdescent : baseEnd_3551500 < baseStart_3551500 := by decide
  rcases family_descends (prefixWord ++ tailWord_3551500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3551515 : List Nat := [1, 1, 1, 1, 1, 1, 6, 1, 5, 4]
def baseStart_3551515 : Nat := 118140960795 + 3551515 * 2 ^ 59
def prefixEnd_3551515 : Nat := 4983230072969 + 3 ^ 40 * 3551515 * 2
def baseEnd_3551515 : Nat := 1215756164435184943286257

theorem tailTrace_3551515 : CollatzResearch.WordTrace tailWord_3551515 prefixEnd_3551515 1215756164435184943286257 := by
  unfold tailWord_3551515
  simp only [CollatzResearch.WordTrace]
  refine ⟨129534393728475180317159999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86356262485650120211439999 129534393728475180317159999)
  ·
    refine ⟨194301590592712770475739999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129534393728475180317159999 194301590592712770475739999)
    ·
      refine ⟨291452385889069155713609999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194301590592712770475739999 291452385889069155713609999)
      ·
        refine ⟨437178578833603733570414999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291452385889069155713609999 437178578833603733570414999)
        ·
          refine ⟨655767868250405600355622499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 437178578833603733570414999 655767868250405600355622499)
          ·
            refine ⟨983651802375608400533433749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 655767868250405600355622499 983651802375608400533433749)
            ·
              refine ⟨46108678236356643775004707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 983651802375608400533433749 46108678236356643775004707)
              ·
                refine ⟨69163017354534965662507061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46108678236356643775004707 69163017354534965662507061)
                ·
                  refine ⟨6484032876987653030860037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69163017354534965662507061 6484032876987653030860037)
                  ·
                    refine ⟨1215756164435184943286257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6484032876987653030860037 1215756164435184943286257)
                    ·
                      rfl

theorem cell22_3551515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 5, 4].length) (baseStart_3551515 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3551515 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3551515 prefixEnd_3551515 := by exact prefixLift 3551515
  have htrace : WordTrace (prefixWord ++ tailWord_3551515) baseStart_3551515 baseEnd_3551515 := by
    simpa [prefixWord, tailWord_3551515, baseEnd_3551515] using wordTrace_append hprefix tailTrace_3551515
  have hstable : (prefixWord ++ tailWord_3551515).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3551515).length < 2 ^ (prefixWord ++ tailWord_3551515).sum := by decide
  have hdescent : baseEnd_3551515 < baseStart_3551515 := by decide
  rcases family_descends (prefixWord ++ tailWord_3551515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3551519 : List Nat := [1, 1, 2, 4, 3, 2, 3, 1, 5]
def baseStart_3551519 : Nat := 118140960795 + 3551519 * 2 ^ 59
def prefixEnd_3551519 : Nat := 4983230072969 + 3 ^ 40 * 3551519 * 2
def baseEnd_3551519 : Nat := 405252511238976755395415

theorem tailTrace_3551519 : CollatzResearch.WordTrace tailWord_3551519 prefixEnd_3551519 405252511238976755395415 := by
  unfold tailWord_3551519
  simp only [CollatzResearch.WordTrace]
  refine ⟨129534539620460689000305611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86356359746973792666870407 129534539620460689000305611)
  ·
    refine ⟨194301809430691033500458417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129534539620460689000305611 194301809430691033500458417)
    ·
      refine ⟨145726357073018275125343813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194301809430691033500458417 145726357073018275125343813)
      ·
        refine ⟨27323691951190926586001965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 145726357073018275125343813 27323691951190926586001965)
        ·
          refine ⟨10246384481696597469750737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27323691951190926586001965 10246384481696597469750737)
          ·
            refine ⟨7684788361272448102313053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10246384481696597469750737 7684788361272448102313053)
            ·
              refine ⟨2881795635477168038367395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7684788361272448102313053 2881795635477168038367395)
              ·
                refine ⟨4322693453215752057551093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2881795635477168038367395 4322693453215752057551093)
                ·
                  refine ⟨405252511238976755395415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4322693453215752057551093 405252511238976755395415)
                  ·
                    rfl

theorem cell22_3551519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 3, 1, 5].length) (baseStart_3551519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3551519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3551519 prefixEnd_3551519 := by exact prefixLift 3551519
  have htrace : WordTrace (prefixWord ++ tailWord_3551519) baseStart_3551519 baseEnd_3551519 := by
    simpa [prefixWord, tailWord_3551519, baseEnd_3551519] using wordTrace_append hprefix tailTrace_3551519
  have hstable : (prefixWord ++ tailWord_3551519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3551519).length < 2 ^ (prefixWord ++ tailWord_3551519).sum := by decide
  have hdescent : baseEnd_3551519 < baseStart_3551519 := by decide
  rcases family_descends (prefixWord ++ tailWord_3551519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3551532 : List Nat := [2, 2, 1, 1, 1, 3, 3, 4, 1, 4]
def baseStart_3551532 : Nat := 118140960795 + 3551532 * 2 ^ 59
def prefixEnd_3551532 : Nat := 4983230072969 + 3 ^ 40 * 3551532 * 2
def baseEnd_3551532 : Nat := 1215761983882602565611205

theorem tailTrace_3551532 : CollatzResearch.WordTrace tailWord_3551532 prefixEnd_3551532 1215761983882602565611205 := by
  unfold tailWord_3551532
  simp only [CollatzResearch.WordTrace]
  refine ⟨64767506884706796110264425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86356675846275728147019233 64767506884706796110264425)
  ·
    refine ⟨48575630163530097082698319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64767506884706796110264425 48575630163530097082698319)
    ·
      refine ⟨72863445245295145624047479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48575630163530097082698319 72863445245295145624047479)
      ·
        refine ⟨109295167867942718436071219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72863445245295145624047479 109295167867942718436071219)
        ·
          refine ⟨163942751801914077654106829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109295167867942718436071219 163942751801914077654106829)
          ·
            refine ⟨61478531925717779120290061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 163942751801914077654106829 61478531925717779120290061)
            ·
              refine ⟨23054449472144167170108773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61478531925717779120290061 23054449472144167170108773)
              ·
                refine ⟨4322709276027031344395395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23054449472144167170108773 4322709276027031344395395)
                ·
                  refine ⟨6484063914040547016593093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4322709276027031344395395 6484063914040547016593093)
                  ·
                    refine ⟨1215761983882602565611205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6484063914040547016593093 1215761983882602565611205)
                    ·
                      rfl

theorem cell22_3551532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 4].length) (baseStart_3551532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3551532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3551532 prefixEnd_3551532 := by exact prefixLift 3551532
  have htrace : WordTrace (prefixWord ++ tailWord_3551532) baseStart_3551532 baseEnd_3551532 := by
    simpa [prefixWord, tailWord_3551532, baseEnd_3551532] using wordTrace_append hprefix tailTrace_3551532
  have hstable : (prefixWord ++ tailWord_3551532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3551532).length < 2 ^ (prefixWord ++ tailWord_3551532).sum := by decide
  have hdescent : baseEnd_3551532 < baseStart_3551532 := by decide
  rcases family_descends (prefixWord ++ tailWord_3551532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3551592 : List Nat := [2, 1, 4, 2, 2, 1, 2, 8]
def baseStart_3551592 : Nat := 118140960795 + 3551592 * 2 ^ 59
def prefixEnd_3551592 : Nat := 4983230072969 + 3 ^ 40 * 3551592 * 2
def baseEnd_3551592 : Nat := 135086947012086934345669

theorem tailTrace_3551592 : CollatzResearch.WordTrace tailWord_3551592 prefixEnd_3551592 135086947012086934345669 := by
  unfold tailWord_3551592
  simp only [CollatzResearch.WordTrace]
  refine ⟨64768601074598111233856515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86358134766130814978475353 64768601074598111233856515)
  ·
    refine ⟨97152901611897166850784773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64768601074598111233856515 97152901611897166850784773)
    ·
      refine ⟨18216169052230718784522145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97152901611897166850784773 18216169052230718784522145)
      ·
        refine ⟨13662126789173039088391609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18216169052230718784522145 13662126789173039088391609)
        ·
          refine ⟨10246595091879779316293707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13662126789173039088391609 10246595091879779316293707)
          ·
            refine ⟨15369892637819668974440561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10246595091879779316293707 15369892637819668974440561)
            ·
              refine ⟨11527419478364751730830421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15369892637819668974440561 11527419478364751730830421)
              ·
                refine ⟨135086947012086934345669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11527419478364751730830421 135086947012086934345669)
                ·
                  rfl

theorem cell22_3551592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 8].length) (baseStart_3551592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3551592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3551592 prefixEnd_3551592 := by exact prefixLift 3551592
  have htrace : WordTrace (prefixWord ++ tailWord_3551592) baseStart_3551592 baseEnd_3551592 := by
    simpa [prefixWord, tailWord_3551592, baseEnd_3551592] using wordTrace_append hprefix tailTrace_3551592
  have hstable : (prefixWord ++ tailWord_3551592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3551592).length < 2 ^ (prefixWord ++ tailWord_3551592).sum := by decide
  have hdescent : baseEnd_3551592 < baseStart_3551592 := by decide
  rcases family_descends (prefixWord ++ tailWord_3551592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3551594 : List Nat := [3, 1, 3, 3, 1, 1, 1, 3, 2, 4]
def baseStart_3551594 : Nat := 118140960795 + 3551594 * 2 ^ 59
def prefixEnd_3551594 : Nat := 4983230072969 + 3 ^ 40 * 3551594 * 2
def baseEnd_3551594 : Nat := 1215783207749655070561015

theorem tailTrace_3551594 : CollatzResearch.WordTrace tailWord_3551594 prefixEnd_3551594 1215783207749655070561015 := by
  unfold tailWord_3551594
  simp only [CollatzResearch.WordTrace]
  refine ⟨32384318773797244202321459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86358183396792651206190557 32384318773797244202321459)
  ·
    refine ⟨48576478160695866303482189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32384318773797244202321459 48576478160695866303482189)
    ·
      refine ⟨18216179310260949863805821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48576478160695866303482189 18216179310260949863805821)
      ·
        refine ⟨6831067241347856198927183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18216179310260949863805821 6831067241347856198927183)
        ·
          refine ⟨10246600862021784298390775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6831067241347856198927183 10246600862021784298390775)
          ·
            refine ⟨15369901293032676447586163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10246600862021784298390775 15369901293032676447586163)
            ·
              refine ⟨23054851939549014671379245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15369901293032676447586163 23054851939549014671379245)
              ·
                refine ⟨8645569477330880501767217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23054851939549014671379245 8645569477330880501767217)
                ·
                  refine ⟨6484177107998160376325413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8645569477330880501767217 6484177107998160376325413)
                  ·
                    refine ⟨1215783207749655070561015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6484177107998160376325413 1215783207749655070561015)
                    ·
                      rfl

theorem cell22_3551594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 3, 2, 4].length) (baseStart_3551594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3551594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3551594 prefixEnd_3551594 := by exact prefixLift 3551594
  have htrace : WordTrace (prefixWord ++ tailWord_3551594) baseStart_3551594 baseEnd_3551594 := by
    simpa [prefixWord, tailWord_3551594, baseEnd_3551594] using wordTrace_append hprefix tailTrace_3551594
  have hstable : (prefixWord ++ tailWord_3551594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3551594).length < 2 ^ (prefixWord ++ tailWord_3551594).sum := by decide
  have hdescent : baseEnd_3551594 < baseStart_3551594 := by decide
  rcases family_descends (prefixWord ++ tailWord_3551594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3551607 : List Nat := [1, 1, 3, 1, 1, 2, 2, 1, 7, 3]
def baseStart_3551607 : Nat := 118140960795 + 3551607 * 2 ^ 59
def prefixEnd_3551607 : Nat := 4983230072969 + 3 ^ 40 * 3551607 * 2
def baseEnd_3551607 : Nat := 1215787657915327369985975

theorem tailTrace_3551607 : CollatzResearch.WordTrace tailWord_3551607 prefixEnd_3551607 1215787657915327369985975 := by
  unfold tailWord_3551607
  simp only [CollatzResearch.WordTrace]
  refine ⟨129537749244141880029509075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86358499496094586686339383 129537749244141880029509075)
  ·
    refine ⟨194306623866212820044263613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129537749244141880029509075 194306623866212820044263613)
    ·
      refine ⟨72864983949829807516598855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 194306623866212820044263613 72864983949829807516598855)
      ·
        refine ⟨109297475924744711274898283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72864983949829807516598855 109297475924744711274898283)
        ·
          refine ⟨163946213887117066912347425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109297475924744711274898283 163946213887117066912347425)
          ·
            refine ⟨122959660415337800184260569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163946213887117066912347425 122959660415337800184260569)
            ·
              refine ⟨92219745311503350138195427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122959660415337800184260569 92219745311503350138195427)
              ·
                refine ⟨138329617967255025207293141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92219745311503350138195427 138329617967255025207293141)
                ·
                  refine ⟨3242100421107539653295933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 138329617967255025207293141 3242100421107539653295933)
                  ·
                    refine ⟨1215787657915327369985975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3242100421107539653295933 1215787657915327369985975)
                    ·
                      rfl

theorem cell22_3551607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 7, 3].length) (baseStart_3551607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3551607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3551607 prefixEnd_3551607 := by exact prefixLift 3551607
  have htrace : WordTrace (prefixWord ++ tailWord_3551607) baseStart_3551607 baseEnd_3551607 := by
    simpa [prefixWord, tailWord_3551607, baseEnd_3551607] using wordTrace_append hprefix tailTrace_3551607
  have hstable : (prefixWord ++ tailWord_3551607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3551607).length < 2 ^ (prefixWord ++ tailWord_3551607).sum := by decide
  have hdescent : baseEnd_3551607 < baseStart_3551607 := by decide
  rcases family_descends (prefixWord ++ tailWord_3551607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3551624 : List Nat := [2, 1, 3, 3, 1, 1, 2, 3, 3, 3]
def baseStart_3551624 : Nat := 118140960795 + 3551624 * 2 ^ 59
def prefixEnd_3551624 : Nat := 4983230072969 + 3 ^ 40 * 3551624 * 2
def baseEnd_3551624 : Nat := 1215793477362744992310923

theorem tailTrace_3551624 : CollatzResearch.WordTrace tailWord_3551624 prefixEnd_3551624 1215793477362744992310923 := by
  unfold tailWord_3551624
  simp only [CollatzResearch.WordTrace]
  refine ⟨64769184642540145966438963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86358912856720194621918617 64769184642540145966438963)
  ·
    refine ⟨97153776963810218949658445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64769184642540145966438963 97153776963810218949658445)
    ·
      refine ⟨36432666361428832106121917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97153776963810218949658445 36432666361428832106121917)
      ·
        refine ⟨13662249885535812039795719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36432666361428832106121917 13662249885535812039795719)
        ·
          refine ⟨20493374828303718059693579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13662249885535812039795719 20493374828303718059693579)
          ·
            refine ⟨30740062242455577089540369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20493374828303718059693579 30740062242455577089540369)
            ·
              refine ⟨23055046681841682817155277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30740062242455577089540369 23055046681841682817155277)
              ·
                refine ⟨8645642505690631056433229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23055046681841682817155277 8645642505690631056433229)
                ·
                  refine ⟨3242115939633986646162461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8645642505690631056433229 3242115939633986646162461)
                  ·
                    refine ⟨1215793477362744992310923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3242115939633986646162461 1215793477362744992310923)
                    ·
                      rfl

theorem cell22_3551624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 3, 3, 3].length) (baseStart_3551624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3551624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3551624 prefixEnd_3551624 := by exact prefixLift 3551624
  have htrace : WordTrace (prefixWord ++ tailWord_3551624) baseStart_3551624 baseEnd_3551624 := by
    simpa [prefixWord, tailWord_3551624, baseEnd_3551624] using wordTrace_append hprefix tailTrace_3551624
  have hstable : (prefixWord ++ tailWord_3551624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3551624).length < 2 ^ (prefixWord ++ tailWord_3551624).sum := by decide
  have hdescent : baseEnd_3551624 < baseStart_3551624 := by decide
  rcases family_descends (prefixWord ++ tailWord_3551624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3551626 : List Nat := [3, 1, 2, 5, 1, 2, 1, 7]
def baseStart_3551626 : Nat := 118140960795 + 3551626 * 2 ^ 59
def prefixEnd_3551626 : Nat := 4983230072969 + 3 ^ 40 * 3551626 * 2
def baseEnd_3551626 : Nat := 135088240222624183751213

theorem tailTrace_3551626 : CollatzResearch.WordTrace tailWord_3551626 prefixEnd_3551626 135088240222624183751213 := by
  unfold tailWord_3551626
  simp only [CollatzResearch.WordTrace]
  refine ⟨32384610557768261568612683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86358961487382030849633821 32384610557768261568612683)
  ·
    refine ⟨48576915836652392352919025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32384610557768261568612683 48576915836652392352919025)
    ·
      refine ⟨36432686877489294264689269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48576915836652392352919025 36432686877489294264689269)
      ·
        refine ⟨3415564394764621337314619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36432686877489294264689269 3415564394764621337314619)
        ·
          refine ⟨5123346592146932005971929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3415564394764621337314619 5123346592146932005971929)
          ·
            refine ⟨3842509944110199004478947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5123346592146932005971929 3842509944110199004478947)
            ·
              refine ⟨5763764916165298506718421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3842509944110199004478947 5763764916165298506718421)
              ·
                refine ⟨135088240222624183751213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5763764916165298506718421 135088240222624183751213)
                ·
                  rfl

theorem cell22_3551626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 1, 7].length) (baseStart_3551626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3551626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3551626 prefixEnd_3551626 := by exact prefixLift 3551626
  have htrace : WordTrace (prefixWord ++ tailWord_3551626) baseStart_3551626 baseEnd_3551626 := by
    simpa [prefixWord, tailWord_3551626, baseEnd_3551626] using wordTrace_append hprefix tailTrace_3551626
  have hstable : (prefixWord ++ tailWord_3551626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3551626).length < 2 ^ (prefixWord ++ tailWord_3551626).sum := by decide
  have hdescent : baseEnd_3551626 < baseStart_3551626 := by decide
  rcases family_descends (prefixWord ++ tailWord_3551626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3551701 : List Nat := [1, 3, 2, 3, 1, 3, 2, 2, 1, 4]
def baseStart_3551701 : Nat := 118140960795 + 3551701 * 2 ^ 59
def prefixEnd_3551701 : Nat := 4983230072969 + 3 ^ 40 * 3551701 * 2
def baseEnd_3551701 : Nat := 1215819836036342458135687

theorem tailTrace_3551701 : CollatzResearch.WordTrace tailWord_3551701 prefixEnd_3551701 1215819836036342458135687 := by
  unfold tailWord_3551701
  simp only [CollatzResearch.WordTrace]
  refine ⟨129541177705801334083430957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86360785137200889388953971 129541177705801334083430957)
  ·
    refine ⟨48577941639675500281286609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129541177705801334083430957 48577941639675500281286609)
    ·
      refine ⟨36433456229756625210964957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48577941639675500281286609 36433456229756625210964957)
      ·
        refine ⟨13662546086158734454111859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36433456229756625210964957 13662546086158734454111859)
        ·
          refine ⟨20493819129238101681167789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13662546086158734454111859 20493819129238101681167789)
          ·
            refine ⟨7685182173464288130437921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20493819129238101681167789 7685182173464288130437921)
            ·
              refine ⟨5763886630098216097828441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7685182173464288130437921 5763886630098216097828441)
              ·
                refine ⟨4322914972573662073371331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5763886630098216097828441 4322914972573662073371331)
                ·
                  refine ⟨6484372458860493110056997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4322914972573662073371331 6484372458860493110056997)
                  ·
                    refine ⟨1215819836036342458135687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6484372458860493110056997 1215819836036342458135687)
                    ·
                      rfl

theorem cell22_3551701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 2, 2, 1, 4].length) (baseStart_3551701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3551701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3551701 prefixEnd_3551701 := by exact prefixLift 3551701
  have htrace : WordTrace (prefixWord ++ tailWord_3551701) baseStart_3551701 baseEnd_3551701 := by
    simpa [prefixWord, tailWord_3551701, baseEnd_3551701] using wordTrace_append hprefix tailTrace_3551701
  have hstable : (prefixWord ++ tailWord_3551701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3551701).length < 2 ^ (prefixWord ++ tailWord_3551701).sum := by decide
  have hdescent : baseEnd_3551701 < baseStart_3551701 := by decide
  rcases family_descends (prefixWord ++ tailWord_3551701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3551712 : List Nat := [2, 1, 1, 3, 1, 1, 3, 3, 1, 6]
def baseStart_3551712 : Nat := 118140960795 + 3551712 * 2 ^ 59
def prefixEnd_3551712 : Nat := 4983230072969 + 3 ^ 40 * 3551712 * 2
def baseEnd_3551712 : Nat := 1215823601561142096110653

theorem tailTrace_3551712 : CollatzResearch.WordTrace tailWord_3551712 prefixEnd_3551712 1215823601561142096110653 := by
  unfold tailWord_3551712
  simp only [CollatzResearch.WordTrace]
  refine ⟨64770789454380741481040695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86361052605840988641387593 64770789454380741481040695)
  ·
    refine ⟨97156184181571112221561043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64770789454380741481040695 97156184181571112221561043)
    ·
      refine ⟨145734276272356668332341565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97156184181571112221561043 145734276272356668332341565)
      ·
        refine ⟨54650353602133750624628087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145734276272356668332341565 54650353602133750624628087)
        ·
          refine ⟨81975530403200625936942131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54650353602133750624628087 81975530403200625936942131)
          ·
            refine ⟨122963295604800938905413197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81975530403200625936942131 122963295604800938905413197)
            ·
              refine ⟨46111235851800352089529949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 122963295604800938905413197 46111235851800352089529949)
              ·
                refine ⟨17291713444425132033573731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46111235851800352089529949 17291713444425132033573731)
                ·
                  refine ⟨25937570166637698050360597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17291713444425132033573731 25937570166637698050360597)
                  ·
                    refine ⟨1215823601561142096110653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25937570166637698050360597 1215823601561142096110653)
                    ·
                      rfl

theorem cell22_3551712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 3, 1, 6].length) (baseStart_3551712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3551712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3551712 prefixEnd_3551712 := by exact prefixLift 3551712
  have htrace : WordTrace (prefixWord ++ tailWord_3551712) baseStart_3551712 baseEnd_3551712 := by
    simpa [prefixWord, tailWord_3551712, baseEnd_3551712] using wordTrace_append hprefix tailTrace_3551712
  have hstable : (prefixWord ++ tailWord_3551712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3551712).length < 2 ^ (prefixWord ++ tailWord_3551712).sum := by decide
  have hdescent : baseEnd_3551712 < baseStart_3551712 := by decide
  rcases family_descends (prefixWord ++ tailWord_3551712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3551729 : List Nat := [1, 2, 2, 2, 3, 1, 3, 2, 2, 4]
def baseStart_3551729 : Nat := 118140960795 + 3551729 * 2 ^ 59
def prefixEnd_3551729 : Nat := 4983230072969 + 3 ^ 40 * 3551729 * 2
def baseEnd_3551729 : Nat := 1215829421008559718435601

theorem tailTrace_3551729 : CollatzResearch.WordTrace tailWord_3551729 prefixEnd_3551729 1215829421008559718435601 := by
  unfold tailWord_3551729
  simp only [CollatzResearch.WordTrace]
  refine ⟨129542198949699894865450241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86361465966466596576966827 129542198949699894865450241)
  ·
    refine ⟨97156649212274921149087681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129542198949699894865450241 97156649212274921149087681)
    ·
      refine ⟨72867486909206190861815761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97156649212274921149087681 72867486909206190861815761)
      ·
        refine ⟨54650615181904643146361821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72867486909206190861815761 54650615181904643146361821)
        ·
          refine ⟨20493980693214241179885683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54650615181904643146361821 20493980693214241179885683)
          ·
            refine ⟨30740971039821361769828525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20493980693214241179885683 30740971039821361769828525)
            ·
              refine ⟨11527864139933010663685697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30740971039821361769828525 11527864139933010663685697)
              ·
                refine ⟨8645898104949757997764273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11527864139933010663685697 8645898104949757997764273)
                ·
                  refine ⟨6484423578712318498323205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8645898104949757997764273 6484423578712318498323205)
                  ·
                    refine ⟨1215829421008559718435601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6484423578712318498323205 1215829421008559718435601)
                    ·
                      rfl

theorem cell22_3551729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 2, 2, 4].length) (baseStart_3551729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3551729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3551729 prefixEnd_3551729 := by exact prefixLift 3551729
  have htrace : WordTrace (prefixWord ++ tailWord_3551729) baseStart_3551729 baseEnd_3551729 := by
    simpa [prefixWord, tailWord_3551729, baseEnd_3551729] using wordTrace_append hprefix tailTrace_3551729
  have hstable : (prefixWord ++ tailWord_3551729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3551729).length < 2 ^ (prefixWord ++ tailWord_3551729).sum := by decide
  have hdescent : baseEnd_3551729 < baseStart_3551729 := by decide
  rcases family_descends (prefixWord ++ tailWord_3551729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3551733 : List Nat := [1, 3, 5, 1, 2, 2, 1, 1, 6]
def baseStart_3551733 : Nat := 118140960795 + 3551733 * 2 ^ 59
def prefixEnd_3551733 : Nat := 4983230072969 + 3 ^ 40 * 3551733 * 2
def baseEnd_3551733 : Nat := 405276930096768347111863

theorem tailTrace_3551733 : CollatzResearch.WordTrace tailWord_3551733 prefixEnd_3551733 405276930096768347111863 := by
  unfold tailWord_3551733
  simp only [CollatzResearch.WordTrace]
  refine ⟨129542344841685403548595853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86361563227790269032397235 129542344841685403548595853)
  ·
    refine ⟨48578379315632026330723445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129542344841685403548595853 48578379315632026330723445)
    ·
      refine ⟨4554223060840502468505323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 48578379315632026330723445 4554223060840502468505323)
      ·
        refine ⟨6831334591260753702757985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4554223060840502468505323 6831334591260753702757985)
        ·
          refine ⟨5123500943445565277068489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6831334591260753702757985 5123500943445565277068489)
          ·
            refine ⟨3842625707584173957801367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5123500943445565277068489 3842625707584173957801367)
            ·
              refine ⟨5763938561376260936702051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3842625707584173957801367 5763938561376260936702051)
              ·
                refine ⟨8645907842064391405053077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5763938561376260936702051 8645907842064391405053077)
                ·
                  refine ⟨405276930096768347111863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8645907842064391405053077 405276930096768347111863)
                  ·
                    rfl

theorem cell22_3551733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 1, 1, 6].length) (baseStart_3551733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3551733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3551733 prefixEnd_3551733 := by exact prefixLift 3551733
  have htrace : WordTrace (prefixWord ++ tailWord_3551733) baseStart_3551733 baseEnd_3551733 := by
    simpa [prefixWord, tailWord_3551733, baseEnd_3551733] using wordTrace_append hprefix tailTrace_3551733
  have hstable : (prefixWord ++ tailWord_3551733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3551733).length < 2 ^ (prefixWord ++ tailWord_3551733).sum := by decide
  have hdescent : baseEnd_3551733 < baseStart_3551733 := by decide
  rcases family_descends (prefixWord ++ tailWord_3551733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3551748 : List Nat := [2, 3, 2, 3, 1, 2, 1, 3, 2, 3]
def baseStart_3551748 : Nat := 118140960795 + 3551748 * 2 ^ 59
def prefixEnd_3551748 : Nat := 4983230072969 + 3 ^ 40 * 3551748 * 2
def baseEnd_3551748 : Nat := 1215835925096850002210543

theorem tailTrace_3551748 : CollatzResearch.WordTrace tailWord_3551748 prefixEnd_3551748 1215835925096850002210543 := by
  unfold tailWord_3551748
  simp only [CollatzResearch.WordTrace]
  refine ⟨64771445968315530555195949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86361927957754040740261265 64771445968315530555195949)
  ·
    refine ⟨24289292238118323958198481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64771445968315530555195949 24289292238118323958198481)
    ·
      refine ⟨18216969178588742968648861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24289292238118323958198481 18216969178588742968648861)
      ·
        refine ⟨6831363441970778613243323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18216969178588742968648861 6831363441970778613243323)
        ·
          refine ⟨10247045162956167919864985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6831363441970778613243323 10247045162956167919864985)
          ·
            refine ⟨7685283872217125939898739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10247045162956167919864985 7685283872217125939898739)
            ·
              refine ⟨11527925808325688909848109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7685283872217125939898739 11527925808325688909848109)
              ·
                refine ⟨4322972178122133341193041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11527925808325688909848109 4322972178122133341193041)
                ·
                  refine ⟨3242229133591600005894781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4322972178122133341193041 3242229133591600005894781)
                  ·
                    refine ⟨1215835925096850002210543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3242229133591600005894781 1215835925096850002210543)
                    ·
                      rfl

theorem cell22_3551748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 3, 2, 3].length) (baseStart_3551748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3551748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3551748 prefixEnd_3551748 := by exact prefixLift 3551748
  have htrace : WordTrace (prefixWord ++ tailWord_3551748) baseStart_3551748 baseEnd_3551748 := by
    simpa [prefixWord, tailWord_3551748, baseEnd_3551748] using wordTrace_append hprefix tailTrace_3551748
  have hstable : (prefixWord ++ tailWord_3551748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3551748).length < 2 ^ (prefixWord ++ tailWord_3551748).sum := by decide
  have hdescent : baseEnd_3551748 < baseStart_3551748 := by decide
  rcases family_descends (prefixWord ++ tailWord_3551748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3551787 : List Nat := [1, 1, 1, 1, 2, 1, 3, 2, 3, 7]
def baseStart_3551787 : Nat := 118140960795 + 3551787 * 2 ^ 59
def prefixEnd_3551787 : Nat := 4983230072969 + 3 ^ 40 * 3551787 * 2
def baseEnd_3551787 : Nat := 1215849275593866900485423

theorem tailTrace_3551787 : CollatzResearch.WordTrace tailWord_3551787 prefixEnd_3551787 1215849275593866900485423 := by
  unfold tailWord_3551787
  simp only [CollatzResearch.WordTrace]
  refine ⟨129544314383489770771061615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86362876255659847180707743 129544314383489770771061615)
  ·
    refine ⟨194316471575234656156592423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129544314383489770771061615 194316471575234656156592423)
    ·
      refine ⟨291474707362851984234888635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194316471575234656156592423 291474707362851984234888635)
      ·
        refine ⟨437212061044277976352332953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291474707362851984234888635 437212061044277976352332953)
        ·
          refine ⟨327909045783208482264249715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 437212061044277976352332953 327909045783208482264249715)
          ·
            refine ⟨491863568674812723396374573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 327909045783208482264249715 491863568674812723396374573)
            ·
              refine ⟨184448838253054771273640465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 491863568674812723396374573 184448838253054771273640465)
              ·
                refine ⟨138336628689791078455230349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 184448838253054771273640465 138336628689791078455230349)
                ·
                  refine ⟨51876235758671654420711381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 138336628689791078455230349 51876235758671654420711381)
                  ·
                    refine ⟨1215849275593866900485423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51876235758671654420711381 1215849275593866900485423)
                    ·
                      rfl

theorem cell22_3551787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 3, 7].length) (baseStart_3551787 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3551787 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3551787 prefixEnd_3551787 := by exact prefixLift 3551787
  have htrace : WordTrace (prefixWord ++ tailWord_3551787) baseStart_3551787 baseEnd_3551787 := by
    simpa [prefixWord, tailWord_3551787, baseEnd_3551787] using wordTrace_append hprefix tailTrace_3551787
  have hstable : (prefixWord ++ tailWord_3551787).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3551787).length < 2 ^ (prefixWord ++ tailWord_3551787).sum := by decide
  have hdescent : baseEnd_3551787 < baseStart_3551787 := by decide
  rcases family_descends (prefixWord ++ tailWord_3551787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3551804 : List Nat := [2, 2, 2, 2, 3, 1, 1, 1, 1, 7]
def baseStart_3551804 : Nat := 118140960795 + 3551804 * 2 ^ 59
def prefixEnd_3551804 : Nat := 4983230072969 + 3 ^ 40 * 3551804 * 2
def baseEnd_3551804 : Nat := 1215855095041284522810371

theorem tailTrace_3551804 : CollatzResearch.WordTrace tailWord_3551804 prefixEnd_3551804 1215855095041284522810371 := by
  unfold tailWord_3551804
  simp only [CollatzResearch.WordTrace]
  refine ⟨64772467212214091337215233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86363289616285455116286977 64772467212214091337215233)
  ·
    refine ⟨48579350409160568502911425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64772467212214091337215233 48579350409160568502911425)
    ·
      refine ⟨36434512806870426377183569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48579350409160568502911425 36434512806870426377183569)
      ·
        refine ⟨27325884605152819782887677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36434512806870426377183569 27325884605152819782887677)
        ·
          refine ⟨10247206726932307418582879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27325884605152819782887677 10247206726932307418582879)
          ·
            refine ⟨15370810090398461127874319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10247206726932307418582879 15370810090398461127874319)
            ·
              refine ⟨23056215135597691691811479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15370810090398461127874319 23056215135597691691811479)
              ·
                refine ⟨34584322703396537537717219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23056215135597691691811479 34584322703396537537717219)
                ·
                  refine ⟨51876484055094806306575829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34584322703396537537717219 51876484055094806306575829)
                  ·
                    refine ⟨1215855095041284522810371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51876484055094806306575829 1215855095041284522810371)
                    ·
                      rfl

theorem cell22_3551804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 1, 1, 7].length) (baseStart_3551804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3551804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3551804 prefixEnd_3551804 := by exact prefixLift 3551804
  have htrace : WordTrace (prefixWord ++ tailWord_3551804) baseStart_3551804 baseEnd_3551804 := by
    simpa [prefixWord, tailWord_3551804, baseEnd_3551804] using wordTrace_append hprefix tailTrace_3551804
  have hstable : (prefixWord ++ tailWord_3551804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3551804).length < 2 ^ (prefixWord ++ tailWord_3551804).sum := by decide
  have hdescent : baseEnd_3551804 < baseStart_3551804 := by decide
  rcases family_descends (prefixWord ++ tailWord_3551804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3551819 : List Nat := [1, 1, 1, 1, 3, 1, 6, 1, 3, 4]
def baseStart_3551819 : Nat := 118140960795 + 3551819 * 2 ^ 59
def prefixEnd_3551819 : Nat := 4983230072969 + 3 ^ 40 * 3551819 * 2
def baseEnd_3551819 : Nat := 1215860229847829483685325

theorem tailTrace_3551819 : CollatzResearch.WordTrace tailWord_3551819 prefixEnd_3551819 1215860229847829483685325 := by
  unfold tailWord_3551819
  simp only [CollatzResearch.WordTrace]
  refine ⟨129545481519373840236226511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86363654346249226824151007 129545481519373840236226511)
  ·
    refine ⟨194318222279060760354339767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129545481519373840236226511 194318222279060760354339767)
    ·
      refine ⟨291477333418591140531509651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194318222279060760354339767 291477333418591140531509651)
      ·
        refine ⟨437216000127886710797264477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291477333418591140531509651 437216000127886710797264477)
        ·
          refine ⟨163956000047957516548974179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 437216000127886710797264477 163956000047957516548974179)
          ·
            refine ⟨245934000071936274823461269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163956000047957516548974179 245934000071936274823461269)
            ·
              refine ⟨11528156253372012882349747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 245934000071936274823461269 11528156253372012882349747)
              ·
                refine ⟨17292234380058019323524621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11528156253372012882349747 17292234380058019323524621)
                ·
                  refine ⟨6484587892521757246321733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17292234380058019323524621 6484587892521757246321733)
                  ·
                    refine ⟨1215860229847829483685325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6484587892521757246321733 1215860229847829483685325)
                    ·
                      rfl

theorem cell22_3551819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 1, 3, 4].length) (baseStart_3551819 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3551819 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3551819 prefixEnd_3551819 := by exact prefixLift 3551819
  have htrace : WordTrace (prefixWord ++ tailWord_3551819) baseStart_3551819 baseEnd_3551819 := by
    simpa [prefixWord, tailWord_3551819, baseEnd_3551819] using wordTrace_append hprefix tailTrace_3551819
  have hstable : (prefixWord ++ tailWord_3551819).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3551819).length < 2 ^ (prefixWord ++ tailWord_3551819).sum := by decide
  have hdescent : baseEnd_3551819 < baseStart_3551819 := by decide
  rcases family_descends (prefixWord ++ tailWord_3551819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3551864 : List Nat := [2, 1, 2, 1, 1, 1, 2, 4, 4, 4]
def baseStart_3551864 : Nat := 118140960795 + 3551864 * 2 ^ 59
def prefixEnd_3551864 : Nat := 4983230072969 + 3 ^ 40 * 3551864 * 2
def baseEnd_3551864 : Nat := 1215875634267464366310187

theorem tailTrace_3551864 : CollatzResearch.WordTrace tailWord_3551864 prefixEnd_3551864 1215875634267464366310187 := by
  unfold tailWord_3551864
  simp only [CollatzResearch.WordTrace]
  refine ⟨64773561402105406460807323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86364748536140541947743097 64773561402105406460807323)
  ·
    refine ⟨97160342103158109691210985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64773561402105406460807323 97160342103158109691210985)
    ·
      refine ⟨72870256577368582268408239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97160342103158109691210985 72870256577368582268408239)
      ·
        refine ⟨109305384866052873402612359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72870256577368582268408239 109305384866052873402612359)
        ·
          refine ⟨163958077299079310103918539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109305384866052873402612359 163958077299079310103918539)
          ·
            refine ⟨245937115948618965155877809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163958077299079310103918539 245937115948618965155877809)
            ·
              refine ⟨184452836961464223866908357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 245937115948618965155877809 184452836961464223866908357)
              ·
                refine ⟨34584906930274541975045317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 184452836961464223866908357 34584906930274541975045317)
                ·
                  refine ⟨6484670049426476620320997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34584906930274541975045317 6484670049426476620320997)
                  ·
                    refine ⟨1215875634267464366310187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6484670049426476620320997 1215875634267464366310187)
                    ·
                      rfl

theorem cell22_3551864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 4, 4].length) (baseStart_3551864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3551864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3551864 prefixEnd_3551864 := by exact prefixLift 3551864
  have htrace : WordTrace (prefixWord ++ tailWord_3551864) baseStart_3551864 baseEnd_3551864 := by
    simpa [prefixWord, tailWord_3551864, baseEnd_3551864] using wordTrace_append hprefix tailTrace_3551864
  have hstable : (prefixWord ++ tailWord_3551864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3551864).length < 2 ^ (prefixWord ++ tailWord_3551864).sum := by decide
  have hdescent : baseEnd_3551864 < baseStart_3551864 := by decide
  rcases family_descends (prefixWord ++ tailWord_3551864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3551879 : List Nat := [1, 1, 4, 2, 1, 2, 3, 8]
def baseStart_3551879 : Nat := 118140960795 + 3551879 * 2 ^ 59
def prefixEnd_3551879 : Nat := 4983230072969 + 3 ^ 40 * 3551879 * 2
def baseEnd_3551879 : Nat := 135097863230445480798349

theorem tailTrace_3551879 : CollatzResearch.WordTrace tailWord_3551879 prefixEnd_3551879 135097863230445480798349 := by
  unfold tailWord_3551879
  simp only [CollatzResearch.WordTrace]
  refine ⟨129547669899156470483410691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86365113266104313655607127 129547669899156470483410691)
  ·
    refine ⟨194321504848734705725116037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129547669899156470483410691 194321504848734705725116037)
    ·
      refine ⟨36435282159137757323459257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 194321504848734705725116037 36435282159137757323459257)
      ·
        refine ⟨27326461619353317992594443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36435282159137757323459257 27326461619353317992594443)
        ·
          refine ⟨40989692429029976988891665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27326461619353317992594443 40989692429029976988891665)
          ·
            refine ⟨30742269321772482741668749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40989692429029976988891665 30742269321772482741668749)
            ·
              refine ⟨11528350995664681028125781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30742269321772482741668749 11528350995664681028125781)
              ·
                refine ⟨135097863230445480798349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11528350995664681028125781 135097863230445480798349)
                ·
                  rfl

theorem cell22_3551879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 8].length) (baseStart_3551879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3551879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3551879 prefixEnd_3551879 := by exact prefixLift 3551879
  have htrace : WordTrace (prefixWord ++ tailWord_3551879) baseStart_3551879 baseEnd_3551879 := by
    simpa [prefixWord, tailWord_3551879, baseEnd_3551879] using wordTrace_append hprefix tailTrace_3551879
  have hstable : (prefixWord ++ tailWord_3551879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3551879).length < 2 ^ (prefixWord ++ tailWord_3551879).sum := by decide
  have hdescent : baseEnd_3551879 < baseStart_3551879 := by decide
  rcases family_descends (prefixWord ++ tailWord_3551879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3551909 : List Nat := [1, 3, 1, 2, 1, 2, 1, 3, 2, 6]
def baseStart_3551909 : Nat := 118140960795 + 3551909 * 2 ^ 59
def prefixEnd_3551909 : Nat := 4983230072969 + 3 ^ 40 * 3551909 * 2
def baseEnd_3551909 : Nat := 1215891038687099248935049

theorem tailTrace_3551909 : CollatzResearch.WordTrace tailWord_3551909 prefixEnd_3551909 1215891038687099248935049 := by
  unfold tailWord_3551909
  simp only [CollatzResearch.WordTrace]
  refine ⟨129548764089047785607002781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86365842726031857071335187 129548764089047785607002781)
  ·
    refine ⟨48580786533392919602626043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129548764089047785607002781 48580786533392919602626043)
    ·
      refine ⟨72871179800089379403939065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48580786533392919602626043 72871179800089379403939065)
      ·
        refine ⟨54653384850067034552954299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72871179800089379403939065 54653384850067034552954299)
        ·
          refine ⟨81980077275100551829431449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54653384850067034552954299 81980077275100551829431449)
          ·
            refine ⟨61485057956325413872073587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81980077275100551829431449 61485057956325413872073587)
            ·
              refine ⟨92227586934488120808110381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61485057956325413872073587 92227586934488120808110381)
              ·
                refine ⟨34585345100433045303041393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92227586934488120808110381 34585345100433045303041393)
                ·
                  refine ⟨25939008825324783977281045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34585345100433045303041393 25939008825324783977281045)
                  ·
                    refine ⟨1215891038687099248935049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25939008825324783977281045 1215891038687099248935049)
                    ·
                      rfl

theorem cell22_3551909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 3, 2, 6].length) (baseStart_3551909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3551909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3551909 prefixEnd_3551909 := by exact prefixLift 3551909
  have htrace : WordTrace (prefixWord ++ tailWord_3551909) baseStart_3551909 baseEnd_3551909 := by
    simpa [prefixWord, tailWord_3551909, baseEnd_3551909] using wordTrace_append hprefix tailTrace_3551909
  have hstable : (prefixWord ++ tailWord_3551909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3551909).length < 2 ^ (prefixWord ++ tailWord_3551909).sum := by decide
  have hdescent : baseEnd_3551909 < baseStart_3551909 := by decide
  rcases family_descends (prefixWord ++ tailWord_3551909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3551917 : List Nat := [1, 5, 2, 1, 1, 4, 2, 1, 2, 3]
def baseStart_3551917 : Nat := 118140960795 + 3551917 * 2 ^ 59
def prefixEnd_3551917 : Nat := 4983230072969 + 3 ^ 40 * 3551917 * 2
def baseEnd_3551917 : Nat := 1215893777250589894735025

theorem tailTrace_3551917 : CollatzResearch.WordTrace tailWord_3551917 prefixEnd_3551917 1215893777250589894735025 := by
  unfold tailWord_3551917
  simp only [CollatzResearch.WordTrace]
  refine ⟨129549055873018802973294005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86366037248679201982196003 129549055873018802973294005)
  ·
    refine ⟨12145223988095512778746313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 129549055873018802973294005 12145223988095512778746313)
    ·
      refine ⟨9108917991071634584059735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12145223988095512778746313 9108917991071634584059735)
      ·
        refine ⟨13663376986607451876089603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9108917991071634584059735 13663376986607451876089603)
        ·
          refine ⟨20495065479911177814134405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13663376986607451876089603 20495065479911177814134405)
          ·
            refine ⟨3842824777483345840150201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20495065479911177814134405 3842824777483345840150201)
            ·
              refine ⟨2882118583112509380112651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3842824777483345840150201 2882118583112509380112651)
              ·
                refine ⟨4323177874668764070168977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2882118583112509380112651 4323177874668764070168977)
                ·
                  refine ⟨3242383406001573052626733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4323177874668764070168977 3242383406001573052626733)
                  ·
                    refine ⟨1215893777250589894735025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3242383406001573052626733 1215893777250589894735025)
                    ·
                      rfl

theorem cell22_3551917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 2, 1, 2, 3].length) (baseStart_3551917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3551917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3551917 prefixEnd_3551917 := by exact prefixLift 3551917
  have htrace : WordTrace (prefixWord ++ tailWord_3551917) baseStart_3551917 baseEnd_3551917 := by
    simpa [prefixWord, tailWord_3551917, baseEnd_3551917] using wordTrace_append hprefix tailTrace_3551917
  have hstable : (prefixWord ++ tailWord_3551917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3551917).length < 2 ^ (prefixWord ++ tailWord_3551917).sum := by decide
  have hdescent : baseEnd_3551917 < baseStart_3551917 := by decide
  rcases family_descends (prefixWord ++ tailWord_3551917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3551986 : List Nat := [3, 2, 1, 3, 1, 2, 1, 1, 8]
def baseStart_3551986 : Nat := 118140960795 + 3551986 * 2 ^ 59
def prefixEnd_3551986 : Nat := 4983230072969 + 3 ^ 40 * 3551986 * 2
def baseEnd_3551986 : Nat := 405305799120232238253271

theorem tailTrace_3551986 : CollatzResearch.WordTrace tailWord_3551986 prefixEnd_3551986 405305799120232238253271 := by
  unfold tailWord_3551986
  simp only [CollatzResearch.WordTrace]
  refine ⟨32387893127442206939388953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86367715006512551838370541 32387893127442206939388953)
  ·
    refine ⟨24290919845581655204541715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32387893127442206939388953 24290919845581655204541715)
    ·
      refine ⟨36436379768372482806812573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24290919845581655204541715 36436379768372482806812573)
      ·
        refine ⟨13663642413139681052554715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36436379768372482806812573 13663642413139681052554715)
        ·
          refine ⟨20495463619709521578832073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13663642413139681052554715 20495463619709521578832073)
          ·
            refine ⟨15371597714782141184124055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20495463619709521578832073 15371597714782141184124055)
            ·
              refine ⟨23057396572173211776186083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15371597714782141184124055 23057396572173211776186083)
              ·
                refine ⟨34586094858259817664279125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23057396572173211776186083 34586094858259817664279125)
                ·
                  refine ⟨405305799120232238253271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34586094858259817664279125 405305799120232238253271)
                  ·
                    rfl

theorem cell22_3551986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 1, 8].length) (baseStart_3551986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3551986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3551986 prefixEnd_3551986 := by exact prefixLift 3551986
  have htrace : WordTrace (prefixWord ++ tailWord_3551986) baseStart_3551986 baseEnd_3551986 := by
    simpa [prefixWord, tailWord_3551986, baseEnd_3551986] using wordTrace_append hprefix tailTrace_3551986
  have hstable : (prefixWord ++ tailWord_3551986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3551986).length < 2 ^ (prefixWord ++ tailWord_3551986).sum := by decide
  have hdescent : baseEnd_3551986 < baseStart_3551986 := by decide
  rcases family_descends (prefixWord ++ tailWord_3551986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3552054 : List Nat := [5, 1, 2, 2, 2, 2, 1, 3, 4]
def baseStart_3552054 : Nat := 118140960795 + 3552054 * 2 ^ 59
def prefixEnd_3552054 : Nat := 4983230072969 + 3 ^ 40 * 3552054 * 2
def baseEnd_3552054 : Nat := 405313558383455734686535

theorem tailTrace_3552054 : CollatzResearch.WordTrace tailWord_3552054 prefixEnd_3552054 405313558383455734686535 := by
  unfold tailWord_3552054
  simp only [CollatzResearch.WordTrace]
  refine ⟨8097128292095154710689451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 86369368449014983580687477 8097128292095154710689451)
  ·
    refine ⟨12145692438142732066034177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8097128292095154710689451 12145692438142732066034177)
    ·
      refine ⟨9109269328607049049525633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12145692438142732066034177 9109269328607049049525633)
      ·
        refine ⟨6831951996455286787144225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9109269328607049049525633 6831951996455286787144225)
        ·
          refine ⟨5123963997341465090358169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6831951996455286787144225 5123963997341465090358169)
          ·
            refine ⟨3842972998006098817768627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5123963997341465090358169 3842972998006098817768627)
            ·
              refine ⟨5764459497009148226652941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3842972998006098817768627 5764459497009148226652941)
              ·
                refine ⟨2161672311378430584994853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5764459497009148226652941 2161672311378430584994853)
                ·
                  refine ⟨405313558383455734686535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2161672311378430584994853 405313558383455734686535)
                  ·
                    rfl

theorem cell22_3552054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 1, 3, 4].length) (baseStart_3552054 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3552054 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3552054 prefixEnd_3552054 := by exact prefixLift 3552054
  have htrace : WordTrace (prefixWord ++ tailWord_3552054) baseStart_3552054 baseEnd_3552054 := by
    simpa [prefixWord, tailWord_3552054, baseEnd_3552054] using wordTrace_append hprefix tailTrace_3552054
  have hstable : (prefixWord ++ tailWord_3552054).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3552054).length < 2 ^ (prefixWord ++ tailWord_3552054).sum := by decide
  have hdescent : baseEnd_3552054 < baseStart_3552054 := by decide
  rcases family_descends (prefixWord ++ tailWord_3552054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3552065 : List Nat := [1, 2, 5, 3, 1, 2, 8]
def baseStart_3552065 : Nat := 118140960795 + 3552065 * 2 ^ 59
def prefixEnd_3552065 : Nat := 4983230072969 + 3 ^ 40 * 3552065 * 2
def baseEnd_3552065 : Nat := 45034979284265438593873

theorem tailTrace_3552065 : CollatzResearch.WordTrace tailWord_3552065 prefixEnd_3552065 45034979284265438593873 := by
  unfold tailWord_3552065
  simp only [CollatzResearch.WordTrace]
  refine ⟨129554453876482624249681649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86369635917655082833121099 129554453876482624249681649)
  ·
    refine ⟨97165840407361968187261237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129554453876482624249681649 97165840407361968187261237)
    ·
      refine ⟨9109297538190184517555741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 97165840407361968187261237 9109297538190184517555741)
      ·
        refine ⟨3415986576821319194083403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9109297538190184517555741 3415986576821319194083403)
        ·
          refine ⟨5123979865231978791125105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3415986576821319194083403 5123979865231978791125105)
          ·
            refine ⟨3842984898923984093343829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5123979865231978791125105 3842984898923984093343829)
            ·
              refine ⟨45034979284265438593873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3842984898923984093343829 45034979284265438593873)
              ·
                rfl

theorem cell22_3552065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 8].length) (baseStart_3552065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3552065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3552065 prefixEnd_3552065 := by exact prefixLift 3552065
  have htrace : WordTrace (prefixWord ++ tailWord_3552065) baseStart_3552065 baseEnd_3552065 := by
    simpa [prefixWord, tailWord_3552065, baseEnd_3552065] using wordTrace_append hprefix tailTrace_3552065
  have hstable : (prefixWord ++ tailWord_3552065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3552065).length < 2 ^ (prefixWord ++ tailWord_3552065).sum := by decide
  have hdescent : baseEnd_3552065 < baseStart_3552065 := by decide
  rcases family_descends (prefixWord ++ tailWord_3552065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3552080 : List Nat := [2, 1, 1, 1, 1, 4, 2, 6, 1, 3]
def baseStart_3552080 : Nat := 118140960795 + 3552080 * 2 ^ 59
def prefixEnd_3552080 : Nat := 4983230072969 + 3 ^ 40 * 3552080 * 2
def baseEnd_3552080 : Nat := 1215949575481711802909525

theorem tailTrace_3552080 : CollatzResearch.WordTrace tailWord_3552080 prefixEnd_3552080 1215949575481711802909525 := by
  unfold tailWord_3552080
  simp only [CollatzResearch.WordTrace]
  refine ⟨64777500485714140905738847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86370000647618854540985129 64777500485714140905738847)
  ·
    refine ⟨97166250728571211358608271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64777500485714140905738847 97166250728571211358608271)
    ·
      refine ⟨145749376092856817037912407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97166250728571211358608271 145749376092856817037912407)
      ·
        refine ⟨218624064139285225556868611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145749376092856817037912407 218624064139285225556868611)
        ·
          refine ⟨327936096208927838335302917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218624064139285225556868611 327936096208927838335302917)
          ·
            refine ⟨61488018039173969687869297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 327936096208927838335302917 61488018039173969687869297)
            ·
              refine ⟨46116013529380477265901973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61488018039173969687869297 46116013529380477265901973)
              ·
                refine ⟨2161688134189709871839155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 46116013529380477265901973 2161688134189709871839155)
                ·
                  refine ⟨3242532201284564807758733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2161688134189709871839155 3242532201284564807758733)
                  ·
                    refine ⟨1215949575481711802909525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3242532201284564807758733 1215949575481711802909525)
                    ·
                      rfl

theorem cell22_3552080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 6, 1, 3].length) (baseStart_3552080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3552080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3552080 prefixEnd_3552080 := by exact prefixLift 3552080
  have htrace : WordTrace (prefixWord ++ tailWord_3552080) baseStart_3552080 baseEnd_3552080 := by
    simpa [prefixWord, tailWord_3552080, baseEnd_3552080] using wordTrace_append hprefix tailTrace_3552080
  have hstable : (prefixWord ++ tailWord_3552080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3552080).length < 2 ^ (prefixWord ++ tailWord_3552080).sum := by decide
  have hdescent : baseEnd_3552080 < baseStart_3552080 := by decide
  rcases family_descends (prefixWord ++ tailWord_3552080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3552123 : List Nat := [1, 1, 1, 1, 1, 5, 2, 5, 1, 4]
def baseStart_3552123 : Nat := 118140960795 + 3552123 * 2 ^ 59
def prefixEnd_3552123 : Nat := 4983230072969 + 3 ^ 40 * 3552123 * 2
def baseEnd_3552123 : Nat := 1215964295260474024084393

theorem tailTrace_3552123 : CollatzResearch.WordTrace tailWord_3552123 prefixEnd_3552123 1215964295260474024084393 := by
  unfold tailWord_3552123
  simp only [CollatzResearch.WordTrace]
  refine ⟨129556569310272500155293023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86371046206848333436862015 129556569310272500155293023)
  ·
    refine ⟨194334853965408750232939535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129556569310272500155293023 194334853965408750232939535)
    ·
      refine ⟨291502280948113125349409303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194334853965408750232939535 291502280948113125349409303)
      ·
        refine ⟨437253421422169688024113955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291502280948113125349409303 437253421422169688024113955)
        ·
          refine ⟨655880132133254532036170933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 437253421422169688024113955 655880132133254532036170933)
          ·
            refine ⟨61488762387492612378391025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 655880132133254532036170933 61488762387492612378391025)
            ·
              refine ⟨46116571790619459283793269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61488762387492612378391025 46116571790619459283793269)
              ·
                refine ⟨4323428605370574307855619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46116571790619459283793269 4323428605370574307855619)
                ·
                  refine ⟨6485142908055861461783429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4323428605370574307855619 6485142908055861461783429)
                  ·
                    refine ⟨1215964295260474024084393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6485142908055861461783429 1215964295260474024084393)
                    ·
                      rfl

theorem cell22_3552123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 5, 1, 4].length) (baseStart_3552123 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3552123 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3552123 prefixEnd_3552123 := by exact prefixLift 3552123
  have htrace : WordTrace (prefixWord ++ tailWord_3552123) baseStart_3552123 baseEnd_3552123 := by
    simpa [prefixWord, tailWord_3552123, baseEnd_3552123] using wordTrace_append hprefix tailTrace_3552123
  have hstable : (prefixWord ++ tailWord_3552123).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3552123).length < 2 ^ (prefixWord ++ tailWord_3552123).sum := by decide
  have hdescent : baseEnd_3552123 < baseStart_3552123 := by decide
  rcases family_descends (prefixWord ++ tailWord_3552123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3552153 : List Nat := [1, 2, 1, 2, 1, 3, 1, 2, 6, 3]
def baseStart_3552153 : Nat := 118140960795 + 3552153 * 2 ^ 59
def prefixEnd_3552153 : Nat := 4983230072969 + 3 ^ 40 * 3552153 * 2
def baseEnd_3552153 : Nat := 1215974564873563945834301

theorem tailTrace_3552153 : CollatzResearch.WordTrace tailWord_3552153 prefixEnd_3552153 1215974564873563945834301 := by
  unfold tailWord_3552153
  simp only [CollatzResearch.WordTrace]
  refine ⟨129557663500163815278885113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86371775666775876852590075 129557663500163815278885113)
  ·
    refine ⟨97168247625122861459163835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129557663500163815278885113 97168247625122861459163835)
    ·
      refine ⟨145752371437684292188745753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97168247625122861459163835 145752371437684292188745753)
      ·
        refine ⟨109314278578263219141559315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145752371437684292188745753 109314278578263219141559315)
        ·
          refine ⟨163971417867394828712338973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109314278578263219141559315 163971417867394828712338973)
          ·
            refine ⟨61489281700273060767127115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 163971417867394828712338973 61489281700273060767127115)
            ·
              refine ⟨92233922550409591150690673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61489281700273060767127115 92233922550409591150690673)
              ·
                refine ⟨69175441912807193363018005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92233922550409591150690673 69175441912807193363018005)
                ·
                  refine ⟨3242598839662837188891469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 69175441912807193363018005 3242598839662837188891469)
                  ·
                    refine ⟨1215974564873563945834301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3242598839662837188891469 1215974564873563945834301)
                    ·
                      rfl

theorem cell22_3552153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 6, 3].length) (baseStart_3552153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3552153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3552153 prefixEnd_3552153 := by exact prefixLift 3552153
  have htrace : WordTrace (prefixWord ++ tailWord_3552153) baseStart_3552153 baseEnd_3552153 := by
    simpa [prefixWord, tailWord_3552153, baseEnd_3552153] using wordTrace_append hprefix tailTrace_3552153
  have hstable : (prefixWord ++ tailWord_3552153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3552153).length < 2 ^ (prefixWord ++ tailWord_3552153).sum := by decide
  have hdescent : baseEnd_3552153 < baseStart_3552153 := by decide
  rcases family_descends (prefixWord ++ tailWord_3552153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3552249 : List Nat := [1, 2, 1, 3, 1, 3, 5, 2, 1, 3]
def baseStart_3552249 : Nat := 118140960795 + 3552249 * 2 ^ 59
def prefixEnd_3552249 : Nat := 4983230072969 + 3 ^ 40 * 3552249 * 2
def baseEnd_3552249 : Nat := 1216007427635451695434007

theorem tailTrace_3552249 : CollatzResearch.WordTrace tailWord_3552249 prefixEnd_3552249 1216007427635451695434007 := by
  unfold tailWord_3552249
  simp only [CollatzResearch.WordTrace]
  refine ⟨129561164907816023674379801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86374109938544015782919867 129561164907816023674379801)
  ·
    refine ⟨97170873680862017755784851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129561164907816023674379801 97170873680862017755784851)
    ·
      refine ⟨145756310521293026633677277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97170873680862017755784851 145756310521293026633677277)
      ·
        refine ⟨54658616445484884987628979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145756310521293026633677277 54658616445484884987628979)
        ·
          refine ⟨81987924668227327481443469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54658616445484884987628979 81987924668227327481443469)
          ·
            refine ⟨30745471750585247805541301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81987924668227327481443469 30745471750585247805541301)
            ·
              refine ⟨2882387976617366981769497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30745471750585247805541301 2882387976617366981769497)
              ·
                refine ⟨2161790982463025236327123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2882387976617366981769497 2161790982463025236327123)
                ·
                  refine ⟨3242686473694537854490685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2161790982463025236327123 3242686473694537854490685)
                  ·
                    refine ⟨1216007427635451695434007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3242686473694537854490685 1216007427635451695434007)
                    ·
                      rfl

theorem cell22_3552249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 5, 2, 1, 3].length) (baseStart_3552249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3552249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3552249 prefixEnd_3552249 := by exact prefixLift 3552249
  have htrace : WordTrace (prefixWord ++ tailWord_3552249) baseStart_3552249 baseEnd_3552249 := by
    simpa [prefixWord, tailWord_3552249, baseEnd_3552249] using wordTrace_append hprefix tailTrace_3552249
  have hstable : (prefixWord ++ tailWord_3552249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3552249).length < 2 ^ (prefixWord ++ tailWord_3552249).sum := by decide
  have hdescent : baseEnd_3552249 < baseStart_3552249 := by decide
  rcases family_descends (prefixWord ++ tailWord_3552249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3552273 : List Nat := [1, 2, 2, 1, 1, 2, 1, 6, 6]
def baseStart_3552273 : Nat := 118140960795 + 3552273 * 2 ^ 59
def prefixEnd_3552273 : Nat := 4983230072969 + 3 ^ 40 * 3552273 * 2
def baseEnd_3552273 : Nat := 405338547775307877611311

theorem tailTrace_3552273 : CollatzResearch.WordTrace tailWord_3552273 prefixEnd_3552273 405338547775307877611311 := by
  unfold tailWord_3552273
  simp only [CollatzResearch.WordTrace]
  refine ⟨129562040259729075773253473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86374693506486050515502315 129562040259729075773253473)
  ·
    refine ⟨97171530194796806829940105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129562040259729075773253473 97171530194796806829940105)
    ·
      refine ⟨72878647646097605122455079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97171530194796806829940105 72878647646097605122455079)
      ·
        refine ⟨109317971469146407683682619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72878647646097605122455079 109317971469146407683682619)
        ·
          refine ⟨163976957203719611525523929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109317971469146407683682619 163976957203719611525523929)
          ·
            refine ⟨122982717902789708644142947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163976957203719611525523929 122982717902789708644142947)
            ·
              refine ⟨184474076854184562966214421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122982717902789708644142947 184474076854184562966214421)
              ·
                refine ⟨8647222352539901389041301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 184474076854184562966214421 8647222352539901389041301)
                ·
                  refine ⟨405338547775307877611311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8647222352539901389041301 405338547775307877611311)
                  ·
                    rfl

theorem cell22_3552273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 6, 6].length) (baseStart_3552273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3552273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3552273 prefixEnd_3552273 := by exact prefixLift 3552273
  have htrace : WordTrace (prefixWord ++ tailWord_3552273) baseStart_3552273 baseEnd_3552273 := by
    simpa [prefixWord, tailWord_3552273, baseEnd_3552273] using wordTrace_append hprefix tailTrace_3552273
  have hstable : (prefixWord ++ tailWord_3552273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3552273).length < 2 ^ (prefixWord ++ tailWord_3552273).sum := by decide
  have hdescent : baseEnd_3552273 < baseStart_3552273 := by decide
  rcases family_descends (prefixWord ++ tailWord_3552273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3552367 : List Nat := [1, 1, 2, 1, 3, 3, 4, 1, 3, 3]
def baseStart_3552367 : Nat := 118140960795 + 3552367 * 2 ^ 59
def prefixEnd_3552367 : Nat := 4983230072969 + 3 ^ 40 * 3552367 * 2
def baseEnd_3552367 : Nat := 1216047821446938720983645

theorem tailTrace_3552367 : CollatzResearch.WordTrace tailWord_3552367 prefixEnd_3552367 1216047821446938720983645 := by
  unfold tailWord_3552367
  simp only [CollatzResearch.WordTrace]
  refine ⟨129565468721388529827175355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86376979147592353218116903 129565468721388529827175355)
  ·
    refine ⟨194348203082082794740763033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129565468721388529827175355 194348203082082794740763033)
    ·
      refine ⟨145761152311562096055572275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194348203082082794740763033 145761152311562096055572275)
      ·
        refine ⟨218641728467343144083358413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145761152311562096055572275 218641728467343144083358413)
        ·
          refine ⟨81990648175253679031259405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 218641728467343144083358413 81990648175253679031259405)
          ·
            refine ⟨30746493065720129636722277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81990648175253679031259405 30746493065720129636722277)
            ·
              refine ⟨5764967449822524306885427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30746493065720129636722277 5764967449822524306885427)
              ·
                refine ⟨8647451174733786460328141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5764967449822524306885427 8647451174733786460328141)
                ·
                  refine ⟨3242794190525169922623053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8647451174733786460328141 3242794190525169922623053)
                  ·
                    refine ⟨1216047821446938720983645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3242794190525169922623053 1216047821446938720983645)
                    ·
                      rfl

theorem cell22_3552367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 4, 1, 3, 3].length) (baseStart_3552367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3552367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3552367 prefixEnd_3552367 := by exact prefixLift 3552367
  have htrace : WordTrace (prefixWord ++ tailWord_3552367) baseStart_3552367 baseEnd_3552367 := by
    simpa [prefixWord, tailWord_3552367, baseEnd_3552367] using wordTrace_append hprefix tailTrace_3552367
  have hstable : (prefixWord ++ tailWord_3552367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3552367).length < 2 ^ (prefixWord ++ tailWord_3552367).sum := by decide
  have hdescent : baseEnd_3552367 < baseStart_3552367 := by decide
  rcases family_descends (prefixWord ++ tailWord_3552367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3552373 : List Nat := [1, 3, 4, 3, 1, 1, 3, 1, 2, 3]
def baseStart_3552373 : Nat := 118140960795 + 3552373 * 2 ^ 59
def prefixEnd_3552373 : Nat := 4983230072969 + 3 ^ 40 * 3552373 * 2
def baseEnd_3552373 : Nat := 1216049875369556705333627

theorem tailTrace_3552373 : CollatzResearch.WordTrace tailWord_3552373 prefixEnd_3552373 1216049875369556705333627 := by
  unfold tailWord_3552373
  simp only [CollatzResearch.WordTrace]
  refine ⟨129565687559366792851893773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86377125039577861901262515 129565687559366792851893773)
  ·
    refine ⟨48587132834762547319460165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129565687559366792851893773 48587132834762547319460165)
    ·
      refine ⟨9110087406517977622398781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48587132834762547319460165 9110087406517977622398781)
      ·
        refine ⟨3416282777444241608399543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9110087406517977622398781 3416282777444241608399543)
        ·
          refine ⟨5124424166166362412599315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3416282777444241608399543 5124424166166362412599315)
          ·
            refine ⟨7686636249249543618898973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5124424166166362412599315 7686636249249543618898973)
            ·
              refine ⟨2882488593468578857087115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7686636249249543618898973 2882488593468578857087115)
              ·
                refine ⟨4323732890202868285630673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2882488593468578857087115 4323732890202868285630673)
                ·
                  refine ⟨3242799667652151214223005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4323732890202868285630673 3242799667652151214223005)
                  ·
                    refine ⟨1216049875369556705333627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3242799667652151214223005 1216049875369556705333627)
                    ·
                      rfl

theorem cell22_3552373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 3, 1, 2, 3].length) (baseStart_3552373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3552373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3552373 prefixEnd_3552373 := by exact prefixLift 3552373
  have htrace : WordTrace (prefixWord ++ tailWord_3552373) baseStart_3552373 baseEnd_3552373 := by
    simpa [prefixWord, tailWord_3552373, baseEnd_3552373] using wordTrace_append hprefix tailTrace_3552373
  have hstable : (prefixWord ++ tailWord_3552373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3552373).length < 2 ^ (prefixWord ++ tailWord_3552373).sum := by decide
  have hdescent : baseEnd_3552373 < baseStart_3552373 := by decide
  rcases family_descends (prefixWord ++ tailWord_3552373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3552418 : List Nat := [3, 3, 1, 3, 3, 1, 1, 1, 3, 3]
def baseStart_3552418 : Nat := 118140960795 + 3552418 * 2 ^ 59
def prefixEnd_3552418 : Nat := 4983230072969 + 3 ^ 40 * 3552418 * 2
def baseEnd_3552418 : Nat := 1216065279789191587958489

theorem tailTrace_3552418 : CollatzResearch.WordTrace tailWord_3552418 prefixEnd_3552418 1216065279789191587958489 := by
  unfold tailWord_3552418
  simp only [CollatzResearch.WordTrace]
  refine ⟨32391832211050941384320477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86378219229469177024854605 32391832211050941384320477)
  ·
    refine ⟨12146937079144103019120179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32391832211050941384320477 12146937079144103019120179)
    ·
      refine ⟨18220405618716154528680269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12146937079144103019120179 18220405618716154528680269)
      ·
        refine ⟨6832652107018557948255101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18220405618716154528680269 6832652107018557948255101)
        ·
          refine ⟨2562244540131959230595663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6832652107018557948255101 2562244540131959230595663)
          ·
            refine ⟨3843366810197938845893495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2562244540131959230595663 3843366810197938845893495)
            ·
              refine ⟨5765050215296908268840243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3843366810197938845893495 5765050215296908268840243)
              ·
                refine ⟨8647575322945362403260365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5765050215296908268840243 8647575322945362403260365)
                ·
                  refine ⟨3242840746104510901222637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8647575322945362403260365 3242840746104510901222637)
                  ·
                    refine ⟨1216065279789191587958489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3242840746104510901222637 1216065279789191587958489)
                    ·
                      rfl

theorem cell22_3552418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 1, 1, 3, 3].length) (baseStart_3552418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3552418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3552418 prefixEnd_3552418 := by exact prefixLift 3552418
  have htrace : WordTrace (prefixWord ++ tailWord_3552418) baseStart_3552418 baseEnd_3552418 := by
    simpa [prefixWord, tailWord_3552418, baseEnd_3552418] using wordTrace_append hprefix tailTrace_3552418
  have hstable : (prefixWord ++ tailWord_3552418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3552418).length < 2 ^ (prefixWord ++ tailWord_3552418).sum := by decide
  have hdescent : baseEnd_3552418 < baseStart_3552418 := by decide
  rcases family_descends (prefixWord ++ tailWord_3552418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3552444 : List Nat := [2, 2, 2, 3, 2, 1, 3, 2, 1, 4]
def baseStart_3552444 : Nat := 118140960795 + 3552444 * 2 ^ 59
def prefixEnd_3552444 : Nat := 4983230072969 + 3 ^ 40 * 3552444 * 2
def baseEnd_3552444 : Nat := 1216074180120536186808409

theorem tailTrace_3552444 : CollatzResearch.WordTrace tailWord_3552444 prefixEnd_3552444 1216074180120536186808409 := by
  unfold tailWord_3552444
  simp only [CollatzResearch.WordTrace]
  refine ⟨64784138571054785988864193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86378851428073047985152257 64784138571054785988864193)
  ·
    refine ⟨48588103928291089491648145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64784138571054785988864193 48588103928291089491648145)
    ·
      refine ⟨36441077946218317118736109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48588103928291089491648145 36441077946218317118736109)
      ·
        refine ⟨13665404229831868919526041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36441077946218317118736109 13665404229831868919526041)
        ·
          refine ⟨10249053172373901689644531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13665404229831868919526041 10249053172373901689644531)
          ·
            refine ⟨15373579758560852534466797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10249053172373901689644531 15373579758560852534466797)
            ·
              refine ⟨5765092409460319700425049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15373579758560852534466797 5765092409460319700425049)
              ·
                refine ⟨4323819307095239775318787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5765092409460319700425049 4323819307095239775318787)
                ·
                  refine ⟨6485728960642859662978181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4323819307095239775318787 6485728960642859662978181)
                  ·
                    refine ⟨1216074180120536186808409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6485728960642859662978181 1216074180120536186808409)
                    ·
                      rfl

theorem cell22_3552444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 3, 2, 1, 4].length) (baseStart_3552444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3552444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3552444 prefixEnd_3552444 := by exact prefixLift 3552444
  have htrace : WordTrace (prefixWord ++ tailWord_3552444) baseStart_3552444 baseEnd_3552444 := by
    simpa [prefixWord, tailWord_3552444, baseEnd_3552444] using wordTrace_append hprefix tailTrace_3552444
  have hstable : (prefixWord ++ tailWord_3552444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3552444).length < 2 ^ (prefixWord ++ tailWord_3552444).sum := by decide
  have hdescent : baseEnd_3552444 < baseStart_3552444 := by decide
  rcases family_descends (prefixWord ++ tailWord_3552444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3552455 : List Nat := [1, 1, 4, 1, 1, 1, 1, 5, 1, 6]
def baseStart_3552455 : Nat := 118140960795 + 3552455 * 2 ^ 59
def prefixEnd_3552455 : Nat := 4983230072969 + 3 ^ 40 * 3552455 * 2
def baseEnd_3552455 : Nat := 1216077945645335824783375

theorem tailTrace_3552455 : CollatzResearch.WordTrace tailWord_3552455 prefixEnd_3552455 1216077945645335824783375 := by
  unfold tailWord_3552455
  simp only [CollatzResearch.WordTrace]
  refine ⟨129568678345069720856378819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86379118896713147237585879 129568678345069720856378819)
  ·
    refine ⟨194353017517604581284568229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129568678345069720856378819 194353017517604581284568229)
    ·
      refine ⟨36441190784550858990856543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 194353017517604581284568229 36441190784550858990856543)
      ·
        refine ⟨54661786176826288486284815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36441190784550858990856543 54661786176826288486284815)
        ·
          refine ⟨81992679265239432729427223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54661786176826288486284815 81992679265239432729427223)
          ·
            refine ⟨122989018897859149094140835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81992679265239432729427223 122989018897859149094140835)
            ·
              refine ⟨184483528346788723641211253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122989018897859149094140835 184483528346788723641211253)
              ·
                refine ⟨17295330782511442841363555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 184483528346788723641211253 17295330782511442841363555)
                ·
                  refine ⟨25942996173767164262045333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17295330782511442841363555 25942996173767164262045333)
                  ·
                    refine ⟨1216077945645335824783375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25942996173767164262045333 1216077945645335824783375)
                    ·
                      rfl

theorem cell22_3552455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 5, 1, 6].length) (baseStart_3552455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3552455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3552455 prefixEnd_3552455 := by exact prefixLift 3552455
  have htrace : WordTrace (prefixWord ++ tailWord_3552455) baseStart_3552455 baseEnd_3552455 := by
    simpa [prefixWord, tailWord_3552455, baseEnd_3552455] using wordTrace_append hprefix tailTrace_3552455
  have hstable : (prefixWord ++ tailWord_3552455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3552455).length < 2 ^ (prefixWord ++ tailWord_3552455).sum := by decide
  have hdescent : baseEnd_3552455 < baseStart_3552455 := by decide
  rcases family_descends (prefixWord ++ tailWord_3552455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3552536 : List Nat := [2, 1, 2, 3, 1, 3, 2, 4, 1, 3]
def baseStart_3552536 : Nat := 118140960795 + 3552536 * 2 ^ 59
def prefixEnd_3552536 : Nat := 4983230072969 + 3 ^ 40 * 3552536 * 2
def baseEnd_3552536 : Nat := 1216105673600678613508127

theorem tailTrace_3552536 : CollatzResearch.WordTrace tailWord_3552536 prefixEnd_3552536 1216105673600678613508127 := by
  unfold tailWord_3552536
  simp only [CollatzResearch.WordTrace]
  refine ⟨64785816328888135845038731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86381088438517514460051641 64785816328888135845038731)
  ·
    refine ⟨97178724493332203767558097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64785816328888135845038731 97178724493332203767558097)
    ·
      refine ⟨72884043369999152825668573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97178724493332203767558097 72884043369999152825668573)
      ·
        refine ⟨27331516263749682309625715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72884043369999152825668573 27331516263749682309625715)
        ·
          refine ⟨40997274395624523464438573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27331516263749682309625715 40997274395624523464438573)
          ·
            refine ⟨15373977898359196299164465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40997274395624523464438573 15373977898359196299164465)
            ·
              refine ⟨11530483423769397224373349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15373977898359196299164465 11530483423769397224373349)
              ·
                refine ⟨2161965641956761979570003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11530483423769397224373349 2161965641956761979570003)
                ·
                  refine ⟨3242948462935142969355005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2161965641956761979570003 3242948462935142969355005)
                  ·
                    refine ⟨1216105673600678613508127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3242948462935142969355005 1216105673600678613508127)
                    ·
                      rfl

theorem cell22_3552536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 4, 1, 3].length) (baseStart_3552536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3552536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3552536 prefixEnd_3552536 := by exact prefixLift 3552536
  have htrace : WordTrace (prefixWord ++ tailWord_3552536) baseStart_3552536 baseEnd_3552536 := by
    simpa [prefixWord, tailWord_3552536, baseEnd_3552536] using wordTrace_append hprefix tailTrace_3552536
  have hstable : (prefixWord ++ tailWord_3552536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3552536).length < 2 ^ (prefixWord ++ tailWord_3552536).sum := by decide
  have hdescent : baseEnd_3552536 < baseStart_3552536 := by decide
  rcases family_descends (prefixWord ++ tailWord_3552536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3552547 : List Nat := [1, 1, 1, 4, 2, 3, 2, 1, 2, 5]
def baseStart_3552547 : Nat := 118140960795 + 3552547 * 2 ^ 59
def prefixEnd_3552547 : Nat := 4983230072969 + 3 ^ 40 * 3552547 * 2
def baseEnd_3552547 : Nat := 1216109439125478251483093

theorem tailTrace_3552547 : CollatzResearch.WordTrace tailWord_3552547 prefixEnd_3552547 1216109439125478251483093 := by
  unfold tailWord_3552547
  simp only [CollatzResearch.WordTrace]
  refine ⟨129572033860736420568727895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86381355907157613712485263 129572033860736420568727895)
  ·
    refine ⟨194358050791104630853091843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129572033860736420568727895 194358050791104630853091843)
    ·
      refine ⟨291537076186656946279637765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194358050791104630853091843 291537076186656946279637765)
      ·
        refine ⟨54663201784998177427432081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 291537076186656946279637765 54663201784998177427432081)
        ·
          refine ⟨40997401338748633070574061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54663201784998177427432081 40997401338748633070574061)
          ·
            refine ⟨15374025502030737401465273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40997401338748633070574061 15374025502030737401465273)
            ·
              refine ⟨11530519126523053051098955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15374025502030737401465273 11530519126523053051098955)
              ·
                refine ⟨17295778689784579576648433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11530519126523053051098955 17295778689784579576648433)
                ·
                  refine ⟨12971834017338434682486325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17295778689784579576648433 12971834017338434682486325)
                  ·
                    refine ⟨1216109439125478251483093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12971834017338434682486325 1216109439125478251483093)
                    ·
                      rfl

theorem cell22_3552547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 1, 2, 5].length) (baseStart_3552547 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3552547 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3552547 prefixEnd_3552547 := by exact prefixLift 3552547
  have htrace : WordTrace (prefixWord ++ tailWord_3552547) baseStart_3552547 baseEnd_3552547 := by
    simpa [prefixWord, tailWord_3552547, baseEnd_3552547] using wordTrace_append hprefix tailTrace_3552547
  have hstable : (prefixWord ++ tailWord_3552547).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3552547).length < 2 ^ (prefixWord ++ tailWord_3552547).sum := by decide
  have hdescent : baseEnd_3552547 < baseStart_3552547 := by decide
  rcases family_descends (prefixWord ++ tailWord_3552547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3552607 : List Nat := [1, 1, 2, 3, 1, 2, 1, 1, 6, 4]
def baseStart_3552607 : Nat := 118140960795 + 3552607 * 2 ^ 59
def prefixEnd_3552607 : Nat := 4983230072969 + 3 ^ 40 * 3552607 * 2
def baseEnd_3552607 : Nat := 1216129978351658094982909

theorem tailTrace_3552607 : CollatzResearch.WordTrace tailWord_3552607 prefixEnd_3552607 1216129978351658094982909 := by
  unfold tailWord_3552607
  simp only [CollatzResearch.WordTrace]
  refine ⟨129574222240519050815912075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86382814827012700543941383 129574222240519050815912075)
  ·
    refine ⟨194361333360778576223868113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129574222240519050815912075 194361333360778576223868113)
    ·
      refine ⟨145771000020583932167901085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194361333360778576223868113 145771000020583932167901085)
      ·
        refine ⟨54664125007718974562962907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145771000020583932167901085 54664125007718974562962907)
        ·
          refine ⟨81996187511578461844444361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54664125007718974562962907 81996187511578461844444361)
          ·
            refine ⟨61497140633683846383333271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81996187511578461844444361 61497140633683846383333271)
            ·
              refine ⟨92245710950525769574999907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61497140633683846383333271 92245710950525769574999907)
              ·
                refine ⟨138368566425788654362499861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92245710950525769574999907 138368566425788654362499861)
                ·
                  refine ⟨6486026551208843173242181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 138368566425788654362499861 6486026551208843173242181)
                  ·
                    refine ⟨1216129978351658094982909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6486026551208843173242181 1216129978351658094982909)
                    ·
                      rfl

theorem cell22_3552607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 6, 4].length) (baseStart_3552607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3552607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3552607 prefixEnd_3552607 := by exact prefixLift 3552607
  have htrace : WordTrace (prefixWord ++ tailWord_3552607) baseStart_3552607 baseEnd_3552607 := by
    simpa [prefixWord, tailWord_3552607, baseEnd_3552607] using wordTrace_append hprefix tailTrace_3552607
  have hstable : (prefixWord ++ tailWord_3552607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3552607).length < 2 ^ (prefixWord ++ tailWord_3552607).sum := by decide
  have hdescent : baseEnd_3552607 < baseStart_3552607 := by decide
  rcases family_descends (prefixWord ++ tailWord_3552607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3552624 : List Nat := [2, 1, 1, 1, 4, 2, 4, 1, 2, 4]
def baseStart_3552624 : Nat := 118140960795 + 3552624 * 2 ^ 59
def prefixEnd_3552624 : Nat := 4983230072969 + 3 ^ 40 * 3552624 * 2
def baseEnd_3552624 : Nat := 1216135797799075717307857

theorem tailTrace_3552624 : CollatzResearch.WordTrace tailWord_3552624 prefixEnd_3552624 1216135797799075717307857 := by
  unfold tailWord_3552624
  simp only [CollatzResearch.WordTrace]
  refine ⟨64787421140728731359640463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86383228187638308479520617 64787421140728731359640463)
  ·
    refine ⟨97181131711093097039460695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64787421140728731359640463 97181131711093097039460695)
    ·
      refine ⟨145771697566639645559191043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97181131711093097039460695 145771697566639645559191043)
      ·
        refine ⟨218657546349959468338786565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145771697566639645559191043 218657546349959468338786565)
        ·
          refine ⟨40998289940617400313522481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 218657546349959468338786565 40998289940617400313522481)
          ·
            refine ⟨30748717455463050235141861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40998289940617400313522481 30748717455463050235141861)
            ·
              refine ⟨5765384522899321919089099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30748717455463050235141861 5765384522899321919089099)
              ·
                refine ⟨8648076784348982878633649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5765384522899321919089099 8648076784348982878633649)
                ·
                  refine ⟨6486057588261737158975237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8648076784348982878633649 6486057588261737158975237)
                  ·
                    refine ⟨1216135797799075717307857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6486057588261737158975237 1216135797799075717307857)
                    ·
                      rfl

theorem cell22_3552624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 4, 1, 2, 4].length) (baseStart_3552624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3552624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3552624 prefixEnd_3552624 := by exact prefixLift 3552624
  have htrace : WordTrace (prefixWord ++ tailWord_3552624) baseStart_3552624 baseEnd_3552624 := by
    simpa [prefixWord, tailWord_3552624, baseEnd_3552624] using wordTrace_append hprefix tailTrace_3552624
  have hstable : (prefixWord ++ tailWord_3552624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3552624).length < 2 ^ (prefixWord ++ tailWord_3552624).sum := by decide
  have hdescent : baseEnd_3552624 < baseStart_3552624 := by decide
  rcases family_descends (prefixWord ++ tailWord_3552624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3552652 : List Nat := [2, 2, 1, 2, 1, 3, 1, 1, 1, 8]
def baseStart_3552652 : Nat := 118140960795 + 3552652 * 2 ^ 59
def prefixEnd_3552652 : Nat := 4983230072969 + 3 ^ 40 * 3552652 * 2
def baseEnd_3552652 : Nat := 1216145382771292977607771

theorem tailTrace_3552652 : CollatzResearch.WordTrace tailWord_3552652 prefixEnd_3552652 1216145382771292977607771 := by
  unfold tailWord_3552652
  simp only [CollatzResearch.WordTrace]
  refine ⟨64787931762678011750650105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86383909016904015667533473 64787931762678011750650105)
  ·
    refine ⟨48590948822008508812987579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64787931762678011750650105 48590948822008508812987579)
    ·
      refine ⟨72886423233012763219481369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48590948822008508812987579 72886423233012763219481369)
      ·
        refine ⟨54664817424759572414611027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72886423233012763219481369 54664817424759572414611027)
        ·
          refine ⟨81997226137139358621916541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54664817424759572414611027 81997226137139358621916541)
          ·
            refine ⟨30748959801427259483218703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81997226137139358621916541 30748959801427259483218703)
            ·
              refine ⟨46123439702140889224828055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30748959801427259483218703 46123439702140889224828055)
              ·
                refine ⟨69185159553211333837242083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46123439702140889224828055 69185159553211333837242083)
                ·
                  refine ⟨103777739329817000755863125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69185159553211333837242083 103777739329817000755863125)
                  ·
                    refine ⟨1216145382771292977607771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 103777739329817000755863125 1216145382771292977607771)
                    ·
                      rfl

theorem cell22_3552652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 1, 8].length) (baseStart_3552652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3552652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3552652 prefixEnd_3552652 := by exact prefixLift 3552652
  have htrace : WordTrace (prefixWord ++ tailWord_3552652) baseStart_3552652 baseEnd_3552652 := by
    simpa [prefixWord, tailWord_3552652, baseEnd_3552652] using wordTrace_append hprefix tailTrace_3552652
  have hstable : (prefixWord ++ tailWord_3552652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3552652).length < 2 ^ (prefixWord ++ tailWord_3552652).sum := by decide
  have hdescent : baseEnd_3552652 < baseStart_3552652 := by decide
  rcases family_descends (prefixWord ++ tailWord_3552652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3552671 : List Nat := [1, 1, 2, 5, 1, 3, 1, 2, 3, 3]
def baseStart_3552671 : Nat := 118140960795 + 3552671 * 2 ^ 59
def prefixEnd_3552671 : Nat := 4983230072969 + 3 ^ 40 * 3552671 * 2
def baseEnd_3552671 : Nat := 1216151886859583261382713

theorem tailTrace_3552671 : CollatzResearch.WordTrace tailWord_3552671 prefixEnd_3552671 1216151886859583261382713 := by
  unfold tailWord_3552671
  simp only [CollatzResearch.WordTrace]
  refine ⟨129576556512287189746241867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86384371008191459830827911 129576556512287189746241867)
  ·
    refine ⟨194364834768430784619362801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129576556512287189746241867 194364834768430784619362801)
    ·
      refine ⟨145773626076323088464522101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194364834768430784619362801 145773626076323088464522101)
      ·
        refine ⟨13666277444655289543548947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 145773626076323088464522101 13666277444655289543548947)
        ·
          refine ⟨20499416166982934315323421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13666277444655289543548947 20499416166982934315323421)
          ·
            refine ⟨7687281062618600368246283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20499416166982934315323421 7687281062618600368246283)
            ·
              refine ⟨11530921593927900552369425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7687281062618600368246283 11530921593927900552369425)
              ·
                refine ⟨8648191195445925414277069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11530921593927900552369425 8648191195445925414277069)
                ·
                  refine ⟨3243071698292222030353901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8648191195445925414277069 3243071698292222030353901)
                  ·
                    refine ⟨1216151886859583261382713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3243071698292222030353901 1216151886859583261382713)
                    ·
                      rfl

theorem cell22_3552671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 2, 3, 3].length) (baseStart_3552671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3552671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3552671 prefixEnd_3552671 := by exact prefixLift 3552671
  have htrace : WordTrace (prefixWord ++ tailWord_3552671) baseStart_3552671 baseEnd_3552671 := by
    simpa [prefixWord, tailWord_3552671, baseEnd_3552671] using wordTrace_append hprefix tailTrace_3552671
  have hstable : (prefixWord ++ tailWord_3552671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3552671).length < 2 ^ (prefixWord ++ tailWord_3552671).sum := by decide
  have hdescent : baseEnd_3552671 < baseStart_3552671 := by decide
  rcases family_descends (prefixWord ++ tailWord_3552671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3552729 : List Nat := [1, 2, 1, 2, 4, 2, 2, 2, 6]
def baseStart_3552729 : Nat := 118140960795 + 3552729 * 2 ^ 59
def prefixEnd_3552729 : Nat := 4983230072969 + 3 ^ 40 * 3552729 * 2
def baseEnd_3552729 : Nat := 405390580481630147810845

theorem tailTrace_3552729 : CollatzResearch.WordTrace tailWord_3552729 prefixEnd_3552729 405390580481630147810845 := by
  unfold tailWord_3552729
  simp only [CollatzResearch.WordTrace]
  refine ⟨129578671946077065651853241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86385781297384710434568827 129578671946077065651853241)
  ·
    refine ⟨97184003959557799238889931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129578671946077065651853241 97184003959557799238889931)
    ·
      refine ⟨145776005939336698858334897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97184003959557799238889931 145776005939336698858334897)
      ·
        refine ⟨109332004454502524143751173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145776005939336698858334897 109332004454502524143751173)
        ·
          refine ⟨20499750835219223276953345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 109332004454502524143751173 20499750835219223276953345)
          ·
            refine ⟨15374813126414417457715009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20499750835219223276953345 15374813126414417457715009)
            ·
              refine ⟨11531109844810813093286257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15374813126414417457715009 11531109844810813093286257)
              ·
                refine ⟨8648332383608109819964693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11531109844810813093286257 8648332383608109819964693)
                ·
                  refine ⟨405390580481630147810845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8648332383608109819964693 405390580481630147810845)
                  ·
                    rfl

theorem cell22_3552729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 2, 6].length) (baseStart_3552729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3552729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3552729 prefixEnd_3552729 := by exact prefixLift 3552729
  have htrace : WordTrace (prefixWord ++ tailWord_3552729) baseStart_3552729 baseEnd_3552729 := by
    simpa [prefixWord, tailWord_3552729, baseEnd_3552729] using wordTrace_append hprefix tailTrace_3552729
  have hstable : (prefixWord ++ tailWord_3552729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3552729).length < 2 ^ (prefixWord ++ tailWord_3552729).sum := by decide
  have hdescent : baseEnd_3552729 < baseStart_3552729 := by decide
  rcases family_descends (prefixWord ++ tailWord_3552729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3552744 : List Nat := [2, 1, 4, 1, 1, 2, 2, 1, 3, 5]
def baseStart_3552744 : Nat := 118140960795 + 3552744 * 2 ^ 59
def prefixEnd_3552744 : Nat := 4983230072969 + 3 ^ 40 * 3552744 * 2
def baseEnd_3552744 : Nat := 1216176876251435404307489

theorem tailTrace_3552744 : CollatzResearch.WordTrace tailWord_3552744 prefixEnd_3552744 1216176876251435404307489 := by
  unfold tailWord_3552744
  simp only [CollatzResearch.WordTrace]
  refine ⟨64789609520511361606824643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86386146027348482142432857 64789609520511361606824643)
  ·
    refine ⟨97184414280767042410236965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64789609520511361606824643 97184414280767042410236965)
    ·
      refine ⟨18222077677643820451919431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97184414280767042410236965 18222077677643820451919431)
      ·
        refine ⟨27333116516465730677879147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18222077677643820451919431 27333116516465730677879147)
        ·
          refine ⟨40999674774698596016818721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27333116516465730677879147 40999674774698596016818721)
          ·
            refine ⟨30749756081023947012614041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40999674774698596016818721 30749756081023947012614041)
            ·
              refine ⟨23062317060767960259460531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30749756081023947012614041 23062317060767960259460531)
              ·
                refine ⟨34593475591151940389190797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23062317060767960259460531 34593475591151940389190797)
                ·
                  refine ⟨12972553346681977645946549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34593475591151940389190797 12972553346681977645946549)
                  ·
                    refine ⟨1216176876251435404307489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12972553346681977645946549 1216176876251435404307489)
                    ·
                      rfl

theorem cell22_3552744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 1, 3, 5].length) (baseStart_3552744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3552744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3552744 prefixEnd_3552744 := by exact prefixLift 3552744
  have htrace : WordTrace (prefixWord ++ tailWord_3552744) baseStart_3552744 baseEnd_3552744 := by
    simpa [prefixWord, tailWord_3552744, baseEnd_3552744] using wordTrace_append hprefix tailTrace_3552744
  have hstable : (prefixWord ++ tailWord_3552744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3552744).length < 2 ^ (prefixWord ++ tailWord_3552744).sum := by decide
  have hdescent : baseEnd_3552744 < baseStart_3552744 := by decide
  rcases family_descends (prefixWord ++ tailWord_3552744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3552761 : List Nat := [1, 2, 1, 3, 1, 2, 1, 6, 2, 3]
def baseStart_3552761 : Nat := 118140960795 + 3552761 * 2 ^ 59
def prefixEnd_3552761 : Nat := 4983230072969 + 3 ^ 40 * 3552761 * 2
def baseEnd_3552761 : Nat := 1216182695698853026632437

theorem tailTrace_3552761 : CollatzResearch.WordTrace tailWord_3552761 prefixEnd_3552761 1216182695698853026632437 := by
  unfold tailWord_3552761
  simp only [CollatzResearch.WordTrace]
  refine ⟨129579839081961135117018137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86386559387974090078012091 129579839081961135117018137)
  ·
    refine ⟨97184879311470851337763603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129579839081961135117018137 97184879311470851337763603)
    ·
      refine ⟨145777318967206277006645405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97184879311470851337763603 145777318967206277006645405)
      ·
        refine ⟨54666494612702353877492027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145777318967206277006645405 54666494612702353877492027)
        ·
          refine ⟨81999741919053530816238041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54666494612702353877492027 81999741919053530816238041)
          ·
            refine ⟨61499806439290148112178531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81999741919053530816238041 61499806439290148112178531)
            ·
              refine ⟨92249709658935222168267797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61499806439290148112178531 92249709658935222168267797)
              ·
                refine ⟨4324205140262588539137553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 92249709658935222168267797 4324205140262588539137553)
                ·
                  refine ⟨3243153855196941404353165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4324205140262588539137553 3243153855196941404353165)
                  ·
                    refine ⟨1216182695698853026632437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3243153855196941404353165 1216182695698853026632437)
                    ·
                      rfl

theorem cell22_3552761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 6, 2, 3].length) (baseStart_3552761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3552761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3552761 prefixEnd_3552761 := by exact prefixLift 3552761
  have htrace : WordTrace (prefixWord ++ tailWord_3552761) baseStart_3552761 baseEnd_3552761 := by
    simpa [prefixWord, tailWord_3552761, baseEnd_3552761] using wordTrace_append hprefix tailTrace_3552761
  have hstable : (prefixWord ++ tailWord_3552761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3552761).length < 2 ^ (prefixWord ++ tailWord_3552761).sum := by decide
  have hdescent : baseEnd_3552761 < baseStart_3552761 := by decide
  rcases family_descends (prefixWord ++ tailWord_3552761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3552778 : List Nat := [3, 1, 2, 2, 2, 3, 1, 3, 2, 3]
def baseStart_3552778 : Nat := 118140960795 + 3552778 * 2 ^ 59
def prefixEnd_3552778 : Nat := 4983230072969 + 3 ^ 40 * 3552778 * 2
def baseEnd_3552778 : Nat := 1216188515146270648957385

theorem tailTrace_3552778 : CollatzResearch.WordTrace tailWord_3552778 prefixEnd_3552778 1216188515146270648957385 := by
  unfold tailWord_3552778
  simp only [CollatzResearch.WordTrace]
  refine ⟨32395114780724886755096747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86386972748599698013591325 32395114780724886755096747)
  ·
    refine ⟨48592672171087330132645121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32395114780724886755096747 48592672171087330132645121)
    ·
      refine ⟨36444504128315497599483841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48592672171087330132645121 36444504128315497599483841)
      ·
        refine ⟨27333378096236623199612881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36444504128315497599483841 27333378096236623199612881)
        ·
          refine ⟨20500033572177467399709661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27333378096236623199612881 20500033572177467399709661)
          ·
            refine ⟨7687512589566550274891123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20500033572177467399709661 7687512589566550274891123)
            ·
              refine ⟨11531268884349825412336685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7687512589566550274891123 11531268884349825412336685)
              ·
                refine ⟨4324225831631184529626257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11531268884349825412336685 4324225831631184529626257)
                ·
                  refine ⟨3243169373723388397219693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4324225831631184529626257 3243169373723388397219693)
                  ·
                    refine ⟨1216188515146270648957385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3243169373723388397219693 1216188515146270648957385)
                    ·
                      rfl

theorem cell22_3552778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 3, 2, 3].length) (baseStart_3552778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3552778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3552778 prefixEnd_3552778 := by exact prefixLift 3552778
  have htrace : WordTrace (prefixWord ++ tailWord_3552778) baseStart_3552778 baseEnd_3552778 := by
    simpa [prefixWord, tailWord_3552778, baseEnd_3552778] using wordTrace_append hprefix tailTrace_3552778
  have hstable : (prefixWord ++ tailWord_3552778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3552778).length < 2 ^ (prefixWord ++ tailWord_3552778).sum := by decide
  have hdescent : baseEnd_3552778 < baseStart_3552778 := by decide
  rcases family_descends (prefixWord ++ tailWord_3552778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3552864 : List Nat := [2, 1, 1, 3, 2, 1, 1, 1, 10]
def baseStart_3552864 : Nat := 118140960795 + 3552864 * 2 ^ 59
def prefixEnd_3552864 : Nat := 4983230072969 + 3 ^ 40 * 3552864 * 2
def baseEnd_3552864 : Nat := 405405984901265030435707

theorem tailTrace_3552864 : CollatzResearch.WordTrace tailWord_3552864 prefixEnd_3552864 405405984901265030435707 := by
  unfold tailWord_3552864
  simp only [CollatzResearch.WordTrace]
  refine ⟨64791797900293991854008823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86389063867058655805345097 64791797900293991854008823)
  ·
    refine ⟨97187696850440987781013235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64791797900293991854008823 97187696850440987781013235)
    ·
      refine ⟨145781545275661481671519853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97187696850440987781013235 145781545275661481671519853)
      ·
        refine ⟨54668079478373055626819945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145781545275661481671519853 54668079478373055626819945)
        ·
          refine ⟨41001059608779791720114959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54668079478373055626819945 41001059608779791720114959)
          ·
            refine ⟨61501589413169687580172439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41001059608779791720114959 61501589413169687580172439)
            ·
              refine ⟨92252384119754531370258659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61501589413169687580172439 92252384119754531370258659)
              ·
                refine ⟨138378576179631797055387989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92252384119754531370258659 138378576179631797055387989)
                ·
                  refine ⟨405405984901265030435707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 138378576179631797055387989 405405984901265030435707)
                  ·
                    rfl

theorem cell22_3552864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 10].length) (baseStart_3552864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3552864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3552864 prefixEnd_3552864 := by exact prefixLift 3552864
  have htrace : WordTrace (prefixWord ++ tailWord_3552864) baseStart_3552864 baseEnd_3552864 := by
    simpa [prefixWord, tailWord_3552864, baseEnd_3552864] using wordTrace_append hprefix tailTrace_3552864
  have hstable : (prefixWord ++ tailWord_3552864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3552864).length < 2 ^ (prefixWord ++ tailWord_3552864).sum := by decide
  have hdescent : baseEnd_3552864 < baseStart_3552864 := by decide
  rcases family_descends (prefixWord ++ tailWord_3552864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3552900 : List Nat := [2, 3, 2, 1, 4, 1, 2, 2, 1, 4]
def baseStart_3552900 : Nat := 118140960795 + 3552900 * 2 ^ 59
def prefixEnd_3552900 : Nat := 4983230072969 + 3 ^ 40 * 3552900 * 2
def baseEnd_3552900 : Nat := 1216230278239502997407011

theorem tailTrace_3552900 : CollatzResearch.WordTrace tailWord_3552900 prefixEnd_3552900 1216230278239502997407011 := by
  unfold tailWord_3552900
  simp only [CollatzResearch.WordTrace]
  refine ⟨64792454414228780928164077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86389939218971707904218769 64792454414228780928164077)
  ·
    refine ⟨24297170405335792848061529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64792454414228780928164077 24297170405335792848061529)
    ·
      refine ⟨18222877804001844636046147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24297170405335792848061529 18222877804001844636046147)
      ·
        refine ⟨27334316706002766954069221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18222877804001844636046147 27334316706002766954069221)
        ·
          refine ⟨5125184382375518803887979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27334316706002766954069221 5125184382375518803887979)
          ·
            refine ⟨7687776573563278205831969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5125184382375518803887979 7687776573563278205831969)
            ·
              refine ⟨5765832430172458654373977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7687776573563278205831969 5765832430172458654373977)
              ·
                refine ⟨4324374322629343990780483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5765832430172458654373977 4324374322629343990780483)
                ·
                  refine ⟨6486561483944015986170725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4324374322629343990780483 6486561483944015986170725)
                  ·
                    refine ⟨1216230278239502997407011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6486561483944015986170725 1216230278239502997407011)
                    ·
                      rfl

theorem cell22_3552900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 2, 2, 1, 4].length) (baseStart_3552900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3552900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3552900 prefixEnd_3552900 := by exact prefixLift 3552900
  have htrace : WordTrace (prefixWord ++ tailWord_3552900) baseStart_3552900 baseEnd_3552900 := by
    simpa [prefixWord, tailWord_3552900, baseEnd_3552900] using wordTrace_append hprefix tailTrace_3552900
  have hstable : (prefixWord ++ tailWord_3552900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3552900).length < 2 ^ (prefixWord ++ tailWord_3552900).sum := by decide
  have hdescent : baseEnd_3552900 < baseStart_3552900 := by decide
  rcases family_descends (prefixWord ++ tailWord_3552900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3552928 : List Nat := [2, 1, 1, 4, 3, 2, 1, 2, 2, 4]
def baseStart_3552928 : Nat := 118140960795 + 3552928 * 2 ^ 59
def prefixEnd_3552928 : Nat := 4983230072969 + 3 ^ 40 * 3552928 * 2
def baseEnd_3552928 : Nat := 1216239863211720257706925

theorem tailTrace_3552928 : CollatzResearch.WordTrace tailWord_3552928 prefixEnd_3552928 1216239863211720257706925 := by
  unfold tailWord_3552928
  simp only [CollatzResearch.WordTrace]
  refine ⟨64792965036178061319173719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86390620048237415092231625 64792965036178061319173719)
  ·
    refine ⟨97189447554267091978760579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64792965036178061319173719 97189447554267091978760579)
    ·
      refine ⟨145784171331400637968140869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97189447554267091978760579 145784171331400637968140869)
      ·
        refine ⟨27334532124637619619026413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 145784171331400637968140869 27334532124637619619026413)
        ·
          refine ⟨10250449546739107357134905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27334532124637619619026413 10250449546739107357134905)
          ·
            refine ⟨7687837160054330517851179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10250449546739107357134905 7687837160054330517851179)
            ·
              refine ⟨11531755740081495776776769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7687837160054330517851179 11531755740081495776776769)
              ·
                refine ⟨8648816805061121832582577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11531755740081495776776769 8648816805061121832582577)
                ·
                  refine ⟨6486612603795841374436933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8648816805061121832582577 6486612603795841374436933)
                  ·
                    refine ⟨1216239863211720257706925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6486612603795841374436933 1216239863211720257706925)
                    ·
                      rfl

theorem cell22_3552928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 2, 2, 4].length) (baseStart_3552928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3552928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3552928 prefixEnd_3552928 := by exact prefixLift 3552928
  have htrace : WordTrace (prefixWord ++ tailWord_3552928) baseStart_3552928 baseEnd_3552928 := by
    simpa [prefixWord, tailWord_3552928, baseEnd_3552928] using wordTrace_append hprefix tailTrace_3552928
  have hstable : (prefixWord ++ tailWord_3552928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3552928).length < 2 ^ (prefixWord ++ tailWord_3552928).sum := by decide
  have hdescent : baseEnd_3552928 < baseStart_3552928 := by decide
  rcases family_descends (prefixWord ++ tailWord_3552928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3552992 : List Nat := [2, 1, 1, 3, 1, 2, 6, 2, 1, 3]
def baseStart_3552992 : Nat := 118140960795 + 3552992 * 2 ^ 59
def prefixEnd_3552992 : Nat := 4983230072969 + 3 ^ 40 * 3552992 * 2
def baseEnd_3552992 : Nat := 1216261771719645424106729

theorem tailTrace_3552992 : CollatzResearch.WordTrace tailWord_3552992 prefixEnd_3552992 1216261771719645424106729 := by
  unfold tailWord_3552992
  simp only [CollatzResearch.WordTrace]
  refine ⟨64794132172062130784338615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86392176229416174379118153 64794132172062130784338615)
  ·
    refine ⟨97191198258093196176507923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64794132172062130784338615 97191198258093196176507923)
    ·
      refine ⟨145786797387139794264761885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97191198258093196176507923 145786797387139794264761885)
      ·
        refine ⟨54670049020177422849285707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145786797387139794264761885 54670049020177422849285707)
        ·
          refine ⟨82005073530266134273928561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54670049020177422849285707 82005073530266134273928561)
          ·
            refine ⟨61503805147699600705446421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82005073530266134273928561 61503805147699600705446421)
            ·
              refine ⟨2882990866298418783067801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 61503805147699600705446421 2882990866298418783067801)
              ·
                refine ⟨2162243149723814087300851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2882990866298418783067801 2162243149723814087300851)
                ·
                  refine ⟨3243364724585721130951277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2162243149723814087300851 3243364724585721130951277)
                  ·
                    refine ⟨1216261771719645424106729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3243364724585721130951277 1216261771719645424106729)
                    ·
                      rfl

theorem cell22_3552992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 6, 2, 1, 3].length) (baseStart_3552992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3552992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3552992 prefixEnd_3552992 := by exact prefixLift 3552992
  have htrace : WordTrace (prefixWord ++ tailWord_3552992) baseStart_3552992 baseEnd_3552992 := by
    simpa [prefixWord, tailWord_3552992, baseEnd_3552992] using wordTrace_append hprefix tailTrace_3552992
  have hstable : (prefixWord ++ tailWord_3552992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3552992).length < 2 ^ (prefixWord ++ tailWord_3552992).sum := by decide
  have hdescent : baseEnd_3552992 < baseStart_3552992 := by decide
  rcases family_descends (prefixWord ++ tailWord_3552992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3553018 : List Nat := [3, 1, 1, 1, 1, 3, 1, 6, 1, 4]
def baseStart_3553018 : Nat := 118140960795 + 3553018 * 2 ^ 59
def prefixEnd_3553018 : Nat := 4983230072969 + 3 ^ 40 * 3553018 * 2
def baseEnd_3553018 : Nat := 1216270672050990022956649

theorem tailTrace_3553018 : CollatzResearch.WordTrace tailWord_3553018 prefixEnd_3553018 1216270672050990022956649 := by
  unfold tailWord_3553018
  simp only [CollatzResearch.WordTrace]
  refine ⟨32397303160507517002280927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86392808428020045339415805 32397303160507517002280927)
  ·
    refine ⟨48595954740761275503421391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32397303160507517002280927 48595954740761275503421391)
    ·
      refine ⟨72893932111141913255132087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48595954740761275503421391 72893932111141913255132087)
      ·
        refine ⟨109340898166712869882698131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72893932111141913255132087 109340898166712869882698131)
        ·
          refine ⟨164011347250069304824047197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109340898166712869882698131 164011347250069304824047197)
          ·
            refine ⟨61504255218775989309017699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 164011347250069304824047197 61504255218775989309017699)
            ·
              refine ⟨92256382828163983963526549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61504255218775989309017699 92256382828163983963526549)
              ·
                refine ⟨4324517945070186748290307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 92256382828163983963526549 4324517945070186748290307)
                ·
                  refine ⟨6486776917605280122435461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4324517945070186748290307 6486776917605280122435461)
                  ·
                    refine ⟨1216270672050990022956649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6486776917605280122435461 1216270672050990022956649)
                    ·
                      rfl

theorem cell22_3553018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 6, 1, 4].length) (baseStart_3553018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3553018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3553018 prefixEnd_3553018 := by exact prefixLift 3553018
  have htrace : WordTrace (prefixWord ++ tailWord_3553018) baseStart_3553018 baseEnd_3553018 := by
    simpa [prefixWord, tailWord_3553018, baseEnd_3553018] using wordTrace_append hprefix tailTrace_3553018
  have hstable : (prefixWord ++ tailWord_3553018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3553018).length < 2 ^ (prefixWord ++ tailWord_3553018).sum := by decide
  have hdescent : baseEnd_3553018 < baseStart_3553018 := by decide
  rcases family_descends (prefixWord ++ tailWord_3553018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3553035 : List Nat := [1, 1, 1, 1, 5, 1, 6, 1, 1, 4]
def baseStart_3553035 : Nat := 118140960795 + 3553035 * 2 ^ 59
def prefixEnd_3553035 : Nat := 4983230072969 + 3 ^ 40 * 3553035 * 2
def baseEnd_3553035 : Nat := 1216276491498407645281597

theorem tailTrace_3553035 : CollatzResearch.WordTrace tailWord_3553035 prefixEnd_3553035 1216276491498407645281597 := by
  unfold tailWord_3553035
  simp only [CollatzResearch.WordTrace]
  refine ⟨129589832682968479912492559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86393221788645653274995039 129589832682968479912492559)
  ·
    refine ⟨194384749024452719868738839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129589832682968479912492559 194384749024452719868738839)
    ·
      refine ⟨291577123536679079803108259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194384749024452719868738839 291577123536679079803108259)
      ·
        refine ⟨437365685305018619704662389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291577123536679079803108259 437365685305018619704662389)
        ·
          refine ⟨41003032997345495597312099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 437365685305018619704662389 41003032997345495597312099)
          ·
            refine ⟨61504549496018243395968149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41003032997345495597312099 61504549496018243395968149)
            ·
              refine ⟨2883025757625855159186007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 61504549496018243395968149 2883025757625855159186007)
              ·
                refine ⟨4324538636438782738779011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2883025757625855159186007 4324538636438782738779011)
                ·
                  refine ⟨6486807954658174108168517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4324538636438782738779011 6486807954658174108168517)
                  ·
                    refine ⟨1216276491498407645281597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6486807954658174108168517 1216276491498407645281597)
                    ·
                      rfl

theorem cell22_3553035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 6, 1, 1, 4].length) (baseStart_3553035 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3553035 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3553035 prefixEnd_3553035 := by exact prefixLift 3553035
  have htrace : WordTrace (prefixWord ++ tailWord_3553035) baseStart_3553035 baseEnd_3553035 := by
    simpa [prefixWord, tailWord_3553035, baseEnd_3553035] using wordTrace_append hprefix tailTrace_3553035
  have hstable : (prefixWord ++ tailWord_3553035).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3553035).length < 2 ^ (prefixWord ++ tailWord_3553035).sum := by decide
  have hdescent : baseEnd_3553035 < baseStart_3553035 := by decide
  rcases family_descends (prefixWord ++ tailWord_3553035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3553050 : List Nat := [3, 1, 1, 3, 2, 2, 2, 4, 4]
def baseStart_3553050 : Nat := 118140960795 + 3553050 * 2 ^ 59
def prefixEnd_3553050 : Nat := 4983230072969 + 3 ^ 40 * 3553050 * 2
def baseEnd_3553050 : Nat := 405427208768317535385517

theorem tailTrace_3553050 : CollatzResearch.WordTrace tailWord_3553050 prefixEnd_3553050 405427208768317535385517 := by
  unfold tailWord_3553050
  simp only [CollatzResearch.WordTrace]
  refine ⟨32397594944478534368572151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86393586518609424982859069 32397594944478534368572151)
  ·
    refine ⟨48596392416717801552858227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32397594944478534368572151 48596392416717801552858227)
    ·
      refine ⟨72894588625076702329287341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48596392416717801552858227 72894588625076702329287341)
      ·
        refine ⟨27335470734403763373482753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72894588625076702329287341 27335470734403763373482753)
        ·
          refine ⟨20501603050802822530112065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27335470734403763373482753 20501603050802822530112065)
          ·
            refine ⟨15376202288102116897584049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20501603050802822530112065 15376202288102116897584049)
            ·
              refine ⟨11532151716076587673188037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15376202288102116897584049 11532151716076587673188037)
              ·
                refine ⟨2162278446764360188722757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11532151716076587673188037 2162278446764360188722757)
                ·
                  refine ⟨405427208768317535385517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2162278446764360188722757 405427208768317535385517)
                  ·
                    rfl

theorem cell22_3553050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 4, 4].length) (baseStart_3553050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3553050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3553050 prefixEnd_3553050 := by exact prefixLift 3553050
  have htrace : WordTrace (prefixWord ++ tailWord_3553050) baseStart_3553050 baseEnd_3553050 := by
    simpa [prefixWord, tailWord_3553050, baseEnd_3553050] using wordTrace_append hprefix tailTrace_3553050
  have hstable : (prefixWord ++ tailWord_3553050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3553050).length < 2 ^ (prefixWord ++ tailWord_3553050).sum := by decide
  have hdescent : baseEnd_3553050 < baseStart_3553050 := by decide
  rcases family_descends (prefixWord ++ tailWord_3553050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3553116 : List Nat := [2, 2, 4, 2, 2, 2, 2, 1, 2, 3]
def baseStart_3553116 : Nat := 118140960795 + 3553116 * 2 ^ 59
def prefixEnd_3553116 : Nat := 4983230072969 + 3 ^ 40 * 3553116 * 2
def baseEnd_3553116 : Nat := 1216304219453750434006349

theorem tailTrace_3553116 : CollatzResearch.WordTrace tailWord_3553116 prefixEnd_3553116 1216304219453750434006349 := by
  unfold tailWord_3553116
  simp only [CollatzResearch.WordTrace]
  refine ⟨64796393497837515373095601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86395191330450020497460801 64796393497837515373095601)
  ·
    refine ⟨48597295123378136529821701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64796393497837515373095601 48597295123378136529821701)
    ·
      refine ⟨9111992835633400599341569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48597295123378136529821701 9111992835633400599341569)
      ·
        refine ⟨6833994626725050449506177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9111992835633400599341569 6833994626725050449506177)
        ·
          refine ⟨5125495970043787837129633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6833994626725050449506177 5125495970043787837129633)
          ·
            refine ⟨3844121977532840877847225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5125495970043787837129633 3844121977532840877847225)
            ·
              refine ⟨2883091483149630658385419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3844121977532840877847225 2883091483149630658385419)
              ·
                refine ⟨4324637224724445987578129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2883091483149630658385419 4324637224724445987578129)
                ·
                  refine ⟨3243477918543334490683597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4324637224724445987578129 3243477918543334490683597)
                  ·
                    refine ⟨1216304219453750434006349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3243477918543334490683597 1216304219453750434006349)
                    ·
                      rfl

theorem cell22_3553116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 2, 1, 2, 3].length) (baseStart_3553116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3553116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3553116 prefixEnd_3553116 := by exact prefixLift 3553116
  have htrace : WordTrace (prefixWord ++ tailWord_3553116) baseStart_3553116 baseEnd_3553116 := by
    simpa [prefixWord, tailWord_3553116, baseEnd_3553116] using wordTrace_append hprefix tailTrace_3553116
  have hstable : (prefixWord ++ tailWord_3553116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3553116).length < 2 ^ (prefixWord ++ tailWord_3553116).sum := by decide
  have hdescent : baseEnd_3553116 < baseStart_3553116 := by decide
  rcases family_descends (prefixWord ++ tailWord_3553116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3553138 : List Nat := [3, 2, 1, 2, 1, 1, 1, 2, 4, 5]
def baseStart_3553138 : Nat := 118140960795 + 3553138 * 2 ^ 59
def prefixEnd_3553138 : Nat := 4983230072969 + 3 ^ 40 * 3553138 * 2
def baseEnd_3553138 : Nat := 1216311750503349709956281

theorem tailTrace_3553138 : CollatzResearch.WordTrace tailWord_3553138 prefixEnd_3553138 1216311750503349709956281 := by
  unfold tailWord_3553138
  simp only [CollatzResearch.WordTrace]
  refine ⟨32398397350398832125873017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86395726267730219002328045 32398397350398832125873017)
  ·
    refine ⟨24298798012799124094404763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32398397350398832125873017 24298798012799124094404763)
    ·
      refine ⟨36448197019198686141607145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24298798012799124094404763 36448197019198686141607145)
      ·
        refine ⟨27336147764399014606205359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36448197019198686141607145 27336147764399014606205359)
        ·
          refine ⟨41004221646598521909308039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27336147764399014606205359 41004221646598521909308039)
          ·
            refine ⟨61506332469897782863962059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41004221646598521909308039 61506332469897782863962059)
            ·
              refine ⟨92259498704846674295943089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61506332469897782863962059 92259498704846674295943089)
              ·
                refine ⟨69194624028635005721957317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92259498704846674295943089 69194624028635005721957317)
                ·
                  refine ⟨12973992005369063572866997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69194624028635005721957317 12973992005369063572866997)
                  ·
                    refine ⟨1216311750503349709956281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12973992005369063572866997 1216311750503349709956281)
                    ·
                      rfl

theorem cell22_3553138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 4, 5].length) (baseStart_3553138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3553138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3553138 prefixEnd_3553138 := by exact prefixLift 3553138
  have htrace : WordTrace (prefixWord ++ tailWord_3553138) baseStart_3553138 baseEnd_3553138 := by
    simpa [prefixWord, tailWord_3553138, baseEnd_3553138] using wordTrace_append hprefix tailTrace_3553138
  have hstable : (prefixWord ++ tailWord_3553138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3553138).length < 2 ^ (prefixWord ++ tailWord_3553138).sum := by decide
  have hdescent : baseEnd_3553138 < baseStart_3553138 := by decide
  rcases family_descends (prefixWord ++ tailWord_3553138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3553234 : List Nat := [3, 2, 2, 3, 2, 2, 1, 1, 1, 5]
def baseStart_3553234 : Nat := 118140960795 + 3553234 * 2 ^ 59
def prefixEnd_3553234 : Nat := 4983230072969 + 3 ^ 40 * 3553234 * 2
def baseEnd_3553234 : Nat := 1216344613265237459555987

theorem tailTrace_3553234 : CollatzResearch.WordTrace tailWord_3553234 prefixEnd_3553234 1216344613265237459555987 := by
  unfold tailWord_3553234
  simp only [CollatzResearch.WordTrace]
  refine ⟨32399272702311884224746689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86398060539498357932657837 32399272702311884224746689)
  ·
    refine ⟨24299454526733913168560017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32399272702311884224746689 24299454526733913168560017)
    ·
      refine ⟨18224590895050434876420013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24299454526733913168560017 18224590895050434876420013)
      ·
        refine ⟨6834221585643913078657505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18224590895050434876420013 6834221585643913078657505)
        ·
          refine ⟨5125666189232934808993129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6834221585643913078657505 5125666189232934808993129)
          ·
            refine ⟨3844249641924701106744847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5125666189232934808993129 3844249641924701106744847)
            ·
              refine ⟨5766374462887051660117271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3844249641924701106744847 5766374462887051660117271)
              ·
                refine ⟨8649561694330577490175907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5766374462887051660117271 8649561694330577490175907)
                ·
                  refine ⟨12974342541495866235263861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8649561694330577490175907 12974342541495866235263861)
                  ·
                    refine ⟨1216344613265237459555987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12974342541495866235263861 1216344613265237459555987)
                    ·
                      rfl

theorem cell22_3553234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 1, 1, 1, 5].length) (baseStart_3553234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3553234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3553234 prefixEnd_3553234 := by exact prefixLift 3553234
  have htrace : WordTrace (prefixWord ++ tailWord_3553234) baseStart_3553234 baseEnd_3553234 := by
    simpa [prefixWord, tailWord_3553234, baseEnd_3553234] using wordTrace_append hprefix tailTrace_3553234
  have hstable : (prefixWord ++ tailWord_3553234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3553234).length < 2 ^ (prefixWord ++ tailWord_3553234).sum := by decide
  have hdescent : baseEnd_3553234 < baseStart_3553234 := by decide
  rcases family_descends (prefixWord ++ tailWord_3553234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3553247 : List Nat := [1, 1, 2, 3, 4, 3, 2, 6]
def baseStart_3553247 : Nat := 118140960795 + 3553247 * 2 ^ 59
def prefixEnd_3553247 : Nat := 4983230072969 + 3 ^ 40 * 3553247 * 2
def baseEnd_3553247 : Nat := 135149895936767750997883

theorem tailTrace_3553247 : CollatzResearch.WordTrace tailWord_3553247 prefixEnd_3553247 135149895936767750997883 := by
  unfold tailWord_3553247
  simp only [CollatzResearch.WordTrace]
  refine ⟨129597564958200440119209995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86398376638800293412806663 129597564958200440119209995)
  ·
    refine ⟨194396347437300660178814993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129597564958200440119209995 194396347437300660178814993)
    ·
      refine ⟨145797260577975495134111245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194396347437300660178814993 145797260577975495134111245)
      ·
        refine ⟨54673972716740810675291717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145797260577975495134111245 54673972716740810675291717)
        ·
          refine ⟨10251369884388902001617197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54673972716740810675291717 10251369884388902001617197)
          ·
            refine ⟨3844263706645838250606449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10251369884388902001617197 3844263706645838250606449)
            ·
              refine ⟨2883197779984378687954837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3844263706645838250606449 2883197779984378687954837)
              ·
                refine ⟨135149895936767750997883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2883197779984378687954837 135149895936767750997883)
                ·
                  rfl

theorem cell22_3553247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 2, 6].length) (baseStart_3553247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3553247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3553247 prefixEnd_3553247 := by exact prefixLift 3553247
  have htrace : WordTrace (prefixWord ++ tailWord_3553247) baseStart_3553247 baseEnd_3553247 := by
    simpa [prefixWord, tailWord_3553247, baseEnd_3553247] using wordTrace_append hprefix tailTrace_3553247
  have hstable : (prefixWord ++ tailWord_3553247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3553247).length < 2 ^ (prefixWord ++ tailWord_3553247).sum := by decide
  have hdescent : baseEnd_3553247 < baseStart_3553247 := by decide
  rcases family_descends (prefixWord ++ tailWord_3553247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3553367 : List Nat := [1, 1, 3, 2, 2, 1, 5, 1, 2, 4]
def baseStart_3553367 : Nat := 118140960795 + 3553367 * 2 ^ 59
def prefixEnd_3553367 : Nat := 4983230072969 + 3 ^ 40 * 3553367 * 2
def baseEnd_3553367 : Nat := 1216390141883269445980579

theorem tailTrace_3553367 : CollatzResearch.WordTrace tailWord_3553367 prefixEnd_3553367 1216390141883269445980579 := by
  unfold tailWord_3553367
  simp only [CollatzResearch.WordTrace]
  refine ⟨129601941717765700613578355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86401294478510467075718903 129601941717765700613578355)
  ·
    refine ⟨194402912576648550920367533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129601941717765700613578355 194402912576648550920367533)
    ·
      refine ⟨72901092216243206595137825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 194402912576648550920367533 72901092216243206595137825)
      ·
        refine ⟨54675819162182404946353369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72901092216243206595137825 54675819162182404946353369)
        ·
          refine ⟨41006864371636803709765027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54675819162182404946353369 41006864371636803709765027)
          ·
            refine ⟨61510296557455205564647541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41006864371636803709765027 61510296557455205564647541)
            ·
              refine ⟨5766590302261425521685707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61510296557455205564647541 5766590302261425521685707)
              ·
                refine ⟨8649885453392138282528561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5766590302261425521685707 8649885453392138282528561)
                ·
                  refine ⟨6487414090044103711896421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8649885453392138282528561 6487414090044103711896421)
                  ·
                    refine ⟨1216390141883269445980579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6487414090044103711896421 1216390141883269445980579)
                    ·
                      rfl

theorem cell22_3553367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 5, 1, 2, 4].length) (baseStart_3553367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3553367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3553367 prefixEnd_3553367 := by exact prefixLift 3553367
  have htrace : WordTrace (prefixWord ++ tailWord_3553367) baseStart_3553367 baseEnd_3553367 := by
    simpa [prefixWord, tailWord_3553367, baseEnd_3553367] using wordTrace_append hprefix tailTrace_3553367
  have hstable : (prefixWord ++ tailWord_3553367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3553367).length < 2 ^ (prefixWord ++ tailWord_3553367).sum := by decide
  have hdescent : baseEnd_3553367 < baseStart_3553367 := by decide
  rcases family_descends (prefixWord ++ tailWord_3553367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3553373 : List Nat := [1, 4, 4, 1, 1, 3, 2, 1, 1, 4]
def baseStart_3553373 : Nat := 118140960795 + 3553373 * 2 ^ 59
def prefixEnd_3553373 : Nat := 4983230072969 + 3 ^ 40 * 3553373 * 2
def baseEnd_3553373 : Nat := 1216392195805887430330561

theorem tailTrace_3553373 : CollatzResearch.WordTrace tailWord_3553373 prefixEnd_3553373 1216392195805887430330561 := by
  unfold tailWord_3553373
  simp only [CollatzResearch.WordTrace]
  refine ⟨129602160555743963638296773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86401440370495975758864515 129602160555743963638296773)
  ·
    refine ⟨24300405104201993182180645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129602160555743963638296773 24300405104201993182180645)
    ·
      refine ⟨4556325957037873721658871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24300405104201993182180645 4556325957037873721658871)
      ·
        refine ⟨6834488935556810582488307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4556325957037873721658871 6834488935556810582488307)
        ·
          refine ⟨10251733403335215873732461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6834488935556810582488307 10251733403335215873732461)
          ·
            refine ⟨3844400026250705952649673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10251733403335215873732461 3844400026250705952649673)
            ·
              refine ⟨2883300019688029464487255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3844400026250705952649673 2883300019688029464487255)
              ·
                refine ⟨4324950029532044196730883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2883300019688029464487255 4324950029532044196730883)
                ·
                  refine ⟨6487425044298066295096325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4324950029532044196730883 6487425044298066295096325)
                  ·
                    refine ⟨1216392195805887430330561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6487425044298066295096325 1216392195805887430330561)
                    ·
                      rfl

theorem cell22_3553373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_3553373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3553373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3553373 prefixEnd_3553373 := by exact prefixLift 3553373
  have htrace : WordTrace (prefixWord ++ tailWord_3553373) baseStart_3553373 baseEnd_3553373 := by
    simpa [prefixWord, tailWord_3553373, baseEnd_3553373] using wordTrace_append hprefix tailTrace_3553373
  have hstable : (prefixWord ++ tailWord_3553373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3553373).length < 2 ^ (prefixWord ++ tailWord_3553373).sum := by decide
  have hdescent : baseEnd_3553373 < baseStart_3553373 := by decide
  rcases family_descends (prefixWord ++ tailWord_3553373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3553461 : List Nat := [1, 3, 3, 4, 1, 1, 1, 3, 5]
def baseStart_3553461 : Nat := 118140960795 + 3553461 * 2 ^ 59
def prefixEnd_3553461 : Nat := 4983230072969 + 3 ^ 40 * 3553461 * 2
def baseEnd_3553461 : Nat := 405474106668094844710097

theorem tailTrace_3553461 : CollatzResearch.WordTrace tailWord_3553461 prefixEnd_3553461 405474106668094844710097 := by
  unfold tailWord_3553461
  simp only [CollatzResearch.WordTrace]
  refine ⟨129605370179425154667500237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86403580119616769778333491 129605370179425154667500237)
  ·
    refine ⟨48602013817284433000312589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129605370179425154667500237 48602013817284433000312589)
    ·
      refine ⟨18225755181481662375117221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48602013817284433000312589 18225755181481662375117221)
      ·
        refine ⟨3417329096527811695334479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18225755181481662375117221 3417329096527811695334479)
        ·
          refine ⟨5125993644791717543001719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3417329096527811695334479 5125993644791717543001719)
          ·
            refine ⟨7688990467187576314502579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5125993644791717543001719 7688990467187576314502579)
            ·
              refine ⟨11533485700781364471753869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7688990467187576314502579 11533485700781364471753869)
              ·
                refine ⟨4325057137793011676907701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11533485700781364471753869 4325057137793011676907701)
                ·
                  refine ⟨405474106668094844710097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4325057137793011676907701 405474106668094844710097)
                  ·
                    rfl

theorem cell22_3553461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 3, 5].length) (baseStart_3553461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3553461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3553461 prefixEnd_3553461 := by exact prefixLift 3553461
  have htrace : WordTrace (prefixWord ++ tailWord_3553461) baseStart_3553461 baseEnd_3553461 := by
    simpa [prefixWord, tailWord_3553461, baseEnd_3553461] using wordTrace_append hprefix tailTrace_3553461
  have hstable : (prefixWord ++ tailWord_3553461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3553461).length < 2 ^ (prefixWord ++ tailWord_3553461).sum := by decide
  have hdescent : baseEnd_3553461 < baseStart_3553461 := by decide
  rcases family_descends (prefixWord ++ tailWord_3553461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3553487 : List Nat := [1, 1, 2, 1, 1, 3, 5, 2, 1, 5]
def baseStart_3553487 : Nat := 118140960795 + 3553487 * 2 ^ 59
def prefixEnd_3553487 : Nat := 4983230072969 + 3 ^ 40 * 3553487 * 2
def baseEnd_3553487 : Nat := 1216431220335629132980211

theorem tailTrace_3553487 : CollatzResearch.WordTrace tailWord_3553487 prefixEnd_3553487 1216431220335629132980211 := by
  unfold tailWord_3553487
  simp only [CollatzResearch.WordTrace]
  refine ⟨129606318477330961107946715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86404212318220640738631143 129606318477330961107946715)
  ·
    refine ⟨194409477715996441661920073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129606318477330961107946715 194409477715996441661920073)
    ·
      refine ⟨145807108286997331246440055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194409477715996441661920073 145807108286997331246440055)
      ·
        refine ⟨218710662430495996869660083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145807108286997331246440055 218710662430495996869660083)
        ·
          refine ⟨328065993645743995304490125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218710662430495996869660083 328065993645743995304490125)
          ·
            refine ⟨123024747617153998239183797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 328065993645743995304490125 123024747617153998239183797)
            ·
              refine ⟨11533570089108187334923481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 123024747617153998239183797 11533570089108187334923481)
              ·
                refine ⟨8650177566831140501192611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11533570089108187334923481 8650177566831140501192611)
                ·
                  refine ⟨12975266350246710751788917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8650177566831140501192611 12975266350246710751788917)
                  ·
                    refine ⟨1216431220335629132980211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12975266350246710751788917 1216431220335629132980211)
                    ·
                      rfl

theorem cell22_3553487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 2, 1, 5].length) (baseStart_3553487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3553487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3553487 prefixEnd_3553487 := by exact prefixLift 3553487
  have htrace : WordTrace (prefixWord ++ tailWord_3553487) baseStart_3553487 baseEnd_3553487 := by
    simpa [prefixWord, tailWord_3553487, baseEnd_3553487] using wordTrace_append hprefix tailTrace_3553487
  have hstable : (prefixWord ++ tailWord_3553487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3553487).length < 2 ^ (prefixWord ++ tailWord_3553487).sum := by decide
  have hdescent : baseEnd_3553487 < baseStart_3553487 := by decide
  rcases family_descends (prefixWord ++ tailWord_3553487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3553673 : List Nat := [1, 2, 1, 1, 6, 2, 2, 2, 2, 3]
def baseStart_3553673 : Nat := 118140960795 + 3553673 * 2 ^ 59
def prefixEnd_3553673 : Nat := 4983230072969 + 3 ^ 40 * 3553673 * 2
def baseEnd_3553673 : Nat := 1216494891936786647829641

theorem tailTrace_3553673 : CollatzResearch.WordTrace tailWord_3553673 prefixEnd_3553673 1216494891936786647829641 := by
  unfold tailWord_3553673
  simp only [CollatzResearch.WordTrace]
  refine ⟨129613102454657114874217673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86408734969771409916145115 129613102454657114874217673)
  ·
    refine ⟨97209826840992836155663255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129613102454657114874217673 97209826840992836155663255)
    ·
      refine ⟨145814740261489254233494883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97209826840992836155663255 145814740261489254233494883)
      ·
        refine ⟨218722110392233881350242325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145814740261489254233494883 218722110392233881350242325)
        ·
          refine ⟨10252598924635963188292609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 218722110392233881350242325 10252598924635963188292609)
          ·
            refine ⟨7689449193476972391219457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10252598924635963188292609 7689449193476972391219457)
            ·
              refine ⟨5767086895107729293414593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7689449193476972391219457 5767086895107729293414593)
              ·
                refine ⟨4325315171330796970060945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5767086895107729293414593 4325315171330796970060945)
                ·
                  refine ⟨3243986378498097727545709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4325315171330796970060945 3243986378498097727545709)
                  ·
                    refine ⟨1216494891936786647829641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3243986378498097727545709 1216494891936786647829641)
                    ·
                      rfl

theorem cell22_3553673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 2, 2, 2, 3].length) (baseStart_3553673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3553673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3553673 prefixEnd_3553673 := by exact prefixLift 3553673
  have htrace : WordTrace (prefixWord ++ tailWord_3553673) baseStart_3553673 baseEnd_3553673 := by
    simpa [prefixWord, tailWord_3553673, baseEnd_3553673] using wordTrace_append hprefix tailTrace_3553673
  have hstable : (prefixWord ++ tailWord_3553673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3553673).length < 2 ^ (prefixWord ++ tailWord_3553673).sum := by decide
  have hdescent : baseEnd_3553673 < baseStart_3553673 := by decide
  rcases family_descends (prefixWord ++ tailWord_3553673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3553701 : List Nat := [1, 3, 1, 2, 1, 1, 5, 2, 3, 3]
def baseStart_3553701 : Nat := 118140960795 + 3553701 * 2 ^ 59
def prefixEnd_3553701 : Nat := 4983230072969 + 3 ^ 40 * 3553701 * 2
def baseEnd_3553701 : Nat := 1216504476909003908129555

theorem tailTrace_3553701 : CollatzResearch.WordTrace tailWord_3553701 prefixEnd_3553701 1216504476909003908129555 := by
  unfold tailWord_3553701
  simp only [CollatzResearch.WordTrace]
  refine ⟨129614123698555675656236957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86409415799037117104157971 129614123698555675656236957)
  ·
    refine ⟨48605296386958378371088859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129614123698555675656236957 48605296386958378371088859)
    ·
      refine ⟨72907944580437567556633289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48605296386958378371088859 72907944580437567556633289)
      ·
        refine ⟨54680958435328175667474967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72907944580437567556633289 54680958435328175667474967)
        ·
          refine ⟨82021437652992263501212451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54680958435328175667474967 82021437652992263501212451)
          ·
            refine ⟨123032156479488395251818677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82021437652992263501212451 123032156479488395251818677)
            ·
              refine ⟨11534264669952037054858001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 123032156479488395251818677 11534264669952037054858001)
              ·
                refine ⟨8650698502464027791143501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11534264669952037054858001 8650698502464027791143501)
                ·
                  refine ⟨3244011938424010421678813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8650698502464027791143501 3244011938424010421678813)
                  ·
                    refine ⟨1216504476909003908129555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3244011938424010421678813 1216504476909003908129555)
                    ·
                      rfl

theorem cell22_3553701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 2, 3, 3].length) (baseStart_3553701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3553701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3553701 prefixEnd_3553701 := by exact prefixLift 3553701
  have htrace : WordTrace (prefixWord ++ tailWord_3553701) baseStart_3553701 baseEnd_3553701 := by
    simpa [prefixWord, tailWord_3553701, baseEnd_3553701] using wordTrace_append hprefix tailTrace_3553701
  have hstable : (prefixWord ++ tailWord_3553701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3553701).length < 2 ^ (prefixWord ++ tailWord_3553701).sum := by decide
  have hdescent : baseEnd_3553701 < baseStart_3553701 := by decide
  rcases family_descends (prefixWord ++ tailWord_3553701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3553714 : List Nat := [3, 2, 1, 1, 1, 1, 4, 2, 7]
def baseStart_3553714 : Nat := 118140960795 + 3553714 * 2 ^ 59
def prefixEnd_3553714 : Nat := 4983230072969 + 3 ^ 40 * 3553714 * 2
def baseEnd_3553714 : Nat := 405502975691558735851505

theorem tailTrace_3553714 : CollatzResearch.WordTrace tailWord_3553714 prefixEnd_3553714 405502975691558735851505 := by
  unfold tailWord_3553714
  simp only [CollatzResearch.WordTrace]
  refine ⟨32403649461877144719115049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86409731898339052584306797 32403649461877144719115049)
  ·
    refine ⟨24302737096407858539336287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32403649461877144719115049 24302737096407858539336287)
    ·
      refine ⟨36454105644611787809004431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24302737096407858539336287 36454105644611787809004431)
      ·
        refine ⟨54681158466917681713506647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36454105644611787809004431 54681158466917681713506647)
        ·
          refine ⟨82021737700376522570259971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54681158466917681713506647 82021737700376522570259971)
          ·
            refine ⟨123032606550564783855389957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82021737700376522570259971 123032606550564783855389957)
            ·
              refine ⟨23068613728230896972885617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 123032606550564783855389957 23068613728230896972885617)
              ·
                refine ⟨17301460296173172729664213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23068613728230896972885617 17301460296173172729664213)
                ·
                  refine ⟨405502975691558735851505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17301460296173172729664213 405502975691558735851505)
                  ·
                    rfl

theorem cell22_3553714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 2, 7].length) (baseStart_3553714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3553714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3553714 prefixEnd_3553714 := by exact prefixLift 3553714
  have htrace : WordTrace (prefixWord ++ tailWord_3553714) baseStart_3553714 baseEnd_3553714 := by
    simpa [prefixWord, tailWord_3553714, baseEnd_3553714] using wordTrace_append hprefix tailTrace_3553714
  have hstable : (prefixWord ++ tailWord_3553714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3553714).length < 2 ^ (prefixWord ++ tailWord_3553714).sum := by decide
  have hdescent : baseEnd_3553714 < baseStart_3553714 := by decide
  rcases family_descends (prefixWord ++ tailWord_3553714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3553791 : List Nat := [1, 1, 2, 2, 1, 2, 3, 3, 4, 3]
def baseStart_3553791 : Nat := 118140960795 + 3553791 * 2 ^ 59
def prefixEnd_3553791 : Nat := 4983230072969 + 3 ^ 40 * 3553791 * 2
def baseEnd_3553791 : Nat := 1216535285748273673379279

theorem tailTrace_3553791 : CollatzResearch.WordTrace tailWord_3553791 prefixEnd_3553791 1216535285748273673379279 := by
  unfold tailWord_3553791
  simp only [CollatzResearch.WordTrace]
  refine ⟨129617406268229621027013227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86411604178819747351342151 129617406268229621027013227)
  ·
    refine ⟨194426109402344431540519841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129617406268229621027013227 194426109402344431540519841)
    ·
      refine ⟨145819582051758323655389881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194426109402344431540519841 145819582051758323655389881)
      ·
        refine ⟨109364686538818742741542411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145819582051758323655389881 109364686538818742741542411)
        ·
          refine ⟨164047029808228114112313617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109364686538818742741542411 164047029808228114112313617)
          ·
            refine ⟨123035272356171085584235213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164047029808228114112313617 123035272356171085584235213)
            ·
              refine ⟨46138227133564157094088205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123035272356171085584235213 46138227133564157094088205)
              ·
                refine ⟨17301835175086558910283077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46138227133564157094088205 17301835175086558910283077)
                ·
                  refine ⟨3244094095328729795678077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17301835175086558910283077 3244094095328729795678077)
                  ·
                    refine ⟨1216535285748273673379279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3244094095328729795678077 1216535285748273673379279)
                    ·
                      rfl

theorem cell22_3553791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 3, 4, 3].length) (baseStart_3553791 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3553791 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3553791 prefixEnd_3553791 := by exact prefixLift 3553791
  have htrace : WordTrace (prefixWord ++ tailWord_3553791) baseStart_3553791 baseEnd_3553791 := by
    simpa [prefixWord, tailWord_3553791, baseEnd_3553791] using wordTrace_append hprefix tailTrace_3553791
  have hstable : (prefixWord ++ tailWord_3553791).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3553791).length < 2 ^ (prefixWord ++ tailWord_3553791).sum := by decide
  have hdescent : baseEnd_3553791 < baseStart_3553791 := by decide
  rcases family_descends (prefixWord ++ tailWord_3553791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3553793 : List Nat := [1, 2, 4, 1, 3, 3, 1, 1, 6]
def baseStart_3553793 : Nat := 118140960795 + 3553793 * 2 ^ 59
def prefixEnd_3553793 : Nat := 4983230072969 + 3 ^ 40 * 3553793 * 2
def baseEnd_3553793 : Nat := 405511990129715444943091

theorem tailTrace_3553793 : CollatzResearch.WordTrace tailWord_3553793 prefixEnd_3553793 405511990129715444943091 := by
  unfold tailWord_3553793
  simp only [CollatzResearch.WordTrace]
  refine ⟨129617479214222375368586033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86411652809481583579057355 129617479214222375368586033)
  ·
    refine ⟨97213109410666781526439525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129617479214222375368586033 97213109410666781526439525)
    ·
      refine ⟨18227458014500021536207411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97213109410666781526439525 18227458014500021536207411)
      ·
        refine ⟨27341187021750032304311117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18227458014500021536207411 27341187021750032304311117)
        ·
          refine ⟨10252945133156262114116669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27341187021750032304311117 10252945133156262114116669)
          ·
            refine ⟨3844854424933598292793751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10252945133156262114116669 3844854424933598292793751)
            ·
              refine ⟨5767281637400397439190627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3844854424933598292793751 5767281637400397439190627)
              ·
                refine ⟨8650922456100596158785941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5767281637400397439190627 8650922456100596158785941)
                ·
                  refine ⟨405511990129715444943091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8650922456100596158785941 405511990129715444943091)
                  ·
                    rfl

theorem cell22_3553793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 1, 1, 6].length) (baseStart_3553793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3553793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3553793 prefixEnd_3553793 := by exact prefixLift 3553793
  have htrace : WordTrace (prefixWord ++ tailWord_3553793) baseStart_3553793 baseEnd_3553793 := by
    simpa [prefixWord, tailWord_3553793, baseEnd_3553793] using wordTrace_append hprefix tailTrace_3553793
  have hstable : (prefixWord ++ tailWord_3553793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3553793).length < 2 ^ (prefixWord ++ tailWord_3553793).sum := by decide
  have hdescent : baseEnd_3553793 < baseStart_3553793 := by decide
  rcases family_descends (prefixWord ++ tailWord_3553793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3553812 : List Nat := [2, 4, 3, 1, 1, 3, 1, 2, 1, 4]
def baseStart_3553812 : Nat := 118140960795 + 3553812 * 2 ^ 59
def prefixEnd_3553812 : Nat := 4983230072969 + 3 ^ 40 * 3553812 * 2
def baseEnd_3553812 : Nat := 1216542474477436618604215

theorem tailTrace_3553812 : CollatzResearch.WordTrace tailWord_3553812 prefixEnd_3553812 1216542474477436618604215 := by
  unfold tailWord_3553812
  simp only [CollatzResearch.WordTrace]
  refine ⟨64809086100576770806763845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86412114800769027742351793 64809086100576770806763845)
  ·
    refine ⟨12151703643858144526268221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64809086100576770806763845 12151703643858144526268221)
    ·
      refine ⟨4556888866446804197350583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12151703643858144526268221 4556888866446804197350583)
      ·
        refine ⟨6835333299670206296025875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4556888866446804197350583 6835333299670206296025875)
        ·
          refine ⟨10252999949505309444038813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6835333299670206296025875 10252999949505309444038813)
          ·
            refine ⟨3844874981064491041514555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10252999949505309444038813 3844874981064491041514555)
            ·
              refine ⟨5767312471596736562271833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3844874981064491041514555 5767312471596736562271833)
              ·
                refine ⟨4325484353697552421703875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5767312471596736562271833 4325484353697552421703875)
                ·
                  refine ⟨6488226530546328632555813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4325484353697552421703875 6488226530546328632555813)
                  ·
                    refine ⟨1216542474477436618604215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6488226530546328632555813 1216542474477436618604215)
                    ·
                      rfl

theorem cell22_3553812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_3553812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3553812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3553812 prefixEnd_3553812 := by exact prefixLift 3553812
  have htrace : WordTrace (prefixWord ++ tailWord_3553812) baseStart_3553812 baseEnd_3553812 := by
    simpa [prefixWord, tailWord_3553812, baseEnd_3553812] using wordTrace_append hprefix tailTrace_3553812
  have hstable : (prefixWord ++ tailWord_3553812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3553812).length < 2 ^ (prefixWord ++ tailWord_3553812).sum := by decide
  have hdescent : baseEnd_3553812 < baseStart_3553812 := by decide
  rcases family_descends (prefixWord ++ tailWord_3553812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3553821 : List Nat := [1, 4, 2, 2, 1, 2, 2, 8]
def baseStart_3553821 : Nat := 118140960795 + 3553821 * 2 ^ 59
def prefixEnd_3553821 : Nat := 4983230072969 + 3 ^ 40 * 3553821 * 2
def baseEnd_3553821 : Nat := 135171728373484843903243

theorem tailTrace_3553821 : CollatzResearch.WordTrace tailWord_3553821 prefixEnd_3553821 135171728373484843903243 := by
  unfold tailWord_3553821
  simp only [CollatzResearch.WordTrace]
  refine ⟨129618500458120936150605317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86412333638747290767070211 129618500458120936150605317)
  ·
    refine ⟨24303468835897675528238497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129618500458120936150605317 24303468835897675528238497)
    ·
      refine ⟨18227601626923256646178873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24303468835897675528238497 18227601626923256646178873)
      ·
        refine ⟨13670701220192442484634155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18227601626923256646178873 13670701220192442484634155)
        ·
          refine ⟨20506051830288663726951233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13670701220192442484634155 20506051830288663726951233)
          ·
            refine ⟨15379538872716497795213425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20506051830288663726951233 15379538872716497795213425)
            ·
              refine ⟨11534654154537373346410069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15379538872716497795213425 11534654154537373346410069)
              ·
                refine ⟨135171728373484843903243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11534654154537373346410069 135171728373484843903243)
                ·
                  rfl

theorem cell22_3553821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 8].length) (baseStart_3553821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3553821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3553821 prefixEnd_3553821 := by exact prefixLift 3553821
  have htrace : WordTrace (prefixWord ++ tailWord_3553821) baseStart_3553821 baseEnd_3553821 := by
    simpa [prefixWord, tailWord_3553821, baseEnd_3553821] using wordTrace_append hprefix tailTrace_3553821
  have hstable : (prefixWord ++ tailWord_3553821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3553821).length < 2 ^ (prefixWord ++ tailWord_3553821).sum := by decide
  have hdescent : baseEnd_3553821 < baseStart_3553821 := by decide
  rcases family_descends (prefixWord ++ tailWord_3553821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3553838 : List Nat := [4, 1, 3, 1, 4, 9]
def baseStart_3553838 : Nat := 118140960795 + 3553838 * 2 ^ 59
def prefixEnd_3553838 : Nat := 4983230072969 + 3 ^ 40 * 3553838 * 2
def baseEnd_3553838 : Nat := 15019152775417052067335

theorem tailTrace_3553838 : CollatzResearch.WordTrace tailWord_3553838 prefixEnd_3553838 15019152775417052067335 := by
  unfold tailWord_3553838
  simp only [CollatzResearch.WordTrace]
  refine ⟨16202390062382418506746771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86412746999372898702649445 16202390062382418506746771)
  ·
    refine ⟨24303585093573627760120157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16202390062382418506746771 24303585093573627760120157)
    ·
      refine ⟨9113844410090110410045059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24303585093573627760120157 9113844410090110410045059)
      ·
        refine ⟨13670766615135165615067589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9113844410090110410045059 13670766615135165615067589)
        ·
          refine ⟨2563268740337843552825173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13670766615135165615067589 2563268740337843552825173)
          ·
            refine ⟨15019152775417052067335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2563268740337843552825173 15019152775417052067335)
            ·
              rfl

theorem cell22_3553838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 9].length) (baseStart_3553838 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3553838 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3553838 prefixEnd_3553838 := by exact prefixLift 3553838
  have htrace : WordTrace (prefixWord ++ tailWord_3553838) baseStart_3553838 baseEnd_3553838 := by
    simpa [prefixWord, tailWord_3553838, baseEnd_3553838] using wordTrace_append hprefix tailTrace_3553838
  have hstable : (prefixWord ++ tailWord_3553838).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3553838).length < 2 ^ (prefixWord ++ tailWord_3553838).sum := by decide
  have hdescent : baseEnd_3553838 < baseStart_3553838 := by decide
  rcases family_descends (prefixWord ++ tailWord_3553838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3553911 : List Nat := [1, 1, 3, 1, 1, 3, 3, 3, 6]
def baseStart_3553911 : Nat := 118140960795 + 3553911 * 2 ^ 59
def prefixEnd_3553911 : Nat := 4983230072969 + 3 ^ 40 * 3553911 * 2
def baseEnd_3553911 : Nat := 405525454733544453459637

theorem tailTrace_3553911 : CollatzResearch.WordTrace tailWord_3553911 prefixEnd_3553911 405525454733544453459637 := by
  unfold tailWord_3553911
  simp only [CollatzResearch.WordTrace]
  refine ⟨129621783027794881521381587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86414522018529921014254391 129621783027794881521381587)
  ·
    refine ⟨194432674541692322282072381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129621783027794881521381587 194432674541692322282072381)
    ·
      refine ⟨72912252953134620855777143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 194432674541692322282072381 72912252953134620855777143)
      ·
        refine ⟨109368379429701931283665715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72912252953134620855777143 109368379429701931283665715)
        ·
          refine ⟨164052569144552896925498573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109368379429701931283665715 164052569144552896925498573)
          ·
            refine ⟨61519713429207336347061965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 164052569144552896925498573 61519713429207336347061965)
            ·
              refine ⟨23069892535952751130148237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61519713429207336347061965 23069892535952751130148237)
              ·
                refine ⟨8651209700982281673805589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23069892535952751130148237 8651209700982281673805589)
                ·
                  refine ⟨405525454733544453459637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8651209700982281673805589 405525454733544453459637)
                  ·
                    rfl

theorem cell22_3553911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 3, 6].length) (baseStart_3553911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3553911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3553911 prefixEnd_3553911 := by exact prefixLift 3553911
  have htrace : WordTrace (prefixWord ++ tailWord_3553911) baseStart_3553911 baseEnd_3553911 := by
    simpa [prefixWord, tailWord_3553911, baseEnd_3553911] using wordTrace_append hprefix tailTrace_3553911
  have hstable : (prefixWord ++ tailWord_3553911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3553911).length < 2 ^ (prefixWord ++ tailWord_3553911).sum := by decide
  have hdescent : baseEnd_3553911 < baseStart_3553911 := by decide
  rcases family_descends (prefixWord ++ tailWord_3553911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3553943 : List Nat := [1, 1, 3, 3, 2, 1, 1, 1, 6, 3]
def baseStart_3553943 : Nat := 118140960795 + 3553943 * 2 ^ 59
def prefixEnd_3553943 : Nat := 4983230072969 + 3 ^ 40 * 3553943 * 2
def baseEnd_3553943 : Nat := 1216587318454595943578813

theorem tailTrace_3553943 : CollatzResearch.WordTrace tailWord_3553943 prefixEnd_3553943 1216587318454595943578813 := by
  unfold tailWord_3553943
  simp only [CollatzResearch.WordTrace]
  refine ⟨129622950163678950986546483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86415300109119300657697655 129622950163678950986546483)
  ·
    refine ⟨194434425245518426479819725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129622950163678950986546483 194434425245518426479819725)
    ·
      refine ⟨72912909467069409929932397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 194434425245518426479819725 72912909467069409929932397)
      ·
        refine ⟨27342341050151028723724649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72912909467069409929932397 27342341050151028723724649)
        ·
          refine ⟨20506755787613271542793487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27342341050151028723724649 20506755787613271542793487)
          ·
            refine ⟨30760133681419907314190231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20506755787613271542793487 30760133681419907314190231)
            ·
              refine ⟨46140200522129860971285347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30760133681419907314190231 46140200522129860971285347)
              ·
                refine ⟨69210300783194791456928021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46140200522129860971285347 69210300783194791456928021)
                ·
                  refine ⟨3244232849212255849543501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 69210300783194791456928021 3244232849212255849543501)
                  ·
                    refine ⟨1216587318454595943578813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3244232849212255849543501 1216587318454595943578813)
                    ·
                      rfl

theorem cell22_3553943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 6, 3].length) (baseStart_3553943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3553943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3553943 prefixEnd_3553943 := by exact prefixLift 3553943
  have htrace : WordTrace (prefixWord ++ tailWord_3553943) baseStart_3553943 baseEnd_3553943 := by
    simpa [prefixWord, tailWord_3553943, baseEnd_3553943] using wordTrace_append hprefix tailTrace_3553943
  have hstable : (prefixWord ++ tailWord_3553943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3553943).length < 2 ^ (prefixWord ++ tailWord_3553943).sum := by decide
  have hdescent : baseEnd_3553943 < baseStart_3553943 := by decide
  rcases family_descends (prefixWord ++ tailWord_3553943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3553973 : List Nat := [1, 3, 3, 3, 1, 1, 1, 9]
def baseStart_3553973 : Nat := 118140960795 + 3553973 * 2 ^ 59
def prefixEnd_3553973 : Nat := 4983230072969 + 3 ^ 40 * 3553973 * 2
def baseEnd_3553973 : Nat := 135177509785298429480969

theorem tailTrace_3553973 : CollatzResearch.WordTrace tailWord_3553973 prefixEnd_3553973 135177509785298429480969 := by
  unfold tailWord_3553973
  simp only [CollatzResearch.WordTrace]
  refine ⟨129624044353570266110138573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86416029569046844073425715 129624044353570266110138573)
  ·
    refine ⟨48609016632588849791301965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129624044353570266110138573 48609016632588849791301965)
    ·
      refine ⟨18228381237220818671738237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48609016632588849791301965 18228381237220818671738237)
      ·
        refine ⟨6835642963957807001901839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18228381237220818671738237 6835642963957807001901839)
        ·
          refine ⟨10253464445936710502852759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6835642963957807001901839 10253464445936710502852759)
          ·
            refine ⟨15380196668905065754279139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10253464445936710502852759 15380196668905065754279139)
            ·
              refine ⟨23070295003357598631418709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15380196668905065754279139 23070295003357598631418709)
              ·
                refine ⟨135177509785298429480969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23070295003357598631418709 135177509785298429480969)
                ·
                  rfl

theorem cell22_3553973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 9].length) (baseStart_3553973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3553973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3553973 prefixEnd_3553973 := by exact prefixLift 3553973
  have htrace : WordTrace (prefixWord ++ tailWord_3553973) baseStart_3553973 baseEnd_3553973 := by
    simpa [prefixWord, tailWord_3553973, baseEnd_3553973] using wordTrace_append hprefix tailTrace_3553973
  have hstable : (prefixWord ++ tailWord_3553973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3553973).length < 2 ^ (prefixWord ++ tailWord_3553973).sum := by decide
  have hdescent : baseEnd_3553973 < baseStart_3553973 := by decide
  rcases family_descends (prefixWord ++ tailWord_3553973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3554033 : List Nat := [1, 2, 2, 2, 2, 2, 3, 1, 2, 5]
def baseStart_3554033 : Nat := 118140960795 + 3554033 * 2 ^ 59
def prefixEnd_3554033 : Nat := 4983230072969 + 3 ^ 40 * 3554033 * 2
def baseEnd_3554033 : Nat := 1216618127293865708828537

theorem tailTrace_3554033 : CollatzResearch.WordTrace tailWord_3554033 prefixEnd_3554033 1216618127293865708828537 := by
  unfold tailWord_3554033
  simp only [CollatzResearch.WordTrace]
  refine ⟨129626232733352896357322753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86417488488901930904881835 129626232733352896357322753)
  ·
    refine ⟨97219674550014672267992065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129626232733352896357322753 97219674550014672267992065)
    ·
      refine ⟨72914755912511004200994049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97219674550014672267992065 72914755912511004200994049)
      ·
        refine ⟨54686066934383253150745537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72914755912511004200994049 54686066934383253150745537)
        ·
          refine ⟨41014550200787439863059153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54686066934383253150745537 41014550200787439863059153)
          ·
            refine ⟨30760912650590579897294365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41014550200787439863059153 30760912650590579897294365)
            ·
              refine ⟨11535342243971467461485387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30760912650590579897294365 11535342243971467461485387)
              ·
                refine ⟨17303013365957201192228081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11535342243971467461485387 17303013365957201192228081)
                ·
                  refine ⟨12977260024467900894171061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17303013365957201192228081 12977260024467900894171061)
                  ·
                    refine ⟨1216618127293865708828537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12977260024467900894171061 1216618127293865708828537)
                    ·
                      rfl

theorem cell22_3554033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 1, 2, 5].length) (baseStart_3554033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3554033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3554033 prefixEnd_3554033 := by exact prefixLift 3554033
  have htrace : WordTrace (prefixWord ++ tailWord_3554033) baseStart_3554033 baseEnd_3554033 := by
    simpa [prefixWord, tailWord_3554033, baseEnd_3554033] using wordTrace_append hprefix tailTrace_3554033
  have hstable : (prefixWord ++ tailWord_3554033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3554033).length < 2 ^ (prefixWord ++ tailWord_3554033).sum := by decide
  have hdescent : baseEnd_3554033 < baseStart_3554033 := by decide
  rcases family_descends (prefixWord ++ tailWord_3554033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3554080 : List Nat := [2, 1, 1, 5, 1, 3, 2, 1, 6]
def baseStart_3554080 : Nat := 118140960795 + 3554080 * 2 ^ 59
def prefixEnd_3554080 : Nat := 4983230072969 + 3 ^ 40 * 3554080 * 2
def baseEnd_3554080 : Nat := 405544738784791084301131

theorem tailTrace_3554080 : CollatzResearch.WordTrace tailWord_3554080 prefixEnd_3554080 405544738784791084301131 := by
  unfold tailWord_3554080
  simp only [CollatzResearch.WordTrace]
  refine ⟨64813973482091311692141847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86418631309455082256189129 64813973482091311692141847)
  ·
    refine ⟨97220960223136967538212771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64813973482091311692141847 97220960223136967538212771)
    ·
      refine ⟨145831440334705451307319157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97220960223136967538212771 145831440334705451307319157)
      ·
        refine ⟨13671697531378636060061171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 145831440334705451307319157 13671697531378636060061171)
        ·
          refine ⟨20507546297067954090091757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13671697531378636060061171 20507546297067954090091757)
          ·
            refine ⟨7690329861400482783784409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20507546297067954090091757 7690329861400482783784409)
            ·
              refine ⟨5767747396050362087838307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7690329861400482783784409 5767747396050362087838307)
              ·
                refine ⟨8651621094075543131757461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5767747396050362087838307 8651621094075543131757461)
                ·
                  refine ⟨405544738784791084301131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8651621094075543131757461 405544738784791084301131)
                  ·
                    rfl

theorem cell22_3554080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 2, 1, 6].length) (baseStart_3554080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3554080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3554080 prefixEnd_3554080 := by exact prefixLift 3554080
  have htrace : WordTrace (prefixWord ++ tailWord_3554080) baseStart_3554080 baseEnd_3554080 := by
    simpa [prefixWord, tailWord_3554080, baseEnd_3554080] using wordTrace_append hprefix tailTrace_3554080
  have hstable : (prefixWord ++ tailWord_3554080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3554080).length < 2 ^ (prefixWord ++ tailWord_3554080).sum := by decide
  have hdescent : baseEnd_3554080 < baseStart_3554080 := by decide
  rcases family_descends (prefixWord ++ tailWord_3554080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3554168 : List Nat := [2, 1, 2, 1, 1, 1, 1, 3, 3, 7]
def baseStart_3554168 : Nat := 118140960795 + 3554168 * 2 ^ 59
def prefixEnd_3554168 : Nat := 4983230072969 + 3 ^ 40 * 3554168 * 2
def baseEnd_3554168 : Nat := 1216664340552770356703123

theorem tailTrace_3554168 : CollatzResearch.WordTrace tailWord_3554168 prefixEnd_3554168 1216664340552770356703123 := by
  unfold tailWord_3554168
  simp only [CollatzResearch.WordTrace]
  refine ⟨64815578293931907206743579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86420771058575876275658105 64815578293931907206743579)
  ·
    refine ⟨97223367440897860810115369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64815578293931907206743579 97223367440897860810115369)
    ·
      refine ⟨72917525580673395607586527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97223367440897860810115369 72917525580673395607586527)
      ·
        refine ⟨109376288371010093411379791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72917525580673395607586527 109376288371010093411379791)
        ·
          refine ⟨164064432556515140117069687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109376288371010093411379791 164064432556515140117069687)
          ·
            refine ⟨246096648834772710175604531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164064432556515140117069687 246096648834772710175604531)
            ·
              refine ⟨369144973252159065263406797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 246096648834772710175604531 369144973252159065263406797)
              ·
                refine ⟨138429364969559649473777549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 369144973252159065263406797 138429364969559649473777549)
                ·
                  refine ⟨51911011863584868552666581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 138429364969559649473777549 51911011863584868552666581)
                  ·
                    refine ⟨1216664340552770356703123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51911011863584868552666581 1216664340552770356703123)
                    ·
                      rfl

theorem cell22_3554168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 3, 7].length) (baseStart_3554168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3554168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3554168 prefixEnd_3554168 := by exact prefixLift 3554168
  have htrace : WordTrace (prefixWord ++ tailWord_3554168) baseStart_3554168 baseEnd_3554168 := by
    simpa [prefixWord, tailWord_3554168, baseEnd_3554168] using wordTrace_append hprefix tailTrace_3554168
  have hstable : (prefixWord ++ tailWord_3554168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3554168).length < 2 ^ (prefixWord ++ tailWord_3554168).sum := by decide
  have hdescent : baseEnd_3554168 < baseStart_3554168 := by decide
  rcases family_descends (prefixWord ++ tailWord_3554168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3554202 : List Nat := [3, 1, 1, 4, 3, 1, 1, 1, 2, 5]
def baseStart_3554202 : Nat := 118140960795 + 3554202 * 2 ^ 59
def prefixEnd_3554202 : Nat := 4983230072969 + 3 ^ 40 * 3554202 * 2
def baseEnd_3554202 : Nat := 1216675979447605601353019

theorem tailTrace_3554202 : CollatzResearch.WordTrace tailWord_3554202 prefixEnd_3554202 1216675979447605601353019 := by
  unfold tailWord_3554202
  simp only [CollatzResearch.WordTrace]
  refine ⟨32408099167435159555056215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86421597779827092146816573 32408099167435159555056215)
  ·
    refine ⟨48612148751152739332584323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32408099167435159555056215 48612148751152739332584323)
    ·
      refine ⟨72918223126729108998876485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48612148751152739332584323 72918223126729108998876485)
      ·
        refine ⟨13672166836261707937289341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72918223126729108998876485 13672166836261707937289341)
        ·
          refine ⟨5127062563598140476483503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13672166836261707937289341 5127062563598140476483503)
          ·
            refine ⟨7690593845397210714725255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5127062563598140476483503 7690593845397210714725255)
            ·
              refine ⟨11535890768095816072087883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7690593845397210714725255 11535890768095816072087883)
              ·
                refine ⟨17303836152143724108131825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11535890768095816072087883 17303836152143724108131825)
                ·
                  refine ⟨12977877114107793081098869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17303836152143724108131825 12977877114107793081098869)
                  ·
                    refine ⟨1216675979447605601353019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12977877114107793081098869 1216675979447605601353019)
                    ·
                      rfl

theorem cell22_3554202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 1, 2, 5].length) (baseStart_3554202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3554202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3554202 prefixEnd_3554202 := by exact prefixLift 3554202
  have htrace : WordTrace (prefixWord ++ tailWord_3554202) baseStart_3554202 baseEnd_3554202 := by
    simpa [prefixWord, tailWord_3554202, baseEnd_3554202] using wordTrace_append hprefix tailTrace_3554202
  have hstable : (prefixWord ++ tailWord_3554202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3554202).length < 2 ^ (prefixWord ++ tailWord_3554202).sum := by decide
  have hdescent : baseEnd_3554202 < baseStart_3554202 := by decide
  rcases family_descends (prefixWord ++ tailWord_3554202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3554232 : List Nat := [2, 1, 2, 1, 2, 4, 1, 5, 4]
def baseStart_3554232 : Nat := 118140960795 + 3554232 * 2 ^ 59
def prefixEnd_3554232 : Nat := 4983230072969 + 3 ^ 40 * 3554232 * 2
def baseEnd_3554232 : Nat := 405562083020231841034309

theorem tailTrace_3554232 : CollatzResearch.WordTrace tailWord_3554232 prefixEnd_3554232 405562083020231841034309 := by
  unfold tailWord_3554232
  simp only [CollatzResearch.WordTrace]
  refine ⟨64816745429815976671908475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86422327239754635562544633 64816745429815976671908475)
  ·
    refine ⟨97225118144723965007862713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64816745429815976671908475 97225118144723965007862713)
    ·
      refine ⟨72918838608542973755897035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97225118144723965007862713 72918838608542973755897035)
      ·
        refine ⟨109378257912814460633845553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72918838608542973755897035 109378257912814460633845553)
        ·
          refine ⟨82033693434610845475384165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109378257912814460633845553 82033693434610845475384165)
          ·
            refine ⟨15381317518989533526634531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82033693434610845475384165 15381317518989533526634531)
            ·
              refine ⟨23071976278484300289951797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15381317518989533526634531 23071976278484300289951797)
              ·
                refine ⟨2162997776107903152182981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23071976278484300289951797 2162997776107903152182981)
                ·
                  refine ⟨405562083020231841034309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2162997776107903152182981 405562083020231841034309)
                  ·
                    rfl

theorem cell22_3554232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 5, 4].length) (baseStart_3554232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3554232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3554232 prefixEnd_3554232 := by exact prefixLift 3554232
  have htrace : WordTrace (prefixWord ++ tailWord_3554232) baseStart_3554232 baseEnd_3554232 := by
    simpa [prefixWord, tailWord_3554232, baseEnd_3554232] using wordTrace_append hprefix tailTrace_3554232
  have hstable : (prefixWord ++ tailWord_3554232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3554232).length < 2 ^ (prefixWord ++ tailWord_3554232).sum := by decide
  have hdescent : baseEnd_3554232 < baseStart_3554232 := by decide
  rcases family_descends (prefixWord ++ tailWord_3554232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3554275 : List Nat := [1, 1, 1, 6, 1, 1, 1, 1, 2, 7]
def baseStart_3554275 : Nat := 118140960795 + 3554275 * 2 ^ 59
def prefixEnd_3554275 : Nat := 4983230072969 + 3 ^ 40 * 3554275 * 2
def baseEnd_3554275 : Nat := 1216700968839457744277795

theorem tailTrace_3554275 : CollatzResearch.WordTrace tailWord_3554275 prefixEnd_3554275 1216700968839457744277795 := by
  unfold tailWord_3554275
  simp only [CollatzResearch.WordTrace]
  refine ⟨129635059198476171687632279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86423372798984114458421519 129635059198476171687632279)
  ·
    refine ⟨194452588797714257531448419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129635059198476171687632279 194452588797714257531448419)
    ·
      refine ⟨291678883196571386297172629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194452588797714257531448419 291678883196571386297172629)
      ·
        refine ⟨13672447649839283732679967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 291678883196571386297172629 13672447649839283732679967)
        ·
          refine ⟨20508671474758925599019951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13672447649839283732679967 20508671474758925599019951)
          ·
            refine ⟨30763007212138388398529927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20508671474758925599019951 30763007212138388398529927)
            ·
              refine ⟨46144510818207582597794891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30763007212138388398529927 46144510818207582597794891)
              ·
                refine ⟨69216766227311373896692337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46144510818207582597794891 69216766227311373896692337)
                ·
                  refine ⟨51912574670483530422519253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69216766227311373896692337 51912574670483530422519253)
                  ·
                    refine ⟨1216700968839457744277795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51912574670483530422519253 1216700968839457744277795)
                    ·
                      rfl

theorem cell22_3554275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 2, 7].length) (baseStart_3554275 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3554275 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3554275 prefixEnd_3554275 := by exact prefixLift 3554275
  have htrace : WordTrace (prefixWord ++ tailWord_3554275) baseStart_3554275 baseEnd_3554275 := by
    simpa [prefixWord, tailWord_3554275, baseEnd_3554275] using wordTrace_append hprefix tailTrace_3554275
  have hstable : (prefixWord ++ tailWord_3554275).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3554275).length < 2 ^ (prefixWord ++ tailWord_3554275).sum := by decide
  have hdescent : baseEnd_3554275 < baseStart_3554275 := by decide
  rcases family_descends (prefixWord ++ tailWord_3554275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3554356 : List Nat := [2, 5, 1, 2, 1, 2, 2, 2, 5]
def baseStart_3554356 : Nat := 118140960795 + 3554356 * 2 ^ 59
def prefixEnd_3554356 : Nat := 4983230072969 + 3 ^ 40 * 3554356 * 2
def baseEnd_3554356 : Nat := 405576232264933511000849

theorem tailTrace_3554356 : CollatzResearch.WordTrace tailWord_3554356 prefixEnd_3554356 405576232264933511000849 := by
  unfold tailWord_3554356
  simp only [CollatzResearch.WordTrace]
  refine ⟨64819006755591361260665461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86425342340788481680887281 64819006755591361260665461)
  ·
    refine ⟨6076781883336690118187387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 64819006755591361260665461 6076781883336690118187387)
    ·
      refine ⟨9115172825005035177281081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6076781883336690118187387 9115172825005035177281081)
      ·
        refine ⟨6836379618753776382960811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9115172825005035177281081 6836379618753776382960811)
        ·
          refine ⟨10254569428130664574441217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6836379618753776382960811 10254569428130664574441217)
          ·
            refine ⟨7690927071097998430830913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10254569428130664574441217 7690927071097998430830913)
            ·
              refine ⟨5768195303323498823123185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7690927071097998430830913 5768195303323498823123185)
              ·
                refine ⟨4326146477492624117342389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5768195303323498823123185 4326146477492624117342389)
                ·
                  refine ⟨405576232264933511000849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4326146477492624117342389 405576232264933511000849)
                  ·
                    rfl

theorem cell22_3554356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 2, 2, 5].length) (baseStart_3554356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3554356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3554356 prefixEnd_3554356 := by exact prefixLift 3554356
  have htrace : WordTrace (prefixWord ++ tailWord_3554356) baseStart_3554356 baseEnd_3554356 := by
    simpa [prefixWord, tailWord_3554356, baseEnd_3554356] using wordTrace_append hprefix tailTrace_3554356
  have hstable : (prefixWord ++ tailWord_3554356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3554356).length < 2 ^ (prefixWord ++ tailWord_3554356).sum := by decide
  have hdescent : baseEnd_3554356 < baseStart_3554356 := by decide
  rcases family_descends (prefixWord ++ tailWord_3554356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3554433 : List Nat := [1, 2, 4, 2, 2, 2, 3, 1, 2, 3]
def baseStart_3554433 : Nat := 118140960795 + 3554433 * 2 ^ 59
def prefixEnd_3554433 : Nat := 4983230072969 + 3 ^ 40 * 3554433 * 2
def baseEnd_3554433 : Nat := 1216755055468397998827311

theorem tailTrace_3554433 : CollatzResearch.WordTrace tailWord_3554433 prefixEnd_3554433 1216755055468397998827311 := by
  unfold tailWord_3554433
  simp only [CollatzResearch.WordTrace]
  refine ⟨129640821931903764671883953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86427214621269176447922635 129640821931903764671883953)
  ·
    refine ⟨97230616448927823503912965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129640821931903764671883953 97230616448927823503912965)
    ·
      refine ⟨18230740584173966906983681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97230616448927823503912965 18230740584173966906983681)
      ·
        refine ⟨13673055438130475180237761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18230740584173966906983681 13673055438130475180237761)
        ·
          refine ⟨10254791578597856385178321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13673055438130475180237761 10254791578597856385178321)
          ·
            refine ⟨7691093683948392288883741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10254791578597856385178321 7691093683948392288883741)
            ·
              refine ⟨2884160131480647108331403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7691093683948392288883741 2884160131480647108331403)
              ·
                refine ⟨4326240197220970662497105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2884160131480647108331403 4326240197220970662497105)
                ·
                  refine ⟨3244680147915727996872829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4326240197220970662497105 3244680147915727996872829)
                  ·
                    refine ⟨1216755055468397998827311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3244680147915727996872829 1216755055468397998827311)
                    ·
                      rfl

theorem cell22_3554433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 3, 1, 2, 3].length) (baseStart_3554433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3554433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3554433 prefixEnd_3554433 := by exact prefixLift 3554433
  have htrace : WordTrace (prefixWord ++ tailWord_3554433) baseStart_3554433 baseEnd_3554433 := by
    simpa [prefixWord, tailWord_3554433, baseEnd_3554433] using wordTrace_append hprefix tailTrace_3554433
  have hstable : (prefixWord ++ tailWord_3554433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3554433).length < 2 ^ (prefixWord ++ tailWord_3554433).sum := by decide
  have hdescent : baseEnd_3554433 < baseStart_3554433 := by decide
  rcases family_descends (prefixWord ++ tailWord_3554433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3554446 : List Nat := [4, 1, 1, 3, 2, 3, 2, 6]
def baseStart_3554446 : Nat := 118140960795 + 3554446 * 2 ^ 59
def prefixEnd_3554446 : Nat := 4983230072969 + 3 ^ 40 * 3554446 * 2
def baseEnd_3554446 : Nat := 135195500626007810916919

theorem tailTrace_3554446 : CollatzResearch.WordTrace tailWord_3554446 prefixEnd_3554446 135195500626007810916919 := by
  unfold tailWord_3554446
  simp only [CollatzResearch.WordTrace]
  refine ⟨16205162010107083486513399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86427530720571111928071461 16205162010107083486513399)
  ·
    refine ⟨24307743015160625229770099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16205162010107083486513399 24307743015160625229770099)
    ·
      refine ⟨36461614522740937844655149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24307743015160625229770099 36461614522740937844655149)
      ·
        refine ⟨13673105446027851691745681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36461614522740937844655149 13673105446027851691745681)
        ·
          refine ⟨10254829084520888768809261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13673105446027851691745681 10254829084520888768809261)
          ·
            refine ⟨3845560906695333288303473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10254829084520888768809261 3845560906695333288303473)
            ·
              refine ⟨2884170680021499966227605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3845560906695333288303473 2884170680021499966227605)
              ·
                refine ⟨135195500626007810916919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2884170680021499966227605 135195500626007810916919)
                ·
                  rfl

theorem cell22_3554446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 2, 6].length) (baseStart_3554446 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3554446 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3554446 prefixEnd_3554446 := by exact prefixLift 3554446
  have htrace : WordTrace (prefixWord ++ tailWord_3554446) baseStart_3554446 baseEnd_3554446 := by
    simpa [prefixWord, tailWord_3554446, baseEnd_3554446] using wordTrace_append hprefix tailTrace_3554446
  have hstable : (prefixWord ++ tailWord_3554446).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3554446).length < 2 ^ (prefixWord ++ tailWord_3554446).sum := by decide
  have hdescent : baseEnd_3554446 < baseStart_3554446 := by decide
  rcases family_descends (prefixWord ++ tailWord_3554446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3554536 : List Nat := [2, 1, 4, 1, 2, 1, 3, 4, 4]
def baseStart_3554536 : Nat := 118140960795 + 3554536 * 2 ^ 59
def prefixEnd_3554536 : Nat := 4983230072969 + 3 ^ 40 * 3554536 * 2
def baseEnd_3554536 : Nat := 405596771491113354500665

theorem tailTrace_3554536 : CollatzResearch.WordTrace tailWord_3554536 prefixEnd_3554536 405596771491113354500665 := by
  unfold tailWord_3554536
  simp only [CollatzResearch.WordTrace]
  refine ⟨64822289325265306631441731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86429719100353742175255641 64822289325265306631441731)
  ·
    refine ⟨97233433987897959947162597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64822289325265306631441731 97233433987897959947162597)
    ·
      refine ⟨18231268872730867490092987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97233433987897959947162597 18231268872730867490092987)
      ·
        refine ⟨27346903309096301235139481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18231268872730867490092987 27346903309096301235139481)
        ·
          refine ⟨20510177481822225926354611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27346903309096301235139481 20510177481822225926354611)
          ·
            refine ⟨30765266222733338889531917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20510177481822225926354611 30765266222733338889531917)
            ·
              refine ⟨11536974833525002083574469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30765266222733338889531917 11536974833525002083574469)
              ·
                refine ⟨2163182781285937890670213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11536974833525002083574469 2163182781285937890670213)
                ·
                  refine ⟨405596771491113354500665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2163182781285937890670213 405596771491113354500665)
                  ·
                    rfl

theorem cell22_3554536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 4, 4].length) (baseStart_3554536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3554536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3554536 prefixEnd_3554536 := by exact prefixLift 3554536
  have htrace : WordTrace (prefixWord ++ tailWord_3554536) baseStart_3554536 baseEnd_3554536 := by
    simpa [prefixWord, tailWord_3554536, baseEnd_3554536] using wordTrace_append hprefix tailTrace_3554536
  have hstable : (prefixWord ++ tailWord_3554536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3554536).length < 2 ^ (prefixWord ++ tailWord_3554536).sum := by decide
  have hdescent : baseEnd_3554536 < baseStart_3554536 := by decide
  rcases family_descends (prefixWord ++ tailWord_3554536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3554776 : List Nat := [2, 1, 2, 2, 2, 1, 4, 1, 2, 5]
def baseStart_3554776 : Nat := 118140960795 + 3554776 * 2 ^ 59
def prefixEnd_3554776 : Nat := 4983230072969 + 3 ^ 40 * 3554776 * 2
def baseEnd_3554776 : Nat := 1216872471378059437501259

theorem tailTrace_3554776 : CollatzResearch.WordTrace tailWord_3554776 prefixEnd_3554776 1216872471378059437501259 := by
  unfold tailWord_3554776
  simp only [CollatzResearch.WordTrace]
  refine ⟨64826666084830567125810091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86435554779774089501080121 64826666084830567125810091)
  ·
    refine ⟨97239999127245850688715137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64826666084830567125810091 97239999127245850688715137)
    ·
      refine ⟨72929999345434388016536353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97239999127245850688715137 72929999345434388016536353)
      ·
        refine ⟨54697499509075791012402265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72929999345434388016536353 54697499509075791012402265)
        ·
          refine ⟨41023124631806843259301699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54697499509075791012402265 41023124631806843259301699)
          ·
            refine ⟨61534686947710264888952549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41023124631806843259301699 61534686947710264888952549)
            ·
              refine ⟨11537753802695674666678603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61534686947710264888952549 11537753802695674666678603)
              ·
                refine ⟨17306630704043512000017905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11537753802695674666678603 17306630704043512000017905)
                ·
                  refine ⟨12979973028032634000013429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17306630704043512000017905 12979973028032634000013429)
                  ·
                    refine ⟨1216872471378059437501259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12979973028032634000013429 1216872471378059437501259)
                    ·
                      rfl

theorem cell22_3554776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 1, 2, 5].length) (baseStart_3554776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3554776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3554776 prefixEnd_3554776 := by exact prefixLift 3554776
  have htrace : WordTrace (prefixWord ++ tailWord_3554776) baseStart_3554776 baseEnd_3554776 := by
    simpa [prefixWord, tailWord_3554776, baseEnd_3554776] using wordTrace_append hprefix tailTrace_3554776
  have hstable : (prefixWord ++ tailWord_3554776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3554776).length < 2 ^ (prefixWord ++ tailWord_3554776).sum := by decide
  have hdescent : baseEnd_3554776 < baseStart_3554776 := by decide
  rcases family_descends (prefixWord ++ tailWord_3554776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3554808 : List Nat := [2, 1, 2, 1, 1, 5, 2, 3, 1, 4]
def baseStart_3554808 : Nat := 118140960795 + 3554808 * 2 ^ 59
def prefixEnd_3554808 : Nat := 4983230072969 + 3 ^ 40 * 3554808 * 2
def baseEnd_3554808 : Nat := 1216883425632022020701161

theorem tailTrace_3554808 : CollatzResearch.WordTrace tailWord_3554808 prefixEnd_3554808 1216883425632022020701161 := by
  unfold tailWord_3554808
  simp only [CollatzResearch.WordTrace]
  refine ⟨64827249652772601858392539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86436332870363469144523385 64827249652772601858392539)
  ·
    refine ⟨97240874479158902787588809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64827249652772601858392539 97240874479158902787588809)
    ·
      refine ⟨72930655859369177090691607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97240874479158902787588809 72930655859369177090691607)
      ·
        refine ⟨109395983789053765636037411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72930655859369177090691607 109395983789053765636037411)
        ·
          refine ⟨164093975683580648454056117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109395983789053765636037411 164093975683580648454056117)
          ·
            refine ⟨15383810220335685792567761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 164093975683580648454056117 15383810220335685792567761)
            ·
              refine ⟨11537857665251764344425821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15383810220335685792567761 11537857665251764344425821)
              ·
                refine ⟨4326696624469411629159683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11537857665251764344425821 4326696624469411629159683)
                ·
                  refine ⟨6490044936704117443739525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4326696624469411629159683 6490044936704117443739525)
                  ·
                    refine ⟨1216883425632022020701161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6490044936704117443739525 1216883425632022020701161)
                    ·
                      rfl

theorem cell22_3554808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 3, 1, 4].length) (baseStart_3554808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3554808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3554808 prefixEnd_3554808 := by exact prefixLift 3554808
  have htrace : WordTrace (prefixWord ++ tailWord_3554808) baseStart_3554808 baseEnd_3554808 := by
    simpa [prefixWord, tailWord_3554808, baseEnd_3554808] using wordTrace_append hprefix tailTrace_3554808
  have hstable : (prefixWord ++ tailWord_3554808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3554808).length < 2 ^ (prefixWord ++ tailWord_3554808).sum := by decide
  have hdescent : baseEnd_3554808 < baseStart_3554808 := by decide
  rcases family_descends (prefixWord ++ tailWord_3554808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3554823 : List Nat := [1, 1, 4, 3, 2, 1, 3, 1, 6]
def baseStart_3554823 : Nat := 118140960795 + 3554823 * 2 ^ 59
def prefixEnd_3554823 : Nat := 4983230072969 + 3 ^ 40 * 3554823 * 2
def baseEnd_3554823 : Nat := 405629520146188993858705

theorem tailTrace_3554823 : CollatzResearch.WordTrace tailWord_3554823 prefixEnd_3554823 405629520146188993858705 := by
  unfold tailWord_3554823
  simp only [CollatzResearch.WordTrace]
  refine ⟨129655046400490861278581123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86436697600327240852387415 129655046400490861278581123)
  ·
    refine ⟨194482569600736291917871685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129655046400490861278581123 194482569600736291917871685)
    ·
      refine ⟨36465481800138054734600941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 194482569600736291917871685 36465481800138054734600941)
      ·
        refine ⟨13674555675051770525475353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36465481800138054734600941 13674555675051770525475353)
        ·
          refine ⟨10255916756288827894106515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13674555675051770525475353 10255916756288827894106515)
          ·
            refine ⟨15383875134433241841159773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10255916756288827894106515 15383875134433241841159773)
            ·
              refine ⟨5768953175412465690434915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15383875134433241841159773 5768953175412465690434915)
              ·
                refine ⟨8653429763118698535652373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5768953175412465690434915 8653429763118698535652373)
                ·
                  refine ⟨405629520146188993858705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8653429763118698535652373 405629520146188993858705)
                  ·
                    rfl

theorem cell22_3554823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 3, 1, 6].length) (baseStart_3554823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3554823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3554823 prefixEnd_3554823 := by exact prefixLift 3554823
  have htrace : WordTrace (prefixWord ++ tailWord_3554823) baseStart_3554823 baseEnd_3554823 := by
    simpa [prefixWord, tailWord_3554823, baseEnd_3554823] using wordTrace_append hprefix tailTrace_3554823
  have hstable : (prefixWord ++ tailWord_3554823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3554823).length < 2 ^ (prefixWord ++ tailWord_3554823).sum := by decide
  have hdescent : baseEnd_3554823 < baseStart_3554823 := by decide
  rcases family_descends (prefixWord ++ tailWord_3554823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3554900 : List Nat := [2, 4, 1, 1, 1, 2, 3, 2, 3, 3]
def baseStart_3554900 : Nat := 118140960795 + 3554900 * 2 ^ 59
def prefixEnd_3554900 : Nat := 4983230072969 + 3 ^ 40 * 3554900 * 2
def baseEnd_3554900 : Nat := 1216914919112164447400879

theorem tailTrace_3554900 : CollatzResearch.WordTrace tailWord_3554900 prefixEnd_3554900 1216914919112164447400879 := by
  unfold tailWord_3554900
  simp only [CollatzResearch.WordTrace]
  refine ⟨64828927410605951714567077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86438569880807935619422769 64828927410605951714567077)
  ·
    refine ⟨12155423889488615946481327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64828927410605951714567077 12155423889488615946481327)
    ·
      refine ⟨18233135834232923919721991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12155423889488615946481327 18233135834232923919721991)
      ·
        refine ⟨27349703751349385879582987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18233135834232923919721991 27349703751349385879582987)
        ·
          refine ⟨41024555627024078819374481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27349703751349385879582987 41024555627024078819374481)
          ·
            refine ⟨30768416720268059114530861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41024555627024078819374481 30768416720268059114530861)
            ·
              refine ⟨11538156270100522167949073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30768416720268059114530861 11538156270100522167949073)
              ·
                refine ⟨8653617202575391625961805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11538156270100522167949073 8653617202575391625961805)
                ·
                  refine ⟨3245106450965771859735677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8653617202575391625961805 3245106450965771859735677)
                  ·
                    refine ⟨1216914919112164447400879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3245106450965771859735677 1216914919112164447400879)
                    ·
                      rfl

theorem cell22_3554900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 2, 3, 3].length) (baseStart_3554900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3554900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3554900 prefixEnd_3554900 := by exact prefixLift 3554900
  have htrace : WordTrace (prefixWord ++ tailWord_3554900) baseStart_3554900 baseEnd_3554900 := by
    simpa [prefixWord, tailWord_3554900, baseEnd_3554900] using wordTrace_append hprefix tailTrace_3554900
  have hstable : (prefixWord ++ tailWord_3554900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3554900).length < 2 ^ (prefixWord ++ tailWord_3554900).sum := by decide
  have hdescent : baseEnd_3554900 < baseStart_3554900 := by decide
  rcases family_descends (prefixWord ++ tailWord_3554900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3554917 : List Nat := [1, 3, 1, 3, 3, 1, 1, 5, 1, 3]
def baseStart_3554917 : Nat := 118140960795 + 3554917 * 2 ^ 59
def prefixEnd_3554917 : Nat := 4983230072969 + 3 ^ 40 * 3554917 * 2
def baseEnd_3554917 : Nat := 1216920738559582069725827

theorem tailTrace_3554917 : CollatzResearch.WordTrace tailWord_3554917 prefixEnd_3554917 1216920738559582069725827 := by
  unfold tailWord_3554917
  simp only [CollatzResearch.WordTrace]
  refine ⟨129658474862150315332503005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86438983241433543555002003 129658474862150315332503005)
  ·
    refine ⟨48621928073306368249688627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129658474862150315332503005 48621928073306368249688627)
    ·
      refine ⟨72932892109959552374532941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48621928073306368249688627 72932892109959552374532941)
      ·
        refine ⟨27349834541234832140449853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72932892109959552374532941 27349834541234832140449853)
        ·
          refine ⟨10256187952963062052668695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27349834541234832140449853 10256187952963062052668695)
          ·
            refine ⟨15384281929444593079003043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10256187952963062052668695 15384281929444593079003043)
            ·
              refine ⟨23076422894166889618504565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15384281929444593079003043 23076422894166889618504565)
              ·
                refine ⟨2163414646328145901734803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23076422894166889618504565 2163414646328145901734803)
                ·
                  refine ⟨3245121969492218852602205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2163414646328145901734803 3245121969492218852602205)
                  ·
                    refine ⟨1216920738559582069725827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3245121969492218852602205 1216920738559582069725827)
                    ·
                      rfl

theorem cell22_3554917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 5, 1, 3].length) (baseStart_3554917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3554917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3554917 prefixEnd_3554917 := by exact prefixLift 3554917
  have htrace : WordTrace (prefixWord ++ tailWord_3554917) baseStart_3554917 baseEnd_3554917 := by
    simpa [prefixWord, tailWord_3554917, baseEnd_3554917] using wordTrace_append hprefix tailTrace_3554917
  have hstable : (prefixWord ++ tailWord_3554917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3554917).length < 2 ^ (prefixWord ++ tailWord_3554917).sum := by decide
  have hdescent : baseEnd_3554917 < baseStart_3554917 := by decide
  rcases family_descends (prefixWord ++ tailWord_3554917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3554928 : List Nat := [2, 1, 1, 1, 6, 1, 1, 2, 2, 5]
def baseStart_3554928 : Nat := 118140960795 + 3554928 * 2 ^ 59
def prefixEnd_3554928 : Nat := 4983230072969 + 3 ^ 40 * 3554928 * 2
def baseEnd_3554928 : Nat := 1216924504084381707700793

theorem tailTrace_3554928 : CollatzResearch.WordTrace tailWord_3554928 prefixEnd_3554928 1216924504084381707700793 := by
  unfold tailWord_3554928
  simp only [CollatzResearch.WordTrace]
  refine ⟨64829438032555232105576719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86439250710073642807435625 64829438032555232105576719)
  ·
    refine ⟨97244157048832848158365079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64829438032555232105576719 97244157048832848158365079)
    ·
      refine ⟨145866235573249272237547619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97244157048832848158365079 145866235573249272237547619)
      ·
        refine ⟨218799353359873908356321429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145866235573249272237547619 218799353359873908356321429)
        ·
          refine ⟨10256219688744089454202567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 218799353359873908356321429 10256219688744089454202567)
          ·
            refine ⟨15384329533116134181303851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10256219688744089454202567 15384329533116134181303851)
            ·
              refine ⟨23076494299674201271955777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15384329533116134181303851 23076494299674201271955777)
              ·
                refine ⟨17307370724755650953966833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23076494299674201271955777 17307370724755650953966833)
                ·
                  refine ⟨12980528043566738215475125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17307370724755650953966833 12980528043566738215475125)
                  ·
                    refine ⟨1216924504084381707700793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12980528043566738215475125 1216924504084381707700793)
                    ·
                      rfl

theorem cell22_3554928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 2, 2, 5].length) (baseStart_3554928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3554928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3554928 prefixEnd_3554928 := by exact prefixLift 3554928
  have htrace : WordTrace (prefixWord ++ tailWord_3554928) baseStart_3554928 baseEnd_3554928 := by
    simpa [prefixWord, tailWord_3554928, baseEnd_3554928] using wordTrace_append hprefix tailTrace_3554928
  have hstable : (prefixWord ++ tailWord_3554928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3554928).length < 2 ^ (prefixWord ++ tailWord_3554928).sum := by decide
  have hdescent : baseEnd_3554928 < baseStart_3554928 := by decide
  rcases family_descends (prefixWord ++ tailWord_3554928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3554930 : List Nat := [3, 2, 1, 2, 3, 1, 3, 2, 5]
def baseStart_3554930 : Nat := 118140960795 + 3554930 * 2 ^ 59
def prefixEnd_3554930 : Nat := 4983230072969 + 3 ^ 40 * 3554930 * 2
def baseEnd_3554930 : Nat := 405641729575084789716929

theorem tailTrace_3554930 : CollatzResearch.WordTrace tailWord_3554930 prefixEnd_3554930 405641729575084789716929 := by
  unfold tailWord_3554930
  simp only [CollatzResearch.WordTrace]
  refine ⟨32414737252775804638181561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86439299340735479035150829 32414737252775804638181561)
  ·
    refine ⟨24311052939581853478636171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32414737252775804638181561 24311052939581853478636171)
    ·
      refine ⟨36466579409372780217954257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24311052939581853478636171 36466579409372780217954257)
      ·
        refine ⟨27349934557029585163465693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36466579409372780217954257 27349934557029585163465693)
        ·
          refine ⟨10256225458886094436299635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27349934557029585163465693 10256225458886094436299635)
          ·
            refine ⟨15384338188329141654449453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10256225458886094436299635 15384338188329141654449453)
            ·
              refine ⟨5769126820623428120418545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15384338188329141654449453 5769126820623428120418545)
              ·
                refine ⟨4326845115467571090313909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5769126820623428120418545 4326845115467571090313909)
                ·
                  refine ⟨405641729575084789716929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4326845115467571090313909 405641729575084789716929)
                  ·
                    rfl

theorem cell22_3554930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 3, 2, 5].length) (baseStart_3554930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3554930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3554930 prefixEnd_3554930 := by exact prefixLift 3554930
  have htrace : WordTrace (prefixWord ++ tailWord_3554930) baseStart_3554930 baseEnd_3554930 := by
    simpa [prefixWord, tailWord_3554930, baseEnd_3554930] using wordTrace_append hprefix tailTrace_3554930
  have hstable : (prefixWord ++ tailWord_3554930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3554930).length < 2 ^ (prefixWord ++ tailWord_3554930).sum := by decide
  have hdescent : baseEnd_3554930 < baseStart_3554930 := by decide
  rcases family_descends (prefixWord ++ tailWord_3554930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3554934 : List Nat := [5, 1, 1, 2, 2, 1, 2, 4, 1, 3]
def baseStart_3554934 : Nat := 118140960795 + 3554934 * 2 ^ 59
def prefixEnd_3554934 : Nat := 4983230072969 + 3 ^ 40 * 3554934 * 2
def baseEnd_3554934 : Nat := 1216926558006999692050775

theorem tailTrace_3554934 : CollatzResearch.WordTrace tailWord_3554934 prefixEnd_3554934 1216926558006999692050775 := by
  unfold tailWord_3554934
  simp only [CollatzResearch.WordTrace]
  refine ⟨8103693431443045452241991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 86439396602059151490581237 8103693431443045452241991)
  ·
    refine ⟨12155540147164568178362987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8103693431443045452241991 12155540147164568178362987)
    ·
      refine ⟨18233310220746852267544481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12155540147164568178362987 18233310220746852267544481)
      ·
        refine ⟨13674982665560139200658361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18233310220746852267544481 13674982665560139200658361)
        ·
          refine ⟨10256236999170104400493771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13674982665560139200658361 10256236999170104400493771)
          ·
            refine ⟨15384355498755156600740657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10256236999170104400493771 15384355498755156600740657)
            ·
              refine ⟨11538266624066367450555493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15384355498755156600740657 11538266624066367450555493)
              ·
                refine ⟨2163424992012443896979155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11538266624066367450555493 2163424992012443896979155)
                ·
                  refine ⟨3245137488018665845468733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2163424992012443896979155 3245137488018665845468733)
                  ·
                    refine ⟨1216926558006999692050775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3245137488018665845468733 1216926558006999692050775)
                    ·
                      rfl

theorem cell22_3554934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 4, 1, 3].length) (baseStart_3554934 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3554934 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3554934 prefixEnd_3554934 := by exact prefixLift 3554934
  have htrace : WordTrace (prefixWord ++ tailWord_3554934) baseStart_3554934 baseEnd_3554934 := by
    simpa [prefixWord, tailWord_3554934, baseEnd_3554934] using wordTrace_append hprefix tailTrace_3554934
  have hstable : (prefixWord ++ tailWord_3554934).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3554934).length < 2 ^ (prefixWord ++ tailWord_3554934).sum := by decide
  have hdescent : baseEnd_3554934 < baseStart_3554934 := by decide
  rcases family_descends (prefixWord ++ tailWord_3554934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3554973 : List Nat := [1, 4, 2, 1, 1, 1, 1, 3, 3, 5]
def baseStart_3554973 : Nat := 118140960795 + 3554973 * 2 ^ 59
def prefixEnd_3554973 : Nat := 4983230072969 + 3 ^ 40 * 3554973 * 2
def baseEnd_3554973 : Nat := 1216939908504016590325655

theorem tailTrace_3554973 : CollatzResearch.WordTrace tailWord_3554973 prefixEnd_3554973 1216939908504016590325655 := by
  unfold tailWord_3554973
  simp only [CollatzResearch.WordTrace]
  refine ⟨129660517349947436896541573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86440344899964957931027715 129660517349947436896541573)
  ·
    refine ⟨24311347003115144418101545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129660517349947436896541573 24311347003115144418101545)
    ·
      refine ⟨18233510252336358313576159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24311347003115144418101545 18233510252336358313576159)
      ·
        refine ⟨27350265378504537470364239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18233510252336358313576159 27350265378504537470364239)
        ·
          refine ⟨41025398067756806205546359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27350265378504537470364239 41025398067756806205546359)
          ·
            refine ⟨61538097101635209308319539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41025398067756806205546359 61538097101635209308319539)
            ·
              refine ⟨92307145652452813962479309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61538097101635209308319539 92307145652452813962479309)
              ·
                refine ⟨34615179619669805235929741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92307145652452813962479309 34615179619669805235929741)
                ·
                  refine ⟨12980692357376176963473653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34615179619669805235929741 12980692357376176963473653)
                  ·
                    refine ⟨1216939908504016590325655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12980692357376176963473653 1216939908504016590325655)
                    ·
                      rfl

theorem cell22_3554973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 3, 3, 5].length) (baseStart_3554973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3554973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3554973 prefixEnd_3554973 := by exact prefixLift 3554973
  have htrace : WordTrace (prefixWord ++ tailWord_3554973) baseStart_3554973 baseEnd_3554973 := by
    simpa [prefixWord, tailWord_3554973, baseEnd_3554973] using wordTrace_append hprefix tailTrace_3554973
  have hstable : (prefixWord ++ tailWord_3554973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3554973).length < 2 ^ (prefixWord ++ tailWord_3554973).sum := by decide
  have hdescent : baseEnd_3554973 < baseStart_3554973 := by decide
  rcases family_descends (prefixWord ++ tailWord_3554973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3555037 : List Nat := [1, 4, 3, 3, 2, 9]
def baseStart_3555037 : Nat := 118140960795 + 3555037 * 2 ^ 59
def prefixEnd_3555037 : Nat := 4983230072969 + 3 ^ 40 * 3555037 * 2
def baseEnd_3555037 : Nat := 15024219963110392058339

theorem tailTrace_3555037 : CollatzResearch.WordTrace tailWord_3555037 prefixEnd_3555037 15024219963110392058339 := by
  unfold tailWord_3555037
  simp only [CollatzResearch.WordTrace]
  refine ⟨129662851621715575826871365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86441901081143717217914243 129662851621715575826871365)
  ·
    refine ⟨24311784679071670467538381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129662851621715575826871365 24311784679071670467538381)
    ·
      refine ⟨9116919254651876425326893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24311784679071670467538381 9116919254651876425326893)
      ·
        refine ⟨3418844720494453659497585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9116919254651876425326893 3418844720494453659497585)
        ·
          refine ⟨2564133540370840244623189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3418844720494453659497585 2564133540370840244623189)
          ·
            refine ⟨15024219963110392058339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2564133540370840244623189 15024219963110392058339)
            ·
              rfl

theorem cell22_3555037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 9].length) (baseStart_3555037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3555037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3555037 prefixEnd_3555037 := by exact prefixLift 3555037
  have htrace : WordTrace (prefixWord ++ tailWord_3555037) baseStart_3555037 baseEnd_3555037 := by
    simpa [prefixWord, tailWord_3555037, baseEnd_3555037] using wordTrace_append hprefix tailTrace_3555037
  have hstable : (prefixWord ++ tailWord_3555037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3555037).length < 2 ^ (prefixWord ++ tailWord_3555037).sum := by decide
  have hdescent : baseEnd_3555037 < baseStart_3555037 := by decide
  rcases family_descends (prefixWord ++ tailWord_3555037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3555063 : List Nat := [1, 1, 3, 1, 1, 1, 5, 1, 1, 7]
def baseStart_3555063 : Nat := 118140960795 + 3555063 * 2 ^ 59
def prefixEnd_3555063 : Nat := 4983230072969 + 3 ^ 40 * 3555063 * 2
def baseEnd_3555063 : Nat := 1216970717343286355575379

theorem tailTrace_3555063 : CollatzResearch.WordTrace tailWord_3555063 prefixEnd_3555063 1216970717343286355575379 := by
  unfold tailWord_3555063
  simp only [CollatzResearch.WordTrace]
  refine ⟨129663799919621382267317843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86442533279747588178211895 129663799919621382267317843)
  ·
    refine ⟨194495699879432073400976765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129663799919621382267317843 194495699879432073400976765)
    ·
      refine ⟨72935887454787027525366287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 194495699879432073400976765 72935887454787027525366287)
      ·
        refine ⟨109403831182180541288049431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72935887454787027525366287 109403831182180541288049431)
        ·
          refine ⟨164105746773270811932074147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109403831182180541288049431 164105746773270811932074147)
          ·
            refine ⟨246158620159906217898111221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164105746773270811932074147 246158620159906217898111221)
            ·
              refine ⟨23077370639991207927947927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 246158620159906217898111221 23077370639991207927947927)
              ·
                refine ⟨34616055959986811891921891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23077370639991207927947927 34616055959986811891921891)
                ·
                  refine ⟨51924083939980217837882837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34616055959986811891921891 51924083939980217837882837)
                  ·
                    refine ⟨1216970717343286355575379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51924083939980217837882837 1216970717343286355575379)
                    ·
                      rfl

theorem cell22_3555063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 1, 1, 7].length) (baseStart_3555063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3555063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3555063 prefixEnd_3555063 := by exact prefixLift 3555063
  have htrace : WordTrace (prefixWord ++ tailWord_3555063) baseStart_3555063 baseEnd_3555063 := by
    simpa [prefixWord, tailWord_3555063, baseEnd_3555063] using wordTrace_append hprefix tailTrace_3555063
  have hstable : (prefixWord ++ tailWord_3555063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3555063).length < 2 ^ (prefixWord ++ tailWord_3555063).sum := by decide
  have hdescent : baseEnd_3555063 < baseStart_3555063 := by decide
  rcases family_descends (prefixWord ++ tailWord_3555063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3555144 : List Nat := [2, 1, 3, 1, 1, 6, 1, 3, 4]
def baseStart_3555144 : Nat := 118140960795 + 3555144 * 2 ^ 59
def prefixEnd_3555144 : Nat := 4983230072969 + 3 ^ 40 * 3555144 * 2
def baseEnd_3555144 : Nat := 405666148432876381433377

theorem tailTrace_3555144 : CollatzResearch.WordTrace tailWord_3555144 prefixEnd_3555144 405666148432876381433377 := by
  unfold tailWord_3555144
  simp only [CollatzResearch.WordTrace]
  refine ⟨64833377116163966550508243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86444502821551955400677657 64833377116163966550508243)
  ·
    refine ⟨97250065674245949825762365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64833377116163966550508243 97250065674245949825762365)
    ·
      refine ⟨36468774627842231184660887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97250065674245949825762365 36468774627842231184660887)
      ·
        refine ⟨54703161941763346776991331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36468774627842231184660887 54703161941763346776991331)
        ·
          refine ⟨82054742912645020165486997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54703161941763346776991331 82054742912645020165486997)
          ·
            refine ⟨3846316074030235320257203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 82054742912645020165486997 3846316074030235320257203)
            ·
              refine ⟨5769474111045352980385805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3846316074030235320257203 5769474111045352980385805)
              ·
                refine ⟨2163552791642007367644677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5769474111045352980385805 2163552791642007367644677)
                ·
                  refine ⟨405666148432876381433377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2163552791642007367644677 405666148432876381433377)
                  ·
                    rfl

theorem cell22_3555144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 1, 3, 4].length) (baseStart_3555144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3555144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3555144 prefixEnd_3555144 := by exact prefixLift 3555144
  have htrace : WordTrace (prefixWord ++ tailWord_3555144) baseStart_3555144 baseEnd_3555144 := by
    simpa [prefixWord, tailWord_3555144, baseEnd_3555144] using wordTrace_append hprefix tailTrace_3555144
  have hstable : (prefixWord ++ tailWord_3555144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3555144).length < 2 ^ (prefixWord ++ tailWord_3555144).sum := by decide
  have hdescent : baseEnd_3555144 < baseStart_3555144 := by decide
  rcases family_descends (prefixWord ++ tailWord_3555144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3555157 : List Nat := [1, 3, 2, 2, 2, 3, 1, 2, 2, 4]
def baseStart_3555157 : Nat := 118140960795 + 3555157 * 2 ^ 59
def prefixEnd_3555157 : Nat := 4983230072969 + 3 ^ 40 * 3555157 * 2
def baseEnd_3555157 : Nat := 1217002895464301443725091

theorem tailTrace_3555157 : CollatzResearch.WordTrace tailWord_3555157 prefixEnd_3555157 1217002895464301443725091 := by
  unfold tailWord_3555157
  simp only [CollatzResearch.WordTrace]
  refine ⟨129667228381280836321239725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86444818920853890880826483 129667228381280836321239725)
  ·
    refine ⟨48625210642980313620464897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129667228381280836321239725 48625210642980313620464897)
    ·
      refine ⟨36468907982235235215348673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48625210642980313620464897 36468907982235235215348673)
      ·
        refine ⟨27351680986676426411511505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36468907982235235215348673 27351680986676426411511505)
        ·
          refine ⟨20513760740007319808633629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27351680986676426411511505 20513760740007319808633629)
          ·
            refine ⟨7692660277502744928237611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20513760740007319808633629 7692660277502744928237611)
            ·
              refine ⟨11538990416254117392356417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7692660277502744928237611 11538990416254117392356417)
              ·
                refine ⟨8654242812190588044267313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11538990416254117392356417 8654242812190588044267313)
                ·
                  refine ⟨6490682109142941033200485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8654242812190588044267313 6490682109142941033200485)
                  ·
                    refine ⟨1217002895464301443725091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6490682109142941033200485 1217002895464301443725091)
                    ·
                      rfl

theorem cell22_3555157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 2, 2, 4].length) (baseStart_3555157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3555157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3555157 prefixEnd_3555157 := by exact prefixLift 3555157
  have htrace : WordTrace (prefixWord ++ tailWord_3555157) baseStart_3555157 baseEnd_3555157 := by
    simpa [prefixWord, tailWord_3555157, baseEnd_3555157] using wordTrace_append hprefix tailTrace_3555157
  have hstable : (prefixWord ++ tailWord_3555157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3555157).length < 2 ^ (prefixWord ++ tailWord_3555157).sum := by decide
  have hdescent : baseEnd_3555157 < baseStart_3555157 := by decide
  rcases family_descends (prefixWord ++ tailWord_3555157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3555172 : List Nat := [2, 3, 1, 1, 5, 1, 2, 7]
def baseStart_3555172 : Nat := 118140960795 + 3555172 * 2 ^ 59
def prefixEnd_3555172 : Nat := 4983230072969 + 3 ^ 40 * 3555172 * 2
def baseEnd_3555172 : Nat := 135223114474538489400005

theorem tailTrace_3555172 : CollatzResearch.WordTrace tailWord_3555172 prefixEnd_3555172 135223114474538489400005 := by
  unfold tailWord_3555172
  simp only [CollatzResearch.WordTrace]
  refine ⟨64833887738113246941517885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86445183650817662588690513 64833887738113246941517885)
  ·
    refine ⟨24312707901792467603069207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64833887738113246941517885 24312707901792467603069207)
    ·
      refine ⟨36469061852688701404603811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24312707901792467603069207 36469061852688701404603811)
      ·
        refine ⟨54703592779033052106905717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36469061852688701404603811 54703592779033052106905717)
        ·
          refine ⟨5128461823034348635022411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54703592779033052106905717 5128461823034348635022411)
          ·
            refine ⟨7692692734551522952533617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5128461823034348635022411 7692692734551522952533617)
            ·
              refine ⟨5769519550913642214400213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7692692734551522952533617 5769519550913642214400213)
              ·
                refine ⟨135223114474538489400005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5769519550913642214400213 135223114474538489400005)
                ·
                  rfl

theorem cell22_3555172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 2, 7].length) (baseStart_3555172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3555172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3555172 prefixEnd_3555172 := by exact prefixLift 3555172
  have htrace : WordTrace (prefixWord ++ tailWord_3555172) baseStart_3555172 baseEnd_3555172 := by
    simpa [prefixWord, tailWord_3555172, baseEnd_3555172] using wordTrace_append hprefix tailTrace_3555172
  have hstable : (prefixWord ++ tailWord_3555172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3555172).length < 2 ^ (prefixWord ++ tailWord_3555172).sum := by decide
  have hdescent : baseEnd_3555172 < baseStart_3555172 := by decide
  rcases family_descends (prefixWord ++ tailWord_3555172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3555247 : List Nat := [1, 1, 2, 1, 2, 2, 4, 4, 1, 4]
def baseStart_3555247 : Nat := 118140960795 + 3555247 * 2 ^ 59
def prefixEnd_3555247 : Nat := 4983230072969 + 3 ^ 40 * 3555247 * 2
def baseEnd_3555247 : Nat := 1217033704303571208974815

theorem tailTrace_3555247 : CollatzResearch.WordTrace tailWord_3555247 prefixEnd_3555247 1217033704303571208974815 := by
  unfold tailWord_3555247
  simp only [CollatzResearch.WordTrace]
  refine ⟨129670510950954781692015995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86447007300636521128010663 129670510950954781692015995)
  ·
    refine ⟨194505766426432172538023993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129670510950954781692015995 194505766426432172538023993)
    ·
      refine ⟨145879324819824129403517995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194505766426432172538023993 145879324819824129403517995)
      ·
        refine ⟨218818987229736194105276993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145879324819824129403517995 218818987229736194105276993)
        ·
          refine ⟨164114240422302145578957745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218818987229736194105276993 164114240422302145578957745)
          ·
            refine ⟨123085680316726609184218309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164114240422302145578957745 123085680316726609184218309)
            ·
              refine ⟨23078565059386239222040933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 123085680316726609184218309 23078565059386239222040933)
              ·
                refine ⟨4327230948634919854132675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23078565059386239222040933 4327230948634919854132675)
                ·
                  refine ⟨6490846422952379781199013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4327230948634919854132675 6490846422952379781199013)
                  ·
                    refine ⟨1217033704303571208974815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6490846422952379781199013 1217033704303571208974815)
                    ·
                      rfl

theorem cell22_3555247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 4, 1, 4].length) (baseStart_3555247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3555247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3555247 prefixEnd_3555247 := by exact prefixLift 3555247
  have htrace : WordTrace (prefixWord ++ tailWord_3555247) baseStart_3555247 baseEnd_3555247 := by
    simpa [prefixWord, tailWord_3555247, baseEnd_3555247] using wordTrace_append hprefix tailTrace_3555247
  have hstable : (prefixWord ++ tailWord_3555247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3555247).length < 2 ^ (prefixWord ++ tailWord_3555247).sum := by decide
  have hdescent : baseEnd_3555247 < baseStart_3555247 := by decide
  rcases family_descends (prefixWord ++ tailWord_3555247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3555298 : List Nat := [3, 3, 3, 1, 2, 1, 2, 2, 1, 4]
def baseStart_3555298 : Nat := 118140960795 + 3555298 * 2 ^ 59
def prefixEnd_3555298 : Nat := 4983230072969 + 3 ^ 40 * 3555298 * 2
def baseEnd_3555298 : Nat := 1217051162645824075949659

theorem tailTrace_3555298 : CollatzResearch.WordTrace tailWord_3555298 prefixEnd_3555298 1217051162645824075949659 := by
  unfold tailWord_3555298
  simp only [CollatzResearch.WordTrace]
  refine ⟨32418092768442504350530637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86448247382513344934748365 32418092768442504350530637)
  ·
    refine ⟨12156784788165939131448989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32418092768442504350530637 12156784788165939131448989)
    ·
      refine ⟨4558794295562227174293371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12156784788165939131448989 4558794295562227174293371)
      ·
        refine ⟨6838191443343340761440057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4558794295562227174293371 6838191443343340761440057)
        ·
          refine ⟨5128643582507505571080043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6838191443343340761440057 5128643582507505571080043)
          ·
            refine ⟨7692965373761258356620065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5128643582507505571080043 7692965373761258356620065)
            ·
              refine ⟨5769724030320943767465049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7692965373761258356620065 5769724030320943767465049)
              ·
                refine ⟨4327293022740707825598787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5769724030320943767465049 4327293022740707825598787)
                ·
                  refine ⟨6490939534111061738398181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4327293022740707825598787 6490939534111061738398181)
                  ·
                    refine ⟨1217051162645824075949659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6490939534111061738398181 1217051162645824075949659)
                    ·
                      rfl

theorem cell22_3555298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_3555298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3555298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3555298 prefixEnd_3555298 := by exact prefixLift 3555298
  have htrace : WordTrace (prefixWord ++ tailWord_3555298) baseStart_3555298 baseEnd_3555298 := by
    simpa [prefixWord, tailWord_3555298, baseEnd_3555298] using wordTrace_append hprefix tailTrace_3555298
  have hstable : (prefixWord ++ tailWord_3555298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3555298).length < 2 ^ (prefixWord ++ tailWord_3555298).sum := by decide
  have hdescent : baseEnd_3555298 < baseStart_3555298 := by decide
  rcases family_descends (prefixWord ++ tailWord_3555298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3555313 : List Nat := [1, 2, 2, 2, 6, 1, 1, 3, 4]
def baseStart_3555313 : Nat := 118140960795 + 3555313 * 2 ^ 59
def prefixEnd_3555313 : Nat := 4983230072969 + 3 ^ 40 * 3555313 * 2
def baseEnd_3555313 : Nat := 405685432484123012274871

theorem tailTrace_3555313 : CollatzResearch.WordTrace tailWord_3555313 prefixEnd_3555313 405685432484123012274871 := by
  unfold tailWord_3555313
  simp only [CollatzResearch.WordTrace]
  refine ⟨129672918168715674963918593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86448612112477116642612395 129672918168715674963918593)
  ·
    refine ⟨97254688626536756222938945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129672918168715674963918593 97254688626536756222938945)
    ·
      refine ⟨72941016469902567167204209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97254688626536756222938945 72941016469902567167204209)
      ·
        refine ⟨54705762352426925375403157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72941016469902567167204209 54705762352426925375403157)
        ·
          refine ⟨2564332610270012126972023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 54705762352426925375403157 2564332610270012126972023)
          ·
            refine ⟨3846498915405018190458035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2564332610270012126972023 3846498915405018190458035)
            ·
              refine ⟨5769748373107527285687053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3846498915405018190458035 5769748373107527285687053)
              ·
                refine ⟨2163655639915322732132645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5769748373107527285687053 2163655639915322732132645)
                ·
                  refine ⟨405685432484123012274871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2163655639915322732132645 405685432484123012274871)
                  ·
                    rfl

theorem cell22_3555313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 1, 3, 4].length) (baseStart_3555313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3555313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3555313 prefixEnd_3555313 := by exact prefixLift 3555313
  have htrace : WordTrace (prefixWord ++ tailWord_3555313) baseStart_3555313 baseEnd_3555313 := by
    simpa [prefixWord, tailWord_3555313, baseEnd_3555313] using wordTrace_append hprefix tailTrace_3555313
  have hstable : (prefixWord ++ tailWord_3555313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3555313).length < 2 ^ (prefixWord ++ tailWord_3555313).sum := by decide
  have hdescent : baseEnd_3555313 < baseStart_3555313 := by decide
  rcases family_descends (prefixWord ++ tailWord_3555313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3555326 : List Nat := [4, 2, 2, 2, 1, 2, 1, 2, 2, 4]
def baseStart_3555326 : Nat := 118140960795 + 3555326 * 2 ^ 59
def prefixEnd_3555326 : Nat := 4983230072969 + 3 ^ 40 * 3555326 * 2
def baseEnd_3555326 : Nat := 1217060747618041336249573

theorem tailTrace_3555326 : CollatzResearch.WordTrace tailWord_3555326 prefixEnd_3555326 1217060747618041336249573 := by
  unfold tailWord_3555326
  simp only [CollatzResearch.WordTrace]
  refine ⟨16209174039708572273017729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86448928211779052122761221 16209174039708572273017729)
  ·
    refine ⟨12156880529781429204763297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16209174039708572273017729 12156880529781429204763297)
    ·
      refine ⟨9117660397336071903572473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12156880529781429204763297 9117660397336071903572473)
      ·
        refine ⟨6838245298002053927679355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9117660397336071903572473 6838245298002053927679355)
        ·
          refine ⟨10257367947003080891519033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6838245298002053927679355 10257367947003080891519033)
          ·
            refine ⟨7693025960252310668639275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10257367947003080891519033 7693025960252310668639275)
            ·
              refine ⟨11539538940378466002958913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7693025960252310668639275 11539538940378466002958913)
              ·
                refine ⟨8654654205283849502219185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11539538940378466002958913 8654654205283849502219185)
                ·
                  refine ⟨6490990653962887126664389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8654654205283849502219185 6490990653962887126664389)
                  ·
                    refine ⟨1217060747618041336249573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6490990653962887126664389 1217060747618041336249573)
                    ·
                      rfl

theorem cell22_3555326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_3555326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3555326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3555326 prefixEnd_3555326 := by exact prefixLift 3555326
  have htrace : WordTrace (prefixWord ++ tailWord_3555326) baseStart_3555326 baseEnd_3555326 := by
    simpa [prefixWord, tailWord_3555326, baseEnd_3555326] using wordTrace_append hprefix tailTrace_3555326
  have hstable : (prefixWord ++ tailWord_3555326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3555326).length < 2 ^ (prefixWord ++ tailWord_3555326).sum := by decide
  have hdescent : baseEnd_3555326 < baseStart_3555326 := by decide
  rcases family_descends (prefixWord ++ tailWord_3555326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3555390 : List Nat := [4, 2, 1, 3, 2, 1, 1, 4, 1, 3]
def baseStart_3555390 : Nat := 118140960795 + 3555390 * 2 ^ 59
def prefixEnd_3555390 : Nat := 4983230072969 + 3 ^ 40 * 3555390 * 2
def baseEnd_3555390 : Nat := 1217082656125966502649377

theorem tailTrace_3555390 : CollatzResearch.WordTrace tailWord_3555390 prefixEnd_3555390 1217082656125966502649377 := by
  unfold tailWord_3555390
  simp only [CollatzResearch.WordTrace]
  refine ⟨16209465823679589639308953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86450484392957811409647749 16209465823679589639308953)
  ·
    refine ⟨12157099367759692229481715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16209465823679589639308953 12157099367759692229481715)
    ·
      refine ⟨18235649051639538344222573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12157099367759692229481715 18235649051639538344222573)
      ·
        refine ⟨6838368394364826879083465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18235649051639538344222573 6838368394364826879083465)
        ·
          refine ⟨5128776295773620159312599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6838368394364826879083465 5128776295773620159312599)
          ·
            refine ⟨7693164443660430238968899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5128776295773620159312599 7693164443660430238968899)
            ·
              refine ⟨11539746665490645358453349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7693164443660430238968899 11539746665490645358453349)
              ·
                refine ⟨2163702499779496004710003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11539746665490645358453349 2163702499779496004710003)
                ·
                  refine ⟨3245553749669244007065005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2163702499779496004710003 3245553749669244007065005)
                  ·
                    refine ⟨1217082656125966502649377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3245553749669244007065005 1217082656125966502649377)
                    ·
                      rfl

theorem cell22_3555390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 4, 1, 3].length) (baseStart_3555390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3555390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3555390 prefixEnd_3555390 := by exact prefixLift 3555390
  have htrace : WordTrace (prefixWord ++ tailWord_3555390) baseStart_3555390 baseEnd_3555390 := by
    simpa [prefixWord, tailWord_3555390, baseEnd_3555390] using wordTrace_append hprefix tailTrace_3555390
  have hstable : (prefixWord ++ tailWord_3555390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3555390).length < 2 ^ (prefixWord ++ tailWord_3555390).sum := by decide
  have hdescent : baseEnd_3555390 < baseStart_3555390 := by decide
  rcases family_descends (prefixWord ++ tailWord_3555390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3555397 : List Nat := [1, 3, 1, 1, 1, 3, 1, 5, 6]
def baseStart_3555397 : Nat := 118140960795 + 3555397 * 2 ^ 59
def prefixEnd_3555397 : Nat := 4983230072969 + 3 ^ 40 * 3555397 * 2
def baseEnd_3555397 : Nat := 405695017456340272574785

theorem tailTrace_3555397 : CollatzResearch.WordTrace tailWord_3555397 prefixEnd_3555397 405695017456340272574785 := by
  unfold tailWord_3555397
  simp only [CollatzResearch.WordTrace]
  refine ⟨129675981900411357309976445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86450654600274238206650963 129675981900411357309976445)
  ·
    refine ⟨48628493212654258991241167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129675981900411357309976445 48628493212654258991241167)
    ·
      refine ⟨72942739818981388486861751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48628493212654258991241167 72942739818981388486861751)
      ·
        refine ⟨109414109728472082730292627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72942739818981388486861751 109414109728472082730292627)
        ·
          refine ⟨164121164592708124095438941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109414109728472082730292627 164121164592708124095438941)
          ·
            refine ⟨61545436722265546535789603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 164121164592708124095438941 61545436722265546535789603)
            ·
              refine ⟨92318155083398319803684405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61545436722265546535789603 92318155083398319803684405)
              ·
                refine ⟨8654827039068592481595413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 92318155083398319803684405 8654827039068592481595413)
                ·
                  refine ⟨405695017456340272574785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8654827039068592481595413 405695017456340272574785)
                  ·
                    rfl

theorem cell22_3555397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 5, 6].length) (baseStart_3555397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3555397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3555397 prefixEnd_3555397 := by exact prefixLift 3555397
  have htrace : WordTrace (prefixWord ++ tailWord_3555397) baseStart_3555397 baseEnd_3555397 := by
    simpa [prefixWord, tailWord_3555397, baseEnd_3555397] using wordTrace_append hprefix tailTrace_3555397
  have hstable : (prefixWord ++ tailWord_3555397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3555397).length < 2 ^ (prefixWord ++ tailWord_3555397).sum := by decide
  have hdescent : baseEnd_3555397 < baseStart_3555397 := by decide
  rcases family_descends (prefixWord ++ tailWord_3555397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3555429 : List Nat := [1, 3, 1, 3, 2, 2, 2, 2, 1, 5]
def baseStart_3555429 : Nat := 118140960795 + 3555429 * 2 ^ 59
def prefixEnd_3555429 : Nat := 4983230072969 + 3 ^ 40 * 3555429 * 2
def baseEnd_3555429 : Nat := 1217096006622983400924257

theorem tailTrace_3555429 : CollatzResearch.WordTrace tailWord_3555429 prefixEnd_3555429 1217096006622983400924257 := by
  unfold tailWord_3555429
  simp only [CollatzResearch.WordTrace]
  refine ⟨129677149036295426775141341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86451432690863617850094227 129677149036295426775141341)
  ·
    refine ⟨48628930888610785040678003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129677149036295426775141341 48628930888610785040678003)
    ·
      refine ⟨72943396332916177561017005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48628930888610785040678003 72943396332916177561017005)
      ·
        refine ⟨27353773624843566585381377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72943396332916177561017005 27353773624843566585381377)
        ·
          refine ⟨20515330218632674939036033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27353773624843566585381377 20515330218632674939036033)
          ·
            refine ⟨15386497663974506204277025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20515330218632674939036033 15386497663974506204277025)
            ·
              refine ⟨11539873247980879653207769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15386497663974506204277025 11539873247980879653207769)
              ·
                refine ⟨8654904935985659739905827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11539873247980879653207769 8654904935985659739905827)
                ·
                  refine ⟨12982357403978489609858741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8654904935985659739905827 12982357403978489609858741)
                  ·
                    refine ⟨1217096006622983400924257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12982357403978489609858741 1217096006622983400924257)
                    ·
                      rfl

theorem cell22_3555429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 2, 1, 5].length) (baseStart_3555429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3555429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3555429 prefixEnd_3555429 := by exact prefixLift 3555429
  have htrace : WordTrace (prefixWord ++ tailWord_3555429) baseStart_3555429 baseEnd_3555429 := by
    simpa [prefixWord, tailWord_3555429, baseEnd_3555429] using wordTrace_append hprefix tailTrace_3555429
  have hstable : (prefixWord ++ tailWord_3555429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3555429).length < 2 ^ (prefixWord ++ tailWord_3555429).sum := by decide
  have hdescent : baseEnd_3555429 < baseStart_3555429 := by decide
  rcases family_descends (prefixWord ++ tailWord_3555429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3555431 : List Nat := [1, 1, 5, 1, 1, 2, 4, 3, 4]
def baseStart_3555431 : Nat := 118140960795 + 3555431 * 2 ^ 59
def prefixEnd_3555431 : Nat := 4983230072969 + 3 ^ 40 * 3555431 * 2
def baseEnd_3555431 : Nat := 405698897087952020791417

theorem tailTrace_3555431 : CollatzResearch.WordTrace tailWord_3555431 prefixEnd_3555431 405698897087952020791417 := by
  unfold tailWord_3555431
  simp only [CollatzResearch.WordTrace]
  refine ⟨129677221982288181116714147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86451481321525454077809431 129677221982288181116714147)
  ·
    refine ⟨194515832973432271675071221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129677221982288181116714147 194515832973432271675071221)
    ·
      refine ⟨18235859341259275469537927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 194515832973432271675071221 18235859341259275469537927)
      ·
        refine ⟨27353789011888913204306891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18235859341259275469537927 27353789011888913204306891)
        ·
          refine ⟨41030683517833369806460337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27353789011888913204306891 41030683517833369806460337)
          ·
            refine ⟨30773012638375027354845253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41030683517833369806460337 30773012638375027354845253)
            ·
              refine ⟨5769939869695317629033485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30773012638375027354845253 5769939869695317629033485)
              ·
                refine ⟨2163727451135744110887557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5769939869695317629033485 2163727451135744110887557)
                ·
                  refine ⟨405698897087952020791417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2163727451135744110887557 405698897087952020791417)
                  ·
                    rfl

theorem cell22_3555431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 4, 3, 4].length) (baseStart_3555431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3555431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3555431 prefixEnd_3555431 := by exact prefixLift 3555431
  have htrace : WordTrace (prefixWord ++ tailWord_3555431) baseStart_3555431 baseEnd_3555431 := by
    simpa [prefixWord, tailWord_3555431, baseEnd_3555431] using wordTrace_append hprefix tailTrace_3555431
  have hstable : (prefixWord ++ tailWord_3555431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3555431).length < 2 ^ (prefixWord ++ tailWord_3555431).sum := by decide
  have hdescent : baseEnd_3555431 < baseStart_3555431 := by decide
  rcases family_descends (prefixWord ++ tailWord_3555431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3555474 : List Nat := [3, 2, 3, 1, 1, 1, 1, 1, 2, 7]
def baseStart_3555474 : Nat := 118140960795 + 3555474 * 2 ^ 59
def prefixEnd_3555474 : Nat := 4983230072969 + 3 ^ 40 * 3555474 * 2
def baseEnd_3555474 : Nat := 1217111411042618283549119

theorem tailTrace_3555474 : CollatzResearch.WordTrace tailWord_3555474 prefixEnd_3555474 1217111411042618283549119 := by
  unfold tailWord_3555474
  simp only [CollatzResearch.WordTrace]
  refine ⟨32419697580283099865132369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86452526880754932973686317 32419697580283099865132369)
  ·
    refine ⟨24314773185212324898849277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32419697580283099865132369 24314773185212324898849277)
    ·
      refine ⟨9118039944454621837068479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24314773185212324898849277 9118039944454621837068479)
      ·
        refine ⟨13677059916681932755602719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9118039944454621837068479 13677059916681932755602719)
        ·
          refine ⟨20515589875022899133404079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13677059916681932755602719 20515589875022899133404079)
          ·
            refine ⟨30773384812534348700106119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20515589875022899133404079 30773384812534348700106119)
            ·
              refine ⟨46160077218801523050159179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30773384812534348700106119 46160077218801523050159179)
              ·
                refine ⟨69240115828202284575238769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46160077218801523050159179 69240115828202284575238769)
                ·
                  refine ⟨51930086871151713431429077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69240115828202284575238769 51930086871151713431429077)
                  ·
                    refine ⟨1217111411042618283549119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51930086871151713431429077 1217111411042618283549119)
                    ·
                      rfl

theorem cell22_3555474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_3555474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3555474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3555474 prefixEnd_3555474 := by exact prefixLift 3555474
  have htrace : WordTrace (prefixWord ++ tailWord_3555474) baseStart_3555474 baseEnd_3555474 := by
    simpa [prefixWord, tailWord_3555474, baseEnd_3555474] using wordTrace_append hprefix tailTrace_3555474
  have hstable : (prefixWord ++ tailWord_3555474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3555474).length < 2 ^ (prefixWord ++ tailWord_3555474).sum := by decide
  have hdescent : baseEnd_3555474 < baseStart_3555474 := by decide
  rcases family_descends (prefixWord ++ tailWord_3555474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3555564 : List Nat := [2, 2, 1, 1, 2, 3, 1, 2, 3, 5]
def baseStart_3555564 : Nat := 118140960795 + 3555564 * 2 ^ 59
def prefixEnd_3555564 : Nat := 4983230072969 + 3 ^ 40 * 3555564 * 2
def baseEnd_3555564 : Nat := 1217142219881888048798843

theorem tailTrace_3555564 : CollatzResearch.WordTrace tailWord_3555564 prefixEnd_3555564 1217142219881888048798843 := by
  unfold tailWord_3555564
  simp only [CollatzResearch.WordTrace]
  refine ⟨64841036445403172415652873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86454715260537563220870497 64841036445403172415652873)
  ·
    refine ⟨48630777334052379311739655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64841036445403172415652873 48630777334052379311739655)
    ·
      refine ⟨72946166001078568967609483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48630777334052379311739655 72946166001078568967609483)
      ·
        refine ⟨109419249001617853451414225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72946166001078568967609483 109419249001617853451414225)
        ·
          refine ⟨82064436751213390088560669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109419249001617853451414225 82064436751213390088560669)
          ·
            refine ⟨30774163781705021283210251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82064436751213390088560669 30774163781705021283210251)
            ·
              refine ⟨46161245672557531924815377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30774163781705021283210251 46161245672557531924815377)
              ·
                refine ⟨34620934254418148943611533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46161245672557531924815377 34620934254418148943611533)
                ·
                  refine ⟨12982850345406805853854325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34620934254418148943611533 12982850345406805853854325)
                  ·
                    refine ⟨1217142219881888048798843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12982850345406805853854325 1217142219881888048798843)
                    ·
                      rfl

theorem cell22_3555564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 5].length) (baseStart_3555564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3555564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3555564 prefixEnd_3555564 := by exact prefixLift 3555564
  have htrace : WordTrace (prefixWord ++ tailWord_3555564) baseStart_3555564 baseEnd_3555564 := by
    simpa [prefixWord, tailWord_3555564, baseEnd_3555564] using wordTrace_append hprefix tailTrace_3555564
  have hstable : (prefixWord ++ tailWord_3555564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3555564).length < 2 ^ (prefixWord ++ tailWord_3555564).sum := by decide
  have hdescent : baseEnd_3555564 < baseStart_3555564 := by decide
  rcases family_descends (prefixWord ++ tailWord_3555564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3555594 : List Nat := [3, 1, 2, 2, 1, 1, 2, 10]
def baseStart_3555594 : Nat := 118140960795 + 3555594 * 2 ^ 59
def prefixEnd_3555594 : Nat := 4983230072969 + 3 ^ 40 * 3555594 * 2
def baseEnd_3555594 : Nat := 135239165499441996727639

theorem tailTrace_3555594 : CollatzResearch.WordTrace tailWord_3555594 prefixEnd_3555594 135239165499441996727639 := by
  unfold tailWord_3555594
  simp only [CollatzResearch.WordTrace]
  refine ⟨32420791770174414988724459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86455444720465106636598557 32420791770174414988724459)
  ·
    refine ⟨48631187655261622483086689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32420791770174414988724459 48631187655261622483086689)
    ·
      refine ⟨36473390741446216862315017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48631187655261622483086689 36473390741446216862315017)
      ·
        refine ⟨27355043056084662646736263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36473390741446216862315017 27355043056084662646736263)
        ·
          refine ⟨41032564584126993970104395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27355043056084662646736263 41032564584126993970104395)
          ·
            refine ⟨61548846876190490955156593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41032564584126993970104395 61548846876190490955156593)
            ·
              refine ⟨46161635157142868216367445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61548846876190490955156593 46161635157142868216367445)
              ·
                refine ⟨135239165499441996727639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 46161635157142868216367445 135239165499441996727639)
                ·
                  rfl

theorem cell22_3555594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 10].length) (baseStart_3555594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3555594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3555594 prefixEnd_3555594 := by exact prefixLift 3555594
  have htrace : WordTrace (prefixWord ++ tailWord_3555594) baseStart_3555594 baseEnd_3555594 := by
    simpa [prefixWord, tailWord_3555594, baseEnd_3555594] using wordTrace_append hprefix tailTrace_3555594
  have hstable : (prefixWord ++ tailWord_3555594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3555594).length < 2 ^ (prefixWord ++ tailWord_3555594).sum := by decide
  have hdescent : baseEnd_3555594 < baseStart_3555594 := by decide
  rcases family_descends (prefixWord ++ tailWord_3555594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3555615 : List Nat := [1, 1, 2, 4, 3, 3, 1, 2, 2, 3]
def baseStart_3555615 : Nat := 118140960795 + 3555615 * 2 ^ 59
def prefixEnd_3555615 : Nat := 4983230072969 + 3 ^ 40 * 3555615 * 2
def baseEnd_3555615 : Nat := 1217159678224140915773687

theorem tailTrace_3555615 : CollatzResearch.WordTrace tailWord_3555615 prefixEnd_3555615 1217159678224140915773687 := by
  unfold tailWord_3555615
  simp only [CollatzResearch.WordTrace]
  refine ⟨129683933013621580541412299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86455955342414387027608199 129683933013621580541412299)
  ·
    refine ⟨194525899520432370812118449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129683933013621580541412299 194525899520432370812118449)
    ·
      refine ⟨145894424640324278109088837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194525899520432370812118449 145894424640324278109088837)
      ·
        refine ⟨27355204620060802145454157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 145894424640324278109088837 27355204620060802145454157)
        ·
          refine ⟨10258201732522800804545309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27355204620060802145454157 10258201732522800804545309)
          ·
            refine ⟨3846825649696050301704491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10258201732522800804545309 3846825649696050301704491)
            ·
              refine ⟨5770238474544075452556737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3846825649696050301704491 5770238474544075452556737)
              ·
                refine ⟨4327678855908056589417553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5770238474544075452556737 4327678855908056589417553)
                ·
                  refine ⟨3245759141931042442063165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4327678855908056589417553 3245759141931042442063165)
                  ·
                    refine ⟨1217159678224140915773687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3245759141931042442063165 1217159678224140915773687)
                    ·
                      rfl

theorem cell22_3555615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 1, 2, 2, 3].length) (baseStart_3555615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3555615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3555615 prefixEnd_3555615 := by exact prefixLift 3555615
  have htrace : WordTrace (prefixWord ++ tailWord_3555615) baseStart_3555615 baseEnd_3555615 := by
    simpa [prefixWord, tailWord_3555615, baseEnd_3555615] using wordTrace_append hprefix tailTrace_3555615
  have hstable : (prefixWord ++ tailWord_3555615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3555615).length < 2 ^ (prefixWord ++ tailWord_3555615).sum := by decide
  have hdescent : baseEnd_3555615 < baseStart_3555615 := by decide
  rcases family_descends (prefixWord ++ tailWord_3555615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3555690 : List Nat := [3, 1, 3, 3, 1, 1, 4, 1, 5]
def baseStart_3555690 : Nat := 118140960795 + 3555690 * 2 ^ 59
def prefixEnd_3555690 : Nat := 4983230072969 + 3 ^ 40 * 3555690 * 2
def baseEnd_3555690 : Nat := 405728450752288573382819

theorem tailTrace_3555690 : CollatzResearch.WordTrace tailWord_3555690 prefixEnd_3555690 405728450752288573382819 := by
  unfold tailWord_3555690
  simp only [CollatzResearch.WordTrace]
  refine ⟨32421667122087467087598131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86457778992233245566928349 32421667122087467087598131)
  ·
    refine ⟨48632500683131200631397197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32421667122087467087598131 48632500683131200631397197)
    ·
      refine ⟨18237187756174200236773949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48632500683131200631397197 18237187756174200236773949)
      ·
        refine ⟨6838945408565325088790231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18237187756174200236773949 6838945408565325088790231)
        ·
          refine ⟨10258418112847987633185347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6838945408565325088790231 10258418112847987633185347)
          ·
            refine ⟨15387627169271981449778021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10258418112847987633185347 15387627169271981449778021)
            ·
              refine ⟨2885180094238496521833379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15387627169271981449778021 2885180094238496521833379)
              ·
                refine ⟨4327770141357744782750069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2885180094238496521833379 4327770141357744782750069)
                ·
                  refine ⟨405728450752288573382819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4327770141357744782750069 405728450752288573382819)
                  ·
                    rfl

theorem cell22_3555690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 4, 1, 5].length) (baseStart_3555690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3555690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3555690 prefixEnd_3555690 := by exact prefixLift 3555690
  have htrace : WordTrace (prefixWord ++ tailWord_3555690) baseStart_3555690 baseEnd_3555690 := by
    simpa [prefixWord, tailWord_3555690, baseEnd_3555690] using wordTrace_append hprefix tailTrace_3555690
  have hstable : (prefixWord ++ tailWord_3555690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3555690).length < 2 ^ (prefixWord ++ tailWord_3555690).sum := by decide
  have hdescent : baseEnd_3555690 < baseStart_3555690 := by decide
  rcases family_descends (prefixWord ++ tailWord_3555690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3555720 : List Nat := [2, 1, 3, 3, 1, 1, 5, 1, 1, 4]
def baseStart_3555720 : Nat := 118140960795 + 3555720 * 2 ^ 59
def prefixEnd_3555720 : Nat := 4983230072969 + 3 ^ 40 * 3555720 * 2
def baseEnd_3555720 : Nat := 1217195621869955641898365

theorem tailTrace_3555720 : CollatzResearch.WordTrace tailWord_3555720 prefixEnd_3555720 1217195621869955641898365 := by
  unfold tailWord_3555720
  simp only [CollatzResearch.WordTrace]
  refine ⟨64843881339120591736992307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86458508452160788982656409 64843881339120591736992307)
  ·
    refine ⟨97265822008680887605488461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64843881339120591736992307 97265822008680887605488461)
    ·
      refine ⟨36474683253255332852058173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97265822008680887605488461 36474683253255332852058173)
      ·
        refine ⟨13678006219970749819521815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36474683253255332852058173 13678006219970749819521815)
        ·
          refine ⟨20517009329956124729282723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13678006219970749819521815 20517009329956124729282723)
          ·
            refine ⟨30775513994934187093924085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20517009329956124729282723 30775513994934187093924085)
            ·
              refine ⟨2885204437025080040055383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30775513994934187093924085 2885204437025080040055383)
              ·
                refine ⟨4327806655537620060083075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2885204437025080040055383 4327806655537620060083075)
                ·
                  refine ⟨6491709983306430090124613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4327806655537620060083075 6491709983306430090124613)
                  ·
                    refine ⟨1217195621869955641898365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6491709983306430090124613 1217195621869955641898365)
                    ·
                      rfl

theorem cell22_3555720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 5, 1, 1, 4].length) (baseStart_3555720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3555720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3555720 prefixEnd_3555720 := by exact prefixLift 3555720
  have htrace : WordTrace (prefixWord ++ tailWord_3555720) baseStart_3555720 baseEnd_3555720 := by
    simpa [prefixWord, tailWord_3555720, baseEnd_3555720] using wordTrace_append hprefix tailTrace_3555720
  have hstable : (prefixWord ++ tailWord_3555720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3555720).length < 2 ^ (prefixWord ++ tailWord_3555720).sum := by decide
  have hdescent : baseEnd_3555720 < baseStart_3555720 := by decide
  rcases family_descends (prefixWord ++ tailWord_3555720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3555735 : List Nat := [1, 1, 3, 3, 1, 1, 6, 2, 4]
def baseStart_3555735 : Nat := 118140960795 + 3555735 * 2 ^ 59
def prefixEnd_3555735 : Nat := 4983230072969 + 3 ^ 40 * 3555735 * 2
def baseEnd_3555735 : Nat := 405733585558833534257773

theorem tailTrace_3555735 : CollatzResearch.WordTrace tailWord_3555735 prefixEnd_3555735 405733585558833534257773 := by
  unfold tailWord_3555735
  simp only [CollatzResearch.WordTrace]
  refine ⟨129688309773186841035780659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86458873182124560690520439 129688309773186841035780659)
  ·
    refine ⟨194532464659780261553670989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129688309773186841035780659 194532464659780261553670989)
    ·
      refine ⟨72949674247417598082626621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 194532464659780261553670989 72949674247417598082626621)
      ·
        refine ⟨27356127842781599280984983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72949674247417598082626621 27356127842781599280984983)
        ·
          refine ⟨41034191764172398921477475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27356127842781599280984983 41034191764172398921477475)
          ·
            refine ⟨61551287646258598382216213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41034191764172398921477475 61551287646258598382216213)
            ·
              refine ⟨2885216608418371799166385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 61551287646258598382216213 2885216608418371799166385)
              ·
                refine ⟨2163912456313778849374789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2885216608418371799166385 2163912456313778849374789)
                ·
                  refine ⟨405733585558833534257773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2163912456313778849374789 405733585558833534257773)
                  ·
                    rfl

theorem cell22_3555735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 6, 2, 4].length) (baseStart_3555735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3555735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3555735 prefixEnd_3555735 := by exact prefixLift 3555735
  have htrace : WordTrace (prefixWord ++ tailWord_3555735) baseStart_3555735 baseEnd_3555735 := by
    simpa [prefixWord, tailWord_3555735, baseEnd_3555735] using wordTrace_append hprefix tailTrace_3555735
  have hstable : (prefixWord ++ tailWord_3555735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3555735).length < 2 ^ (prefixWord ++ tailWord_3555735).sum := by decide
  have hdescent : baseEnd_3555735 < baseStart_3555735 := by decide
  rcases family_descends (prefixWord ++ tailWord_3555735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3555846 : List Nat := [6, 2, 1, 1, 1, 1, 3, 1, 3, 3]
def baseStart_3555846 : Nat := 118140960795 + 3555846 * 2 ^ 59
def prefixEnd_3555846 : Nat := 4983230072969 + 3 ^ 40 * 3555846 * 2
def baseEnd_3555846 : Nat := 1217238754244933313247979

theorem tailTrace_3555846 : CollatzResearch.WordTrace tailWord_3555846 prefixEnd_3555846 1217238754244933313247979 := by
  unfold tailWord_3555846
  simp only [CollatzResearch.WordTrace]
  refine ⟨4052886196118272093533481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 86461572183856471328714261 4052886196118272093533481)
  ·
    refine ⟨3039664647088704070150111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4052886196118272093533481 3039664647088704070150111)
    ·
      refine ⟨4559496970633056105225167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3039664647088704070150111 4559496970633056105225167)
      ·
        refine ⟨6839245455949584157837751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4559496970633056105225167 6839245455949584157837751)
        ·
          refine ⟨10258868183924376236756627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6839245455949584157837751 10258868183924376236756627)
          ·
            refine ⟨15388302275886564355134941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10258868183924376236756627 15388302275886564355134941)
            ·
              refine ⟨5770613353457461633175603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15388302275886564355134941 5770613353457461633175603)
              ·
                refine ⟨8655920030186192449763405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5770613353457461633175603 8655920030186192449763405)
                ·
                  refine ⟨3245970011319822168661277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8655920030186192449763405 3245970011319822168661277)
                  ·
                    refine ⟨1217238754244933313247979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3245970011319822168661277 1217238754244933313247979)
                    ·
                      rfl

theorem cell22_3555846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_3555846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3555846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3555846 prefixEnd_3555846 := by exact prefixLift 3555846
  have htrace : WordTrace (prefixWord ++ tailWord_3555846) baseStart_3555846 baseEnd_3555846 := by
    simpa [prefixWord, tailWord_3555846, baseEnd_3555846] using wordTrace_append hprefix tailTrace_3555846
  have hstable : (prefixWord ++ tailWord_3555846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3555846).length < 2 ^ (prefixWord ++ tailWord_3555846).sum := by decide
  have hdescent : baseEnd_3555846 < baseStart_3555846 := by decide
  rcases family_descends (prefixWord ++ tailWord_3555846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3555900 : List Nat := [2, 2, 2, 2, 3, 1, 2, 2, 2, 4]
def baseStart_3555900 : Nat := 118140960795 + 3555900 * 2 ^ 59
def prefixEnd_3555900 : Nat := 4983230072969 + 3 ^ 40 * 3555900 * 2
def baseEnd_3555900 : Nat := 1217257239548495172397813

theorem tailTrace_3555900 : CollatzResearch.WordTrace tailWord_3555900 prefixEnd_3555900 1217257239548495172397813 := by
  unfold tailWord_3555900
  simp only [CollatzResearch.WordTrace]
  refine ⟨64847163908794537107768577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86462885211726049477024769 64847163908794537107768577)
  ·
    refine ⟨48635372931595902830826433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64847163908794537107768577 48635372931595902830826433)
    ·
      refine ⟨36476529698696927123119825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48635372931595902830826433 36476529698696927123119825)
      ·
        refine ⟨27357397274022695342339869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36476529698696927123119825 27357397274022695342339869)
        ·
          refine ⟨10259023977758510753377451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27357397274022695342339869 10259023977758510753377451)
          ·
            refine ⟨15388535966637766130066177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10259023977758510753377451 15388535966637766130066177)
            ·
              refine ⟨11541401974978324597549633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15388535966637766130066177 11541401974978324597549633)
              ·
                refine ⟨8656051481233743448162225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11541401974978324597549633 8656051481233743448162225)
                ·
                  refine ⟨6492038610925307586121669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8656051481233743448162225 6492038610925307586121669)
                  ·
                    refine ⟨1217257239548495172397813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6492038610925307586121669 1217257239548495172397813)
                    ·
                      rfl

theorem cell22_3555900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 2, 2, 4].length) (baseStart_3555900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3555900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3555900 prefixEnd_3555900 := by exact prefixLift 3555900
  have htrace : WordTrace (prefixWord ++ tailWord_3555900) baseStart_3555900 baseEnd_3555900 := by
    simpa [prefixWord, tailWord_3555900, baseEnd_3555900] using wordTrace_append hprefix tailTrace_3555900
  have hstable : (prefixWord ++ tailWord_3555900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3555900).length < 2 ^ (prefixWord ++ tailWord_3555900).sum := by decide
  have hdescent : baseEnd_3555900 < baseStart_3555900 := by decide
  rcases family_descends (prefixWord ++ tailWord_3555900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3555932 : List Nat := [2, 2, 4, 1, 3, 1, 3, 6]
def baseStart_3555932 : Nat := 118140960795 + 3555932 * 2 ^ 59
def prefixEnd_3555932 : Nat := 4983230072969 + 3 ^ 40 * 3555932 * 2
def baseEnd_3555932 : Nat := 135252021533606417288635

theorem tailTrace_3555932 : CollatzResearch.WordTrace tailWord_3555932 prefixEnd_3555932 135252021533606417288635 := by
  unfold tailWord_3555932
  simp only [CollatzResearch.WordTrace]
  refine ⟨64847747476736571840351025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86463663302315429120468033 64847747476736571840351025)
  ·
    refine ⟨48635810607552428880263269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64847747476736571840351025 48635810607552428880263269)
    ·
      refine ⟨9119214488916080415049363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48635810607552428880263269 9119214488916080415049363)
      ·
        refine ⟨13678821733374120622574045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9119214488916080415049363 13678821733374120622574045)
        ·
          refine ⟨5129558150015295233465267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13678821733374120622574045 5129558150015295233465267)
          ·
            refine ⟨7694337225022942850197901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5129558150015295233465267 7694337225022942850197901)
            ·
              refine ⟨2885376459383603568824213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7694337225022942850197901 2885376459383603568824213)
              ·
                refine ⟨135252021533606417288635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2885376459383603568824213 135252021533606417288635)
                ·
                  rfl

theorem cell22_3555932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 3, 6].length) (baseStart_3555932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3555932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3555932 prefixEnd_3555932 := by exact prefixLift 3555932
  have htrace : WordTrace (prefixWord ++ tailWord_3555932) baseStart_3555932 baseEnd_3555932 := by
    simpa [prefixWord, tailWord_3555932, baseEnd_3555932] using wordTrace_append hprefix tailTrace_3555932
  have hstable : (prefixWord ++ tailWord_3555932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3555932).length < 2 ^ (prefixWord ++ tailWord_3555932).sum := by decide
  have hdescent : baseEnd_3555932 < baseStart_3555932 := by decide
  rcases family_descends (prefixWord ++ tailWord_3555932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3555943 : List Nat := [1, 1, 5, 1, 1, 1, 1, 4, 7]
def baseStart_3555943 : Nat := 118140960795 + 3555943 * 2 ^ 59
def prefixEnd_3555943 : Nat := 4983230072969 + 3 ^ 40 * 3555943 * 2
def baseEnd_3555943 : Nat := 405757319775752464524227

theorem tailTrace_3555943 : CollatzResearch.WordTrace tailWord_3555943 prefixEnd_3555943 405757319775752464524227 := by
  unfold tailWord_3555943
  simp only [CollatzResearch.WordTrace]
  refine ⟨129695896156433292559352483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86463930770955528372901655 129695896156433292559352483)
  ·
    refine ⟨194543844234649938839028725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129695896156433292559352483 194543844234649938839028725)
    ·
      refine ⟨18238485396998431766158943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 194543844234649938839028725 18238485396998431766158943)
      ·
        refine ⟨27357728095497647649238415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18238485396998431766158943 27357728095497647649238415)
        ·
          refine ⟨41036592143246471473857623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27357728095497647649238415 41036592143246471473857623)
          ·
            refine ⟨61554888214869707210786435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41036592143246471473857623 61554888214869707210786435)
            ·
              refine ⟨92332332322304560816179653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61554888214869707210786435 92332332322304560816179653)
              ·
                refine ⟨17312312310432105153033685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 92332332322304560816179653 17312312310432105153033685)
                ·
                  refine ⟨405757319775752464524227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17312312310432105153033685 405757319775752464524227)
                  ·
                    rfl

theorem cell22_3555943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 4, 7].length) (baseStart_3555943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3555943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3555943 prefixEnd_3555943 := by exact prefixLift 3555943
  have htrace : WordTrace (prefixWord ++ tailWord_3555943) baseStart_3555943 baseEnd_3555943 := by
    simpa [prefixWord, tailWord_3555943, baseEnd_3555943] using wordTrace_append hprefix tailTrace_3555943
  have hstable : (prefixWord ++ tailWord_3555943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3555943).length < 2 ^ (prefixWord ++ tailWord_3555943).sum := by decide
  have hdescent : baseEnd_3555943 < baseStart_3555943 := by decide
  rcases family_descends (prefixWord ++ tailWord_3555943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3555970 : List Nat := [3, 4, 3, 1, 1, 1, 3, 1, 2, 3]
def baseStart_3555970 : Nat := 118140960795 + 3555970 * 2 ^ 59
def prefixEnd_3555970 : Nat := 4983230072969 + 3 ^ 40 * 3555970 * 2
def baseEnd_3555970 : Nat := 1217281201979038323147599

theorem tailTrace_3555970 : CollatzResearch.WordTrace tailWord_3555970 prefixEnd_3555970 1217281201979038323147599 := by
  unfold tailWord_3555970
  simp only [CollatzResearch.WordTrace]
  refine ⟨32424220231833869042646341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86464587284890317447056909 32424220231833869042646341)
  ·
    refine ⟨6079541293468850445496189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32424220231833869042646341 6079541293468850445496189)
    ·
      refine ⟨2279827985050818917061071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6079541293468850445496189 2279827985050818917061071)
      ·
        refine ⟨3419741977576228375591607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2279827985050818917061071 3419741977576228375591607)
        ·
          refine ⟨5129612966364342563387411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3419741977576228375591607 5129612966364342563387411)
          ·
            refine ⟨7694419449546513845081117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5129612966364342563387411 7694419449546513845081117)
            ·
              refine ⟨2885407293579942691905419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7694419449546513845081117 2885407293579942691905419)
              ·
                refine ⟨4328110940369914037858129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2885407293579942691905419 4328110940369914037858129)
                ·
                  refine ⟨3246083205277435528393597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4328110940369914037858129 3246083205277435528393597)
                  ·
                    refine ⟨1217281201979038323147599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3246083205277435528393597 1217281201979038323147599)
                    ·
                      rfl

theorem cell22_3555970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_3555970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3555970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3555970 prefixEnd_3555970 := by exact prefixLift 3555970
  have htrace : WordTrace (prefixWord ++ tailWord_3555970) baseStart_3555970 baseEnd_3555970 := by
    simpa [prefixWord, tailWord_3555970, baseEnd_3555970] using wordTrace_append hprefix tailTrace_3555970
  have hstable : (prefixWord ++ tailWord_3555970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3555970).length < 2 ^ (prefixWord ++ tailWord_3555970).sum := by decide
  have hdescent : baseEnd_3555970 < baseStart_3555970 := by decide
  rcases family_descends (prefixWord ++ tailWord_3555970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3556110 : List Nat := [4, 1, 1, 2, 1, 1, 1, 1, 3, 7]
def baseStart_3556110 : Nat := 118140960795 + 3556110 * 2 ^ 59
def prefixEnd_3556110 : Nat := 4983230072969 + 3 ^ 40 * 3556110 * 2
def baseEnd_3556110 : Nat := 1217329126840124624647169

theorem tailTrace_3556110 : CollatzResearch.WordTrace tailWord_3556110 prefixEnd_3556110 1217329126840124624647169 := by
  unfold tailWord_3556110
  simp only [CollatzResearch.WordTrace]
  refine ⟨16212748393353535010085223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86467991431218853387121189 16212748393353535010085223)
  ·
    refine ⟨24319122590030302515127835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16212748393353535010085223 24319122590030302515127835)
    ·
      refine ⟨36478683885045453772691753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24319122590030302515127835 36478683885045453772691753)
      ·
        refine ⟨27359012913784090329518815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36478683885045453772691753 27359012913784090329518815)
        ·
          refine ⟨41038519370676135494278223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27359012913784090329518815 41038519370676135494278223)
          ·
            refine ⟨61557779056014203241417335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41038519370676135494278223 61557779056014203241417335)
            ·
              refine ⟨92336668584021304862126003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61557779056014203241417335 92336668584021304862126003)
              ·
                refine ⟨138505002876031957293189005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92336668584021304862126003 138505002876031957293189005)
                ·
                  refine ⟨51939376078511983984945877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 138505002876031957293189005 51939376078511983984945877)
                  ·
                    refine ⟨1217329126840124624647169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51939376078511983984945877 1217329126840124624647169)
                    ·
                      rfl

theorem cell22_3556110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 3, 7].length) (baseStart_3556110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3556110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3556110 prefixEnd_3556110 := by exact prefixLift 3556110
  have htrace : WordTrace (prefixWord ++ tailWord_3556110) baseStart_3556110 baseEnd_3556110 := by
    simpa [prefixWord, tailWord_3556110, baseEnd_3556110] using wordTrace_append hprefix tailTrace_3556110
  have hstable : (prefixWord ++ tailWord_3556110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3556110).length < 2 ^ (prefixWord ++ tailWord_3556110).sum := by decide
  have hdescent : baseEnd_3556110 < baseStart_3556110 := by decide
  rcases family_descends (prefixWord ++ tailWord_3556110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3556159 : List Nat := [1, 1, 2, 2, 5, 2, 2, 2, 1, 4]
def baseStart_3556159 : Nat := 118140960795 + 3556159 * 2 ^ 59
def prefixEnd_3556159 : Nat := 4983230072969 + 3 ^ 40 * 3556159 * 2
def baseEnd_3556159 : Nat := 1217345900541504830172019

theorem tailTrace_3556159 : CollatzResearch.WordTrace tailWord_3556159 prefixEnd_3556159 1217345900541504830172019 := by
  unfold tailWord_3556159
  simp only [CollatzResearch.WordTrace]
  refine ⟨129703774323650761449215531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86469182882433840966143687 129703774323650761449215531)
  ·
    refine ⟨194555661485476142173823297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129703774323650761449215531 194555661485476142173823297)
    ·
      refine ⟨145916746114107106630367473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194555661485476142173823297 145916746114107106630367473)
      ·
        refine ⟨109437559585580329972775605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145916746114107106630367473 109437559585580329972775605)
        ·
          refine ⟨10259771211148155934947713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 109437559585580329972775605 10259771211148155934947713)
          ·
            refine ⟨7694828408361116951210785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10259771211148155934947713 7694828408361116951210785)
            ·
              refine ⟨5771121306270837713408089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7694828408361116951210785 5771121306270837713408089)
              ·
                refine ⟨4328340979703128285056067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5771121306270837713408089 4328340979703128285056067)
                ·
                  refine ⟨6492511469554692427584101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4328340979703128285056067 6492511469554692427584101)
                  ·
                    refine ⟨1217345900541504830172019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6492511469554692427584101 1217345900541504830172019)
                    ·
                      rfl

theorem cell22_3556159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 2, 2, 1, 4].length) (baseStart_3556159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3556159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3556159 prefixEnd_3556159 := by exact prefixLift 3556159
  have htrace : WordTrace (prefixWord ++ tailWord_3556159) baseStart_3556159 baseEnd_3556159 := by
    simpa [prefixWord, tailWord_3556159, baseEnd_3556159] using wordTrace_append hprefix tailTrace_3556159
  have hstable : (prefixWord ++ tailWord_3556159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3556159).length < 2 ^ (prefixWord ++ tailWord_3556159).sum := by decide
  have hdescent : baseEnd_3556159 < baseStart_3556159 := by decide
  rcases family_descends (prefixWord ++ tailWord_3556159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3556185 : List Nat := [1, 2, 1, 2, 2, 4, 10]
def baseStart_3556185 : Nat := 118140960795 + 3556185 * 2 ^ 59
def prefixEnd_3556185 : Nat := 4983230072969 + 3 ^ 40 * 3556185 * 2
def baseEnd_3556185 : Nat := 45087214847142571445257

theorem tailTrace_3556185 : CollatzResearch.WordTrace tailWord_3556185 prefixEnd_3556185 45087214847142571445257 := by
  unfold tailWord_3556185
  simp only [CollatzResearch.WordTrace]
  refine ⟨129704722621556567889662009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86469815081037711926441339 129704722621556567889662009)
  ·
    refine ⟨97278541966167425917246507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129704722621556567889662009 97278541966167425917246507)
    ·
      refine ⟨145917812949251138875869761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97278541966167425917246507 145917812949251138875869761)
      ·
        refine ⟨109438359711938354156902321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145917812949251138875869761 109438359711938354156902321)
        ·
          refine ⟨82078769783953765617676741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109438359711938354156902321 82078769783953765617676741)
          ·
            refine ⟨15389769334491331053314389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82078769783953765617676741 15389769334491331053314389)
            ·
              refine ⟨45087214847142571445257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 15389769334491331053314389 45087214847142571445257)
              ·
                rfl

theorem cell22_3556185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 10].length) (baseStart_3556185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3556185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3556185 prefixEnd_3556185 := by exact prefixLift 3556185
  have htrace : WordTrace (prefixWord ++ tailWord_3556185) baseStart_3556185 baseEnd_3556185 := by
    simpa [prefixWord, tailWord_3556185, baseEnd_3556185] using wordTrace_append hprefix tailTrace_3556185
  have hstable : (prefixWord ++ tailWord_3556185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3556185).length < 2 ^ (prefixWord ++ tailWord_3556185).sum := by decide
  have hdescent : baseEnd_3556185 < baseStart_3556185 := by decide
  rcases family_descends (prefixWord ++ tailWord_3556185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3556375 : List Nat := [1, 1, 3, 5, 1, 3, 2, 1, 2, 3]
def baseStart_3556375 : Nat := 118140960795 + 3556375 * 2 ^ 59
def prefixEnd_3556375 : Nat := 4983230072969 + 3 ^ 40 * 3556375 * 2
def baseEnd_3556375 : Nat := 1217419841755752266771357

theorem tailTrace_3556375 : CollatzResearch.WordTrace tailWord_3556375 prefixEnd_3556375 1217419841755752266771357 := by
  unfold tailWord_3556375
  simp only [CollatzResearch.WordTrace]
  refine ⟨129711652490868230339078579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86474434993912153559385719 129711652490868230339078579)
  ·
    refine ⟨194567478736302345508617869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129711652490868230339078579 194567478736302345508617869)
    ·
      refine ⟨72962804526113379565731701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 194567478736302345508617869 72962804526113379565731701)
      ·
        refine ⟨6840262924323129334287347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 72962804526113379565731701 6840262924323129334287347)
        ·
          refine ⟨10260394386484694001431021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6840262924323129334287347 10260394386484694001431021)
          ·
            refine ⟨3847647894931760250536633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10260394386484694001431021 3847647894931760250536633)
            ·
              refine ⟨2885735921198820187902475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3847647894931760250536633 2885735921198820187902475)
              ·
                refine ⟨4328603881798230281853713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2885735921198820187902475 4328603881798230281853713)
                ·
                  refine ⟨3246452911348672711390285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4328603881798230281853713 3246452911348672711390285)
                  ·
                    refine ⟨1217419841755752266771357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3246452911348672711390285 1217419841755752266771357)
                    ·
                      rfl

theorem cell22_3556375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 2, 1, 2, 3].length) (baseStart_3556375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3556375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3556375 prefixEnd_3556375 := by exact prefixLift 3556375
  have htrace : WordTrace (prefixWord ++ tailWord_3556375) baseStart_3556375 baseEnd_3556375 := by
    simpa [prefixWord, tailWord_3556375, baseEnd_3556375] using wordTrace_append hprefix tailTrace_3556375
  have hstable : (prefixWord ++ tailWord_3556375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3556375).length < 2 ^ (prefixWord ++ tailWord_3556375).sum := by decide
  have hdescent : baseEnd_3556375 < baseStart_3556375 := by decide
  rcases family_descends (prefixWord ++ tailWord_3556375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3556476 : List Nat := [2, 2, 2, 1, 1, 3, 3, 1, 4, 3]
def baseStart_3556476 : Nat := 118140960795 + 3556476 * 2 ^ 59
def prefixEnd_3556476 : Nat := 4983230072969 + 3 ^ 40 * 3556476 * 2
def baseEnd_3556476 : Nat := 1217454416119821669996047

theorem tailTrace_3556476 : CollatzResearch.WordTrace tailWord_3556476 prefixEnd_3556476 1217454416119821669996047 := by
  unfold tailWord_3556476
  simp only [CollatzResearch.WordTrace]
  refine ⟨64857668131751162294252641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86476890842334883059003521 64857668131751162294252641)
  ·
    refine ⟨48643251098813371720689481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64857668131751162294252641 48643251098813371720689481)
    ·
      refine ⟨36482438324110028790517111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48643251098813371720689481 36482438324110028790517111)
      ·
        refine ⟨54723657486165043185775667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36482438324110028790517111 54723657486165043185775667)
        ·
          refine ⟨82085486229247564778663501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54723657486165043185775667 82085486229247564778663501)
          ·
            refine ⟨30782057335967836791998813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82085486229247564778663501 30782057335967836791998813)
            ·
              refine ⟨11543271500987938796999555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30782057335967836791998813 11543271500987938796999555)
              ·
                refine ⟨17314907251481908195499333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11543271500987938796999555 17314907251481908195499333)
                ·
                  refine ⟨3246545109652857786656125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17314907251481908195499333 3246545109652857786656125)
                  ·
                    refine ⟨1217454416119821669996047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3246545109652857786656125 1217454416119821669996047)
                    ·
                      rfl

theorem cell22_3556476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 1, 4, 3].length) (baseStart_3556476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3556476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3556476 prefixEnd_3556476 := by exact prefixLift 3556476
  have htrace : WordTrace (prefixWord ++ tailWord_3556476) baseStart_3556476 baseEnd_3556476 := by
    simpa [prefixWord, tailWord_3556476, baseEnd_3556476] using wordTrace_append hprefix tailTrace_3556476
  have hstable : (prefixWord ++ tailWord_3556476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3556476).length < 2 ^ (prefixWord ++ tailWord_3556476).sum := by decide
  have hdescent : baseEnd_3556476 < baseStart_3556476 := by decide
  rcases family_descends (prefixWord ++ tailWord_3556476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3556506 : List Nat := [3, 1, 1, 5, 1, 2, 1, 8]
def baseStart_3556506 : Nat := 118140960795 + 3556506 * 2 ^ 59
def prefixEnd_3556506 : Nat := 4983230072969 + 3 ^ 40 * 3556506 * 2
def baseEnd_3556506 : Nat := 135273853970323510193995

theorem tailTrace_3556506 : CollatzResearch.WordTrace tailWord_3556506 prefixEnd_3556506 135273853970323510193995 := by
  unfold tailWord_3556506
  simp only [CollatzResearch.WordTrace]
  refine ⟨32429107613348409928024343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86477620302262426474731581 32429107613348409928024343)
  ·
    refine ⟨48643661420022614892036515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32429107613348409928024343 48643661420022614892036515)
    ·
      refine ⟨72965492130033922338054773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48643661420022614892036515 72965492130033922338054773)
      ·
        refine ⟨6840514887190680219192635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 72965492130033922338054773 6840514887190680219192635)
        ·
          refine ⟨10260772330786020328788953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6840514887190680219192635 10260772330786020328788953)
          ·
            refine ⟨7695579248089515246591715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10260772330786020328788953 7695579248089515246591715)
            ·
              refine ⟨11543368872134272869887573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7695579248089515246591715 11543368872134272869887573)
              ·
                refine ⟨135273853970323510193995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11543368872134272869887573 135273853970323510193995)
                ·
                  rfl

theorem cell22_3556506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 8].length) (baseStart_3556506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3556506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3556506 prefixEnd_3556506 := by exact prefixLift 3556506
  have htrace : WordTrace (prefixWord ++ tailWord_3556506) baseStart_3556506 baseEnd_3556506 := by
    simpa [prefixWord, tailWord_3556506, baseEnd_3556506] using wordTrace_append hprefix tailTrace_3556506
  have hstable : (prefixWord ++ tailWord_3556506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3556506).length < 2 ^ (prefixWord ++ tailWord_3556506).sum := by decide
  have hdescent : baseEnd_3556506 < baseStart_3556506 := by decide
  rcases family_descends (prefixWord ++ tailWord_3556506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3556549 : List Nat := [1, 3, 1, 1, 1, 1, 3, 3, 1, 7]
def baseStart_3556549 : Nat := 118140960795 + 3556549 * 2 ^ 59
def prefixEnd_3556549 : Nat := 4983230072969 + 3 ^ 40 * 3556549 * 2
def baseEnd_3556549 : Nat := 1217479405511673812920823

theorem tailTrace_3556549 : CollatzResearch.WordTrace tailWord_3556549 prefixEnd_3556549 1217479405511673812920823 := by
  unfold tailWord_3556549
  simp only [CollatzResearch.WordTrace]
  refine ⟨129717998792237858055912701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86478665861491905370608467 129717998792237858055912701)
  ·
    refine ⟨48644249547089196770967263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129717998792237858055912701 48644249547089196770967263)
    ·
      refine ⟨72966374320633795156450895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48644249547089196770967263 72966374320633795156450895)
      ·
        refine ⟨109449561480950692734676343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72966374320633795156450895 109449561480950692734676343)
        ·
          refine ⟨164174342221426039102014515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109449561480950692734676343 164174342221426039102014515)
          ·
            refine ⟨246261513332139058653021773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164174342221426039102014515 246261513332139058653021773)
            ·
              refine ⟨92348067499552146994883165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 246261513332139058653021773 92348067499552146994883165)
              ·
                refine ⟨34630525312332055123081187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92348067499552146994883165 34630525312332055123081187)
                ·
                  refine ⟨51945787968498082684621781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34630525312332055123081187 51945787968498082684621781)
                  ·
                    refine ⟨1217479405511673812920823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51945787968498082684621781 1217479405511673812920823)
                    ·
                      rfl

theorem cell22_3556549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 3, 1, 7].length) (baseStart_3556549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3556549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3556549 prefixEnd_3556549 := by exact prefixLift 3556549
  have htrace : WordTrace (prefixWord ++ tailWord_3556549) baseStart_3556549 baseEnd_3556549 := by
    simpa [prefixWord, tailWord_3556549, baseEnd_3556549] using wordTrace_append hprefix tailTrace_3556549
  have hstable : (prefixWord ++ tailWord_3556549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3556549).length < 2 ^ (prefixWord ++ tailWord_3556549).sum := by decide
  have hdescent : baseEnd_3556549 < baseStart_3556549 := by decide
  rcases family_descends (prefixWord ++ tailWord_3556549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3556589 : List Nat := [1, 5, 1, 2, 2, 3, 2, 2, 1, 3]
def baseStart_3556589 : Nat := 118140960795 + 3556589 * 2 ^ 59
def prefixEnd_3556589 : Nat := 4983230072969 + 3 ^ 40 * 3556589 * 2
def baseEnd_3556589 : Nat := 1217493098329127041920701

theorem tailTrace_3556589 : CollatzResearch.WordTrace tailWord_3556589 prefixEnd_3556589 1217493098329127041920701 := by
  unfold tailWord_3556589
  simp only [CollatzResearch.WordTrace]
  refine ⟨129719457712092944887368821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86479638474728629924912547 129719457712092944887368821)
  ·
    refine ⟨12161199160508713583190827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 129719457712092944887368821 12161199160508713583190827)
    ·
      refine ⟨18241798740763070374786241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12161199160508713583190827 18241798740763070374786241)
      ·
        refine ⟨13681349055572302781089681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18241798740763070374786241 13681349055572302781089681)
        ·
          refine ⟨10261011791679227085817261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13681349055572302781089681 10261011791679227085817261)
          ·
            refine ⟨3847879421879710157181473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10261011791679227085817261 3847879421879710157181473)
            ·
              refine ⟨2885909566409782617886105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3847879421879710157181473 2885909566409782617886105)
              ·
                refine ⟨2164432174807336963414579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2885909566409782617886105 2164432174807336963414579)
                ·
                  refine ⟨3246648262211005445121869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2164432174807336963414579 3246648262211005445121869)
                  ·
                    refine ⟨1217493098329127041920701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3246648262211005445121869 1217493098329127041920701)
                    ·
                      rfl

theorem cell22_3556589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 2, 2, 1, 3].length) (baseStart_3556589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3556589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3556589 prefixEnd_3556589 := by exact prefixLift 3556589
  have htrace : WordTrace (prefixWord ++ tailWord_3556589) baseStart_3556589 baseEnd_3556589 := by
    simpa [prefixWord, tailWord_3556589, baseEnd_3556589] using wordTrace_append hprefix tailTrace_3556589
  have hstable : (prefixWord ++ tailWord_3556589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3556589).length < 2 ^ (prefixWord ++ tailWord_3556589).sum := by decide
  have hdescent : baseEnd_3556589 < baseStart_3556589 := by decide
  rcases family_descends (prefixWord ++ tailWord_3556589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3556611 : List Nat := [1, 1, 1, 3, 2, 4, 1, 3, 1, 5]
def baseStart_3556611 : Nat := 118140960795 + 3556611 * 2 ^ 59
def prefixEnd_3556611 : Nat := 4983230072969 + 3 ^ 40 * 3556611 * 2
def baseEnd_3556611 : Nat := 1217500629378726317870633

theorem tailTrace_3556611 : CollatzResearch.WordTrace tailWord_3556611 prefixEnd_3556611 1217500629378726317870633 := by
  unfold tailWord_3556611
  simp only [CollatzResearch.WordTrace]
  refine ⟨129720260118013242644669687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86480173412008828429779791 129720260118013242644669687)
  ·
    refine ⟨194580390177019863967004531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129720260118013242644669687 194580390177019863967004531)
    ·
      refine ⟨291870585265529795950506797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194580390177019863967004531 291870585265529795950506797)
      ·
        refine ⟨109451469474573673481440049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 291870585265529795950506797 109451469474573673481440049)
        ·
          refine ⟨82088602105930255111080037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109451469474573673481440049 82088602105930255111080037)
          ·
            refine ⟨15391612894861922833327507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82088602105930255111080037 15391612894861922833327507)
            ·
              refine ⟨23087419342292884249991261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15391612894861922833327507 23087419342292884249991261)
              ·
                refine ⟨8657782253359831593746723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23087419342292884249991261 8657782253359831593746723)
                ·
                  refine ⟨12986673380039747390620085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8657782253359831593746723 12986673380039747390620085)
                  ·
                    refine ⟨1217500629378726317870633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12986673380039747390620085 1217500629378726317870633)
                    ·
                      rfl

theorem cell22_3556611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 3, 1, 5].length) (baseStart_3556611 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3556611 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3556611 prefixEnd_3556611 := by exact prefixLift 3556611
  have htrace : WordTrace (prefixWord ++ tailWord_3556611) baseStart_3556611 baseEnd_3556611 := by
    simpa [prefixWord, tailWord_3556611, baseEnd_3556611] using wordTrace_append hprefix tailTrace_3556611
  have hstable : (prefixWord ++ tailWord_3556611).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3556611).length < 2 ^ (prefixWord ++ tailWord_3556611).sum := by decide
  have hdescent : baseEnd_3556611 < baseStart_3556611 := by decide
  rcases family_descends (prefixWord ++ tailWord_3556611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3556645 : List Nat := [1, 3, 1, 2, 4, 1, 3, 2, 2, 3]
def baseStart_3556645 : Nat := 118140960795 + 3556645 * 2 ^ 59
def prefixEnd_3556645 : Nat := 4983230072969 + 3 ^ 40 * 3556645 * 2
def baseEnd_3556645 : Nat := 1217512268273561562520529

theorem tailTrace_3556645 : CollatzResearch.WordTrace tailWord_3556645 prefixEnd_3556645 1217512268273561562520529 := by
  unfold tailWord_3556645
  simp only [CollatzResearch.WordTrace]
  refine ⟨129721500199890066451407389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86481000133260044300938259 129721500199890066451407389)
  ·
    refine ⟨48645562574958774919277771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129721500199890066451407389 48645562574958774919277771)
    ·
      refine ⟨72968343862438162378916657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48645562574958774919277771 72968343862438162378916657)
      ·
        refine ⟨54726257896828621784187493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72968343862438162378916657 54726257896828621784187493)
        ·
          refine ⟨10261173355655366584535155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54726257896828621784187493 10261173355655366584535155)
          ·
            refine ⟨15391760033483049876802733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10261173355655366584535155 15391760033483049876802733)
            ·
              refine ⟨5771910012556143703801025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15391760033483049876802733 5771910012556143703801025)
              ·
                refine ⟨4328932509417107777850769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5771910012556143703801025 4328932509417107777850769)
                ·
                  refine ⟨3246699382062830833388077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4328932509417107777850769 3246699382062830833388077)
                  ·
                    refine ⟨1217512268273561562520529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3246699382062830833388077 1217512268273561562520529)
                    ·
                      rfl

theorem cell22_3556645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 3, 2, 2, 3].length) (baseStart_3556645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3556645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3556645 prefixEnd_3556645 := by exact prefixLift 3556645
  have htrace : WordTrace (prefixWord ++ tailWord_3556645) baseStart_3556645 baseEnd_3556645 := by
    simpa [prefixWord, tailWord_3556645, baseEnd_3556645] using wordTrace_append hprefix tailTrace_3556645
  have hstable : (prefixWord ++ tailWord_3556645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3556645).length < 2 ^ (prefixWord ++ tailWord_3556645).sum := by decide
  have hdescent : baseEnd_3556645 < baseStart_3556645 := by decide
  rcases family_descends (prefixWord ++ tailWord_3556645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3556686 : List Nat := [4, 1, 1, 1, 1, 1, 3, 1, 9]
def baseStart_3556686 : Nat := 118140960795 + 3556686 * 2 ^ 59
def prefixEnd_3556686 : Nat := 4983230072969 + 3 ^ 40 * 3556686 * 2
def baseEnd_3556686 : Nat := 405842101137150374081801

theorem tailTrace_3556686 : CollatzResearch.WordTrace tailWord_3556686 prefixEnd_3556686 405842101137150374081801 := by
  unfold tailWord_3556686
  simp only [CollatzResearch.WordTrace]
  refine ⟨16215374449092691306706239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86481997061827686969099941 16215374449092691306706239)
  ·
    refine ⟨24323061673639036960059359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16215374449092691306706239 24323061673639036960059359)
    ·
      refine ⟨36484592510458555440089039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24323061673639036960059359 36484592510458555440089039)
      ·
        refine ⟨54726888765687833160133559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36484592510458555440089039 54726888765687833160133559)
        ·
          refine ⟨82090333148531749740200339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54726888765687833160133559 82090333148531749740200339)
          ·
            refine ⟨123135499722797624610300509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82090333148531749740200339 123135499722797624610300509)
            ·
              refine ⟨46175812396049109228862691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123135499722797624610300509 46175812396049109228862691)
              ·
                refine ⟨69263718594073663843294037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46175812396049109228862691 69263718594073663843294037)
                ·
                  refine ⟨405842101137150374081801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 69263718594073663843294037 405842101137150374081801)
                  ·
                    rfl

theorem cell22_3556686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 9].length) (baseStart_3556686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3556686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3556686 prefixEnd_3556686 := by exact prefixLift 3556686
  have htrace : WordTrace (prefixWord ++ tailWord_3556686) baseStart_3556686 baseEnd_3556686 := by
    simpa [prefixWord, tailWord_3556686, baseEnd_3556686] using wordTrace_append hprefix tailTrace_3556686
  have hstable : (prefixWord ++ tailWord_3556686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3556686).length < 2 ^ (prefixWord ++ tailWord_3556686).sum := by decide
  have hdescent : baseEnd_3556686 < baseStart_3556686 := by decide
  rcases family_descends (prefixWord ++ tailWord_3556686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3556731 : List Nat := [1, 1, 1, 1, 1, 6, 2, 1, 8]
def baseStart_3556731 : Nat := 118140960795 + 3556731 * 2 ^ 59
def prefixEnd_3556731 : Nat := 4983230072969 + 3 ^ 40 * 3556731 * 2
def baseEnd_3556731 : Nat := 405847235943695334956755

theorem tailTrace_3556731 : CollatzResearch.WordTrace tailWord_3556731 prefixEnd_3556731 405847235943695334956755 := by
  unfold tailWord_3556731
  simp only [CollatzResearch.WordTrace]
  refine ⟨129724636877578503139038047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86483091251719002092692031 129724636877578503139038047)
  ·
    refine ⟨194586955316367754708557071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129724636877578503139038047 194586955316367754708557071)
    ·
      refine ⟨291880432974551632062835607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194586955316367754708557071 291880432974551632062835607)
      ·
        refine ⟨437820649461827448094253411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291880432974551632062835607 437820649461827448094253411)
        ·
          refine ⟨656730974192741172141380117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 437820649461827448094253411 656730974192741172141380117)
          ·
            refine ⟨30784264415284742444127193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 656730974192741172141380117 30784264415284742444127193)
            ·
              refine ⟨23088198311463556833095395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30784264415284742444127193 23088198311463556833095395)
              ·
                refine ⟨34632297467195335249643093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23088198311463556833095395 34632297467195335249643093)
                ·
                  refine ⟨405847235943695334956755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34632297467195335249643093 405847235943695334956755)
                  ·
                    rfl

theorem cell22_3556731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 1, 8].length) (baseStart_3556731 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3556731 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3556731 prefixEnd_3556731 := by exact prefixLift 3556731
  have htrace : WordTrace (prefixWord ++ tailWord_3556731) baseStart_3556731 baseEnd_3556731 := by
    simpa [prefixWord, tailWord_3556731, baseEnd_3556731] using wordTrace_append hprefix tailTrace_3556731
  have hstable : (prefixWord ++ tailWord_3556731).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3556731).length < 2 ^ (prefixWord ++ tailWord_3556731).sum := by decide
  have hdescent : baseEnd_3556731 < baseStart_3556731 := by decide
  rcases family_descends (prefixWord ++ tailWord_3556731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3556733 : List Nat := [1, 4, 1, 1, 2, 2, 3, 1, 3, 4]
def baseStart_3556733 : Nat := 118140960795 + 3556733 * 2 ^ 59
def prefixEnd_3556733 : Nat := 4983230072969 + 3 ^ 40 * 3556733 * 2
def baseEnd_3556733 : Nat := 1217542392471958666320259

theorem tailTrace_3556733 : CollatzResearch.WordTrace tailWord_3556733 prefixEnd_3556733 1217542392471958666320259 := by
  unfold tailWord_3556733
  simp only [CollatzResearch.WordTrace]
  refine ⟨129724709823571257480610853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86483139882380838320407235 129724709823571257480610853)
  ·
    refine ⟨24323383091919610777614535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129724709823571257480610853 24323383091919610777614535)
    ·
      refine ⟨36485074637879416166421803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24323383091919610777614535 36485074637879416166421803)
      ·
        refine ⟨54727611956819124249632705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36485074637879416166421803 54727611956819124249632705)
        ·
          refine ⟨41045708967614343187224529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54727611956819124249632705 41045708967614343187224529)
          ·
            refine ⟨30784281725710757390418397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41045708967614343187224529 30784281725710757390418397)
            ·
              refine ⟨11544105647141534021406899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30784281725710757390418397 11544105647141534021406899)
              ·
                refine ⟨17316158470712301032110349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11544105647141534021406899 17316158470712301032110349)
                ·
                  refine ⟨6493559426517112887041381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17316158470712301032110349 6493559426517112887041381)
                  ·
                    refine ⟨1217542392471958666320259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6493559426517112887041381 1217542392471958666320259)
                    ·
                      rfl

theorem cell22_3556733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 1, 3, 4].length) (baseStart_3556733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3556733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3556733 prefixEnd_3556733 := by exact prefixLift 3556733
  have htrace : WordTrace (prefixWord ++ tailWord_3556733) baseStart_3556733 baseEnd_3556733 := by
    simpa [prefixWord, tailWord_3556733, baseEnd_3556733] using wordTrace_append hprefix tailTrace_3556733
  have hstable : (prefixWord ++ tailWord_3556733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3556733).length < 2 ^ (prefixWord ++ tailWord_3556733).sum := by decide
  have hdescent : baseEnd_3556733 < baseStart_3556733 := by decide
  rcases family_descends (prefixWord ++ tailWord_3556733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3556780 : List Nat := [2, 2, 1, 1, 1, 1, 6, 3, 2, 3]
def baseStart_3556780 : Nat := 118140960795 + 3556780 * 2 ^ 59
def prefixEnd_3556780 : Nat := 4983230072969 + 3 ^ 40 * 3556780 * 2
def baseEnd_3556780 : Nat := 1217558481532466210395115

theorem tailTrace_3556780 : CollatzResearch.WordTrace tailWord_3556780 prefixEnd_3556780 1217558481532466210395115 := by
  unfold tailWord_3556780
  simp only [CollatzResearch.WordTrace]
  refine ⟨64863212027200492253785897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86484282702933989671714529 64863212027200492253785897)
  ·
    refine ⟨48647409020400369190339423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64863212027200492253785897 48647409020400369190339423)
    ·
      refine ⟨72971113530600553785509135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48647409020400369190339423 72971113530600553785509135)
      ·
        refine ⟨109456670295900830678263703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72971113530600553785509135 109456670295900830678263703)
        ·
          refine ⟨164185005443851246017395555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109456670295900830678263703 164185005443851246017395555)
          ·
            refine ⟨246277508165776869026093333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164185005443851246017395555 246277508165776869026093333)
            ·
              refine ⟨11544258195270790735598125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 246277508165776869026093333 11544258195270790735598125)
              ·
                refine ⟨4329096823226546525849297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11544258195270790735598125 4329096823226546525849297)
                ·
                  refine ⟨3246822617419909894386973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4329096823226546525849297 3246822617419909894386973)
                  ·
                    refine ⟨1217558481532466210395115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3246822617419909894386973 1217558481532466210395115)
                    ·
                      rfl

theorem cell22_3556780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 3].length) (baseStart_3556780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3556780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3556780 prefixEnd_3556780 := by exact prefixLift 3556780
  have htrace : WordTrace (prefixWord ++ tailWord_3556780) baseStart_3556780 baseEnd_3556780 := by
    simpa [prefixWord, tailWord_3556780, baseEnd_3556780] using wordTrace_append hprefix tailTrace_3556780
  have hstable : (prefixWord ++ tailWord_3556780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3556780).length < 2 ^ (prefixWord ++ tailWord_3556780).sum := by decide
  have hdescent : baseEnd_3556780 < baseStart_3556780 := by decide
  rcases family_descends (prefixWord ++ tailWord_3556780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3556825 : List Nat := [1, 2, 1, 2, 4, 2, 1, 3, 3, 3]
def baseStart_3556825 : Nat := 118140960795 + 3556825 * 2 ^ 59
def prefixEnd_3556825 : Nat := 4983230072969 + 3 ^ 40 * 3556825 * 2
def baseEnd_3556825 : Nat := 1217573885952101093019977

theorem tailTrace_3556825 : CollatzResearch.WordTrace tailWord_3556825 prefixEnd_3556825 1217573885952101093019977 := by
  unfold tailWord_3556825
  simp only [CollatzResearch.WordTrace]
  refine ⟨129728065339237957192959929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86485376892825304795306619 129728065339237957192959929)
  ·
    refine ⟨97296049004428467894719947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129728065339237957192959929 97296049004428467894719947)
    ·
      refine ⟨145944073506642701842079921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97296049004428467894719947 145944073506642701842079921)
      ·
        refine ⟨109458055129982026381559941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145944073506642701842079921 109458055129982026381559941)
        ·
          refine ⟨20523385336871629946542489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 109458055129982026381559941 20523385336871629946542489)
          ·
            refine ⟨15392539002653722459906867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20523385336871629946542489 15392539002653722459906867)
            ·
              refine ⟨23088808503980583689860301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15392539002653722459906867 23088808503980583689860301)
              ·
                refine ⟨8658303188992718883697613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23088808503980583689860301 8658303188992718883697613)
                ·
                  refine ⟨3246863695872269581386605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8658303188992718883697613 3246863695872269581386605)
                  ·
                    refine ⟨1217573885952101093019977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3246863695872269581386605 1217573885952101093019977)
                    ·
                      rfl

theorem cell22_3556825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 3, 3, 3].length) (baseStart_3556825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3556825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3556825 prefixEnd_3556825 := by exact prefixLift 3556825
  have htrace : WordTrace (prefixWord ++ tailWord_3556825) baseStart_3556825 baseEnd_3556825 := by
    simpa [prefixWord, tailWord_3556825, baseEnd_3556825] using wordTrace_append hprefix tailTrace_3556825
  have hstable : (prefixWord ++ tailWord_3556825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3556825).length < 2 ^ (prefixWord ++ tailWord_3556825).sum := by decide
  have hdescent : baseEnd_3556825 < baseStart_3556825 := by decide
  rcases family_descends (prefixWord ++ tailWord_3556825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3556876 : List Nat := [2, 2, 1, 2, 5, 1, 3, 2, 1, 3]
def baseStart_3556876 : Nat := 118140960795 + 3556876 * 2 ^ 59
def prefixEnd_3556876 : Nat := 4983230072969 + 3 ^ 40 * 3556876 * 2
def baseEnd_3556876 : Nat := 1217591344294353959994821

theorem tailTrace_3556876 : CollatzResearch.WordTrace tailWord_3556876 prefixEnd_3556876 1217591344294353959994821 := by
  unfold tailWord_3556876
  simp only [CollatzResearch.WordTrace]
  refine ⟨64864962731026596451533241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86486616974702128602044321 64864962731026596451533241)
  ·
    refine ⟨48648722048269947338649931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64864962731026596451533241 48648722048269947338649931)
    ·
      refine ⟨72973083072404921007974897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48648722048269947338649931 72973083072404921007974897)
      ·
        refine ⟨54729812304303690755981173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72973083072404921007974897 54729812304303690755981173)
        ·
          refine ⟨5130919903528471008373235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54729812304303690755981173 5130919903528471008373235)
          ·
            refine ⟨7696379855292706512559853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5130919903528471008373235 7696379855292706512559853)
            ·
              refine ⟨2886142445734764942209945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7696379855292706512559853 2886142445734764942209945)
              ·
                refine ⟨2164606834301073706657459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2886142445734764942209945 2164606834301073706657459)
                ·
                  refine ⟨3246910251451610559986189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2164606834301073706657459 3246910251451610559986189)
                  ·
                    refine ⟨1217591344294353959994821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3246910251451610559986189 1217591344294353959994821)
                    ·
                      rfl

theorem cell22_3556876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 3, 2, 1, 3].length) (baseStart_3556876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3556876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3556876 prefixEnd_3556876 := by exact prefixLift 3556876
  have htrace : WordTrace (prefixWord ++ tailWord_3556876) baseStart_3556876 baseEnd_3556876 := by
    simpa [prefixWord, tailWord_3556876, baseEnd_3556876] using wordTrace_append hprefix tailTrace_3556876
  have hstable : (prefixWord ++ tailWord_3556876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3556876).length < 2 ^ (prefixWord ++ tailWord_3556876).sum := by decide
  have hdescent : baseEnd_3556876 < baseStart_3556876 := by decide
  rcases family_descends (prefixWord ++ tailWord_3556876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3556915 : List Nat := [1, 1, 1, 2, 4, 4, 1, 2, 1, 5]
def baseStart_3556915 : Nat := 118140960795 + 3556915 * 2 ^ 59
def prefixEnd_3556915 : Nat := 4983230072969 + 3 ^ 40 * 3556915 * 2
def baseEnd_3556915 : Nat := 1217604694791370858269701

theorem tailTrace_3556915 : CollatzResearch.WordTrace tailWord_3556915 prefixEnd_3556915 1217604694791370858269701 := by
  unfold tailWord_3556915
  simp only [CollatzResearch.WordTrace]
  refine ⟨129731347908911902563736199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86487565272607935042490799 129731347908911902563736199)
  ·
    refine ⟨194597021863367853845604299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129731347908911902563736199 194597021863367853845604299)
    ·
      refine ⟨291895532795051780768406449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194597021863367853845604299 291895532795051780768406449)
      ·
        refine ⟨218921649596288835576304837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 291895532795051780768406449 218921649596288835576304837)
        ·
          refine ⟨41047809299304156670557157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 218921649596288835576304837 41047809299304156670557157)
          ·
            refine ⟨7696464243619529375729467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41047809299304156670557157 7696464243619529375729467)
            ·
              refine ⟨11544696365429294063594201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7696464243619529375729467 11544696365429294063594201)
              ·
                refine ⟨8658522274071970547695651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11544696365429294063594201 8658522274071970547695651)
                ·
                  refine ⟨12987783411107955821543477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8658522274071970547695651 12987783411107955821543477)
                  ·
                    refine ⟨1217604694791370858269701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12987783411107955821543477 1217604694791370858269701)
                    ·
                      rfl

theorem cell22_3556915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 2, 1, 5].length) (baseStart_3556915 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3556915 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3556915 prefixEnd_3556915 := by exact prefixLift 3556915
  have htrace : WordTrace (prefixWord ++ tailWord_3556915) baseStart_3556915 baseEnd_3556915 := by
    simpa [prefixWord, tailWord_3556915, baseEnd_3556915] using wordTrace_append hprefix tailTrace_3556915
  have hstable : (prefixWord ++ tailWord_3556915).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3556915).length < 2 ^ (prefixWord ++ tailWord_3556915).sum := by decide
  have hdescent : baseEnd_3556915 < baseStart_3556915 := by decide
  rcases family_descends (prefixWord ++ tailWord_3556915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3556943 : List Nat := [1, 1, 2, 1, 1, 2, 3, 2, 2, 7]
def baseStart_3556943 : Nat := 118140960795 + 3556943 * 2 ^ 59
def prefixEnd_3556943 : Nat := 4983230072969 + 3 ^ 40 * 3556943 * 2
def baseEnd_3556943 : Nat := 1217614279763588118569615

theorem tailTrace_3556943 : CollatzResearch.WordTrace tailWord_3556943 prefixEnd_3556943 1217614279763588118569615 := by
  unfold tailWord_3556943
  simp only [CollatzResearch.WordTrace]
  refine ⟨129732369152810463345755483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86488246101873642230503655 129732369152810463345755483)
  ·
    refine ⟨194598553729215695018633225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129732369152810463345755483 194598553729215695018633225)
    ·
      refine ⟨145948915296911771263974919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194598553729215695018633225 145948915296911771263974919)
      ·
        refine ⟨218923372945367656895962379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145948915296911771263974919 218923372945367656895962379)
        ·
          refine ⟨328385059418051485343943569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218923372945367656895962379 328385059418051485343943569)
          ·
            refine ⟨246288794563538614007957677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 328385059418051485343943569 246288794563538614007957677)
            ·
              refine ⟨92358297961326980252984129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 246288794563538614007957677 92358297961326980252984129)
              ·
                refine ⟨69268723470995235189738097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92358297961326980252984129 69268723470995235189738097)
                ·
                  refine ⟨51951542603246426392303573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69268723470995235189738097 51951542603246426392303573)
                  ·
                    refine ⟨1217614279763588118569615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51951542603246426392303573 1217614279763588118569615)
                    ·
                      rfl

theorem cell22_3556943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 2, 7].length) (baseStart_3556943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3556943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3556943 prefixEnd_3556943 := by exact prefixLift 3556943
  have htrace : WordTrace (prefixWord ++ tailWord_3556943) baseStart_3556943 baseEnd_3556943 := by
    simpa [prefixWord, tailWord_3556943, baseEnd_3556943] using wordTrace_append hprefix tailTrace_3556943
  have hstable : (prefixWord ++ tailWord_3556943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3556943).length < 2 ^ (prefixWord ++ tailWord_3556943).sum := by decide
  have hdescent : baseEnd_3556943 < baseStart_3556943 := by decide
  rcases family_descends (prefixWord ++ tailWord_3556943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3557052 : List Nat := [2, 2, 2, 3, 1, 2, 3, 1, 6]
def baseStart_3557052 : Nat := 118140960795 + 3557052 * 2 ^ 59
def prefixEnd_3557052 : Nat := 4983230072969 + 3 ^ 40 * 3557052 * 2
def baseEnd_3557052 : Nat := 405883864230382722531427

theorem tailTrace_3557052 : CollatzResearch.WordTrace tailWord_3557052 prefixEnd_3557052 405883864230382722531427 := by
  unfold tailWord_3557052
  simp only [CollatzResearch.WordTrace]
  refine ⟨64868172354707787480736705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86490896472943716640982273 64868172354707787480736705)
  ·
    refine ⟨48651129266030840610552529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64868172354707787480736705 48651129266030840610552529)
    ·
      refine ⟨36488346949523130457914397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48651129266030840610552529 36488346949523130457914397)
      ·
        refine ⟨13683130106071173921717899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36488346949523130457914397 13683130106071173921717899)
        ·
          refine ⟨20524695159106760882576849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13683130106071173921717899 20524695159106760882576849)
          ·
            refine ⟨15393521369330070661932637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20524695159106760882576849 15393521369330070661932637)
            ·
              refine ⟨5772570513498776498224739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15393521369330070661932637 5772570513498776498224739)
              ·
                refine ⟨8658855770248164747337109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5772570513498776498224739 8658855770248164747337109)
                ·
                  refine ⟨405883864230382722531427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8658855770248164747337109 405883864230382722531427)
                  ·
                    rfl

theorem cell22_3557052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 3, 1, 6].length) (baseStart_3557052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3557052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3557052 prefixEnd_3557052 := by exact prefixLift 3557052
  have htrace : WordTrace (prefixWord ++ tailWord_3557052) baseStart_3557052 baseEnd_3557052 := by
    simpa [prefixWord, tailWord_3557052, baseEnd_3557052] using wordTrace_append hprefix tailTrace_3557052
  have hstable : (prefixWord ++ tailWord_3557052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3557052).length < 2 ^ (prefixWord ++ tailWord_3557052).sum := by decide
  have hdescent : baseEnd_3557052 < baseStart_3557052 := by decide
  rcases family_descends (prefixWord ++ tailWord_3557052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3557058 : List Nat := [3, 5, 1, 2, 1, 1, 1, 3, 5]
def baseStart_3557058 : Nat := 118140960795 + 3557058 * 2 ^ 59
def prefixEnd_3557058 : Nat := 4983230072969 + 3 ^ 40 * 3557058 * 2
def baseEnd_3557058 : Nat := 405884548871255383981421

theorem tailTrace_3557058 : CollatzResearch.WordTrace tailWord_3557058 prefixEnd_3557058 405884548871255383981421 := by
  unfold tailWord_3557058
  simp only [CollatzResearch.WordTrace]
  refine ⟨32434140886848459496547957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86491042364929225324127885 32434140886848459496547957)
  ·
    refine ⟨3040700708142043077801371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32434140886848459496547957 3040700708142043077801371)
    ·
      refine ⟨4561051062213064616702057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3040700708142043077801371 4561051062213064616702057)
      ·
        refine ⟨3420788296659798462526543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4561051062213064616702057 3420788296659798462526543)
        ·
          refine ⟨5131182444989697693789815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3420788296659798462526543 5131182444989697693789815)
          ·
            refine ⟨7696773667484546540684723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5131182444989697693789815 7696773667484546540684723)
            ·
              refine ⟨11545160501226819811027085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7696773667484546540684723 11545160501226819811027085)
              ·
                refine ⟨4329435187960057429135157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11545160501226819811027085 4329435187960057429135157)
                ·
                  refine ⟨405884548871255383981421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4329435187960057429135157 405884548871255383981421)
                  ·
                    rfl

theorem cell22_3557058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_3557058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3557058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3557058 prefixEnd_3557058 := by exact prefixLift 3557058
  have htrace : WordTrace (prefixWord ++ tailWord_3557058) baseStart_3557058 baseEnd_3557058 := by
    simpa [prefixWord, tailWord_3557058, baseEnd_3557058] using wordTrace_append hprefix tailTrace_3557058
  have hstable : (prefixWord ++ tailWord_3557058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3557058).length < 2 ^ (prefixWord ++ tailWord_3557058).sum := by decide
  have hdescent : baseEnd_3557058 < baseStart_3557058 := by decide
  rcases family_descends (prefixWord ++ tailWord_3557058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3557080 : List Nat := [2, 1, 2, 2, 3, 1, 1, 10]
def baseStart_3557080 : Nat := 118140960795 + 3557080 * 2 ^ 59
def prefixEnd_3557080 : Nat := 4983230072969 + 3 ^ 40 * 3557080 * 2
def baseEnd_3557080 : Nat := 135295686407040603099355

theorem tailTrace_3557080 : CollatzResearch.WordTrace tailWord_3557080 prefixEnd_3557080 135295686407040603099355 := by
  unfold tailWord_3557080
  simp only [CollatzResearch.WordTrace]
  refine ⟨64868682976657067871746347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86491577302209423828995129 64868682976657067871746347)
  ·
    refine ⟨97303024464985601807619521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64868682976657067871746347 97303024464985601807619521)
    ·
      refine ⟨72977268348739201355714641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97303024464985601807619521 72977268348739201355714641)
      ·
        refine ⟨54732951261554401016785981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72977268348739201355714641 54732951261554401016785981)
        ·
          refine ⟨20524856723082900381294743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54732951261554401016785981 20524856723082900381294743)
          ·
            refine ⟨30787285084624350571942115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20524856723082900381294743 30787285084624350571942115)
            ·
              refine ⟨46180927626936525857913173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30787285084624350571942115 46180927626936525857913173)
              ·
                refine ⟨135295686407040603099355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 46180927626936525857913173 135295686407040603099355)
                ·
                  rfl

theorem cell22_3557080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 10].length) (baseStart_3557080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3557080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3557080 prefixEnd_3557080 := by exact prefixLift 3557080
  have htrace : WordTrace (prefixWord ++ tailWord_3557080) baseStart_3557080 baseEnd_3557080 := by
    simpa [prefixWord, tailWord_3557080, baseEnd_3557080] using wordTrace_append hprefix tailTrace_3557080
  have hstable : (prefixWord ++ tailWord_3557080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3557080).length < 2 ^ (prefixWord ++ tailWord_3557080).sum := by decide
  have hdescent : baseEnd_3557080 < baseStart_3557080 := by decide
  rcases family_descends (prefixWord ++ tailWord_3557080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3557082 : List Nat := [3, 1, 1, 2, 2, 3, 1, 3, 2, 4]
def baseStart_3557082 : Nat := 118140960795 + 3557082 * 2 ^ 59
def prefixEnd_3557082 : Nat := 4983230072969 + 3 ^ 40 * 3557082 * 2
def baseEnd_3557082 : Nat := 1217661862304238089344189

theorem tailTrace_3557082 : CollatzResearch.WordTrace tailWord_3557082 prefixEnd_3557082 1217661862304238089344189 := by
  unfold tailWord_3557082
  simp only [CollatzResearch.WordTrace]
  refine ⟨32434359724826722521266375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86491625932871260056710333 32434359724826722521266375)
  ·
    refine ⟨48651539587240083781899563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32434359724826722521266375 48651539587240083781899563)
    ·
      refine ⟨72977309380860125672849345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48651539587240083781899563 72977309380860125672849345)
      ·
        refine ⟨54732982035645094254637009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72977309380860125672849345 54732982035645094254637009)
        ·
          refine ⟨41049736526733820690977757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54732982035645094254637009 41049736526733820690977757)
          ·
            refine ⟨15393651197525182759116659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41049736526733820690977757 15393651197525182759116659)
            ·
              refine ⟨23090476796287774138674989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15393651197525182759116659 23090476796287774138674989)
              ·
                refine ⟨8658928798607915302003121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23090476796287774138674989 8658928798607915302003121)
                ·
                  refine ⟨6494196598955936476502341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8658928798607915302003121 6494196598955936476502341)
                  ·
                    refine ⟨1217661862304238089344189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6494196598955936476502341 1217661862304238089344189)
                    ·
                      rfl

theorem cell22_3557082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 3, 2, 4].length) (baseStart_3557082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3557082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3557082 prefixEnd_3557082 := by exact prefixLift 3557082
  have htrace : WordTrace (prefixWord ++ tailWord_3557082) baseStart_3557082 baseEnd_3557082 := by
    simpa [prefixWord, tailWord_3557082, baseEnd_3557082] using wordTrace_append hprefix tailTrace_3557082
  have hstable : (prefixWord ++ tailWord_3557082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3557082).length < 2 ^ (prefixWord ++ tailWord_3557082).sum := by decide
  have hdescent : baseEnd_3557082 < baseStart_3557082 := by decide
  rcases family_descends (prefixWord ++ tailWord_3557082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3557101 : List Nat := [1, 5, 1, 2, 1, 3, 2, 2, 2, 3]
def baseStart_3557101 : Nat := 118140960795 + 3557101 * 2 ^ 59
def prefixEnd_3557101 : Nat := 4983230072969 + 3 ^ 40 * 3557101 * 2
def baseEnd_3557101 : Nat := 1217668366392528373119131

theorem tailTrace_3557101 : CollatzResearch.WordTrace tailWord_3557101 prefixEnd_3557101 1217668366392528373119131 := by
  unfold tailWord_3557101
  simp only [CollatzResearch.WordTrace]
  refine ⟨129738131886238056330007157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86492087924158704220004771 129738131886238056330007157)
  ·
    refine ⟨12162949864334817780938171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 129738131886238056330007157 12162949864334817780938171)
    ·
      refine ⟨18244424796502226671407257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12162949864334817780938171 18244424796502226671407257)
      ·
        refine ⟨13683318597376670003555443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18244424796502226671407257 13683318597376670003555443)
        ·
          refine ⟨20524977896065005005333165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13683318597376670003555443 20524977896065005005333165)
          ·
            refine ⟨7696866711024376876999937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20524977896065005005333165 7696866711024376876999937)
            ·
              refine ⟨5772650033268282657749953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7696866711024376876999937 5772650033268282657749953)
              ·
                refine ⟨4329487524951211993312465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5772650033268282657749953 4329487524951211993312465)
                ·
                  refine ⟨3247115643713408994984349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4329487524951211993312465 3247115643713408994984349)
                  ·
                    refine ⟨1217668366392528373119131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3247115643713408994984349 1217668366392528373119131)
                    ·
                      rfl

theorem cell22_3557101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 2, 2, 2, 3].length) (baseStart_3557101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3557101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3557101 prefixEnd_3557101 := by exact prefixLift 3557101
  have htrace : WordTrace (prefixWord ++ tailWord_3557101) baseStart_3557101 baseEnd_3557101 := by
    simpa [prefixWord, tailWord_3557101, baseEnd_3557101] using wordTrace_append hprefix tailTrace_3557101
  have hstable : (prefixWord ++ tailWord_3557101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3557101).length < 2 ^ (prefixWord ++ tailWord_3557101).sum := by decide
  have hdescent : baseEnd_3557101 < baseStart_3557101 := by decide
  rcases family_descends (prefixWord ++ tailWord_3557101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3557125 : List Nat := [1, 3, 1, 1, 2, 1, 1, 1, 11]
def baseStart_3557125 : Nat := 118140960795 + 3557125 * 2 ^ 59
def prefixEnd_3557125 : Nat := 4983230072969 + 3 ^ 40 * 3557125 * 2
def baseEnd_3557125 : Nat := 405892194027666770173019

theorem tailTrace_3557125 : CollatzResearch.WordTrace tailWord_3557125 prefixEnd_3557125 405892194027666770173019 := by
  unfold tailWord_3557125
  simp only [CollatzResearch.WordTrace]
  refine ⟨129739007238151108428880829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86492671492100738952587219 129739007238151108428880829)
  ·
    refine ⟨48652127714306665660830311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129739007238151108428880829 48652127714306665660830311)
    ·
      refine ⟨72978191571459998491245467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48652127714306665660830311 72978191571459998491245467)
      ·
        refine ⟨109467287357189997736868201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72978191571459998491245467 109467287357189997736868201)
        ·
          refine ⟨82100465517892498302651151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109467287357189997736868201 82100465517892498302651151)
          ·
            refine ⟨123150698276838747453976727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82100465517892498302651151 123150698276838747453976727)
            ·
              refine ⟨184726047415258121180965091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123150698276838747453976727 184726047415258121180965091)
              ·
                refine ⟨277089071122887181771447637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 184726047415258121180965091 277089071122887181771447637)
                ·
                  refine ⟨405892194027666770173019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 277089071122887181771447637 405892194027666770173019)
                  ·
                    rfl

theorem cell22_3557125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 11].length) (baseStart_3557125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3557125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3557125 prefixEnd_3557125 := by exact prefixLift 3557125
  have htrace : WordTrace (prefixWord ++ tailWord_3557125) baseStart_3557125 baseEnd_3557125 := by
    simpa [prefixWord, tailWord_3557125, baseEnd_3557125] using wordTrace_append hprefix tailTrace_3557125
  have hstable : (prefixWord ++ tailWord_3557125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3557125).length < 2 ^ (prefixWord ++ tailWord_3557125).sum := by decide
  have hdescent : baseEnd_3557125 < baseStart_3557125 := by decide
  rcases family_descends (prefixWord ++ tailWord_3557125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3557146 : List Nat := [3, 1, 1, 3, 2, 2, 1, 5, 1, 3]
def baseStart_3557146 : Nat := 118140960795 + 3557146 * 2 ^ 59
def prefixEnd_3557146 : Nat := 4983230072969 + 3 ^ 40 * 3557146 * 2
def baseEnd_3557146 : Nat := 1217683770812163255743993

theorem tailTrace_3557146 : CollatzResearch.WordTrace tailWord_3557146 prefixEnd_3557146 1217683770812163255743993 := by
  unfold tailWord_3557146
  simp only [CollatzResearch.WordTrace]
  refine ⟨32434943292768757253848823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86493182114050019343596861 32434943292768757253848823)
  ·
    refine ⟨48652414939153135880773235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32434943292768757253848823 48652414939153135880773235)
    ·
      refine ⟨72978622408729703821159853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48652414939153135880773235 72978622408729703821159853)
      ·
        refine ⟨27366983403273638932934945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72978622408729703821159853 27366983403273638932934945)
        ·
          refine ⟨20525237552455229199701209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27366983403273638932934945 20525237552455229199701209)
          ·
            refine ⟨15393928164341421899775907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20525237552455229199701209 15393928164341421899775907)
            ·
              refine ⟨23090892246512132849663861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15393928164341421899775907 23090892246512132849663861)
              ·
                refine ⟨2164771148110512454655987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23090892246512132849663861 2164771148110512454655987)
                ·
                  refine ⟨3247156722165768681983981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2164771148110512454655987 3247156722165768681983981)
                  ·
                    refine ⟨1217683770812163255743993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3247156722165768681983981 1217683770812163255743993)
                    ·
                      rfl

theorem cell22_3557146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 5, 1, 3].length) (baseStart_3557146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3557146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3557146 prefixEnd_3557146 := by exact prefixLift 3557146
  have htrace : WordTrace (prefixWord ++ tailWord_3557146) baseStart_3557146 baseEnd_3557146 := by
    simpa [prefixWord, tailWord_3557146, baseEnd_3557146] using wordTrace_append hprefix tailTrace_3557146
  have hstable : (prefixWord ++ tailWord_3557146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3557146).length < 2 ^ (prefixWord ++ tailWord_3557146).sum := by decide
  have hdescent : baseEnd_3557146 < baseStart_3557146 := by decide
  rcases family_descends (prefixWord ++ tailWord_3557146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3557157 : List Nat := [1, 3, 1, 2, 3, 2, 1, 2, 2, 5]
def baseStart_3557157 : Nat := 118140960795 + 3557157 * 2 ^ 59
def prefixEnd_3557157 : Nat := 4983230072969 + 3 ^ 40 * 3557157 * 2
def baseEnd_3557157 : Nat := 1217687536336962893718959

theorem tailTrace_3557157 : CollatzResearch.WordTrace tailWord_3557157 prefixEnd_3557157 1217687536336962893718959 := by
  unfold tailWord_3557157
  simp only [CollatzResearch.WordTrace]
  refine ⟨129740174374035177894045725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86493449582690118596030483 129740174374035177894045725)
  ·
    refine ⟨48652565390263191710267147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129740174374035177894045725 48652565390263191710267147)
    ·
      refine ⟨72978848085394787565400721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48652565390263191710267147 72978848085394787565400721)
      ·
        refine ⟨54734136064046090674050541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72978848085394787565400721 54734136064046090674050541)
        ·
          refine ⟨20525301024017284002768953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54734136064046090674050541 20525301024017284002768953)
          ·
            refine ⟨15393975768012963002076715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20525301024017284002768953 15393975768012963002076715)
            ·
              refine ⟨23090963652019444503115073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15393975768012963002076715 23090963652019444503115073)
              ·
                refine ⟨17318222739014583377336305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23090963652019444503115073 17318222739014583377336305)
                ·
                  refine ⟨12988667054260937533002229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17318222739014583377336305 12988667054260937533002229)
                  ·
                    refine ⟨1217687536336962893718959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12988667054260937533002229 1217687536336962893718959)
                    ·
                      rfl

theorem cell22_3557157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 2, 2, 5].length) (baseStart_3557157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3557157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3557157 prefixEnd_3557157 := by exact prefixLift 3557157
  have htrace : WordTrace (prefixWord ++ tailWord_3557157) baseStart_3557157 baseEnd_3557157 := by
    simpa [prefixWord, tailWord_3557157, baseEnd_3557157] using wordTrace_append hprefix tailTrace_3557157
  have hstable : (prefixWord ++ tailWord_3557157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3557157).length < 2 ^ (prefixWord ++ tailWord_3557157).sum := by decide
  have hdescent : baseEnd_3557157 < baseStart_3557157 := by decide
  rcases family_descends (prefixWord ++ tailWord_3557157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3557187 : List Nat := [1, 1, 1, 3, 1, 5, 2, 2, 6]
def baseStart_3557187 : Nat := 118140960795 + 3557187 * 2 ^ 59
def prefixEnd_3557187 : Nat := 4983230072969 + 3 ^ 40 * 3557187 * 2
def baseEnd_3557187 : Nat := 405899268650017605156289

theorem tailTrace_3557187 : CollatzResearch.WordTrace tailWord_3557187 prefixEnd_3557187 405899268650017605156289 := by
  unfold tailWord_3557187
  simp only [CollatzResearch.WordTrace]
  refine ⟨129741268563926493017637815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86494179042617662011758543 129741268563926493017637815)
  ·
    refine ⟨194611902845889739526456723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129741268563926493017637815 194611902845889739526456723)
    ·
      refine ⟨291917854268834609289685085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194611902845889739526456723 291917854268834609289685085)
      ·
        refine ⟨109469195350812978483631907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 291917854268834609289685085 109469195350812978483631907)
        ·
          refine ⟨164203793026219467725447861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109469195350812978483631907 164203793026219467725447861)
          ·
            refine ⟨15394105596208075099260737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 164203793026219467725447861 15394105596208075099260737)
            ·
              refine ⟨11545579197156056324445553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15394105596208075099260737 11545579197156056324445553)
              ·
                refine ⟨8659184397867042243334165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11545579197156056324445553 8659184397867042243334165)
                ·
                  refine ⟨405899268650017605156289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8659184397867042243334165 405899268650017605156289)
                  ·
                    rfl

theorem cell22_3557187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 2, 6].length) (baseStart_3557187 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3557187 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3557187 prefixEnd_3557187 := by exact prefixLift 3557187
  have htrace : WordTrace (prefixWord ++ tailWord_3557187) baseStart_3557187 baseEnd_3557187 := by
    simpa [prefixWord, tailWord_3557187, baseEnd_3557187] using wordTrace_append hprefix tailTrace_3557187
  have hstable : (prefixWord ++ tailWord_3557187).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3557187).length < 2 ^ (prefixWord ++ tailWord_3557187).sum := by decide
  have hdescent : baseEnd_3557187 < baseStart_3557187 := by decide
  rcases family_descends (prefixWord ++ tailWord_3557187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3557189 : List Nat := [1, 3, 1, 1, 1, 2, 6, 2, 1, 4]
def baseStart_3557189 : Nat := 118140960795 + 3557189 * 2 ^ 59
def prefixEnd_3557189 : Nat := 4983230072969 + 3 ^ 40 * 3557189 * 2
def baseEnd_3557189 : Nat := 1217698490590925476918861

theorem tailTrace_3557189 : CollatzResearch.WordTrace tailWord_3557189 prefixEnd_3557189 1217698490590925476918861 := by
  unfold tailWord_3557189
  simp only [CollatzResearch.WordTrace]
  refine ⟨129741341509919247359210621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86494227673279498239473747 129741341509919247359210621)
  ·
    refine ⟨48653003066219717759703983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129741341509919247359210621 48653003066219717759703983)
    ·
      refine ⟨72979504599329576639555975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48653003066219717759703983 72979504599329576639555975)
      ·
        refine ⟨109469256898994364959333963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72979504599329576639555975 109469256898994364959333963)
        ·
          refine ⟨164203885348491547439000945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109469256898994364959333963 164203885348491547439000945)
          ·
            refine ⟨123152914011368660579250709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164203885348491547439000945 123152914011368660579250709)
            ·
              refine ⟨5772792844282905964652377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 123152914011368660579250709 5772792844282905964652377)
              ·
                refine ⟨4329594633212179473489283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5772792844282905964652377 4329594633212179473489283)
                ·
                  refine ⟨6494391949818269210233925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4329594633212179473489283 6494391949818269210233925)
                  ·
                    refine ⟨1217698490590925476918861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6494391949818269210233925 1217698490590925476918861)
                    ·
                      rfl

theorem cell22_3557189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 6, 2, 1, 4].length) (baseStart_3557189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3557189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3557189 prefixEnd_3557189 := by exact prefixLift 3557189
  have htrace : WordTrace (prefixWord ++ tailWord_3557189) baseStart_3557189 baseEnd_3557189 := by
    simpa [prefixWord, tailWord_3557189, baseEnd_3557189] using wordTrace_append hprefix tailTrace_3557189
  have hstable : (prefixWord ++ tailWord_3557189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3557189).length < 2 ^ (prefixWord ++ tailWord_3557189).sum := by decide
  have hdescent : baseEnd_3557189 < baseStart_3557189 := by decide
  rcases family_descends (prefixWord ++ tailWord_3557189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3557272 : List Nat := [2, 1, 2, 6, 2, 1, 2, 2, 4]
def baseStart_3557272 : Nat := 118140960795 + 3557272 * 2 ^ 59
def prefixEnd_3557272 : Nat := 4983230072969 + 3 ^ 40 * 3557272 * 2
def baseEnd_3557272 : Nat := 405908967729046975697869

theorem tailTrace_3557272 : CollatzResearch.WordTrace tailWord_3557272 prefixEnd_3557272 405908967729046975697869 := by
  unfold tailWord_3557272
  simp only [CollatzResearch.WordTrace]
  refine ⟨64872184384309276267241035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86496245845745701689654713 64872184384309276267241035)
  ·
    refine ⟨97308276576463914400861553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64872184384309276267241035 97308276576463914400861553)
    ·
      refine ⟨72981207432347935800646165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97308276576463914400861553 72981207432347935800646165)
      ·
        refine ⟨3420994098391309490655289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 72981207432347935800646165 3420994098391309490655289)
        ·
          refine ⟨2565745573793482117991467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3420994098391309490655289 2565745573793482117991467)
          ·
            refine ⟨3848618360690223176987201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2565745573793482117991467 3848618360690223176987201)
            ·
              refine ⟨2886463770517667382740401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3848618360690223176987201 2886463770517667382740401)
              ·
                refine ⟨2164847827888250537055301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2886463770517667382740401 2164847827888250537055301)
                ·
                  refine ⟨405908967729046975697869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2164847827888250537055301 405908967729046975697869)
                  ·
                    rfl

theorem cell22_3557272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 2, 2, 4].length) (baseStart_3557272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3557272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3557272 prefixEnd_3557272 := by exact prefixLift 3557272
  have htrace : WordTrace (prefixWord ++ tailWord_3557272) baseStart_3557272 baseEnd_3557272 := by
    simpa [prefixWord, tailWord_3557272, baseEnd_3557272] using wordTrace_append hprefix tailTrace_3557272
  have hstable : (prefixWord ++ tailWord_3557272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3557272).length < 2 ^ (prefixWord ++ tailWord_3557272).sum := by decide
  have hdescent : baseEnd_3557272 < baseStart_3557272 := by decide
  rcases family_descends (prefixWord ++ tailWord_3557272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3557358 : List Nat := [4, 1, 2, 1, 3, 2, 2, 2, 1, 4]
def baseStart_3557358 : Nat := 118140960795 + 3557358 * 2 ^ 59
def prefixEnd_3557358 : Nat := 4983230072969 + 3 ^ 40 * 3557358 * 2
def baseEnd_3557358 : Nat := 1217756342744665369443343

theorem tailTrace_3557358 : CollatzResearch.WordTrace tailWord_3557358 prefixEnd_3557358 1217756342744665369443343 := by
  unfold tailWord_3557358
  simp only [CollatzResearch.WordTrace]
  refine ⟨16218438180788373652764091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86498336964204659481408485 16218438180788373652764091)
  ·
    refine ⟨24327657271182560479146137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16218438180788373652764091 24327657271182560479146137)
    ·
      refine ⟨18245742953386920359359603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24327657271182560479146137 18245742953386920359359603)
      ·
        refine ⟨27368614430080380539039405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18245742953386920359359603 27368614430080380539039405)
        ·
          refine ⟨10263230411280142702139777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27368614430080380539039405 10263230411280142702139777)
          ·
            refine ⟨7697422808460107026604833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10263230411280142702139777 7697422808460107026604833)
            ·
              refine ⟨5773067106345080269953625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7697422808460107026604833 5773067106345080269953625)
              ·
                refine ⟨4329800329758810202465219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5773067106345080269953625 4329800329758810202465219)
                ·
                  refine ⟨6494700494638215303697829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4329800329758810202465219 6494700494638215303697829)
                  ·
                    refine ⟨1217756342744665369443343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6494700494638215303697829 1217756342744665369443343)
                    ·
                      rfl

theorem cell22_3557358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 2, 2, 1, 4].length) (baseStart_3557358 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3557358 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3557358 prefixEnd_3557358 := by exact prefixLift 3557358
  have htrace : WordTrace (prefixWord ++ tailWord_3557358) baseStart_3557358 baseEnd_3557358 := by
    simpa [prefixWord, tailWord_3557358, baseEnd_3557358] using wordTrace_append hprefix tailTrace_3557358
  have hstable : (prefixWord ++ tailWord_3557358).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3557358).length < 2 ^ (prefixWord ++ tailWord_3557358).sum := by decide
  have hdescent : baseEnd_3557358 < baseStart_3557358 := by decide
  rcases family_descends (prefixWord ++ tailWord_3557358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3557369 : List Nat := [1, 2, 1, 3, 1, 4, 2, 1, 1, 6]
def baseStart_3557369 : Nat := 118140960795 + 3557369 * 2 ^ 59
def prefixEnd_3557369 : Nat := 4983230072969 + 3 ^ 40 * 3557369 * 2
def baseEnd_3557369 : Nat := 1217760108269465007418309

theorem tailTrace_3557369 : CollatzResearch.WordTrace tailWord_3557369 prefixEnd_3557369 1217760108269465007418309 := by
  unfold tailWord_3557369
  simp only [CollatzResearch.WordTrace]
  refine ⟨129747906649267138100763161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86498604432844758733842107 129747906649267138100763161)
  ·
    refine ⟨97310929986950353575572371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129747906649267138100763161 97310929986950353575572371)
    ·
      refine ⟨145966394980425530363358557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97310929986950353575572371 145966394980425530363358557)
      ·
        refine ⟨54737398117659573886259459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145966394980425530363358557 54737398117659573886259459)
        ·
          refine ⟨82106097176489360829389189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54737398117659573886259459 82106097176489360829389189)
          ·
            refine ⟨15394893220591755155510473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82106097176489360829389189 15394893220591755155510473)
            ·
              refine ⟨11546169915443816366632855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15394893220591755155510473 11546169915443816366632855)
              ·
                refine ⟨17319254873165724549949283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11546169915443816366632855 17319254873165724549949283)
                ·
                  refine ⟨25978882309748586824923925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17319254873165724549949283 25978882309748586824923925)
                  ·
                    refine ⟨1217760108269465007418309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25978882309748586824923925 1217760108269465007418309)
                    ·
                      rfl

theorem cell22_3557369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 1, 1, 6].length) (baseStart_3557369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3557369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3557369 prefixEnd_3557369 := by exact prefixLift 3557369
  have htrace : WordTrace (prefixWord ++ tailWord_3557369) baseStart_3557369 baseEnd_3557369 := by
    simpa [prefixWord, tailWord_3557369, baseEnd_3557369] using wordTrace_append hprefix tailTrace_3557369
  have hstable : (prefixWord ++ tailWord_3557369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3557369).length < 2 ^ (prefixWord ++ tailWord_3557369).sum := by decide
  have hdescent : baseEnd_3557369 < baseStart_3557369 := by decide
  rcases family_descends (prefixWord ++ tailWord_3557369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3557405 : List Nat := [1, 4, 2, 2, 2, 1, 4, 1, 2, 3]
def baseStart_3557405 : Nat := 118140960795 + 3557405 * 2 ^ 59
def prefixEnd_3557405 : Nat := 4983230072969 + 3 ^ 40 * 3557405 * 2
def baseEnd_3557405 : Nat := 1217772431805172913518199

theorem tailTrace_3557405 : CollatzResearch.WordTrace tailWord_3557405 prefixEnd_3557405 1217772431805172913518199 := by
  unfold tailWord_3557405
  simp only [CollatzResearch.WordTrace]
  refine ⟨129749219677136716249073669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86499479784757810832715779 129749219677136716249073669)
  ·
    refine ⟨24327978689463134296701313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129749219677136716249073669 24327978689463134296701313)
    ·
      refine ⟨18245984017097350722525985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24327978689463134296701313 18245984017097350722525985)
      ·
        refine ⟨13684488012823013041894489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18245984017097350722525985 13684488012823013041894489)
        ·
          refine ⟨10263366009617259781420867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13684488012823013041894489 10263366009617259781420867)
          ·
            refine ⟨15395049014425889672131301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10263366009617259781420867 15395049014425889672131301)
            ·
              refine ⟨2886571690204854313524619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15395049014425889672131301 2886571690204854313524619)
              ·
                refine ⟨4329857535307281470286929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2886571690204854313524619 4329857535307281470286929)
                ·
                  refine ⟨3247393151480461102715197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4329857535307281470286929 3247393151480461102715197)
                  ·
                    refine ⟨1217772431805172913518199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3247393151480461102715197 1217772431805172913518199)
                    ·
                      rfl

theorem cell22_3557405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 4, 1, 2, 3].length) (baseStart_3557405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3557405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3557405 prefixEnd_3557405 := by exact prefixLift 3557405
  have htrace : WordTrace (prefixWord ++ tailWord_3557405) baseStart_3557405 baseEnd_3557405 := by
    simpa [prefixWord, tailWord_3557405, baseEnd_3557405] using wordTrace_append hprefix tailTrace_3557405
  have hstable : (prefixWord ++ tailWord_3557405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3557405).length < 2 ^ (prefixWord ++ tailWord_3557405).sum := by decide
  have hdescent : baseEnd_3557405 < baseStart_3557405 := by decide
  rcases family_descends (prefixWord ++ tailWord_3557405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3557429 : List Nat := [1, 3, 3, 1, 1, 1, 2, 1, 9]
def baseStart_3557429 : Nat := 118140960795 + 3557429 * 2 ^ 59
def prefixEnd_3557429 : Nat := 4983230072969 + 3 ^ 40 * 3557429 * 2
def baseEnd_3557429 : Nat := 405926882498548283639375

theorem tailTrace_3557429 : CollatzResearch.WordTrace tailWord_3557429 prefixEnd_3557429 405926882498548283639375 := by
  unfold tailWord_3557429
  simp only [CollatzResearch.WordTrace]
  refine ⟨129750095029049768347947341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86500063352699845565298227 129750095029049768347947341)
  ·
    refine ⟨48656285635893663130480253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129750095029049768347947341 48656285635893663130480253)
    ·
      refine ⟨18246107113460123673930095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48656285635893663130480253 18246107113460123673930095)
      ·
        refine ⟨27369160670190185510895143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18246107113460123673930095 27369160670190185510895143)
        ·
          refine ⟨41053741005285278266342715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27369160670190185510895143 41053741005285278266342715)
          ·
            refine ⟨61580611507927917399514073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41053741005285278266342715 61580611507927917399514073)
            ·
              refine ⟨46185458630945938049635555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61580611507927917399514073 46185458630945938049635555)
              ·
                refine ⟨69278187946418907074453333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46185458630945938049635555 69278187946418907074453333)
                ·
                  refine ⟨405926882498548283639375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 69278187946418907074453333 405926882498548283639375)
                  ·
                    rfl

theorem cell22_3557429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 9].length) (baseStart_3557429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3557429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3557429 prefixEnd_3557429 := by exact prefixLift 3557429
  have htrace : WordTrace (prefixWord ++ tailWord_3557429) baseStart_3557429 baseEnd_3557429 := by
    simpa [prefixWord, tailWord_3557429, baseEnd_3557429] using wordTrace_append hprefix tailTrace_3557429
  have hstable : (prefixWord ++ tailWord_3557429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3557429).length < 2 ^ (prefixWord ++ tailWord_3557429).sum := by decide
  have hdescent : baseEnd_3557429 < baseStart_3557429 := by decide
  rcases family_descends (prefixWord ++ tailWord_3557429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3557461 : List Nat := [1, 3, 2, 2, 1, 4, 1, 1, 2, 5]
def baseStart_3557461 : Nat := 118140960795 + 3557461 * 2 ^ 59
def prefixEnd_3557461 : Nat := 4983230072969 + 3 ^ 40 * 3557461 * 2
def baseEnd_3557461 : Nat := 1217791601749607434118027

theorem tailTrace_3557461 : CollatzResearch.WordTrace tailWord_3557461 prefixEnd_3557461 1217791601749607434118027 := by
  unfold tailWord_3557461
  simp only [CollatzResearch.WordTrace]
  refine ⟨129751262164933837813112237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86500841443289225208741491 129751262164933837813112237)
  ·
    refine ⟨48656723311850189179917089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129751262164933837813112237 48656723311850189179917089)
    ·
      refine ⟨36492542483887641884937817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48656723311850189179917089 36492542483887641884937817)
      ·
        refine ⟨27369406862915731413703363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36492542483887641884937817 27369406862915731413703363)
        ·
          refine ⟨41054110294373597120555045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27369406862915731413703363 41054110294373597120555045)
          ·
            refine ⟨7697645680195049460104071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41054110294373597120555045 7697645680195049460104071)
            ·
              refine ⟨11546468520292574190156107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7697645680195049460104071 11546468520292574190156107)
              ·
                refine ⟨17319702780438861285234161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11546468520292574190156107 17319702780438861285234161)
                ·
                  refine ⟨12989777085329145963925621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17319702780438861285234161 12989777085329145963925621)
                  ·
                    refine ⟨1217791601749607434118027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12989777085329145963925621 1217791601749607434118027)
                    ·
                      rfl

theorem cell22_3557461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 1, 2, 5].length) (baseStart_3557461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3557461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3557461 prefixEnd_3557461 := by exact prefixLift 3557461
  have htrace : WordTrace (prefixWord ++ tailWord_3557461) baseStart_3557461 baseEnd_3557461 := by
    simpa [prefixWord, tailWord_3557461, baseEnd_3557461] using wordTrace_append hprefix tailTrace_3557461
  have hstable : (prefixWord ++ tailWord_3557461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3557461).length < 2 ^ (prefixWord ++ tailWord_3557461).sum := by decide
  have hdescent : baseEnd_3557461 < baseStart_3557461 := by decide
  rcases family_descends (prefixWord ++ tailWord_3557461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3557476 : List Nat := [2, 3, 1, 1, 2, 1, 4, 1, 3, 4]
def baseStart_3557476 : Nat := 118140960795 + 3557476 * 2 ^ 59
def prefixEnd_3557476 : Nat := 4983230072969 + 3 ^ 40 * 3557476 * 2
def baseEnd_3557476 : Nat := 1217796736556152394992981

theorem tailTrace_3557476 : CollatzResearch.WordTrace tailWord_3557476 prefixEnd_3557476 1217796736556152394992981 := by
  unfold tailWord_3557476
  simp only [CollatzResearch.WordTrace]
  refine ⟨64875904629939747687454141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86501206173252996916605521 64875904629939747687454141)
  ·
    refine ⟨24328464236227405382795303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64875904629939747687454141 24328464236227405382795303)
    ·
      refine ⟨36492696354341108074192955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24328464236227405382795303 36492696354341108074192955)
      ·
        refine ⟨54739044531511662111289433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36492696354341108074192955 54739044531511662111289433)
        ·
          refine ⟨41054283398633746583467075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54739044531511662111289433 41054283398633746583467075)
          ·
            refine ⟨61581425097950619875200613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41054283398633746583467075 61581425097950619875200613)
            ·
              refine ⟨11546517205865741226600115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61581425097950619875200613 11546517205865741226600115)
              ·
                refine ⟨17319775808798611839900173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11546517205865741226600115 17319775808798611839900173)
                ·
                  refine ⟨6494915928299479439962565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17319775808798611839900173 6494915928299479439962565)
                  ·
                    refine ⟨1217796736556152394992981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6494915928299479439962565 1217796736556152394992981)
                    ·
                      rfl

theorem cell22_3557476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 1, 3, 4].length) (baseStart_3557476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3557476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3557476 prefixEnd_3557476 := by exact prefixLift 3557476
  have htrace : WordTrace (prefixWord ++ tailWord_3557476) baseStart_3557476 baseEnd_3557476 := by
    simpa [prefixWord, tailWord_3557476, baseEnd_3557476] using wordTrace_append hprefix tailTrace_3557476
  have hstable : (prefixWord ++ tailWord_3557476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3557476).length < 2 ^ (prefixWord ++ tailWord_3557476).sum := by decide
  have hdescent : baseEnd_3557476 < baseStart_3557476 := by decide
  rcases family_descends (prefixWord ++ tailWord_3557476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3557508 : List Nat := [2, 3, 2, 1, 2, 1, 1, 6, 4]
def baseStart_3557508 : Nat := 118140960795 + 3557508 * 2 ^ 59
def prefixEnd_3557508 : Nat := 4983230072969 + 3 ^ 40 * 3557508 * 2
def baseEnd_3557508 : Nat := 405935896936704992730961

theorem tailTrace_3557508 : CollatzResearch.WordTrace tailWord_3557508 prefixEnd_3557508 405935896936704992730961 := by
  unfold tailWord_3557508
  simp only [CollatzResearch.WordTrace]
  refine ⟨64876488197881782420036589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86501984263842376560048785 64876488197881782420036589)
  ·
    refine ⟨24328683074205668407513721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64876488197881782420036589 24328683074205668407513721)
    ·
      refine ⟨18246512305654251305635291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24328683074205668407513721 18246512305654251305635291)
      ·
        refine ⟨27369768458481376958452937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18246512305654251305635291 27369768458481376958452937)
        ·
          refine ⟨20527326343861032718839703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27369768458481376958452937 20527326343861032718839703)
          ·
            refine ⟨30790989515791549078259555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20527326343861032718839703 30790989515791549078259555)
            ·
              refine ⟨46186484273687323617389333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30790989515791549078259555 46186484273687323617389333)
              ·
                refine ⟨2164991450329093294565125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 46186484273687323617389333 2164991450329093294565125)
                ·
                  refine ⟨405935896936704992730961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2164991450329093294565125 405935896936704992730961)
                  ·
                    rfl

theorem cell22_3557508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 6, 4].length) (baseStart_3557508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3557508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3557508 prefixEnd_3557508 := by exact prefixLift 3557508
  have htrace : WordTrace (prefixWord ++ tailWord_3557508) baseStart_3557508 baseEnd_3557508 := by
    simpa [prefixWord, tailWord_3557508, baseEnd_3557508] using wordTrace_append hprefix tailTrace_3557508
  have hstable : (prefixWord ++ tailWord_3557508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3557508).length < 2 ^ (prefixWord ++ tailWord_3557508).sum := by decide
  have hdescent : baseEnd_3557508 < baseStart_3557508 := by decide
  rcases family_descends (prefixWord ++ tailWord_3557508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3557536 : List Nat := [2, 1, 1, 4, 2, 3, 1, 8]
def baseStart_3557536 : Nat := 118140960795 + 3557536 * 2 ^ 59
def prefixEnd_3557536 : Nat := 4983230072969 + 3 ^ 40 * 3557536 * 2
def baseEnd_3557536 : Nat := 135313030642481359832533

theorem tailTrace_3557536 : CollatzResearch.WordTrace tailWord_3557536 prefixEnd_3557536 135313030642481359832533 := by
  unfold tailWord_3557536
  simp only [CollatzResearch.WordTrace]
  refine ⟨64876998819831062811046231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86502665093108083748061641 64876998819831062811046231)
  ·
    refine ⟨97315498229746594216569347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64876998819831062811046231 97315498229746594216569347)
    ·
      refine ⟨145973247344619891324854021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97315498229746594216569347 145973247344619891324854021)
      ·
        refine ⟨27369983877116229623410129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 145973247344619891324854021 27369983877116229623410129)
        ·
          refine ⟨20527487907837172217557597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27369983877116229623410129 20527487907837172217557597)
          ·
            refine ⟨7697807965438939581584099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20527487907837172217557597 7697807965438939581584099)
            ·
              refine ⟨11546711948158409372376149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7697807965438939581584099 11546711948158409372376149)
              ·
                refine ⟨135313030642481359832533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11546711948158409372376149 135313030642481359832533)
                ·
                  rfl

theorem cell22_3557536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 8].length) (baseStart_3557536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3557536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3557536 prefixEnd_3557536 := by exact prefixLift 3557536
  have htrace : WordTrace (prefixWord ++ tailWord_3557536) baseStart_3557536 baseEnd_3557536 := by
    simpa [prefixWord, tailWord_3557536, baseEnd_3557536] using wordTrace_append hprefix tailTrace_3557536
  have hstable : (prefixWord ++ tailWord_3557536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3557536).length < 2 ^ (prefixWord ++ tailWord_3557536).sum := by decide
  have hdescent : baseEnd_3557536 < baseStart_3557536 := by decide
  rcases family_descends (prefixWord ++ tailWord_3557536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3557538 : List Nat := [3, 3, 1, 3, 1, 1, 2, 1, 1, 6]
def baseStart_3557538 : Nat := 118140960795 + 3557538 * 2 ^ 59
def prefixEnd_3557538 : Nat := 4983230072969 + 3 ^ 40 * 3557538 * 2
def baseEnd_3557538 : Nat := 1217817960423204899942791

theorem tailTrace_3557538 : CollatzResearch.WordTrace tailWord_3557538 prefixEnd_3557538 1217817960423204899942791 := by
  unfold tailWord_3557538
  simp only [CollatzResearch.WordTrace]
  refine ⟨32438517646413719990916317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86502713723769919975776845 32438517646413719990916317)
  ·
    refine ⟨12164444117405144996593619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32438517646413719990916317 12164444117405144996593619)
    ·
      refine ⟨18246666176107717494890429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12164444117405144996593619 18246666176107717494890429)
      ·
        refine ⟨6842499816040394060583911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18246666176107717494890429 6842499816040394060583911)
        ·
          refine ⟨10263749724060591090875867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6842499816040394060583911 10263749724060591090875867)
          ·
            refine ⟨15395624586090886636313801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10263749724060591090875867 15395624586090886636313801)
            ·
              refine ⟨11546718439568164977235351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15395624586090886636313801 11546718439568164977235351)
              ·
                refine ⟨17320077659352247465853027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11546718439568164977235351 17320077659352247465853027)
                ·
                  refine ⟨25980116489028371198779541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17320077659352247465853027 25980116489028371198779541)
                  ·
                    refine ⟨1217817960423204899942791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25980116489028371198779541 1217817960423204899942791)
                    ·
                      rfl

theorem cell22_3557538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 1, 1, 6].length) (baseStart_3557538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3557538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3557538 prefixEnd_3557538 := by exact prefixLift 3557538
  have htrace : WordTrace (prefixWord ++ tailWord_3557538) baseStart_3557538 baseEnd_3557538 := by
    simpa [prefixWord, tailWord_3557538, baseEnd_3557538] using wordTrace_append hprefix tailTrace_3557538
  have hstable : (prefixWord ++ tailWord_3557538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3557538).length < 2 ^ (prefixWord ++ tailWord_3557538).sum := by decide
  have hdescent : baseEnd_3557538 < baseStart_3557538 := by decide
  rcases family_descends (prefixWord ++ tailWord_3557538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3557553 : List Nat := [1, 2, 2, 5, 2, 2, 8]
def baseStart_3557553 : Nat := 118140960795 + 3557553 * 2 ^ 59
def prefixEnd_3557553 : Nat := 4983230072969 + 3 ^ 40 * 3557553 * 2
def baseEnd_3557553 : Nat := 45104559082583328178435

theorem tailTrace_3557553 : CollatzResearch.WordTrace tailWord_3557553 prefixEnd_3557553 45104559082583328178435 := by
  unfold tailWord_3557553
  simp only [CollatzResearch.WordTrace]
  refine ⟨129754617680600537525461313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86503078453733691683640875 129754617680600537525461313)
  ·
    refine ⟨97315963260450403144095985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129754617680600537525461313 97315963260450403144095985)
    ·
      refine ⟨72986972445337802358071989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97315963260450403144095985 72986972445337802358071989)
      ·
        refine ⟨6842528666750418971069249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 72986972445337802358071989 6842528666750418971069249)
        ·
          refine ⟨5131896500062814228301937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6842528666750418971069249 5131896500062814228301937)
          ·
            refine ⟨3848922375047110671226453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5131896500062814228301937 3848922375047110671226453)
            ·
              refine ⟨45104559082583328178435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3848922375047110671226453 45104559082583328178435)
              ·
                rfl

theorem cell22_3557553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 8].length) (baseStart_3557553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3557553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3557553 prefixEnd_3557553 := by exact prefixLift 3557553
  have htrace : WordTrace (prefixWord ++ tailWord_3557553) baseStart_3557553 baseEnd_3557553 := by
    simpa [prefixWord, tailWord_3557553, baseEnd_3557553] using wordTrace_append hprefix tailTrace_3557553
  have hstable : (prefixWord ++ tailWord_3557553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3557553).length < 2 ^ (prefixWord ++ tailWord_3557553).sum := by decide
  have hdescent : baseEnd_3557553 < baseStart_3557553 := by decide
  rcases family_descends (prefixWord ++ tailWord_3557553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3557570 : List Nat := [3, 5, 1, 1, 1, 1, 1, 9]
def baseStart_3557570 : Nat := 118140960795 + 3557570 * 2 ^ 59
def prefixEnd_3557570 : Nat := 4983230072969 + 3 ^ 40 * 3557570 * 2
def baseEnd_3557570 : Nat := 135314323853018609238077

theorem tailTrace_3557570 : CollatzResearch.WordTrace tailWord_3557570 prefixEnd_3557570 135314323853018609238077 := by
  unfold tailWord_3557570
  simp only [CollatzResearch.WordTrace]
  refine ⟨32438809430384737357207541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86503491814359299619220109 32438809430384737357207541)
  ·
    refine ⟨3041138384098569127238207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32438809430384737357207541 3041138384098569127238207)
    ·
      refine ⟨4561707576147853690857311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3041138384098569127238207 4561707576147853690857311)
      ·
        refine ⟨6842561364221780536285967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4561707576147853690857311 6842561364221780536285967)
        ·
          refine ⟨10263842046332670804428951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6842561364221780536285967 10263842046332670804428951)
          ·
            refine ⟨15395763069499006206643427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10263842046332670804428951 15395763069499006206643427)
            ·
              refine ⟨23093644604248509309965141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15395763069499006206643427 23093644604248509309965141)
              ·
                refine ⟨135314323853018609238077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23093644604248509309965141 135314323853018609238077)
                ·
                  rfl

theorem cell22_3557570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 9].length) (baseStart_3557570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3557570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3557570 prefixEnd_3557570 := by exact prefixLift 3557570
  have htrace : WordTrace (prefixWord ++ tailWord_3557570) baseStart_3557570 baseEnd_3557570 := by
    simpa [prefixWord, tailWord_3557570, baseEnd_3557570] using wordTrace_append hprefix tailTrace_3557570
  have hstable : (prefixWord ++ tailWord_3557570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3557570).length < 2 ^ (prefixWord ++ tailWord_3557570).sum := by decide
  have hdescent : baseEnd_3557570 < baseStart_3557570 := by decide
  rcases family_descends (prefixWord ++ tailWord_3557570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3557628 : List Nat := [2, 2, 2, 1, 4, 1, 1, 2, 3, 4]
def baseStart_3557628 : Nat := 118140960795 + 3557628 * 2 ^ 59
def prefixEnd_3557628 : Nat := 4983230072969 + 3 ^ 40 * 3557628 * 2
def baseEnd_3557628 : Nat := 1217848769262474665192515

theorem tailTrace_3557628 : CollatzResearch.WordTrace tailWord_3557628 prefixEnd_3557628 1217848769262474665192515 := by
  unfold tailWord_3557628
  simp only [CollatzResearch.WordTrace]
  refine ⟨64878676577664412667220769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86504902103552550222961025 64878676577664412667220769)
  ·
    refine ⟨48659007433248309500415577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64878676577664412667220769 48659007433248309500415577)
    ·
      refine ⟨36494255574936232125311683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48659007433248309500415577 36494255574936232125311683)
      ·
        refine ⟨54741383362404348187967525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36494255574936232125311683 54741383362404348187967525)
        ·
          refine ⟨10264009380450815285243911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54741383362404348187967525 10264009380450815285243911)
          ·
            refine ⟨15396014070676222927865867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10264009380450815285243911 15396014070676222927865867)
            ·
              refine ⟨23094021106014334391798801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15396014070676222927865867 23094021106014334391798801)
              ·
                refine ⟨17320515829510750793849101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23094021106014334391798801 17320515829510750793849101)
                ·
                  refine ⟨6495193436066531547693413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17320515829510750793849101 6495193436066531547693413)
                  ·
                    refine ⟨1217848769262474665192515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6495193436066531547693413 1217848769262474665192515)
                    ·
                      rfl

theorem cell22_3557628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 2, 3, 4].length) (baseStart_3557628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3557628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3557628 prefixEnd_3557628 := by exact prefixLift 3557628
  have htrace : WordTrace (prefixWord ++ tailWord_3557628) baseStart_3557628 baseEnd_3557628 := by
    simpa [prefixWord, tailWord_3557628, baseEnd_3557628] using wordTrace_append hprefix tailTrace_3557628
  have hstable : (prefixWord ++ tailWord_3557628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3557628).length < 2 ^ (prefixWord ++ tailWord_3557628).sum := by decide
  have hdescent : baseEnd_3557628 < baseStart_3557628 := by decide
  rcases family_descends (prefixWord ++ tailWord_3557628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3557677 : List Nat := [1, 5, 3, 1, 2, 1, 2, 1, 6]
def baseStart_3557677 : Nat := 118140960795 + 3557677 * 2 ^ 59
def prefixEnd_3557677 : Nat := 4983230072969 + 3 ^ 40 * 3557677 * 2
def baseEnd_3557677 : Nat := 405955180987951623572455

theorem tailTrace_3557677 : CollatzResearch.WordTrace tailWord_3557677 prefixEnd_3557677 405955180987951623572455 := by
  unfold tailWord_3557677
  simp only [CollatzResearch.WordTrace]
  refine ⟨129759140332151306702975285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86506093554767537801983523 129759140332151306702975285)
  ·
    refine ⟨12164919406139185003403933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 129759140332151306702975285 12164919406139185003403933)
    ·
      refine ⟨4561844777302194376276475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12164919406139185003403933 4561844777302194376276475)
      ·
        refine ⟨6842767165953291564414713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4561844777302194376276475 6842767165953291564414713)
        ·
          refine ⟨5132075374464968673311035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6842767165953291564414713 5132075374464968673311035)
          ·
            refine ⟨7698113061697453009966553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5132075374464968673311035 7698113061697453009966553)
            ·
              refine ⟨5773584796273089757474915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7698113061697453009966553 5773584796273089757474915)
              ·
                refine ⟨8660377194409634636212373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5773584796273089757474915 8660377194409634636212373)
                ·
                  refine ⟨405955180987951623572455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8660377194409634636212373 405955180987951623572455)
                  ·
                    rfl

theorem cell22_3557677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 2, 1, 6].length) (baseStart_3557677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3557677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3557677 prefixEnd_3557677 := by exact prefixLift 3557677
  have htrace : WordTrace (prefixWord ++ tailWord_3557677) baseStart_3557677 baseEnd_3557677 := by
    simpa [prefixWord, tailWord_3557677, baseEnd_3557677] using wordTrace_append hprefix tailTrace_3557677
  have hstable : (prefixWord ++ tailWord_3557677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3557677).length < 2 ^ (prefixWord ++ tailWord_3557677).sum := by decide
  have hdescent : baseEnd_3557677 < baseStart_3557677 := by decide
  rcases family_descends (prefixWord ++ tailWord_3557677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3557692 : List Nat := [2, 2, 2, 2, 1, 2, 5, 1, 2, 3]
def baseStart_3557692 : Nat := 118140960795 + 3557692 * 2 ^ 59
def prefixEnd_3557692 : Nat := 4983230072969 + 3 ^ 40 * 3557692 * 2
def baseEnd_3557692 : Nat := 1217870677770399831592319

theorem tailTrace_3557692 : CollatzResearch.WordTrace tailWord_3557692 prefixEnd_3557692 1217870677770399831592319 := by
  unfold tailWord_3557692
  simp only [CollatzResearch.WordTrace]
  refine ⟨64879843713548482132385665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86506458284731309509847553 64879843713548482132385665)
  ·
    refine ⟨48659882785161361599289249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64879843713548482132385665 48659882785161361599289249)
    ·
      refine ⟨36494912088871021199466937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48659882785161361599289249 36494912088871021199466937)
      ·
        refine ⟨27371184066653265899600203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36494912088871021199466937 27371184066653265899600203)
        ·
          refine ⟨41056776099979898849400305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27371184066653265899600203 41056776099979898849400305)
          ·
            refine ⟨30792582074984924137050229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41056776099979898849400305 30792582074984924137050229)
            ·
              refine ⟨2886804569529836637848459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30792582074984924137050229 2886804569529836637848459)
              ·
                refine ⟨4330206854294754956772689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2886804569529836637848459 4330206854294754956772689)
                ·
                  refine ⟨3247655140721066217579517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4330206854294754956772689 3247655140721066217579517)
                  ·
                    refine ⟨1217870677770399831592319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3247655140721066217579517 1217870677770399831592319)
                    ·
                      rfl

theorem cell22_3557692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 5, 1, 2, 3].length) (baseStart_3557692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3557692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3557692 prefixEnd_3557692 := by exact prefixLift 3557692
  have htrace : WordTrace (prefixWord ++ tailWord_3557692) baseStart_3557692 baseEnd_3557692 := by
    simpa [prefixWord, tailWord_3557692, baseEnd_3557692] using wordTrace_append hprefix tailTrace_3557692
  have hstable : (prefixWord ++ tailWord_3557692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3557692).length < 2 ^ (prefixWord ++ tailWord_3557692).sum := by decide
  have hdescent : baseEnd_3557692 < baseStart_3557692 := by decide
  rcases family_descends (prefixWord ++ tailWord_3557692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3557733 : List Nat := [1, 3, 1, 3, 1, 3, 2, 1, 7]
def baseStart_3557733 : Nat := 118140960795 + 3557733 * 2 ^ 59
def prefixEnd_3557733 : Nat := 4983230072969 + 3 ^ 40 * 3557733 * 2
def baseEnd_3557733 : Nat := 405961570969429797105731

theorem tailTrace_3557733 : CollatzResearch.WordTrace tailWord_3557733 prefixEnd_3557733 405961570969429797105731 := by
  unfold tailWord_3557733
  simp only [CollatzResearch.WordTrace]
  refine ⟨129761182819948428267013853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86507455213298952178009235 129761182819948428267013853)
  ·
    refine ⟨48660443557480660600130195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129761182819948428267013853 48660443557480660600130195)
    ·
      refine ⟨72990665336220990900195293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48660443557480660600130195 72990665336220990900195293)
      ·
        refine ⟨27371499501082871587573235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72990665336220990900195293 27371499501082871587573235)
        ·
          refine ⟨41057249251624307381359853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27371499501082871587573235 41057249251624307381359853)
          ·
            refine ⟨15396468469359115268009945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41057249251624307381359853 15396468469359115268009945)
            ·
              refine ⟨11547351352019336451007459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15396468469359115268009945 11547351352019336451007459)
              ·
                refine ⟨17321027028029004676511189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11547351352019336451007459 17321027028029004676511189)
                ·
                  refine ⟨405961570969429797105731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17321027028029004676511189 405961570969429797105731)
                  ·
                    rfl

theorem cell22_3557733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 1, 7].length) (baseStart_3557733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3557733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3557733 prefixEnd_3557733 := by exact prefixLift 3557733
  have htrace : WordTrace (prefixWord ++ tailWord_3557733) baseStart_3557733 baseEnd_3557733 := by
    simpa [prefixWord, tailWord_3557733, baseEnd_3557733] using wordTrace_append hprefix tailTrace_3557733
  have hstable : (prefixWord ++ tailWord_3557733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3557733).length < 2 ^ (prefixWord ++ tailWord_3557733).sum := by decide
  have hdescent : baseEnd_3557733 < baseStart_3557733 := by decide
  rcases family_descends (prefixWord ++ tailWord_3557733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3557810 : List Nat := [3, 2, 1, 1, 1, 1, 6, 1, 1, 5]
def baseStart_3557810 : Nat := 118140960795 + 3557810 * 2 ^ 59
def prefixEnd_3557810 : Nat := 4983230072969 + 3 ^ 40 * 3557810 * 2
def baseEnd_3557810 : Nat := 1217911071581886857141957

theorem tailTrace_3557810 : CollatzResearch.WordTrace tailWord_3557810 prefixEnd_3557810 1217911071581886857141957 := by
  unfold tailWord_3557810
  simp only [CollatzResearch.WordTrace]
  refine ⟨32440997810167367604391721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86509327493779646945044589 32440997810167367604391721)
  ·
    refine ⟨24330748357625525703293791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32440997810167367604391721 24330748357625525703293791)
    ·
      refine ⟨36496122536438288554940687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24330748357625525703293791 36496122536438288554940687)
      ·
        refine ⟨54744183804657432832411031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36496122536438288554940687 54744183804657432832411031)
        ·
          refine ⟨82116275706986149248616547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54744183804657432832411031 82116275706986149248616547)
          ·
            refine ⟨123174413560479223872924821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82116275706986149248616547 123174413560479223872924821)
            ·
              refine ⟨5773800635647463619043351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 123174413560479223872924821 5773800635647463619043351)
              ·
                refine ⟨8660700953471195428565027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5773800635647463619043351 8660700953471195428565027)
                ·
                  refine ⟨12991051430206793142847541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8660700953471195428565027 12991051430206793142847541)
                  ·
                    refine ⟨1217911071581886857141957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12991051430206793142847541 1217911071581886857141957)
                    ·
                      rfl

theorem cell22_3557810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 6, 1, 1, 5].length) (baseStart_3557810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3557810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3557810 prefixEnd_3557810 := by exact prefixLift 3557810
  have htrace : WordTrace (prefixWord ++ tailWord_3557810) baseStart_3557810 baseEnd_3557810 := by
    simpa [prefixWord, tailWord_3557810, baseEnd_3557810] using wordTrace_append hprefix tailTrace_3557810
  have hstable : (prefixWord ++ tailWord_3557810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3557810).length < 2 ^ (prefixWord ++ tailWord_3557810).sum := by decide
  have hdescent : baseEnd_3557810 < baseStart_3557810 := by decide
  rcases family_descends (prefixWord ++ tailWord_3557810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3557844 : List Nat := [2, 4, 1, 2, 2, 1, 3, 2, 2, 3]
def baseStart_3557844 : Nat := 118140960795 + 3557844 * 2 ^ 59
def prefixEnd_3557844 : Nat := 4983230072969 + 3 ^ 40 * 3557844 * 2
def baseEnd_3557844 : Nat := 1217922710476722101791853

theorem tailTrace_3557844 : CollatzResearch.WordTrace tailWord_3557844 prefixEnd_3557844 1217922710476722101791853 := by
  unfold tailWord_3557844
  simp only [CollatzResearch.WordTrace]
  refine ⟨64882615661273147112152293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86510154215030862816203057 64882615661273147112152293)
  ·
    refine ⟨12165490436488715083528555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64882615661273147112152293 12165490436488715083528555)
    ·
      refine ⟨18248235654733072625292833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12165490436488715083528555 18248235654733072625292833)
      ·
        refine ⟨13686176741049804468969625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18248235654733072625292833 13686176741049804468969625)
        ·
          refine ⟨10264632555787353351727219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13686176741049804468969625 10264632555787353351727219)
          ·
            refine ⟨15396948833681030027590829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10264632555787353351727219 15396948833681030027590829)
            ·
              refine ⟨5773855812630386260346561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15396948833681030027590829 5773855812630386260346561)
              ·
                refine ⟨4330391859472789695259921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5773855812630386260346561 4330391859472789695259921)
                ·
                  refine ⟨3247793894604592271444941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4330391859472789695259921 3247793894604592271444941)
                  ·
                    refine ⟨1217922710476722101791853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3247793894604592271444941 1217922710476722101791853)
                    ·
                      rfl

theorem cell22_3557844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 3, 2, 2, 3].length) (baseStart_3557844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3557844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3557844 prefixEnd_3557844 := by exact prefixLift 3557844
  have htrace : WordTrace (prefixWord ++ tailWord_3557844) baseStart_3557844 baseEnd_3557844 := by
    simpa [prefixWord, tailWord_3557844, baseEnd_3557844] using wordTrace_append hprefix tailTrace_3557844
  have hstable : (prefixWord ++ tailWord_3557844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3557844).length < 2 ^ (prefixWord ++ tailWord_3557844).sum := by decide
  have hdescent : baseEnd_3557844 < baseStart_3557844 := by decide
  rcases family_descends (prefixWord ++ tailWord_3557844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3557861 : List Nat := [1, 3, 1, 5, 2, 1, 3, 1, 2, 3]
def baseStart_3557861 : Nat := 118140960795 + 3557861 * 2 ^ 59
def prefixEnd_3557861 : Nat := 4983230072969 + 3 ^ 40 * 3557861 * 2
def baseEnd_3557861 : Nat := 1217928529924139724116801

theorem tailTrace_3557861 : CollatzResearch.WordTrace tailWord_3557861 prefixEnd_3557861 1217928529924139724116801 := by
  unfold tailWord_3557861
  simp only [CollatzResearch.WordTrace]
  refine ⟨129765851363484706127673437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86510567575656470751782291 129765851363484706127673437)
  ·
    refine ⟨48662194261306764797877539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129765851363484706127673437 48662194261306764797877539)
    ·
      refine ⟨72993291391960147196816309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48662194261306764797877539 72993291391960147196816309)
      ·
        refine ⟨6843121067996263799701529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 72993291391960147196816309 6843121067996263799701529)
        ·
          refine ⟨5132340800997197849776147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6843121067996263799701529 5132340800997197849776147)
          ·
            refine ⟨7698511201495796774664221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5132340800997197849776147 7698511201495796774664221)
            ·
              refine ⟨2886941700560923790499083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7698511201495796774664221 2886941700560923790499083)
              ·
                refine ⟨4330412550841385685748625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2886941700560923790499083 4330412550841385685748625)
                ·
                  refine ⟨3247809413131039264311469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4330412550841385685748625 3247809413131039264311469)
                  ·
                    refine ⟨1217928529924139724116801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3247809413131039264311469 1217928529924139724116801)
                    ·
                      rfl

theorem cell22_3557861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 3, 1, 2, 3].length) (baseStart_3557861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3557861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3557861 prefixEnd_3557861 := by exact prefixLift 3557861
  have htrace : WordTrace (prefixWord ++ tailWord_3557861) baseStart_3557861 baseEnd_3557861 := by
    simpa [prefixWord, tailWord_3557861, baseEnd_3557861] using wordTrace_append hprefix tailTrace_3557861
  have hstable : (prefixWord ++ tailWord_3557861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3557861).length < 2 ^ (prefixWord ++ tailWord_3557861).sum := by decide
  have hdescent : baseEnd_3557861 < baseStart_3557861 := by decide
  rcases family_descends (prefixWord ++ tailWord_3557861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3557874 : List Nat := [3, 2, 1, 4, 2, 2, 2, 6]
def baseStart_3557874 : Nat := 118140960795 + 3557874 * 2 ^ 59
def prefixEnd_3557874 : Nat := 4983230072969 + 3 ^ 40 * 3557874 * 2
def baseEnd_3557874 : Nat := 135325886676645780393529

theorem tailTrace_3557874 : CollatzResearch.WordTrace tailWord_3557874 prefixEnd_3557874 135325886676645780393529 := by
  unfold tailWord_3557874
  simp only [CollatzResearch.WordTrace]
  refine ⟨32441581378109402336974169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86510883674958406231931117 32441581378109402336974169)
  ·
    refine ⟨24331186033582051752730627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32441581378109402336974169 24331186033582051752730627)
    ·
      refine ⟨36496779050373077629095941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24331186033582051752730627 36496779050373077629095941)
      ·
        refine ⟨6843146071944952055455489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36496779050373077629095941 6843146071944952055455489)
        ·
          refine ⟨5132359553958714041591617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6843146071944952055455489 5132359553958714041591617)
          ·
            refine ⟨3849269665469035531193713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5132359553958714041591617 3849269665469035531193713)
            ·
              refine ⟨2886952249101776648395285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3849269665469035531193713 2886952249101776648395285)
              ·
                refine ⟨135325886676645780393529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2886952249101776648395285 135325886676645780393529)
                ·
                  rfl

theorem cell22_3557874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 2, 6].length) (baseStart_3557874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3557874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3557874 prefixEnd_3557874 := by exact prefixLift 3557874
  have htrace : WordTrace (prefixWord ++ tailWord_3557874) baseStart_3557874 baseEnd_3557874 := by
    simpa [prefixWord, tailWord_3557874, baseEnd_3557874] using wordTrace_append hprefix tailTrace_3557874
  have hstable : (prefixWord ++ tailWord_3557874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3557874).length < 2 ^ (prefixWord ++ tailWord_3557874).sum := by decide
  have hdescent : baseEnd_3557874 < baseStart_3557874 := by decide
  rcases family_descends (prefixWord ++ tailWord_3557874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3558013 : List Nat := [1, 4, 1, 1, 6, 1, 1, 2, 2, 3]
def baseStart_3558013 : Nat := 118140960795 + 3558013 * 2 ^ 59
def prefixEnd_3558013 : Nat := 4983230072969 + 3 ^ 40 * 3558013 * 2
def baseEnd_3558013 : Nat := 1217980562630461994316335

theorem tailTrace_3558013 : CollatzResearch.WordTrace tailWord_3558013 prefixEnd_3558013 1217980562630461994316335 := by
  unfold tailWord_3558013
  simp only [CollatzResearch.WordTrace]
  refine ⟨129771395258934036087206693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86514263505956024058137795 129771395258934036087206693)
  ·
    refine ⟨24332136611050131766351255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129771395258934036087206693 24332136611050131766351255)
    ·
      refine ⟨36498204916575197649526883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24332136611050131766351255 36498204916575197649526883)
      ·
        refine ⟨54747307374862796474290325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36498204916575197649526883 54747307374862796474290325)
        ·
          refine ⟨2566280033196693584732359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 54747307374862796474290325 2566280033196693584732359)
          ·
            refine ⟨3849420049795040377098539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2566280033196693584732359 3849420049795040377098539)
            ·
              refine ⟨5774130074692560565647809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3849420049795040377098539 5774130074692560565647809)
              ·
                refine ⟨4330597556019420424235857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5774130074692560565647809 4330597556019420424235857)
                ·
                  refine ⟨3247948167014565318176893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4330597556019420424235857 3247948167014565318176893)
                  ·
                    refine ⟨1217980562630461994316335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3247948167014565318176893 1217980562630461994316335)
                    ·
                      rfl

theorem cell22_3558013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 1, 2, 2, 3].length) (baseStart_3558013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3558013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3558013 prefixEnd_3558013 := by exact prefixLift 3558013
  have htrace : WordTrace (prefixWord ++ tailWord_3558013) baseStart_3558013 baseEnd_3558013 := by
    simpa [prefixWord, tailWord_3558013, baseEnd_3558013] using wordTrace_append hprefix tailTrace_3558013
  have hstable : (prefixWord ++ tailWord_3558013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3558013).length < 2 ^ (prefixWord ++ tailWord_3558013).sum := by decide
  have hdescent : baseEnd_3558013 < baseStart_3558013 := by decide
  rcases family_descends (prefixWord ++ tailWord_3558013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3558097 : List Nat := [1, 2, 2, 1, 2, 3, 2, 3, 1, 5]
def baseStart_3558097 : Nat := 118140960795 + 3558097 * 2 ^ 59
def prefixEnd_3558097 : Nat := 4983230072969 + 3 ^ 40 * 3558097 * 2
def baseEnd_3558097 : Nat := 1218009317547113775216077

theorem tailTrace_3558097 : CollatzResearch.WordTrace tailWord_3558097 prefixEnd_3558097 1218009317547113775216077 := by
  unfold tailWord_3558097
  simp only [CollatzResearch.WordTrace]
  refine ⟨129774458990629718433264545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86516305993753145622176363 129774458990629718433264545)
  ·
    refine ⟨97330844242972288824948409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129774458990629718433264545 97330844242972288824948409)
    ·
      refine ⟨72998133182229216618711307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97330844242972288824948409 72998133182229216618711307)
      ·
        refine ⟨109497199773343824928066961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72998133182229216618711307 109497199773343824928066961)
        ·
          refine ⟨82122899830007868696050221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109497199773343824928066961 82122899830007868696050221)
          ·
            refine ⟨30796087436252950761018833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82122899830007868696050221 30796087436252950761018833)
            ·
              refine ⟨23097065577189713070764125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30796087436252950761018833 23097065577189713070764125)
              ·
                refine ⟨8661399591446142401536547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23097065577189713070764125 8661399591446142401536547)
                ·
                  refine ⟨12992099387169213602304821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8661399591446142401536547 12992099387169213602304821)
                  ·
                    refine ⟨1218009317547113775216077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12992099387169213602304821 1218009317547113775216077)
                    ·
                      rfl

theorem cell22_3558097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 3, 1, 5].length) (baseStart_3558097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3558097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3558097 prefixEnd_3558097 := by exact prefixLift 3558097
  have htrace : WordTrace (prefixWord ++ tailWord_3558097) baseStart_3558097 baseEnd_3558097 := by
    simpa [prefixWord, tailWord_3558097, baseEnd_3558097] using wordTrace_append hprefix tailTrace_3558097
  have hstable : (prefixWord ++ tailWord_3558097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3558097).length < 2 ^ (prefixWord ++ tailWord_3558097).sum := by decide
  have hdescent : baseEnd_3558097 < baseStart_3558097 := by decide
  rcases family_descends (prefixWord ++ tailWord_3558097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3558101 : List Nat := [1, 3, 2, 5, 1, 1, 1, 1, 3, 4]
def baseStart_3558101 : Nat := 118140960795 + 3558101 * 2 ^ 59
def prefixEnd_3558101 : Nat := 4983230072969 + 3 ^ 40 * 3558101 * 2
def baseEnd_3558101 : Nat := 1218010686828859098116065

theorem tailTrace_3558101 : CollatzResearch.WordTrace tailWord_3558101 prefixEnd_3558101 1218010686828859098116065 := by
  unfold tailWord_3558101
  simp only [CollatzResearch.WordTrace]
  refine ⟨129774604882615227116410157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86516403255076818077606771 129774604882615227116410157)
  ·
    refine ⟨48665476830980710168653809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129774604882615227116410157 48665476830980710168653809)
    ·
      refine ⟨36499107623235532626490357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48665476830980710168653809 36499107623235532626490357)
      ·
        refine ⟨3421791339678331183733471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36499107623235532626490357 3421791339678331183733471)
        ·
          refine ⟨5132687009517496775600207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3421791339678331183733471 5132687009517496775600207)
          ·
            refine ⟨7699030514276245163400311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5132687009517496775600207 7699030514276245163400311)
            ·
              refine ⟨11548545771414367745100467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7699030514276245163400311 11548545771414367745100467)
              ·
                refine ⟨17322818657121551617650701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11548545771414367745100467 17322818657121551617650701)
                ·
                  refine ⟨6496056996420581856619013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17322818657121551617650701 6496056996420581856619013)
                  ·
                    refine ⟨1218010686828859098116065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6496056996420581856619013 1218010686828859098116065)
                    ·
                      rfl

theorem cell22_3558101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 1, 3, 4].length) (baseStart_3558101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3558101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3558101 prefixEnd_3558101 := by exact prefixLift 3558101
  have htrace : WordTrace (prefixWord ++ tailWord_3558101) baseStart_3558101 baseEnd_3558101 := by
    simpa [prefixWord, tailWord_3558101, baseEnd_3558101] using wordTrace_append hprefix tailTrace_3558101
  have hstable : (prefixWord ++ tailWord_3558101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3558101).length < 2 ^ (prefixWord ++ tailWord_3558101).sum := by decide
  have hdescent : baseEnd_3558101 < baseStart_3558101 := by decide
  rcases family_descends (prefixWord ++ tailWord_3558101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3558159 : List Nat := [1, 1, 2, 1, 1, 1, 7, 2, 3, 3]
def baseStart_3558159 : Nat := 118140960795 + 3558159 * 2 ^ 59
def prefixEnd_3558159 : Nat := 4983230072969 + 3 ^ 40 * 3558159 * 2
def baseEnd_3558159 : Nat := 1218030541414166280165887

theorem tailTrace_3558159 : CollatzResearch.WordTrace tailWord_3558159 prefixEnd_3558159 1218030541414166280165887 := by
  unfold tailWord_3558159
  simp only [CollatzResearch.WordTrace]
  refine ⟨129776720316405103022021531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86517813544270068681347687 129776720316405103022021531)
  ·
    refine ⟨194665080474607654533032297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129776720316405103022021531 194665080474607654533032297)
    ·
      refine ⟨145998810355955740899774223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194665080474607654533032297 145998810355955740899774223)
      ·
        refine ⟨218998215533933611349661335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145998810355955740899774223 218998215533933611349661335)
        ·
          refine ⟨328497323300900417024492003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218998215533933611349661335 328497323300900417024492003)
          ·
            refine ⟨492745984951350625536738005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 328497323300900417024492003 492745984951350625536738005)
            ·
              refine ⟨11548734022297280286017297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 492745984951350625536738005 11548734022297280286017297)
              ·
                refine ⟨8661550516722960214512973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11548734022297280286017297 8661550516722960214512973)
                ·
                  refine ⟨3248081443771110080442365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8661550516722960214512973 3248081443771110080442365)
                  ·
                    refine ⟨1218030541414166280165887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3248081443771110080442365 1218030541414166280165887)
                    ·
                      rfl

theorem cell22_3558159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 2, 3, 3].length) (baseStart_3558159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3558159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3558159 prefixEnd_3558159 := by exact prefixLift 3558159
  have htrace : WordTrace (prefixWord ++ tailWord_3558159) baseStart_3558159 baseEnd_3558159 := by
    simpa [prefixWord, tailWord_3558159, baseEnd_3558159] using wordTrace_append hprefix tailTrace_3558159
  have hstable : (prefixWord ++ tailWord_3558159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3558159).length < 2 ^ (prefixWord ++ tailWord_3558159).sum := by decide
  have hdescent : baseEnd_3558159 < baseStart_3558159 := by decide
  rcases family_descends (prefixWord ++ tailWord_3558159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3558187 : List Nat := [1, 1, 1, 1, 2, 1, 2, 6, 2, 5]
def baseStart_3558187 : Nat := 118140960795 + 3558187 * 2 ^ 59
def prefixEnd_3558187 : Nat := 4983230072969 + 3 ^ 40 * 3558187 * 2
def baseEnd_3558187 : Nat := 1218040126386383540465801

theorem tailTrace_3558187 : CollatzResearch.WordTrace tailWord_3558187 prefixEnd_3558187 1218040126386383540465801 := by
  unfold tailWord_3558187
  simp only [CollatzResearch.WordTrace]
  refine ⟨129777741560303663804040815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86518494373535775869360543 129777741560303663804040815)
  ·
    refine ⟨194666612340455495706061223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129777741560303663804040815 194666612340455495706061223)
    ·
      refine ⟨291999918510683243559091835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194666612340455495706061223 291999918510683243559091835)
      ·
        refine ⟨437999877766024865338637753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291999918510683243559091835 437999877766024865338637753)
        ·
          refine ⟨328499908324518649003978315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 437999877766024865338637753 328499908324518649003978315)
          ·
            refine ⟨492749862486777973505967473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 328499908324518649003978315 492749862486777973505967473)
            ·
              refine ⟨369562396865083480129475605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 492749862486777973505967473 369562396865083480129475605)
              ·
                refine ⟨17323237353050788131069169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 369562396865083480129475605 17323237353050788131069169)
                ·
                  refine ⟨12992428014788091098301877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17323237353050788131069169 12992428014788091098301877)
                  ·
                    refine ⟨1218040126386383540465801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12992428014788091098301877 1218040126386383540465801)
                    ·
                      rfl

theorem cell22_3558187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 6, 2, 5].length) (baseStart_3558187 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3558187 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3558187 prefixEnd_3558187 := by exact prefixLift 3558187
  have htrace : WordTrace (prefixWord ++ tailWord_3558187) baseStart_3558187 baseEnd_3558187 := by
    simpa [prefixWord, tailWord_3558187, baseEnd_3558187] using wordTrace_append hprefix tailTrace_3558187
  have hstable : (prefixWord ++ tailWord_3558187).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3558187).length < 2 ^ (prefixWord ++ tailWord_3558187).sum := by decide
  have hdescent : baseEnd_3558187 < baseStart_3558187 := by decide
  rcases family_descends (prefixWord ++ tailWord_3558187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3558279 : List Nat := [1, 1, 4, 2, 3, 1, 2, 8]
def baseStart_3558279 : Nat := 118140960795 + 3558279 * 2 ^ 59
def prefixEnd_3558279 : Nat := 4983230072969 + 3 ^ 40 * 3558279 * 2
def baseEnd_3558279 : Nat := 135341291096280663018391

theorem tailTrace_3558279 : CollatzResearch.WordTrace tailWord_3558279 prefixEnd_3558279 135341291096280663018391 := by
  unfold tailWord_3558279
  simp only [CollatzResearch.WordTrace]
  refine ⟨129781097075970363516389891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86520731383980242344259927 129781097075970363516389891)
  ·
    refine ⟨194671645613955545274584837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129781097075970363516389891 194671645613955545274584837)
    ·
      refine ⟨36500933552616664738984657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 194671645613955545274584837 36500933552616664738984657)
      ·
        refine ⟨27375700164462498554238493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36500933552616664738984657 27375700164462498554238493)
        ·
          refine ⟨10265887561673436957839435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27375700164462498554238493 10265887561673436957839435)
          ·
            refine ⟨15398831342510155436759153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10265887561673436957839435 15398831342510155436759153)
            ·
              refine ⟨11549123506882616577569365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15398831342510155436759153 11549123506882616577569365)
              ·
                refine ⟨135341291096280663018391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11549123506882616577569365 135341291096280663018391)
                ·
                  rfl

theorem cell22_3558279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 8].length) (baseStart_3558279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3558279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3558279 prefixEnd_3558279 := by exact prefixLift 3558279
  have htrace : WordTrace (prefixWord ++ tailWord_3558279) baseStart_3558279 baseEnd_3558279 := by
    simpa [prefixWord, tailWord_3558279, baseEnd_3558279] using wordTrace_append hprefix tailTrace_3558279
  have hstable : (prefixWord ++ tailWord_3558279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3558279).length < 2 ^ (prefixWord ++ tailWord_3558279).sum := by decide
  have hdescent : baseEnd_3558279 < baseStart_3558279 := by decide
  rcases family_descends (prefixWord ++ tailWord_3558279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3558281 : List Nat := [1, 2, 1, 1, 5, 3, 2, 1, 2, 4]
def baseStart_3558281 : Nat := 118140960795 + 3558281 * 2 ^ 59
def prefixEnd_3558281 : Nat := 4983230072969 + 3 ^ 40 * 3558281 * 2
def baseEnd_3558281 : Nat := 1218072304507398628615513

theorem tailTrace_3558281 : CollatzResearch.WordTrace tailWord_3558281 prefixEnd_3558281 1218072304507398628615513 := by
  unfold tailWord_3558281
  simp only [CollatzResearch.WordTrace]
  refine ⟨129781170021963117857962697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86520780014642078571975131 129781170021963117857962697)
  ·
    refine ⟨97335877516472338393472023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129781170021963117857962697 97335877516472338393472023)
    ·
      refine ⟨146003816274708507590208035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97335877516472338393472023 146003816274708507590208035)
      ·
        refine ⟨219005724412062761385312053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146003816274708507590208035 219005724412062761385312053)
        ·
          refine ⟨20531786663630883879873005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 219005724412062761385312053 20531786663630883879873005)
          ·
            refine ⟨7699419998861581454952377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20531786663630883879873005 7699419998861581454952377)
            ·
              refine ⟨5774564999146186091214283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7699419998861581454952377 5774564999146186091214283)
              ·
                refine ⟨8661847498719279136821425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5774564999146186091214283 8661847498719279136821425)
                ·
                  refine ⟨6496385624039459352616069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8661847498719279136821425 6496385624039459352616069)
                  ·
                    refine ⟨1218072304507398628615513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6496385624039459352616069 1218072304507398628615513)
                    ·
                      rfl

theorem cell22_3558281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 2, 1, 2, 4].length) (baseStart_3558281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3558281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3558281 prefixEnd_3558281 := by exact prefixLift 3558281
  have htrace : WordTrace (prefixWord ++ tailWord_3558281) baseStart_3558281 baseEnd_3558281 := by
    simpa [prefixWord, tailWord_3558281, baseEnd_3558281] using wordTrace_append hprefix tailTrace_3558281
  have hstable : (prefixWord ++ tailWord_3558281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3558281).length < 2 ^ (prefixWord ++ tailWord_3558281).sum := by decide
  have hdescent : baseEnd_3558281 < baseStart_3558281 := by decide
  rcases family_descends (prefixWord ++ tailWord_3558281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3558300 : List Nat := [2, 2, 3, 3, 2, 1, 2, 2, 2, 3]
def baseStart_3558300 : Nat := 118140960795 + 3558300 * 2 ^ 59
def prefixEnd_3558300 : Nat := 4983230072969 + 3 ^ 40 * 3558300 * 2
def baseEnd_3558300 : Nat := 1218078808595688912390455

theorem tailTrace_3558300 : CollatzResearch.WordTrace tailWord_3558300 prefixEnd_3558300 1218078808595688912390455 := by
  unfold tailWord_3558300
  simp only [CollatzResearch.WordTrace]
  refine ⟨64890931504447142051452177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86521242005929522735269569 64890931504447142051452177)
  ·
    refine ⟨48668198628335356538589133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64890931504447142051452177 48668198628335356538589133)
    ·
      refine ⟨18250574485625758701970925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48668198628335356538589133 18250574485625758701970925)
      ·
        refine ⟨6843965432109659513239097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18250574485625758701970925 6843965432109659513239097)
        ·
          refine ⟨5132974074082244634929323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6843965432109659513239097 5132974074082244634929323)
          ·
            refine ⟨7699461111123366952393985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5132974074082244634929323 7699461111123366952393985)
            ·
              refine ⟨5774595833342525214295489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7699461111123366952393985 5774595833342525214295489)
              ·
                refine ⟨4330946875006893910721617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5774595833342525214295489 4330946875006893910721617)
                ·
                  refine ⟨3248210156255170433041213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4330946875006893910721617 3248210156255170433041213)
                  ·
                    refine ⟨1218078808595688912390455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3248210156255170433041213 1218078808595688912390455)
                    ·
                      rfl

theorem cell22_3558300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 2, 2, 2, 3].length) (baseStart_3558300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3558300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3558300 prefixEnd_3558300 := by exact prefixLift 3558300
  have htrace : WordTrace (prefixWord ++ tailWord_3558300) baseStart_3558300 baseEnd_3558300 := by
    simpa [prefixWord, tailWord_3558300, baseEnd_3558300] using wordTrace_append hprefix tailTrace_3558300
  have hstable : (prefixWord ++ tailWord_3558300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3558300).length < 2 ^ (prefixWord ++ tailWord_3558300).sum := by decide
  have hdescent : baseEnd_3558300 < baseStart_3558300 := by decide
  rcases family_descends (prefixWord ++ tailWord_3558300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3558356 : List Nat := [2, 4, 1, 2, 1, 2, 1, 2, 2, 5]
def baseStart_3558356 : Nat := 118140960795 + 3558356 * 2 ^ 59
def prefixEnd_3558356 : Nat := 4983230072969 + 3 ^ 40 * 3558356 * 2
def baseEnd_3558356 : Nat := 1218097978540123432990283

theorem tailTrace_3558356 : CollatzResearch.WordTrace tailWord_3558356 prefixEnd_3558356 1218097978540123432990283 := by
  unfold tailWord_3558356
  simp only [CollatzResearch.WordTrace]
  refine ⟨64891952748345702833471461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86522603664460937111295281 64891952748345702833471461)
  ·
    refine ⟨12167241140314819281275899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64891952748345702833471461 12167241140314819281275899)
    ·
      refine ⟨18250861710472228921913849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12167241140314819281275899 18250861710472228921913849)
      ·
        refine ⟨13688146282854171691435387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18250861710472228921913849 13688146282854171691435387)
        ·
          refine ⟨20532219424281257537153081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13688146282854171691435387 20532219424281257537153081)
          ·
            refine ⟨15399164568210943152864811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20532219424281257537153081 15399164568210943152864811)
            ·
              refine ⟨23098746852316414729297217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15399164568210943152864811 23098746852316414729297217)
              ·
                refine ⟨17324060139237311046972913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23098746852316414729297217 17324060139237311046972913)
                ·
                  refine ⟨12993045104427983285229685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17324060139237311046972913 12993045104427983285229685)
                  ·
                    refine ⟨1218097978540123432990283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12993045104427983285229685 1218097978540123432990283)
                    ·
                      rfl

theorem cell22_3558356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 2, 2, 5].length) (baseStart_3558356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3558356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3558356 prefixEnd_3558356 := by exact prefixLift 3558356
  have htrace : WordTrace (prefixWord ++ tailWord_3558356) baseStart_3558356 baseEnd_3558356 := by
    simpa [prefixWord, tailWord_3558356, baseEnd_3558356] using wordTrace_append hprefix tailTrace_3558356
  have hstable : (prefixWord ++ tailWord_3558356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3558356).length < 2 ^ (prefixWord ++ tailWord_3558356).sum := by decide
  have hdescent : baseEnd_3558356 < baseStart_3558356 := by decide
  rcases family_descends (prefixWord ++ tailWord_3558356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3558358 : List Nat := [5, 2, 1, 1, 2, 2, 1, 1, 7]
def baseStart_3558358 : Nat := 118140960795 + 3558358 * 2 ^ 59
def prefixEnd_3558358 : Nat := 4983230072969 + 3 ^ 40 * 3558358 * 2
def baseEnd_3558358 : Nat := 406032887726998698146759

theorem tailTrace_3558358 : CollatzResearch.WordTrace tailWord_3558358 prefixEnd_3558358 406032887726998698146759 := by
  unfold tailWord_3558358
  simp only [CollatzResearch.WordTrace]
  refine ⟨8111498652667760000532233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 86522652295122773339010485 8111498652667760000532233)
  ·
    refine ⟨6083623989500820000399175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8111498652667760000532233 6083623989500820000399175)
    ·
      refine ⟨9125435984251230000598763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6083623989500820000399175 9125435984251230000598763)
      ·
        refine ⟨13688153976376845000898145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9125435984251230000598763 13688153976376845000898145)
        ·
          refine ⟨10266115482282633750673609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13688153976376845000898145 10266115482282633750673609)
          ·
            refine ⟨7699586611711975313005207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10266115482282633750673609 7699586611711975313005207)
            ·
              refine ⟨11549379917567962969507811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7699586611711975313005207 11549379917567962969507811)
              ·
                refine ⟨17324069876351944454261717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11549379917567962969507811 17324069876351944454261717)
                ·
                  refine ⟨406032887726998698146759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17324069876351944454261717 406032887726998698146759)
                  ·
                    rfl

theorem cell22_3558358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_3558358 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3558358 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3558358 prefixEnd_3558358 := by exact prefixLift 3558358
  have htrace : WordTrace (prefixWord ++ tailWord_3558358) baseStart_3558358 baseEnd_3558358 := by
    simpa [prefixWord, tailWord_3558358, baseEnd_3558358] using wordTrace_append hprefix tailTrace_3558358
  have hstable : (prefixWord ++ tailWord_3558358).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3558358).length < 2 ^ (prefixWord ++ tailWord_3558358).sum := by decide
  have hdescent : baseEnd_3558358 < baseStart_3558358 := by decide
  rcases family_descends (prefixWord ++ tailWord_3558358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3558431 : List Nat := [1, 1, 2, 4, 1, 4, 2, 7]
def baseStart_3558431 : Nat := 118140960795 + 3558431 * 2 ^ 59
def prefixEnd_3558431 : Nat := 4983230072969 + 3 ^ 40 * 3558431 * 2
def baseEnd_3558431 : Nat := 135347072508094248596117

theorem tailTrace_3558431 : CollatzResearch.WordTrace tailWord_3558431 prefixEnd_3558431 135347072508094248596117 := by
  unfold tailWord_3558431
  simp only [CollatzResearch.WordTrace]
  refine ⟨129786640971419693475923147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86524427314279795650615431 129786640971419693475923147)
  ·
    refine ⟨194679961457129540213884721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129786640971419693475923147 194679961457129540213884721)
    ·
      refine ⟨146009971092847155160413541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194679961457129540213884721 146009971092847155160413541)
      ·
        refine ⟨27376869579908841592577539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 146009971092847155160413541 27376869579908841592577539)
        ·
          refine ⟨41065304369863262388866309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27376869579908841592577539 41065304369863262388866309)
          ·
            refine ⟨7699744569349361697912433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41065304369863262388866309 7699744569349361697912433)
            ·
              refine ⟨5774808427012021273434325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7699744569349361697912433 5774808427012021273434325)
              ·
                refine ⟨135347072508094248596117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5774808427012021273434325 135347072508094248596117)
                ·
                  rfl

theorem cell22_3558431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 2, 7].length) (baseStart_3558431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3558431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3558431 prefixEnd_3558431 := by exact prefixLift 3558431
  have htrace : WordTrace (prefixWord ++ tailWord_3558431) baseStart_3558431 baseEnd_3558431 := by
    simpa [prefixWord, tailWord_3558431, baseEnd_3558431] using wordTrace_append hprefix tailTrace_3558431
  have hstable : (prefixWord ++ tailWord_3558431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3558431).length < 2 ^ (prefixWord ++ tailWord_3558431).sum := by decide
  have hdescent : baseEnd_3558431 < baseStart_3558431 := by decide
  rcases family_descends (prefixWord ++ tailWord_3558431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3558435 : List Nat := [1, 1, 1, 4, 3, 2, 4, 1, 2, 3]
def baseStart_3558435 : Nat := 118140960795 + 3558435 * 2 ^ 59
def prefixEnd_3558435 : Nat := 4983230072969 + 3 ^ 40 * 3558435 * 2
def baseEnd_3558435 : Nat := 1218125021854593560265041

theorem tailTrace_3558435 : CollatzResearch.WordTrace tailWord_3558435 prefixEnd_3558435 1218125021854593560265041 := by
  unfold tailWord_3558435
  simp only [CollatzResearch.WordTrace]
  refine ⟨129786786863405202159068759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86524524575603468106045839 129786786863405202159068759)
  ·
    refine ⟨194680180295107803238603139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129786786863405202159068759 194680180295107803238603139)
    ·
      refine ⟨292020270442661704857904709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194680180295107803238603139 292020270442661704857904709)
      ·
        refine ⟨54753800707999069660857133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 292020270442661704857904709 54753800707999069660857133)
        ·
          refine ⟨20532675265499651122821425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54753800707999069660857133 20532675265499651122821425)
          ·
            refine ⟨15399506449124738342116069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20532675265499651122821425 15399506449124738342116069)
            ·
              refine ⟨2887407459210888439146763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15399506449124738342116069 2887407459210888439146763)
              ·
                refine ⟨4331111188816332658720145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2887407459210888439146763 4331111188816332658720145)
                ·
                  refine ⟨3248333391612249494040109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4331111188816332658720145 3248333391612249494040109)
                  ·
                    refine ⟨1218125021854593560265041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3248333391612249494040109 1218125021854593560265041)
                    ·
                      rfl

theorem cell22_3558435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 4, 1, 2, 3].length) (baseStart_3558435 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3558435 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3558435 prefixEnd_3558435 := by exact prefixLift 3558435
  have htrace : WordTrace (prefixWord ++ tailWord_3558435) baseStart_3558435 baseEnd_3558435 := by
    simpa [prefixWord, tailWord_3558435, baseEnd_3558435] using wordTrace_append hprefix tailTrace_3558435
  have hstable : (prefixWord ++ tailWord_3558435).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3558435).length < 2 ^ (prefixWord ++ tailWord_3558435).sum := by decide
  have hdescent : baseEnd_3558435 < baseStart_3558435 := by decide
  rcases family_descends (prefixWord ++ tailWord_3558435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3558538 : List Nat := [3, 1, 2, 3, 1, 1, 4, 1, 6]
def baseStart_3558538 : Nat := 118140960795 + 3558538 * 2 ^ 59
def prefixEnd_3558538 : Nat := 4983230072969 + 3 ^ 40 * 3558538 * 2
def baseEnd_3558538 : Nat := 406053426953178541646575

theorem tailTrace_3558538 : CollatzResearch.WordTrace tailWord_3558538 prefixEnd_3558538 406053426953178541646575 := by
  unfold tailWord_3558538
  simp only [CollatzResearch.WordTrace]
  refine ⟨32447635895508012687517067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86527029054688033833378845 32447635895508012687517067)
  ·
    refine ⟨48671453843262019031275601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32447635895508012687517067 48671453843262019031275601)
    ·
      refine ⟨36503590382446514273456701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48671453843262019031275601 36503590382446514273456701)
      ·
        refine ⟨13688846393417442852546263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36503590382446514273456701 13688846393417442852546263)
        ·
          refine ⟨20533269590126164278819395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13688846393417442852546263 20533269590126164278819395)
          ·
            refine ⟨30799904385189246418229093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20533269590126164278819395 30799904385189246418229093)
            ·
              refine ⟨5774982072222983703417955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30799904385189246418229093 5774982072222983703417955)
              ·
                refine ⟨8662473108334475555126933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5774982072222983703417955 8662473108334475555126933)
                ·
                  refine ⟨406053426953178541646575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8662473108334475555126933 406053426953178541646575)
                  ·
                    rfl

theorem cell22_3558538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 4, 1, 6].length) (baseStart_3558538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3558538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3558538 prefixEnd_3558538 := by exact prefixLift 3558538
  have htrace : WordTrace (prefixWord ++ tailWord_3558538) baseStart_3558538 baseEnd_3558538 := by
    simpa [prefixWord, tailWord_3558538, baseEnd_3558538] using wordTrace_append hprefix tailTrace_3558538
  have hstable : (prefixWord ++ tailWord_3558538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3558538).length < 2 ^ (prefixWord ++ tailWord_3558538).sum := by decide
  have hdescent : baseEnd_3558538 < baseStart_3558538 := by decide
  rcases family_descends (prefixWord ++ tailWord_3558538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3558632 : List Nat := [2, 1, 4, 1, 2, 1, 2, 5, 1, 3]
def baseStart_3558632 : Nat := 118140960795 + 3558632 * 2 ^ 59
def prefixEnd_3558632 : Nat := 4983230072969 + 3 ^ 40 * 3558632 * 2
def baseEnd_3558632 : Nat := 1218192458980550713089437

theorem tailTrace_3558632 : CollatzResearch.WordTrace tailWord_3558632 prefixEnd_3558632 1218192458980550713089437 := by
  unfold tailWord_3558632
  simp only [CollatzResearch.WordTrace]
  refine ⟨64896986021845752401995075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86529314695794336535993433 64896986021845752401995075)
  ·
    refine ⟨97345479032768628602992613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64896986021845752401995075 97345479032768628602992613)
    ·
      refine ⟨18252277318644117863061115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97345479032768628602992613 18252277318644117863061115)
      ·
        refine ⟨27378415977966176794591673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18252277318644117863061115 27378415977966176794591673)
        ·
          refine ⟨20533811983474632595943755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27378415977966176794591673 20533811983474632595943755)
          ·
            refine ⟨30800717975211948893915633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20533811983474632595943755 30800717975211948893915633)
            ·
              refine ⟨23100538481408961670436725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30800717975211948893915633 23100538481408961670436725)
              ·
                refine ⟨2165675482632090156603443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23100538481408961670436725 2165675482632090156603443)
                ·
                  refine ⟨3248513223948135234905165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2165675482632090156603443 3248513223948135234905165)
                  ·
                    refine ⟨1218192458980550713089437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3248513223948135234905165 1218192458980550713089437)
                    ·
                      rfl

theorem cell22_3558632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 5, 1, 3].length) (baseStart_3558632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3558632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3558632 prefixEnd_3558632 := by exact prefixLift 3558632
  have htrace : WordTrace (prefixWord ++ tailWord_3558632) baseStart_3558632 baseEnd_3558632 := by
    simpa [prefixWord, tailWord_3558632, baseEnd_3558632] using wordTrace_append hprefix tailTrace_3558632
  have hstable : (prefixWord ++ tailWord_3558632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3558632).length < 2 ^ (prefixWord ++ tailWord_3558632).sum := by decide
  have hdescent : baseEnd_3558632 < baseStart_3558632 := by decide
  rcases family_descends (prefixWord ++ tailWord_3558632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3558660 : List Nat := [2, 3, 2, 2, 2, 2, 1, 1, 2, 5]
def baseStart_3558660 : Nat := 118140960795 + 3558660 * 2 ^ 59
def prefixEnd_3558660 : Nat := 4983230072969 + 3 ^ 40 * 3558660 * 2
def baseEnd_3558660 : Nat := 1218202043952767973389351

theorem tailTrace_3558660 : CollatzResearch.WordTrace tailWord_3558660 prefixEnd_3558660 1218202043952767973389351 := by
  unfold tailWord_3558660
  simp only [CollatzResearch.WordTrace]
  refine ⟨64897496643795032793004717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86529995525060043724006289 64897496643795032793004717)
  ·
    refine ⟨24336561241423137297376769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64897496643795032793004717 24336561241423137297376769)
    ·
      refine ⟨18252420931067352973032577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24336561241423137297376769 18252420931067352973032577)
      ·
        refine ⟨13689315698300514729774433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18252420931067352973032577 13689315698300514729774433)
        ·
          refine ⟨10266986773725386047330825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13689315698300514729774433 10266986773725386047330825)
          ·
            refine ⟨7700240080294039535498119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10266986773725386047330825 7700240080294039535498119)
            ·
              refine ⟨11550360120441059303247179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7700240080294039535498119 11550360120441059303247179)
              ·
                refine ⟨17325540180661588954870769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11550360120441059303247179 17325540180661588954870769)
                ·
                  refine ⟨12994155135496191716153077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17325540180661588954870769 12994155135496191716153077)
                  ·
                    refine ⟨1218202043952767973389351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12994155135496191716153077 1218202043952767973389351)
                    ·
                      rfl

theorem cell22_3558660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 1, 2, 5].length) (baseStart_3558660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3558660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3558660 prefixEnd_3558660 := by exact prefixLift 3558660
  have htrace : WordTrace (prefixWord ++ tailWord_3558660) baseStart_3558660 baseEnd_3558660 := by
    simpa [prefixWord, tailWord_3558660, baseEnd_3558660] using wordTrace_append hprefix tailTrace_3558660
  have hstable : (prefixWord ++ tailWord_3558660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3558660).length < 2 ^ (prefixWord ++ tailWord_3558660).sum := by decide
  have hdescent : baseEnd_3558660 < baseStart_3558660 := by decide
  rcases family_descends (prefixWord ++ tailWord_3558660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3558673 : List Nat := [1, 2, 2, 1, 1, 4, 3, 2, 6]
def baseStart_3558673 : Nat := 118140960795 + 3558673 * 2 ^ 59
def prefixEnd_3558673 : Nat := 4983230072969 + 3 ^ 40 * 3558673 * 2
def baseEnd_3558673 : Nat := 406068831372813424271437

theorem tailTrace_3558673 : CollatzResearch.WordTrace tailWord_3558673 prefixEnd_3558673 406068831372813424271437 := by
  unfold tailWord_3558673
  simp only [CollatzResearch.WordTrace]
  refine ⟨129795467436542968806232673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86530311624361979204155115 129795467436542968806232673)
  ·
    refine ⟨97346600577407226604674505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129795467436542968806232673 97346600577407226604674505)
    ·
      refine ⟨73009950433055419953505879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97346600577407226604674505 73009950433055419953505879)
      ·
        refine ⟨109514925649583129930258819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73009950433055419953505879 109514925649583129930258819)
        ·
          refine ⟨164272388474374694895388229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109514925649583129930258819 164272388474374694895388229)
          ·
            refine ⟨30801072838945255292885293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 164272388474374694895388229 30801072838945255292885293)
            ·
              refine ⟨11550402314604470734831985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30801072838945255292885293 11550402314604470734831985)
              ·
                refine ⟨8662801735953353051123989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11550402314604470734831985 8662801735953353051123989)
                ·
                  refine ⟨406068831372813424271437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8662801735953353051123989 406068831372813424271437)
                  ·
                    rfl

theorem cell22_3558673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 2, 6].length) (baseStart_3558673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3558673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3558673 prefixEnd_3558673 := by exact prefixLift 3558673
  have htrace : WordTrace (prefixWord ++ tailWord_3558673) baseStart_3558673 baseEnd_3558673 := by
    simpa [prefixWord, tailWord_3558673, baseEnd_3558673] using wordTrace_append hprefix tailTrace_3558673
  have hstable : (prefixWord ++ tailWord_3558673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3558673).length < 2 ^ (prefixWord ++ tailWord_3558673).sum := by decide
  have hdescent : baseEnd_3558673 < baseStart_3558673 := by decide
  rcases family_descends (prefixWord ++ tailWord_3558673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3558703 : List Nat := [1, 1, 2, 1, 2, 1, 3, 3, 4, 4]
def baseStart_3558703 : Nat := 118140960795 + 3558703 * 2 ^ 59
def prefixEnd_3558703 : Nat := 4983230072969 + 3 ^ 40 * 3558703 * 2
def baseEnd_3558703 : Nat := 1218216763731530194564219

theorem tailTrace_3558703 : CollatzResearch.WordTrace tailWord_3558703 prefixEnd_3558703 1218216763731530194564219 := by
  unfold tailWord_3558703
  simp only [CollatzResearch.WordTrace]
  refine ⟨129796561626434283929824763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86531041084289522619883175 129796561626434283929824763)
  ·
    refine ⟨194694842439651425894737145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129796561626434283929824763 194694842439651425894737145)
    ·
      refine ⟨146021131829738569421052859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194694842439651425894737145 146021131829738569421052859)
      ·
        refine ⟨219031697744607854131579289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146021131829738569421052859 219031697744607854131579289)
        ·
          refine ⟨164273773308455890598684467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 219031697744607854131579289 164273773308455890598684467)
          ·
            refine ⟨246410659962683835898026701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164273773308455890598684467 246410659962683835898026701)
            ·
              refine ⟨92403997486006438461760013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 246410659962683835898026701 92403997486006438461760013)
              ·
                refine ⟨34651499057252414423160005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92403997486006438461760013 34651499057252414423160005)
                ·
                  refine ⟨6497156073234827704342501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34651499057252414423160005 6497156073234827704342501)
                  ·
                    refine ⟨1218216763731530194564219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6497156073234827704342501 1218216763731530194564219)
                    ·
                      rfl

theorem cell22_3558703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 3, 4, 4].length) (baseStart_3558703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3558703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3558703 prefixEnd_3558703 := by exact prefixLift 3558703
  have htrace : WordTrace (prefixWord ++ tailWord_3558703) baseStart_3558703 baseEnd_3558703 := by
    simpa [prefixWord, tailWord_3558703, baseEnd_3558703] using wordTrace_append hprefix tailTrace_3558703
  have hstable : (prefixWord ++ tailWord_3558703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3558703).length < 2 ^ (prefixWord ++ tailWord_3558703).sum := by decide
  have hdescent : baseEnd_3558703 < baseStart_3558703 := by decide
  rcases family_descends (prefixWord ++ tailWord_3558703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3558773 : List Nat := [1, 3, 4, 1, 4, 1, 2, 1, 2, 3]
def baseStart_3558773 : Nat := 118140960795 + 3558773 * 2 ^ 59
def prefixEnd_3558773 : Nat := 4983230072969 + 3 ^ 40 * 3558773 * 2
def baseEnd_3558773 : Nat := 1218240726162073345314005

theorem tailTrace_3558773 : CollatzResearch.WordTrace tailWord_3558773 prefixEnd_3558773 1218240726162073345314005 := by
  unfold tailWord_3558773
  simp only [CollatzResearch.WordTrace]
  refine ⟨129799114736180685884872973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86532743157453790589915315 129799114736180685884872973)
  ·
    refine ⟨48674668026067757206827365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129799114736180685884872973 48674668026067757206827365)
    ·
      refine ⟨9126500254887704476280131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48674668026067757206827365 9126500254887704476280131)
      ·
        refine ⟨13689750382331556714420197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9126500254887704476280131 13689750382331556714420197)
        ·
          refine ⟨2566828196687166883953787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13689750382331556714420197 2566828196687166883953787)
          ·
            refine ⟨3850242295030750325930681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2566828196687166883953787 3850242295030750325930681)
            ·
              refine ⟨2887681721273062744448011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3850242295030750325930681 2887681721273062744448011)
              ·
                refine ⟨4331522581909594116672017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2887681721273062744448011 4331522581909594116672017)
                ·
                  refine ⟨3248641936432195587504013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4331522581909594116672017 3248641936432195587504013)
                  ·
                    refine ⟨1218240726162073345314005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3248641936432195587504013 1218240726162073345314005)
                    ·
                      rfl

theorem cell22_3558773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 2, 1, 2, 3].length) (baseStart_3558773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3558773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3558773 prefixEnd_3558773 := by exact prefixLift 3558773
  have htrace : WordTrace (prefixWord ++ tailWord_3558773) baseStart_3558773 baseEnd_3558773 := by
    simpa [prefixWord, tailWord_3558773, baseEnd_3558773] using wordTrace_append hprefix tailTrace_3558773
  have hstable : (prefixWord ++ tailWord_3558773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3558773).length < 2 ^ (prefixWord ++ tailWord_3558773).sum := by decide
  have hdescent : baseEnd_3558773 < baseStart_3558773 := by decide
  rcases family_descends (prefixWord ++ tailWord_3558773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3558780 : List Nat := [2, 2, 2, 1, 1, 1, 5, 3, 5]
def baseStart_3558780 : Nat := 118140960795 + 3558780 * 2 ^ 59
def prefixEnd_3558780 : Nat := 4983230072969 + 3 ^ 40 * 3558780 * 2
def baseEnd_3558780 : Nat := 406081040801709220129661

theorem tailTrace_3558780 : CollatzResearch.WordTrace tailWord_3558780 prefixEnd_3558780 406081040801709220129661 := by
  unfold tailWord_3558780
  simp only [CollatzResearch.WordTrace]
  refine ⟨64899685023577663040188897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86532913364770217386918529 64899685023577663040188897)
  ·
    refine ⟨48674763767683247280141673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64899685023577663040188897 48674763767683247280141673)
    ·
      refine ⟨36506072825762435460106255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48674763767683247280141673 36506072825762435460106255)
      ·
        refine ⟨54759109238643653190159383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36506072825762435460106255 54759109238643653190159383)
        ·
          refine ⟨82138663857965479785239075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54759109238643653190159383 82138663857965479785239075)
          ·
            refine ⟨123207995786948219677858613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82138663857965479785239075 123207995786948219677858613)
            ·
              refine ⟨11550749605026395594799245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 123207995786948219677858613 11550749605026395594799245)
              ·
                refine ⟨4331531101884898348049717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11550749605026395594799245 4331531101884898348049717)
                ·
                  refine ⟨406081040801709220129661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4331531101884898348049717 406081040801709220129661)
                  ·
                    rfl

theorem cell22_3558780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 3, 5].length) (baseStart_3558780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3558780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3558780 prefixEnd_3558780 := by exact prefixLift 3558780
  have htrace : WordTrace (prefixWord ++ tailWord_3558780) baseStart_3558780 baseEnd_3558780 := by
    simpa [prefixWord, tailWord_3558780, baseEnd_3558780] using wordTrace_append hprefix tailTrace_3558780
  have hstable : (prefixWord ++ tailWord_3558780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3558780).length < 2 ^ (prefixWord ++ tailWord_3558780).sum := by decide
  have hdescent : baseEnd_3558780 < baseStart_3558780 := by decide
  rcases family_descends (prefixWord ++ tailWord_3558780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3558818 : List Nat := [3, 3, 1, 2, 1, 4, 2, 2, 1, 3]
def baseStart_3558818 : Nat := 118140960795 + 3558818 * 2 ^ 59
def prefixEnd_3558818 : Nat := 4983230072969 + 3 ^ 40 * 3558818 * 2
def baseEnd_3558818 : Nat := 1218256130581708227938867

theorem tailTrace_3558818 : CollatzResearch.WordTrace tailWord_3558818 prefixEnd_3558818 1218256130581708227938867 := by
  unfold tailWord_3558818
  simp only [CollatzResearch.WordTrace]
  refine ⟨32450189005254414642565277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86533837347345105713507405 32450189005254414642565277)
  ·
    refine ⟨12168820876970405490961979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32450189005254414642565277 12168820876970405490961979)
    ·
      refine ⟨18253231315455608236442969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12168820876970405490961979 18253231315455608236442969)
      ·
        refine ⟨13689923486591706177332227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18253231315455608236442969 13689923486591706177332227)
        ·
          refine ⟨20534885229887559265998341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13689923486591706177332227 20534885229887559265998341)
          ·
            refine ⟨3850290980603917362374689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20534885229887559265998341 3850290980603917362374689)
            ·
              refine ⟨2887718235452938021781017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3850290980603917362374689 2887718235452938021781017)
              ·
                refine ⟨2165788676589703516335763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2887718235452938021781017 2165788676589703516335763)
                ·
                  refine ⟨3248683014884555274503645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2165788676589703516335763 3248683014884555274503645)
                  ·
                    refine ⟨1218256130581708227938867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3248683014884555274503645 1218256130581708227938867)
                    ·
                      rfl

theorem cell22_3558818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 2, 2, 1, 3].length) (baseStart_3558818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3558818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3558818 prefixEnd_3558818 := by exact prefixLift 3558818
  have htrace : WordTrace (prefixWord ++ tailWord_3558818) baseStart_3558818 baseEnd_3558818 := by
    simpa [prefixWord, tailWord_3558818, baseEnd_3558818] using wordTrace_append hprefix tailTrace_3558818
  have hstable : (prefixWord ++ tailWord_3558818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3558818).length < 2 ^ (prefixWord ++ tailWord_3558818).sum := by decide
  have hdescent : baseEnd_3558818 < baseStart_3558818 := by decide
  rcases family_descends (prefixWord ++ tailWord_3558818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
