import V185TrunkScan23Chunk1404

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_8322477 : List Nat := [1, 5, 2, 2, 1, 1, 1, 3, 2, 5]
def baseStart_8322477 : Nat := 118140960795 + 8322477 * 2 ^ 59
def prefixEnd_8322477 : Nat := 4983230072969 + 3 ^ 40 * 8322477 * 2
def baseEnd_8322477 : Nat := 1424476978996246668054377

theorem tailTrace_8322477 : CollatzResearch.WordTrace tailWord_8322477 prefixEnd_8322477 1424476978996246668054377 := by
  unfold tailWord_8322477
  simp only [CollatzResearch.WordTrace]
  refine ⟨303545673470094669755989685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202363782313396446503993123 303545673470094669755989685)
  ·
    refine ⟨28457406887821375289624033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 303545673470094669755989685 28457406887821375289624033)
    ·
      refine ⟨21343055165866031467218025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28457406887821375289624033 21343055165866031467218025)
      ·
        refine ⟨16007291374399523600413519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21343055165866031467218025 16007291374399523600413519)
        ·
          refine ⟨24010937061599285400620279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16007291374399523600413519 24010937061599285400620279)
          ·
            refine ⟨36016405592398928100930419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24010937061599285400620279 36016405592398928100930419)
            ·
              refine ⟨54024608388598392151395629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36016405592398928100930419 54024608388598392151395629)
              ·
                refine ⟨20259228145724397056773361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54024608388598392151395629 20259228145724397056773361)
                ·
                  refine ⟨15194421109293297792580021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20259228145724397056773361 15194421109293297792580021)
                  ·
                    refine ⟨1424476978996246668054377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15194421109293297792580021 1424476978996246668054377)
                    ·
                      rfl

theorem cell23_8322477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 3, 2, 5].length) (baseStart_8322477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8322477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8322477 prefixEnd_8322477 := by exact prefixLift 8322477
  have htrace : WordTrace (prefixWord ++ tailWord_8322477) baseStart_8322477 baseEnd_8322477 := by
    simpa [prefixWord, tailWord_8322477, baseEnd_8322477] using wordTrace_append hprefix tailTrace_8322477
  have hstable : (prefixWord ++ tailWord_8322477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8322477).length < 2 ^ (prefixWord ++ tailWord_8322477).sum := by decide
  have hdescent : baseEnd_8322477 < baseStart_8322477 := by decide
  rcases family_descends (prefixWord ++ tailWord_8322477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8322480 : List Nat := [2, 1, 1, 1, 2, 1, 1, 3, 3, 6, 2]
def baseStart_8322480 : Nat := 118140960795 + 8322480 * 2 ^ 59
def prefixEnd_8322480 : Nat := 4983230072969 + 3 ^ 40 * 8322480 * 2
def baseEnd_8322480 : Nat := 4273432477430703492425617

theorem tailTrace_8322480 : CollatzResearch.WordTrace tailWord_8322480 prefixEnd_8322480 4273432477430703492425617 := by
  unfold tailWord_8322480
  simp only [CollatzResearch.WordTrace]
  refine ⟨151772891444541900634174447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202363855259389200845565929 151772891444541900634174447)
  ·
    refine ⟨227659337166812850951261671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151772891444541900634174447 227659337166812850951261671)
    ·
      refine ⟨341489005750219276426892507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227659337166812850951261671 341489005750219276426892507)
      ·
        refine ⟨512233508625328914640338761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341489005750219276426892507 512233508625328914640338761)
        ·
          refine ⟨384175131468996685980254071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 512233508625328914640338761 384175131468996685980254071)
          ·
            refine ⟨576262697203495028970381107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 384175131468996685980254071 576262697203495028970381107)
            ·
              refine ⟨864394045805242543455571661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 576262697203495028970381107 864394045805242543455571661)
              ·
                refine ⟨324147767176965953795839373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 864394045805242543455571661 324147767176965953795839373)
                ·
                  refine ⟨121555412691362232673439765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 324147767176965953795839373 121555412691362232673439765)
                  ·
                    refine ⟨5697909969907604656567489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 121555412691362232673439765 5697909969907604656567489)
                    ·
                      refine ⟨4273432477430703492425617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5697909969907604656567489 4273432477430703492425617)
                      ·
                        rfl

theorem cell23_8322480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 3, 6, 2].length) (baseStart_8322480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8322480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8322480 prefixEnd_8322480 := by exact prefixLift 8322480
  have htrace : WordTrace (prefixWord ++ tailWord_8322480) baseStart_8322480 baseEnd_8322480 := by
    simpa [prefixWord, tailWord_8322480, baseEnd_8322480] using wordTrace_append hprefix tailTrace_8322480
  have hstable : (prefixWord ++ tailWord_8322480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8322480).length < 2 ^ (prefixWord ++ tailWord_8322480).sum := by decide
  have hdescent : baseEnd_8322480 < baseStart_8322480 := by decide
  rcases family_descends (prefixWord ++ tailWord_8322480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8322520 : List Nat := [2, 1, 2, 2, 2, 1, 4, 3, 6]
def baseStart_8322520 : Nat := 118140960795 + 8322520 * 2 ^ 59
def prefixEnd_8322520 : Nat := 4983230072969 + 3 ^ 40 * 8322520 * 2
def baseEnd_8322520 : Nat := 474828112961875926213937

theorem tailTrace_8322520 : CollatzResearch.WordTrace tailWord_8322520 prefixEnd_8322520 474828112961875926213937 := by
  unfold tailWord_8322520
  simp only [CollatzResearch.WordTrace]
  refine ⟨151773620904469444049902507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202364827872625925399870009 151773620904469444049902507)
  ·
    refine ⟨227660431356704166074853761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151773620904469444049902507 227660431356704166074853761)
    ·
      refine ⟨170745323517528124556140321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227660431356704166074853761 170745323517528124556140321)
      ·
        refine ⟨128058992638146093417105241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170745323517528124556140321 128058992638146093417105241)
        ·
          refine ⟨96044244478609570062828931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128058992638146093417105241 96044244478609570062828931)
          ·
            refine ⟨144066366717914355094243397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96044244478609570062828931 144066366717914355094243397)
            ·
              refine ⟨27012443759608941580170637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 144066366717914355094243397 27012443759608941580170637)
              ·
                refine ⟨10129666409853353092563989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27012443759608941580170637 10129666409853353092563989)
                ·
                  refine ⟨474828112961875926213937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10129666409853353092563989 474828112961875926213937)
                  ·
                    rfl

theorem cell23_8322520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 3, 6].length) (baseStart_8322520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8322520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8322520 prefixEnd_8322520 := by exact prefixLift 8322520
  have htrace : WordTrace (prefixWord ++ tailWord_8322520) baseStart_8322520 baseEnd_8322520 := by
    simpa [prefixWord, tailWord_8322520, baseEnd_8322520] using wordTrace_append hprefix tailTrace_8322520
  have hstable : (prefixWord ++ tailWord_8322520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8322520).length < 2 ^ (prefixWord ++ tailWord_8322520).sum := by decide
  have hdescent : baseEnd_8322520 < baseStart_8322520 := by decide
  rcases family_descends (prefixWord ++ tailWord_8322520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8322584 : List Nat := [2, 1, 2, 3, 4, 1, 2, 2, 1, 5]
def baseStart_8322584 : Nat := 118140960795 + 8322584 * 2 ^ 59
def prefixEnd_8322584 : Nat := 4983230072969 + 3 ^ 40 * 8322584 * 2
def baseEnd_8322584 : Nat := 1424495293139590361841713

theorem tailTrace_8322584 : CollatzResearch.WordTrace tailWord_8322584 prefixEnd_8322584 1424495293139590361841713 := by
  unfold tailWord_8322584
  simp only [CollatzResearch.WordTrace]
  refine ⟨151774788040353513515067403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202366384053804684686756537 151774788040353513515067403)
  ·
    refine ⟨227662182060530270272601105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151774788040353513515067403 227662182060530270272601105)
    ·
      refine ⟨170746636545397702704450829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227662182060530270272601105 170746636545397702704450829)
      ·
        refine ⟨64029988704524138514169061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170746636545397702704450829 64029988704524138514169061)
        ·
          refine ⟨12005622882098275971406699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64029988704524138514169061 12005622882098275971406699)
          ·
            refine ⟨18008434323147413957110049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12005622882098275971406699 18008434323147413957110049)
            ·
              refine ⟨13506325742360560467832537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18008434323147413957110049 13506325742360560467832537)
              ·
                refine ⟨10129744306770420350874403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13506325742360560467832537 10129744306770420350874403)
                ·
                  refine ⟨15194616460155630526311605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10129744306770420350874403 15194616460155630526311605)
                  ·
                    refine ⟨1424495293139590361841713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15194616460155630526311605 1424495293139590361841713)
                    ·
                      rfl

theorem cell23_8322584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 2, 2, 1, 5].length) (baseStart_8322584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8322584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8322584 prefixEnd_8322584 := by exact prefixLift 8322584
  have htrace : WordTrace (prefixWord ++ tailWord_8322584) baseStart_8322584 baseEnd_8322584 := by
    simpa [prefixWord, tailWord_8322584, baseEnd_8322584] using wordTrace_append hprefix tailTrace_8322584
  have hstable : (prefixWord ++ tailWord_8322584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8322584).length < 2 ^ (prefixWord ++ tailWord_8322584).sum := by decide
  have hdescent : baseEnd_8322584 < baseStart_8322584 := by decide
  rcases family_descends (prefixWord ++ tailWord_8322584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8322650 : List Nat := [3, 1, 1, 2, 1, 1, 1, 3, 1, 4, 5]
def baseStart_8322650 : Nat := 118140960795 + 8322650 * 2 ^ 59
def prefixEnd_8322650 : Nat := 4983230072969 + 3 ^ 40 * 8322650 * 2
def baseEnd_8322650 : Nat := 4273519769141967827299835

theorem tailTrace_8322650 : CollatzResearch.WordTrace tailWord_8322650 prefixEnd_8322650 4273519769141967827299835 := by
  unfold tailWord_8322650
  simp only [CollatzResearch.WordTrace]
  refine ⟨75887995824616980075509351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202367988865645280201358269 75887995824616980075509351)
  ·
    refine ⟨113831993736925470113264027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75887995824616980075509351 113831993736925470113264027)
    ·
      refine ⟨170747990605388205169896041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113831993736925470113264027 170747990605388205169896041)
      ·
        refine ⟨128060992954041153877422031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170747990605388205169896041 128060992954041153877422031)
        ·
          refine ⟨192091489431061730816133047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128060992954041153877422031 192091489431061730816133047)
          ·
            refine ⟨288137234146592596224199571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192091489431061730816133047 288137234146592596224199571)
            ·
              refine ⟨432205851219888894336299357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 288137234146592596224199571 432205851219888894336299357)
              ·
                refine ⟨162077194207458335376112259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 432205851219888894336299357 162077194207458335376112259)
                ·
                  refine ⟨243115791311187503064168389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 162077194207458335376112259 243115791311187503064168389)
                  ·
                    refine ⟨45584210870847656824531573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 243115791311187503064168389 45584210870847656824531573)
                    ·
                      refine ⟨4273519769141967827299835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45584210870847656824531573 4273519769141967827299835)
                      ·
                        rfl

theorem cell23_8322650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 1, 4, 5].length) (baseStart_8322650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8322650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8322650 prefixEnd_8322650 := by exact prefixLift 8322650
  have htrace : WordTrace (prefixWord ++ tailWord_8322650) baseStart_8322650 baseEnd_8322650 := by
    simpa [prefixWord, tailWord_8322650, baseEnd_8322650] using wordTrace_append hprefix tailTrace_8322650
  have hstable : (prefixWord ++ tailWord_8322650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8322650).length < 2 ^ (prefixWord ++ tailWord_8322650).sum := by decide
  have hdescent : baseEnd_8322650 < baseStart_8322650 := by decide
  rcases family_descends (prefixWord ++ tailWord_8322650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8322722 : List Nat := [3, 3, 1, 4, 2, 1, 1, 2, 2, 1, 3]
def baseStart_8322722 : Nat := 118140960795 + 8322722 * 2 ^ 59
def prefixEnd_8322722 : Nat := 4983230072969 + 3 ^ 40 * 8322722 * 2
def baseEnd_8322722 : Nat := 4273556739749091545599505

theorem tailTrace_8322722 : CollatzResearch.WordTrace tailWord_8322722 prefixEnd_8322722 4273556739749091545599505 := by
  unfold tailWord_8322722
  simp only [CollatzResearch.WordTrace]
  refine ⟨75888652338551769149664605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202369739569471384399105613 75888652338551769149664605)
  ·
    refine ⟨28458244626956913431124227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75888652338551769149664605 28458244626956913431124227)
    ·
      refine ⟨42687366940435370146686341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28458244626956913431124227 42687366940435370146686341)
      ·
        refine ⟨8003881301331631902503689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42687366940435370146686341 8003881301331631902503689)
        ·
          refine ⟨6002910975998723926877767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8003881301331631902503689 6002910975998723926877767)
          ·
            refine ⟨9004366463998085890316651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6002910975998723926877767 9004366463998085890316651)
            ·
              refine ⟨13506549695997128835474977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9004366463998085890316651 13506549695997128835474977)
              ·
                refine ⟨10129912271997846626606233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13506549695997128835474977 10129912271997846626606233)
                ·
                  refine ⟨7597434203998384969954675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10129912271997846626606233 7597434203998384969954675)
                  ·
                    refine ⟨11396151305997577454932013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7597434203998384969954675 11396151305997577454932013)
                    ·
                      refine ⟨4273556739749091545599505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11396151305997577454932013 4273556739749091545599505)
                      ·
                        rfl

theorem cell23_8322722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_8322722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8322722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8322722 prefixEnd_8322722 := by exact prefixLift 8322722
  have htrace : WordTrace (prefixWord ++ tailWord_8322722) baseStart_8322722 baseEnd_8322722 := by
    simpa [prefixWord, tailWord_8322722, baseEnd_8322722] using wordTrace_append hprefix tailTrace_8322722
  have hstable : (prefixWord ++ tailWord_8322722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8322722).length < 2 ^ (prefixWord ++ tailWord_8322722).sum := by decide
  have hdescent : baseEnd_8322722 < baseStart_8322722 := by decide
  rcases family_descends (prefixWord ++ tailWord_8322722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8322767 : List Nat := [1, 1, 2, 1, 1, 3, 1, 2, 6, 1, 4]
def baseStart_8322767 : Nat := 118140960795 + 8322767 * 2 ^ 59
def prefixEnd_8322767 : Nat := 4983230072969 + 3 ^ 40 * 8322767 * 2
def baseEnd_8322767 : Nat := 4273579846378543869536797

theorem tailTrace_8322767 : CollatzResearch.WordTrace tailWord_8322767 prefixEnd_8322767 4273579846378543869536797 := by
  unfold tailWord_8322767
  simp only [CollatzResearch.WordTrace]
  refine ⟨303556250639044049284046555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202370833759362699522697703 303556250639044049284046555)
  ·
    refine ⟨455334375958566073926069833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303556250639044049284046555 455334375958566073926069833)
    ·
      refine ⟨341500781968924555444552375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 455334375958566073926069833 341500781968924555444552375)
      ·
        refine ⟨512251172953386833166828563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341500781968924555444552375 512251172953386833166828563)
        ·
          refine ⟨768376759430080249750242845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 512251172953386833166828563 768376759430080249750242845)
          ·
            refine ⟨288141284786280093656341067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 768376759430080249750242845 288141284786280093656341067)
            ·
              refine ⟨432211927179420140484511601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 288141284786280093656341067 432211927179420140484511601)
              ·
                refine ⟨324158945384565105363383701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 432211927179420140484511601 324158945384565105363383701)
                ·
                  refine ⟨15194950564901489313908611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 324158945384565105363383701 15194950564901489313908611)
                  ·
                    refine ⟨22792425847352233970862917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15194950564901489313908611 22792425847352233970862917)
                    ·
                      refine ⟨4273579846378543869536797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22792425847352233970862917 4273579846378543869536797)
                      ·
                        rfl

theorem cell23_8322767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 6, 1, 4].length) (baseStart_8322767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8322767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8322767 prefixEnd_8322767 := by exact prefixLift 8322767
  have htrace : WordTrace (prefixWord ++ tailWord_8322767) baseStart_8322767 baseEnd_8322767 := by
    simpa [prefixWord, tailWord_8322767, baseEnd_8322767] using wordTrace_append hprefix tailTrace_8322767
  have hstable : (prefixWord ++ tailWord_8322767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8322767).length < 2 ^ (prefixWord ++ tailWord_8322767).sum := by decide
  have hdescent : baseEnd_8322767 < baseStart_8322767 := by decide
  rcases family_descends (prefixWord ++ tailWord_8322767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8322784 : List Nat := [2, 1, 1, 3, 1, 2, 2, 1, 4, 4, 2]
def baseStart_8322784 : Nat := 118140960795 + 8322784 * 2 ^ 59
def prefixEnd_8322784 : Nat := 4983230072969 + 3 ^ 40 * 8322784 * 2
def baseEnd_8322784 : Nat := 4273588575549670303024219

theorem tailTrace_8322784 : CollatzResearch.WordTrace tailWord_8322784 prefixEnd_8322784 4273588575549670303024219 := by
  unfold tailWord_8322784
  simp only [CollatzResearch.WordTrace]
  refine ⟨151778435339991230593707703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202371247119988307458276937 151778435339991230593707703)
  ·
    refine ⟨227667653009986845890561555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151778435339991230593707703 227667653009986845890561555)
    ·
      refine ⟨341501479514980268835842333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227667653009986845890561555 341501479514980268835842333)
      ·
        refine ⟨128063054818117600813440875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 341501479514980268835842333 128063054818117600813440875)
        ·
          refine ⟨192094582227176401220161313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128063054818117600813440875 192094582227176401220161313)
          ·
            refine ⟨144070936670382300915120985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192094582227176401220161313 144070936670382300915120985)
            ·
              refine ⟨108053202502786725686340739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144070936670382300915120985 108053202502786725686340739)
              ·
                refine ⟨162079803754180088529511109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108053202502786725686340739 162079803754180088529511109)
                ·
                  refine ⟨30389963203908766599283333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 162079803754180088529511109 30389963203908766599283333)
                  ·
                    refine ⟨5698118100732893737365625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30389963203908766599283333 5698118100732893737365625)
                    ·
                      refine ⟨4273588575549670303024219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5698118100732893737365625 4273588575549670303024219)
                      ·
                        rfl

theorem cell23_8322784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 4, 4, 2].length) (baseStart_8322784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8322784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8322784 prefixEnd_8322784 := by exact prefixLift 8322784
  have htrace : WordTrace (prefixWord ++ tailWord_8322784) baseStart_8322784 baseEnd_8322784 := by
    simpa [prefixWord, tailWord_8322784, baseEnd_8322784] using wordTrace_append hprefix tailTrace_8322784
  have hstable : (prefixWord ++ tailWord_8322784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8322784).length < 2 ^ (prefixWord ++ tailWord_8322784).sum := by decide
  have hdescent : baseEnd_8322784 < baseStart_8322784 := by decide
  rcases family_descends (prefixWord ++ tailWord_8322784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8322791 : List Nat := [1, 1, 5, 4, 1, 1, 1, 1, 1, 2, 5]
def baseStart_8322791 : Nat := 118140960795 + 8322791 * 2 ^ 59
def prefixEnd_8322791 : Nat := 4983230072969 + 3 ^ 40 * 8322791 * 2
def baseEnd_8322791 : Nat := 4273592169914251775636687

theorem tailTrace_8322791 : CollatzResearch.WordTrace tailWord_8322791 prefixEnd_8322791 4273592169914251775636687 := by
  unfold tailWord_8322791
  simp only [CollatzResearch.WordTrace]
  refine ⟨303557125990957101382920227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202371417327304734255280151 303557125990957101382920227)
  ·
    refine ⟨455335688986435652074380341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303557125990957101382920227 455335688986435652074380341)
    ·
      refine ⟨42687720842478342381973157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 455335688986435652074380341 42687720842478342381973157)
      ·
        refine ⟨8003947657964689196619967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42687720842478342381973157 8003947657964689196619967)
        ·
          refine ⟨12005921486947033794929951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8003947657964689196619967 12005921486947033794929951)
          ·
            refine ⟨18008882230420550692394927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12005921486947033794929951 18008882230420550692394927)
            ·
              refine ⟨27013323345630826038592391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18008882230420550692394927 27013323345630826038592391)
              ·
                refine ⟨40519985018446239057888587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27013323345630826038592391 40519985018446239057888587)
                ·
                  refine ⟨60779977527669358586832881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40519985018446239057888587 60779977527669358586832881)
                  ·
                    refine ⟨45584983145752018940124661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60779977527669358586832881 45584983145752018940124661)
                    ·
                      refine ⟨4273592169914251775636687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45584983145752018940124661 4273592169914251775636687)
                      ·
                        rfl

theorem cell23_8322791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_8322791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8322791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8322791 prefixEnd_8322791 := by exact prefixLift 8322791
  have htrace : WordTrace (prefixWord ++ tailWord_8322791) baseStart_8322791 baseEnd_8322791 := by
    simpa [prefixWord, tailWord_8322791, baseEnd_8322791] using wordTrace_append hprefix tailTrace_8322791
  have hstable : (prefixWord ++ tailWord_8322791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8322791).length < 2 ^ (prefixWord ++ tailWord_8322791).sum := by decide
  have hdescent : baseEnd_8322791 < baseStart_8322791 := by decide
  rcases family_descends (prefixWord ++ tailWord_8322791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8322857 : List Nat := [1, 2, 1, 1, 1, 1, 1, 3, 1, 7, 4]
def baseStart_8322857 : Nat := 118140960795 + 8322857 * 2 ^ 59
def prefixEnd_8322857 : Nat := 4983230072969 + 3 ^ 40 * 8322857 * 2
def baseEnd_8322857 : Nat := 4273626059637448517411383

theorem tailTrace_8322857 : CollatzResearch.WordTrace tailWord_8322857 prefixEnd_8322857 4273626059637448517411383 := by
  unfold tailWord_8322857
  simp only [CollatzResearch.WordTrace]
  refine ⟨303559533208717994654822825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202373022139145329769881883 303559533208717994654822825)
  ·
    refine ⟨227669649906538495991117119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303559533208717994654822825 227669649906538495991117119)
    ·
      refine ⟨341504474859807743986675679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227669649906538495991117119 341504474859807743986675679)
      ·
        refine ⟨512256712289711615980013519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341504474859807743986675679 512256712289711615980013519)
        ·
          refine ⟨768385068434567423970020279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 512256712289711615980013519 768385068434567423970020279)
          ·
            refine ⟨1152577602651851135955030419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 768385068434567423970020279 1152577602651851135955030419)
            ·
              refine ⟨1728866403977776703932545629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1152577602651851135955030419 1728866403977776703932545629)
              ·
                refine ⟨648324901491666263974704611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1728866403977776703932545629 648324901491666263974704611)
                ·
                  refine ⟨972487352237499395962056917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 648324901491666263974704611 972487352237499395962056917)
                  ·
                    refine ⟨22792672318066392092860709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 972487352237499395962056917 22792672318066392092860709)
                    ·
                      refine ⟨4273626059637448517411383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22792672318066392092860709 4273626059637448517411383)
                      ·
                        rfl

theorem cell23_8322857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 7, 4].length) (baseStart_8322857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8322857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8322857 prefixEnd_8322857 := by exact prefixLift 8322857
  have htrace : WordTrace (prefixWord ++ tailWord_8322857) baseStart_8322857 baseEnd_8322857 := by
    simpa [prefixWord, tailWord_8322857, baseEnd_8322857] using wordTrace_append hprefix tailTrace_8322857
  have hstable : (prefixWord ++ tailWord_8322857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8322857).length < 2 ^ (prefixWord ++ tailWord_8322857).sum := by decide
  have hdescent : baseEnd_8322857 < baseStart_8322857 := by decide
  rcases family_descends (prefixWord ++ tailWord_8322857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8322868 : List Nat := [2, 5, 1, 1, 2, 1, 1, 1, 5, 1, 3]
def baseStart_8322868 : Nat := 118140960795 + 8322868 * 2 ^ 59
def prefixEnd_8322868 : Nat := 4983230072969 + 3 ^ 40 * 8322868 * 2
def baseEnd_8322868 : Nat := 4273631707924647974373833

theorem tailTrace_8322868 : CollatzResearch.WordTrace tailWord_8322868 prefixEnd_8322868 4273631707924647974373833 := by
  unfold tailWord_8322868
  simp only [CollatzResearch.WordTrace]
  refine ⟨151779967205839071766736629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202373289607785429022315505 151779967205839071766736629)
  ·
    refine ⟨14229371925547412978131559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 151779967205839071766736629 14229371925547412978131559)
    ·
      refine ⟨21344057888321119467197339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14229371925547412978131559 21344057888321119467197339)
      ·
        refine ⟨32016086832481679200796009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21344057888321119467197339 32016086832481679200796009)
        ·
          refine ⟨24012065124361259400597007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32016086832481679200796009 24012065124361259400597007)
          ·
            refine ⟨36018097686541889100895511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24012065124361259400597007 36018097686541889100895511)
            ·
              refine ⟨54027146529812833651343267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36018097686541889100895511 54027146529812833651343267)
              ·
                refine ⟨81040719794719250477014901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54027146529812833651343267 81040719794719250477014901)
                ·
                  refine ⟨7597567480754929732220147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 81040719794719250477014901 7597567480754929732220147)
                  ·
                    refine ⟨11396351221132394598330221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7597567480754929732220147 11396351221132394598330221)
                    ·
                      refine ⟨4273631707924647974373833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11396351221132394598330221 4273631707924647974373833)
                      ·
                        rfl

theorem cell23_8322868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 1, 5, 1, 3].length) (baseStart_8322868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8322868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8322868 prefixEnd_8322868 := by exact prefixLift 8322868
  have htrace : WordTrace (prefixWord ++ tailWord_8322868) baseStart_8322868 baseEnd_8322868 := by
    simpa [prefixWord, tailWord_8322868, baseEnd_8322868] using wordTrace_append hprefix tailTrace_8322868
  have hstable : (prefixWord ++ tailWord_8322868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8322868).length < 2 ^ (prefixWord ++ tailWord_8322868).sum := by decide
  have hdescent : baseEnd_8322868 < baseStart_8322868 := by decide
  rcases family_descends (prefixWord ++ tailWord_8322868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8322878 : List Nat := [4, 2, 1, 2, 2, 2, 1, 1, 1, 5, 2]
def baseStart_8322878 : Nat := 118140960795 + 8322878 * 2 ^ 59
def prefixEnd_8322878 : Nat := 4983230072969 + 3 ^ 40 * 8322878 * 2
def baseEnd_8322878 : Nat := 4273636842731192935248787

theorem tailTrace_8322878 : CollatzResearch.WordTrace tailWord_8322878 prefixEnd_8322878 4273636842731192935248787 := by
  unfold tailWord_8322878
  simp only [CollatzResearch.WordTrace]
  refine ⟨37945037392705239405167161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202373532761094610160891525 37945037392705239405167161)
  ·
    refine ⟨28458778044528929553875371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37945037392705239405167161 28458778044528929553875371)
    ·
      refine ⟨42688167066793394330813057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28458778044528929553875371 42688167066793394330813057)
      ·
        refine ⟨32016125300095045748109793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42688167066793394330813057 32016125300095045748109793)
        ·
          refine ⟨24012093975071284311082345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32016125300095045748109793 24012093975071284311082345)
          ·
            refine ⟨18009070481303463233311759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24012093975071284311082345 18009070481303463233311759)
            ·
              refine ⟨27013605721955194849967639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18009070481303463233311759 27013605721955194849967639)
              ·
                refine ⟨40520408582932792274951459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27013605721955194849967639 40520408582932792274951459)
                ·
                  refine ⟨60780612874399188412427189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40520408582932792274951459 60780612874399188412427189)
                  ·
                    refine ⟨5698182456974923913665049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60780612874399188412427189 5698182456974923913665049)
                    ·
                      refine ⟨4273636842731192935248787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5698182456974923913665049 4273636842731192935248787)
                      ·
                        rfl

theorem cell23_8322878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 1, 1, 5, 2].length) (baseStart_8322878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8322878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8322878 prefixEnd_8322878 := by exact prefixLift 8322878
  have htrace : WordTrace (prefixWord ++ tailWord_8322878) baseStart_8322878 baseEnd_8322878 := by
    simpa [prefixWord, tailWord_8322878, baseEnd_8322878] using wordTrace_append hprefix tailTrace_8322878
  have hstable : (prefixWord ++ tailWord_8322878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8322878).length < 2 ^ (prefixWord ++ tailWord_8322878).sum := by decide
  have hdescent : baseEnd_8322878 < baseStart_8322878 := by decide
  rcases family_descends (prefixWord ++ tailWord_8322878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8322888 : List Nat := [2, 1, 3, 1, 1, 6, 2, 1, 1, 5]
def baseStart_8322888 : Nat := 118140960795 + 8322888 * 2 ^ 59
def prefixEnd_8322888 : Nat := 4983230072969 + 3 ^ 40 * 8322888 * 2
def baseEnd_8322888 : Nat := 1424547325845912632041247

theorem tailTrace_8322888 : CollatzResearch.WordTrace tailWord_8322888 prefixEnd_8322888 1424547325845912632041247 := by
  unfold tailWord_8322888
  simp only [CollatzResearch.WordTrace]
  refine ⟨151780331935802843474600659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202373775914403791299467545 151780331935802843474600659)
  ·
    refine ⟨227670497903704265211900989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151780331935802843474600659 227670497903704265211900989)
    ·
      refine ⟨85376436713889099454462871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227670497903704265211900989 85376436713889099454462871)
      ·
        refine ⟨128064655070833649181694307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85376436713889099454462871 128064655070833649181694307)
        ·
          refine ⟨192096982606250473772541461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128064655070833649181694307 192096982606250473772541461)
          ·
            refine ⟨9004546059667990958087881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 192096982606250473772541461 9004546059667990958087881)
            ·
              refine ⟨6753409544750993218565911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9004546059667990958087881 6753409544750993218565911)
              ·
                refine ⟨10130114317126489827848867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6753409544750993218565911 10130114317126489827848867)
                ·
                  refine ⟨15195171475689734741773301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10130114317126489827848867 15195171475689734741773301)
                  ·
                    refine ⟨1424547325845912632041247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15195171475689734741773301 1424547325845912632041247)
                    ·
                      rfl

theorem cell23_8322888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 2, 1, 1, 5].length) (baseStart_8322888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8322888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8322888 prefixEnd_8322888 := by exact prefixLift 8322888
  have htrace : WordTrace (prefixWord ++ tailWord_8322888) baseStart_8322888 baseEnd_8322888 := by
    simpa [prefixWord, tailWord_8322888, baseEnd_8322888] using wordTrace_append hprefix tailTrace_8322888
  have hstable : (prefixWord ++ tailWord_8322888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8322888).length < 2 ^ (prefixWord ++ tailWord_8322888).sum := by decide
  have hdescent : baseEnd_8322888 < baseStart_8322888 := by decide
  rcases family_descends (prefixWord ++ tailWord_8322888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8322901 : List Nat := [1, 3, 2, 2, 2, 3, 1, 1, 4, 4]
def baseStart_8322901 : Nat := 118140960795 + 8322901 * 2 ^ 59
def prefixEnd_8322901 : Nat := 4983230072969 + 3 ^ 40 * 8322901 * 2
def baseEnd_8322901 : Nat := 1424549550928748781753727

theorem tailTrace_8322901 : CollatzResearch.WordTrace tailWord_8322901 prefixEnd_8322901 1424549550928748781753727 := by
  unfold tailWord_8322901
  simp only [CollatzResearch.WordTrace]
  refine ⟨303561138020558590169424557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202374092013705726779616371 303561138020558590169424557)
  ·
    refine ⟨113835426757709471313534209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 303561138020558590169424557 113835426757709471313534209)
    ·
      refine ⟨85376570068282103485150657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113835426757709471313534209 85376570068282103485150657)
      ·
        refine ⟨64032427551211577613862993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85376570068282103485150657 64032427551211577613862993)
        ·
          refine ⟨48024320663408683210397245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64032427551211577613862993 48024320663408683210397245)
          ·
            refine ⟨18009120248778256203898967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48024320663408683210397245 18009120248778256203898967)
            ·
              refine ⟨27013680373167384305848451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18009120248778256203898967 27013680373167384305848451)
              ·
                refine ⟨40520520559751076458772677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27013680373167384305848451 40520520559751076458772677)
                ·
                  refine ⟨7597597604953326836019877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40520520559751076458772677 7597597604953326836019877)
                  ·
                    refine ⟨1424549550928748781753727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7597597604953326836019877 1424549550928748781753727)
                    ·
                      rfl

theorem cell23_8322901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 1, 4, 4].length) (baseStart_8322901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8322901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8322901 prefixEnd_8322901 := by exact prefixLift 8322901
  have htrace : WordTrace (prefixWord ++ tailWord_8322901) baseStart_8322901 baseEnd_8322901 := by
    simpa [prefixWord, tailWord_8322901, baseEnd_8322901] using wordTrace_append hprefix tailTrace_8322901
  have hstable : (prefixWord ++ tailWord_8322901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8322901).length < 2 ^ (prefixWord ++ tailWord_8322901).sum := by decide
  have hdescent : baseEnd_8322901 < baseStart_8322901 := by decide
  rcases family_descends (prefixWord ++ tailWord_8322901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8322975 : List Nat := [1, 1, 2, 5, 3, 1, 1, 3, 2, 1, 3]
def baseStart_8322975 : Nat := 118140960795 + 8322975 * 2 ^ 59
def prefixEnd_8322975 : Nat := 4983230072969 + 3 ^ 40 * 8322975 * 2
def baseEnd_8322975 : Nat := 4273686650354679055735841

theorem tailTrace_8322975 : CollatzResearch.WordTrace tailWord_8322975 prefixEnd_8322975 4273686650354679055735841 := by
  unfold tailWord_8322975
  simp only [CollatzResearch.WordTrace]
  refine ⟨303563837022290500807618379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202375891348193667205078919 303563837022290500807618379)
  ·
    refine ⟨455345755533435751211427569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303563837022290500807618379 455345755533435751211427569)
    ·
      refine ⟨341509316650076813408570677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 455345755533435751211427569 341509316650076813408570677)
      ·
        refine ⟨32016498435944701257053501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 341509316650076813408570677 32016498435944701257053501)
        ·
          refine ⟨12006186913479262971395063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32016498435944701257053501 12006186913479262971395063)
          ·
            refine ⟨18009280370218894457092595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12006186913479262971395063 18009280370218894457092595)
            ·
              refine ⟨27013920555328341685638893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18009280370218894457092595 27013920555328341685638893)
              ·
                refine ⟨10130220208248128132114585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27013920555328341685638893 10130220208248128132114585)
                ·
                  refine ⟨7597665156186096099085939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10130220208248128132114585 7597665156186096099085939)
                  ·
                    refine ⟨11396497734279144148628909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7597665156186096099085939 11396497734279144148628909)
                    ·
                      refine ⟨4273686650354679055735841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11396497734279144148628909 4273686650354679055735841)
                      ·
                        rfl

theorem cell23_8322975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 3, 2, 1, 3].length) (baseStart_8322975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8322975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8322975 prefixEnd_8322975 := by exact prefixLift 8322975
  have htrace : WordTrace (prefixWord ++ tailWord_8322975) baseStart_8322975 baseEnd_8322975 := by
    simpa [prefixWord, tailWord_8322975, baseEnd_8322975] using wordTrace_append hprefix tailTrace_8322975
  have hstable : (prefixWord ++ tailWord_8322975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8322975).length < 2 ^ (prefixWord ++ tailWord_8322975).sum := by decide
  have hdescent : baseEnd_8322975 < baseStart_8322975 := by decide
  rcases family_descends (prefixWord ++ tailWord_8322975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8322981 : List Nat := [1, 3, 1, 2, 1, 1, 1, 2, 5, 4, 2]
def baseStart_8322981 : Nat := 118140960795 + 8322981 * 2 ^ 59
def prefixEnd_8322981 : Nat := 4983230072969 + 3 ^ 40 * 8322981 * 2
def baseEnd_8322981 : Nat := 4273689731238606032260813

theorem tailTrace_8322981 : CollatzResearch.WordTrace tailWord_8322981 prefixEnd_8322981 4273689731238606032260813 := by
  unfold tailWord_8322981
  simp only [CollatzResearch.WordTrace]
  refine ⟨303564055860268763832336797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202376037240179175888224531 303564055860268763832336797)
  ·
    refine ⟨113836520947600786437126299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 303564055860268763832336797 113836520947600786437126299)
    ·
      refine ⟨170754781421401179655689449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113836520947600786437126299 170754781421401179655689449)
      ·
        refine ⟨128066086066050884741767087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170754781421401179655689449 128066086066050884741767087)
        ·
          refine ⟨192099129099076327112650631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128066086066050884741767087 192099129099076327112650631)
          ·
            refine ⟨288148693648614490668975947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192099129099076327112650631 288148693648614490668975947)
            ·
              refine ⟨432223040472921736003463921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 288148693648614490668975947 432223040472921736003463921)
              ·
                refine ⟨324167280354691302002597941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 432223040472921736003463921 324167280354691302002597941)
                ·
                  refine ⟨30390682533252309562743557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 324167280354691302002597941 30390682533252309562743557)
                  ·
                    refine ⟨5698252974984808043014417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30390682533252309562743557 5698252974984808043014417)
                    ·
                      refine ⟨4273689731238606032260813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5698252974984808043014417 4273689731238606032260813)
                      ·
                        rfl

theorem cell23_8322981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 5, 4, 2].length) (baseStart_8322981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8322981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8322981 prefixEnd_8322981 := by exact prefixLift 8322981
  have htrace : WordTrace (prefixWord ++ tailWord_8322981) baseStart_8322981 baseEnd_8322981 := by
    simpa [prefixWord, tailWord_8322981, baseEnd_8322981] using wordTrace_append hprefix tailTrace_8322981
  have hstable : (prefixWord ++ tailWord_8322981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8322981).length < 2 ^ (prefixWord ++ tailWord_8322981).sum := by decide
  have hdescent : baseEnd_8322981 < baseStart_8322981 := by decide
  rcases family_descends (prefixWord ++ tailWord_8322981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8323031 : List Nat := [1, 1, 3, 2, 1, 1, 5, 1, 2, 3, 3]
def baseStart_8323031 : Nat := 118140960795 + 8323031 * 2 ^ 59
def prefixEnd_8323031 : Nat := 4983230072969 + 3 ^ 40 * 8323031 * 2
def baseEnd_8323031 : Nat := 4273715405271330836635583

theorem tailTrace_8323031 : CollatzResearch.WordTrace tailWord_8323031 prefixEnd_8323031 4273715405271330836635583 := by
  unfold tailWord_8323031
  simp only [CollatzResearch.WordTrace]
  refine ⟨303565879510087622371656947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202377253006725081581104631 303565879510087622371656947)
  ·
    refine ⟨455348819265131433557485421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303565879510087622371656947 455348819265131433557485421)
    ·
      refine ⟨170755807224424287584057033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 455348819265131433557485421 170755807224424287584057033)
      ·
        refine ⟨128066855418318215688042775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170755807224424287584057033 128066855418318215688042775)
        ·
          refine ⟨192100283127477323532064163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128066855418318215688042775 192100283127477323532064163)
          ·
            refine ⟨288150424691215985298096245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192100283127477323532064163 288150424691215985298096245)
            ·
              refine ⟨27014102314801498621696523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 288150424691215985298096245 27014102314801498621696523)
              ·
                refine ⟨40521153472202247932544785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27014102314801498621696523 40521153472202247932544785)
                ·
                  refine ⟨30390865104151685949408589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40521153472202247932544785 30390865104151685949408589)
                  ·
                    refine ⟨11396574414056882231028221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30390865104151685949408589 11396574414056882231028221)
                    ·
                      refine ⟨4273715405271330836635583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11396574414056882231028221 4273715405271330836635583)
                      ·
                        rfl

theorem cell23_8323031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 1, 2, 3, 3].length) (baseStart_8323031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8323031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8323031 prefixEnd_8323031 := by exact prefixLift 8323031
  have htrace : WordTrace (prefixWord ++ tailWord_8323031) baseStart_8323031 baseEnd_8323031 := by
    simpa [prefixWord, tailWord_8323031, baseEnd_8323031] using wordTrace_append hprefix tailTrace_8323031
  have hstable : (prefixWord ++ tailWord_8323031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8323031).length < 2 ^ (prefixWord ++ tailWord_8323031).sum := by decide
  have hdescent : baseEnd_8323031 < baseStart_8323031 := by decide
  rcases family_descends (prefixWord ++ tailWord_8323031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8323071 : List Nat := [1, 1, 2, 2, 1, 2, 1, 6, 2, 1, 4]
def baseStart_8323071 : Nat := 118140960795 + 8323071 * 2 ^ 59
def prefixEnd_8323071 : Nat := 4983230072969 + 3 ^ 40 * 8323071 * 2
def baseEnd_8323071 : Nat := 4273735944497510680135399

theorem tailTrace_8323071 : CollatzResearch.WordTrace tailWord_8323071 prefixEnd_8323071 4273735944497510680135399 := by
  unfold tailWord_8323071
  simp only [CollatzResearch.WordTrace]
  refine ⟨303567338429942709203113067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202378225619961806135408711 303567338429942709203113067)
  ·
    refine ⟨455351007644914063804669601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303567338429942709203113067 455351007644914063804669601)
    ·
      refine ⟨341513255733685547853502201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 455351007644914063804669601 341513255733685547853502201)
      ·
        refine ⟨256134941800264160890126651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 341513255733685547853502201 256134941800264160890126651)
        ·
          refine ⟨384202412700396241335189977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256134941800264160890126651 384202412700396241335189977)
          ·
            refine ⟨288151809525297181001392483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 384202412700396241335189977 288151809525297181001392483)
            ·
              refine ⟨432227714287945771502088725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 288151809525297181001392483 432227714287945771502088725)
              ·
                refine ⟨20260674107247458039160409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 432227714287945771502088725 20260674107247458039160409)
                ·
                  refine ⟨15195505580435593529370307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20260674107247458039160409 15195505580435593529370307)
                  ·
                    refine ⟨22793258370653390294055461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15195505580435593529370307 22793258370653390294055461)
                    ·
                      refine ⟨4273735944497510680135399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22793258370653390294055461 4273735944497510680135399)
                      ·
                        rfl

theorem cell23_8323071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 6, 2, 1, 4].length) (baseStart_8323071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8323071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8323071 prefixEnd_8323071 := by exact prefixLift 8323071
  have htrace : WordTrace (prefixWord ++ tailWord_8323071) baseStart_8323071 baseEnd_8323071 := by
    simpa [prefixWord, tailWord_8323071, baseEnd_8323071] using wordTrace_append hprefix tailTrace_8323071
  have hstable : (prefixWord ++ tailWord_8323071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8323071).length < 2 ^ (prefixWord ++ tailWord_8323071).sum := by decide
  have hdescent : baseEnd_8323071 < baseStart_8323071 := by decide
  rcases family_descends (prefixWord ++ tailWord_8323071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8323091 : List Nat := [1, 1, 1, 2, 1, 4, 3, 2, 1, 4, 3]
def baseStart_8323091 : Nat := 118140960795 + 8323091 * 2 ^ 59
def prefixEnd_8323091 : Nat := 4983230072969 + 3 ^ 40 * 8323091 * 2
def baseEnd_8323091 : Nat := 4273746214110600601885307

theorem tailTrace_8323091 : CollatzResearch.WordTrace tailWord_8323091 prefixEnd_8323091 4273746214110600601885307 := by
  unfold tailWord_8323091
  simp only [CollatzResearch.WordTrace]
  refine ⟨303568067889870252618841127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202378711926580168412560751 303568067889870252618841127)
  ·
    refine ⟨455352101834805378928261691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303568067889870252618841127 455352101834805378928261691)
    ·
      refine ⟨683028152752208068392392537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 455352101834805378928261691 683028152752208068392392537)
      ·
        refine ⟨512271114564156051294294403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 683028152752208068392392537 512271114564156051294294403)
        ·
          refine ⟨768406671846234076941441605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 512271114564156051294294403 768406671846234076941441605)
          ·
            refine ⟨144076250971168889426520301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 768406671846234076941441605 144076250971168889426520301)
            ·
              refine ⟨54028594114188333534945113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144076250971168889426520301 54028594114188333534945113)
              ·
                refine ⟨40521445585641250151208835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54028594114188333534945113 40521445585641250151208835)
                ·
                  refine ⟨60782168378461875226813253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40521445585641250151208835 60782168378461875226813253)
                  ·
                    refine ⟨11396656570961601605027485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60782168378461875226813253 11396656570961601605027485)
                    ·
                      refine ⟨4273746214110600601885307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11396656570961601605027485 4273746214110600601885307)
                      ·
                        rfl

theorem cell23_8323091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 2, 1, 4, 3].length) (baseStart_8323091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8323091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8323091 prefixEnd_8323091 := by exact prefixLift 8323091
  have htrace : WordTrace (prefixWord ++ tailWord_8323091) baseStart_8323091 baseEnd_8323091 := by
    simpa [prefixWord, tailWord_8323091, baseEnd_8323091] using wordTrace_append hprefix tailTrace_8323091
  have hstable : (prefixWord ++ tailWord_8323091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8323091).length < 2 ^ (prefixWord ++ tailWord_8323091).sum := by decide
  have hdescent : baseEnd_8323091 < baseStart_8323091 := by decide
  rcases family_descends (prefixWord ++ tailWord_8323091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8323098 : List Nat := [3, 1, 1, 3, 1, 3, 2, 2, 3, 4]
def baseStart_8323098 : Nat := 118140960795 + 8323098 * 2 ^ 59
def prefixEnd_8323098 : Nat := 4983230072969 + 3 ^ 40 * 8323098 * 2
def baseEnd_8323098 : Nat := 1424583269491727358165925

theorem tailTrace_8323098 : CollatzResearch.WordTrace tailWord_8323098 prefixEnd_8323098 1424583269491727358165925 := by
  unfold tailWord_8323098
  simp only [CollatzResearch.WordTrace]
  refine ⟨75892080800211223203586487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202378882133896595209563965 75892080800211223203586487)
  ·
    refine ⟨113838121200316834805379731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75892080800211223203586487 113838121200316834805379731)
    ·
      refine ⟨170757181800475252208069597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113838121200316834805379731 170757181800475252208069597)
      ·
        refine ⟨64033943175178219578026099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170757181800475252208069597 64033943175178219578026099)
        ·
          refine ⟨96050914762767329367039149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64033943175178219578026099 96050914762767329367039149)
          ·
            refine ⟨36019093036037748512639681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96050914762767329367039149 36019093036037748512639681)
            ·
              refine ⟨27014319777028311384479761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36019093036037748512639681 27014319777028311384479761)
              ·
                refine ⟨20260739832771233538359821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27014319777028311384479761 20260739832771233538359821)
                ·
                  refine ⟨7597777437289212576884933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20260739832771233538359821 7597777437289212576884933)
                  ·
                    refine ⟨1424583269491727358165925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7597777437289212576884933 1424583269491727358165925)
                    ·
                      rfl

theorem cell23_8323098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 2, 3, 4].length) (baseStart_8323098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8323098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8323098 prefixEnd_8323098 := by exact prefixLift 8323098
  have htrace : WordTrace (prefixWord ++ tailWord_8323098) baseStart_8323098 baseEnd_8323098 := by
    simpa [prefixWord, tailWord_8323098, baseEnd_8323098] using wordTrace_append hprefix tailTrace_8323098
  have hstable : (prefixWord ++ tailWord_8323098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8323098).length < 2 ^ (prefixWord ++ tailWord_8323098).sum := by decide
  have hdescent : baseEnd_8323098 < baseStart_8323098 := by decide
  rcases family_descends (prefixWord ++ tailWord_8323098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8323132 : List Nat := [2, 2, 2, 2, 2, 1, 5, 2, 1, 4]
def baseStart_8323132 : Nat := 118140960795 + 8323132 * 2 ^ 59
def prefixEnd_8323132 : Nat := 4983230072969 + 3 ^ 40 * 8323132 * 2
def baseEnd_8323132 : Nat := 1424589088939144980490873

theorem tailTrace_8323132 : CollatzResearch.WordTrace tailWord_8323132 prefixEnd_8323132 1424589088939144980490873 := by
  unfold tailWord_8323132
  simp only [CollatzResearch.WordTrace]
  refine ⟨151784781641360858310541825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202379708855147811080722433 151784781641360858310541825)
  ·
    refine ⟨113838586231020643732906369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151784781641360858310541825 113838586231020643732906369)
    ·
      refine ⟨85378939673265482799679777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113838586231020643732906369 85378939673265482799679777)
      ·
        refine ⟨64034204754949112099759833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85378939673265482799679777 64034204754949112099759833)
        ·
          refine ⟨48025653566211834074819875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64034204754949112099759833 48025653566211834074819875)
          ·
            refine ⟨72038480349317751112229813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48025653566211834074819875 72038480349317751112229813)
            ·
              refine ⟨6753607532748539166771545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 72038480349317751112229813 6753607532748539166771545)
              ·
                refine ⟨5065205649561404375078659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6753607532748539166771545 5065205649561404375078659)
                ·
                  refine ⟨7597808474342106562617989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5065205649561404375078659 7597808474342106562617989)
                  ·
                    refine ⟨1424589088939144980490873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7597808474342106562617989 1424589088939144980490873)
                    ·
                      rfl

theorem cell23_8323132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 5, 2, 1, 4].length) (baseStart_8323132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8323132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8323132 prefixEnd_8323132 := by exact prefixLift 8323132
  have htrace : WordTrace (prefixWord ++ tailWord_8323132) baseStart_8323132 baseEnd_8323132 := by
    simpa [prefixWord, tailWord_8323132, baseEnd_8323132] using wordTrace_append hprefix tailTrace_8323132
  have hstable : (prefixWord ++ tailWord_8323132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8323132).length < 2 ^ (prefixWord ++ tailWord_8323132).sum := by decide
  have hdescent : baseEnd_8323132 < baseStart_8323132 := by decide
  rcases family_descends (prefixWord ++ tailWord_8323132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8323141 : List Nat := [1, 3, 1, 1, 1, 3, 1, 4, 3, 5]
def baseStart_8323141 : Nat := 118140960795 + 8323141 * 2 ^ 59
def prefixEnd_8323141 : Nat := 4983230072969 + 3 ^ 40 * 8323141 * 2
def baseEnd_8323141 : Nat := 1424590629381108468753359

theorem tailTrace_8323141 : CollatzResearch.WordTrace tailWord_8323141 prefixEnd_8323141 1424590629381108468753359 := by
  unfold tailWord_8323141
  simp only [CollatzResearch.WordTrace]
  refine ⟨303569891539689111158161277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202379927693126074105440851 303569891539689111158161277)
  ·
    refine ⟨113838709327383416684310479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 303569891539689111158161277 113838709327383416684310479)
    ·
      refine ⟨170758063991075125026465719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113838709327383416684310479 170758063991075125026465719)
      ·
        refine ⟨256137095986612687539698579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170758063991075125026465719 256137095986612687539698579)
        ·
          refine ⟨384205643979919031309547869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256137095986612687539698579 384205643979919031309547869)
          ·
            refine ⟨144077116492469636741080451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 384205643979919031309547869 144077116492469636741080451)
            ·
              refine ⟨216115674738704455111620677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144077116492469636741080451 216115674738704455111620677)
              ·
                refine ⟨40521689013507085333428877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 216115674738704455111620677 40521689013507085333428877)
                ·
                  refine ⟨15195633380065157000035829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40521689013507085333428877 15195633380065157000035829)
                  ·
                    refine ⟨1424590629381108468753359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15195633380065157000035829 1424590629381108468753359)
                    ·
                      rfl

theorem cell23_8323141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 4, 3, 5].length) (baseStart_8323141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8323141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8323141 prefixEnd_8323141 := by exact prefixLift 8323141
  have htrace : WordTrace (prefixWord ++ tailWord_8323141) baseStart_8323141 baseEnd_8323141 := by
    simpa [prefixWord, tailWord_8323141, baseEnd_8323141] using wordTrace_append hprefix tailTrace_8323141
  have hstable : (prefixWord ++ tailWord_8323141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8323141).length < 2 ^ (prefixWord ++ tailWord_8323141).sum := by decide
  have hdescent : baseEnd_8323141 < baseStart_8323141 := by decide
  rcases family_descends (prefixWord ++ tailWord_8323141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8323148 : List Nat := [2, 2, 1, 3, 1, 1, 2, 1, 3, 5, 2]
def baseStart_8323148 : Nat := 118140960795 + 8323148 * 2 ^ 59
def prefixEnd_8323148 : Nat := 4983230072969 + 3 ^ 40 * 8323148 * 2
def baseEnd_8323148 : Nat := 4273775482507906878872545

theorem tailTrace_8323148 : CollatzResearch.WordTrace tailWord_8323148 prefixEnd_8323148 4273775482507906878872545 := by
  unfold tailWord_8323148
  simp only [CollatzResearch.WordTrace]
  refine ⟨151785073425331875676833049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202380097900442500902444065 151785073425331875676833049)
  ·
    refine ⟨113838805068998906757624787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151785073425331875676833049 113838805068998906757624787)
    ·
      refine ⟨170758207603498360136437181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113838805068998906757624787 170758207603498360136437181)
      ·
        refine ⟨64034327851311885051163943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170758207603498360136437181 64034327851311885051163943)
        ·
          refine ⟨96051491776967827576745915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64034327851311885051163943 96051491776967827576745915)
          ·
            refine ⟨144077237665451741365118873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96051491776967827576745915 144077237665451741365118873)
            ·
              refine ⟨108057928249088806023839155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144077237665451741365118873 108057928249088806023839155)
              ·
                refine ⟨162086892373633209035758733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108057928249088806023839155 162086892373633209035758733)
                ·
                  refine ⟨60782584640112453388409525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 162086892373633209035758733 60782584640112453388409525)
                  ·
                    refine ⟨5698367310010542505163393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60782584640112453388409525 5698367310010542505163393)
                    ·
                      refine ⟨4273775482507906878872545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5698367310010542505163393 4273775482507906878872545)
                      ·
                        rfl

theorem cell23_8323148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 3, 5, 2].length) (baseStart_8323148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8323148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8323148 prefixEnd_8323148 := by exact prefixLift 8323148
  have htrace : WordTrace (prefixWord ++ tailWord_8323148) baseStart_8323148 baseEnd_8323148 := by
    simpa [prefixWord, tailWord_8323148, baseEnd_8323148] using wordTrace_append hprefix tailTrace_8323148
  have hstable : (prefixWord ++ tailWord_8323148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8323148).length < 2 ^ (prefixWord ++ tailWord_8323148).sum := by decide
  have hdescent : baseEnd_8323148 < baseStart_8323148 := by decide
  rcases family_descends (prefixWord ++ tailWord_8323148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8323171 : List Nat := [1, 1, 1, 5, 1, 1, 3, 1, 3, 6]
def baseStart_8323171 : Nat := 118140960795 + 8323171 * 2 ^ 59
def prefixEnd_8323171 : Nat := 4983230072969 + 3 ^ 40 * 8323171 * 2
def baseEnd_8323171 : Nat := 1424595764187653429628313

theorem tailTrace_8323171 : CollatzResearch.WordTrace tailWord_8323171 prefixEnd_8323171 1424595764187653429628313 := by
  unfold tailWord_8323171
  simp only [CollatzResearch.WordTrace]
  refine ⟨303570985729580426281753367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202380657153053617521168911 303570985729580426281753367)
  ·
    refine ⟨455356478594370639422630051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303570985729580426281753367 455356478594370639422630051)
    ·
      refine ⟨683034717891555959133945077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 455356478594370639422630051 683034717891555959133945077)
      ·
        refine ⟨64034504802333371168807351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 683034717891555959133945077 64034504802333371168807351)
        ·
          refine ⟨96051757203500056753211027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64034504802333371168807351 96051757203500056753211027)
          ·
            refine ⟨144077635805250085129816541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96051757203500056753211027 144077635805250085129816541)
            ·
              refine ⟨54029113426968781923681203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144077635805250085129816541 54029113426968781923681203)
              ·
                refine ⟨81043670140453172885521805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54029113426968781923681203 81043670140453172885521805)
                ·
                  refine ⟨30391376302669939832070677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81043670140453172885521805 30391376302669939832070677)
                  ·
                    refine ⟨1424595764187653429628313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30391376302669939832070677 1424595764187653429628313)
                    ·
                      rfl

theorem cell23_8323171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 1, 3, 6].length) (baseStart_8323171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8323171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8323171 prefixEnd_8323171 := by exact prefixLift 8323171
  have htrace : WordTrace (prefixWord ++ tailWord_8323171) baseStart_8323171 baseEnd_8323171 := by
    simpa [prefixWord, tailWord_8323171, baseEnd_8323171] using wordTrace_append hprefix tailTrace_8323171
  have hstable : (prefixWord ++ tailWord_8323171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8323171).length < 2 ^ (prefixWord ++ tailWord_8323171).sum := by decide
  have hdescent : baseEnd_8323171 < baseStart_8323171 := by decide
  rcases family_descends (prefixWord ++ tailWord_8323171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8323175 : List Nat := [1, 1, 5, 1, 1, 2, 5, 1, 1, 5]
def baseStart_8323175 : Nat := 118140960795 + 8323175 * 2 ^ 59
def prefixEnd_8323175 : Nat := 4983230072969 + 3 ^ 40 * 8323175 * 2
def baseEnd_8323175 : Nat := 1424596448828526091078307

theorem tailTrace_8323175 : CollatzResearch.WordTrace tailWord_8323175 prefixEnd_8323175 1424596448828526091078307 := by
  unfold tailWord_8323175
  simp only [CollatzResearch.WordTrace]
  refine ⟨303571131621565934964898979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202380754414377289976599319 303571131621565934964898979)
  ·
    refine ⟨455356697432348902447348469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303571131621565934964898979 455356697432348902447348469)
    ·
      refine ⟨42689690384282709604438919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 455356697432348902447348469 42689690384282709604438919)
      ·
        refine ⟨64034535576424064406658379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42689690384282709604438919 64034535576424064406658379)
        ·
          refine ⟨96051803364636096609987569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64034535576424064406658379 96051803364636096609987569)
          ·
            refine ⟨72038852523477072457490677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96051803364636096609987569 72038852523477072457490677)
            ·
              refine ⟨6753642424075975542889751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 72038852523477072457490677 6753642424075975542889751)
              ·
                refine ⟨10130463636113963314334627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6753642424075975542889751 10130463636113963314334627)
                ·
                  refine ⟨15195695454170944971501941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10130463636113963314334627 15195695454170944971501941)
                  ·
                    refine ⟨1424596448828526091078307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15195695454170944971501941 1424596448828526091078307)
                    ·
                      rfl

theorem cell23_8323175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 5, 1, 1, 5].length) (baseStart_8323175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8323175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8323175 prefixEnd_8323175 := by exact prefixLift 8323175
  have htrace : WordTrace (prefixWord ++ tailWord_8323175) baseStart_8323175 baseEnd_8323175 := by
    simpa [prefixWord, tailWord_8323175, baseEnd_8323175] using wordTrace_append hprefix tailTrace_8323175
  have hstable : (prefixWord ++ tailWord_8323175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8323175).length < 2 ^ (prefixWord ++ tailWord_8323175).sum := by decide
  have hdescent : baseEnd_8323175 < baseStart_8323175 := by decide
  rcases family_descends (prefixWord ++ tailWord_8323175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8323205 : List Nat := [1, 3, 1, 1, 5, 1, 2, 3, 2, 4]
def baseStart_8323205 : Nat := 118140960795 + 8323205 * 2 ^ 59
def prefixEnd_8323205 : Nat := 4983230072969 + 3 ^ 40 * 8323205 * 2
def baseEnd_8323205 : Nat := 1424601583635071051953261

theorem tailTrace_8323205 : CollatzResearch.WordTrace tailWord_8323205 prefixEnd_8323205 1424601583635071051953261 := by
  unfold tailWord_8323205
  simp only [CollatzResearch.WordTrace]
  refine ⟨303572225811457250088491069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202381483874304833392327379 303572225811457250088491069)
  ·
    refine ⟨113839584679296468783184151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 303572225811457250088491069 113839584679296468783184151)
    ·
      refine ⟨170759377018944703174776227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113839584679296468783184151 170759377018944703174776227)
      ·
        refine ⟨256139065528417054762164341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170759377018944703174776227 256139065528417054762164341)
        ·
          refine ⟨24013037393289098883952907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 256139065528417054762164341 24013037393289098883952907)
          ·
            refine ⟨36019556089933648325929361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24013037393289098883952907 36019556089933648325929361)
            ·
              refine ⟨27014667067450236244447021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36019556089933648325929361 27014667067450236244447021)
              ·
                refine ⟨10130500150293838591667633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27014667067450236244447021 10130500150293838591667633)
                ·
                  refine ⟨7597875112720378943750725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10130500150293838591667633 7597875112720378943750725)
                  ·
                    refine ⟨1424601583635071051953261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7597875112720378943750725 1424601583635071051953261)
                    ·
                      rfl

theorem cell23_8323205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 3, 2, 4].length) (baseStart_8323205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8323205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8323205 prefixEnd_8323205 := by exact prefixLift 8323205
  have htrace : WordTrace (prefixWord ++ tailWord_8323205) baseStart_8323205 baseEnd_8323205 := by
    simpa [prefixWord, tailWord_8323205, baseEnd_8323205] using wordTrace_append hprefix tailTrace_8323205
  have hstable : (prefixWord ++ tailWord_8323205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8323205).length < 2 ^ (prefixWord ++ tailWord_8323205).sum := by decide
  have hdescent : baseEnd_8323205 < baseStart_8323205 := by decide
  rcases family_descends (prefixWord ++ tailWord_8323205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8323229 : List Nat := [1, 4, 2, 1, 1, 3, 1, 5, 1, 2, 2]
def baseStart_8323229 : Nat := 118140960795 + 8323229 * 2 ^ 59
def prefixEnd_8323229 : Nat := 4983230072969 + 3 ^ 40 * 8323229 * 2
def baseEnd_8323229 : Nat := 4273817074440921061959673

theorem tailTrace_8323229 : CollatzResearch.WordTrace tailWord_8323229 prefixEnd_8323229 4273817074440921061959673 := by
  unfold tailWord_8323229
  simp only [CollatzResearch.WordTrace]
  refine ⟨303573101163370302187364741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202382067442246868124909827 303573101163370302187364741)
  ·
    refine ⟨56919956468131931660130889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 303573101163370302187364741 56919956468131931660130889)
    ·
      refine ⟨42689967351098948745098167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56919956468131931660130889 42689967351098948745098167)
      ·
        refine ⟨64034951026648423117647251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42689967351098948745098167 64034951026648423117647251)
        ·
          refine ⟨96052426539972634676470877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64034951026648423117647251 96052426539972634676470877)
          ·
            refine ⟨36019659952489738003676579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96052426539972634676470877 36019659952489738003676579)
            ·
              refine ⟨54029489928734607005514869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36019659952489738003676579 54029489928734607005514869)
              ·
                refine ⟨5065264680818869406767019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 54029489928734607005514869 5065264680818869406767019)
                ·
                  refine ⟨7597897021228304110150529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5065264680818869406767019 7597897021228304110150529)
                  ·
                    refine ⟨5698422765921228082612897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7597897021228304110150529 5698422765921228082612897)
                    ·
                      refine ⟨4273817074440921061959673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5698422765921228082612897 4273817074440921061959673)
                      ·
                        rfl

theorem cell23_8323229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 5, 1, 2, 2].length) (baseStart_8323229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8323229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8323229 prefixEnd_8323229 := by exact prefixLift 8323229
  have htrace : WordTrace (prefixWord ++ tailWord_8323229) baseStart_8323229 baseEnd_8323229 := by
    simpa [prefixWord, tailWord_8323229, baseEnd_8323229] using wordTrace_append hprefix tailTrace_8323229
  have hstable : (prefixWord ++ tailWord_8323229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8323229).length < 2 ^ (prefixWord ++ tailWord_8323229).sum := by decide
  have hdescent : baseEnd_8323229 < baseStart_8323229 := by decide
  rcases family_descends (prefixWord ++ tailWord_8323229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8323232 : List Nat := [2, 1, 1, 4, 2, 2, 4, 1, 1, 2, 3]
def baseStart_8323232 : Nat := 118140960795 + 8323232 * 2 ^ 59
def prefixEnd_8323232 : Nat := 4983230072969 + 3 ^ 40 * 8323232 * 2
def baseEnd_8323232 : Nat := 4273818614882884550222159

theorem tailTrace_8323232 : CollatzResearch.WordTrace tailWord_8323232 prefixEnd_8323232 4273818614882884550222159 := by
  unfold tailWord_8323232
  simp only [CollatzResearch.WordTrace]
  refine ⟨151786605291179716849861975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202382140388239622466482633 151786605291179716849861975)
  ·
    refine ⟨227679907936769575274792963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151786605291179716849861975 227679907936769575274792963)
    ·
      refine ⟨341519861905154362912189445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227679907936769575274792963 341519861905154362912189445)
      ·
        refine ⟨64034974107216443046035521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 341519861905154362912189445 64034974107216443046035521)
        ·
          refine ⟨48026230580412332284526641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64034974107216443046035521 48026230580412332284526641)
          ·
            refine ⟨36019672935309249213394981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48026230580412332284526641 36019672935309249213394981)
            ·
              refine ⟨6753688675370484227511559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36019672935309249213394981 6753688675370484227511559)
              ·
                refine ⟨10130533013055726341267339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6753688675370484227511559 10130533013055726341267339)
                ·
                  refine ⟨15195799519583589511901009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10130533013055726341267339 15195799519583589511901009)
                  ·
                    refine ⟨11396849639687692133925757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15195799519583589511901009 11396849639687692133925757)
                    ·
                      refine ⟨4273818614882884550222159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11396849639687692133925757 4273818614882884550222159)
                      ·
                        rfl

theorem cell23_8323232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 4, 1, 1, 2, 3].length) (baseStart_8323232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8323232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8323232 prefixEnd_8323232 := by exact prefixLift 8323232
  have htrace : WordTrace (prefixWord ++ tailWord_8323232) baseStart_8323232 baseEnd_8323232 := by
    simpa [prefixWord, tailWord_8323232, baseEnd_8323232] using wordTrace_append hprefix tailTrace_8323232
  have hstable : (prefixWord ++ tailWord_8323232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8323232).length < 2 ^ (prefixWord ++ tailWord_8323232).sum := by decide
  have hdescent : baseEnd_8323232 < baseStart_8323232 := by decide
  rcases family_descends (prefixWord ++ tailWord_8323232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8323239 : List Nat := [1, 1, 6, 2, 2, 2, 1, 2, 2, 4]
def baseStart_8323239 : Nat := 118140960795 + 8323239 * 2 ^ 59
def prefixEnd_8323239 : Nat := 4983230072969 + 3 ^ 40 * 8323239 * 2
def baseEnd_8323239 : Nat := 1424607403082488674278209

theorem tailTrace_8323239 : CollatzResearch.WordTrace tailWord_8323239 prefixEnd_8323239 1424607403082488674278209 := by
  unfold tailWord_8323239
  simp only [CollatzResearch.WordTrace]
  refine ⟨303573465893334073895228771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202382310595556049263485847 303573465893334073895228771)
  ·
    refine ⟨455360198840001110842843157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303573465893334073895228771 455360198840001110842843157)
    ·
      refine ⟨21345009320625052070758273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 455360198840001110842843157 21345009320625052070758273)
      ·
        refine ⟨16008756990468789053068705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21345009320625052070758273 16008756990468789053068705)
        ·
          refine ⟨12006567742851591789801529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16008756990468789053068705 12006567742851591789801529)
          ·
            refine ⟨9004925807138693842351147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12006567742851591789801529 9004925807138693842351147)
            ·
              refine ⟨13507388710708040763526721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9004925807138693842351147 13507388710708040763526721)
              ·
                refine ⟨10130541533031030572645041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13507388710708040763526721 10130541533031030572645041)
                ·
                  refine ⟨7597906149773272929483781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10130541533031030572645041 7597906149773272929483781)
                  ·
                    refine ⟨1424607403082488674278209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7597906149773272929483781 1424607403082488674278209)
                    ·
                      rfl

theorem cell23_8323239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 1, 2, 2, 4].length) (baseStart_8323239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8323239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8323239 prefixEnd_8323239 := by exact prefixLift 8323239
  have htrace : WordTrace (prefixWord ++ tailWord_8323239) baseStart_8323239 baseEnd_8323239 := by
    simpa [prefixWord, tailWord_8323239, baseEnd_8323239] using wordTrace_append hprefix tailTrace_8323239
  have hstable : (prefixWord ++ tailWord_8323239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8323239).length < 2 ^ (prefixWord ++ tailWord_8323239).sum := by decide
  have hdescent : baseEnd_8323239 < baseStart_8323239 := by decide
  rcases family_descends (prefixWord ++ tailWord_8323239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8323266 : List Nat := [3, 5, 1, 1, 1, 2, 2, 2, 1, 2, 3]
def baseStart_8323266 : Nat := 118140960795 + 8323266 * 2 ^ 59
def prefixEnd_8323266 : Nat := 4983230072969 + 3 ^ 40 * 8323266 * 2
def baseEnd_8323266 : Nat := 4273836073225137417197003

theorem tailTrace_8323266 : CollatzResearch.WordTrace tailWord_8323266 prefixEnd_8323266 4273836073225137417197003 := by
  unfold tailWord_8323266
  simp only [CollatzResearch.WordTrace]
  refine ⟨75893612666059064376615413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202382967109490838337641101 75893612666059064376615413)
  ·
    refine ⟨7115026187443037285307695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 75893612666059064376615413 7115026187443037285307695)
    ·
      refine ⟨10672539281164555927961543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7115026187443037285307695 10672539281164555927961543)
      ·
        refine ⟨16008808921746833891942315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10672539281164555927961543 16008808921746833891942315)
        ·
          refine ⟨24013213382620250837913473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16008808921746833891942315 24013213382620250837913473)
          ·
            refine ⟨18009910036965188128435105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24013213382620250837913473 18009910036965188128435105)
            ·
              refine ⟨13507432527723891096326329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18009910036965188128435105 13507432527723891096326329)
              ·
                refine ⟨10130574395792918322244747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13507432527723891096326329 10130574395792918322244747)
                ·
                  refine ⟨15195861593689377483367121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10130574395792918322244747 15195861593689377483367121)
                  ·
                    refine ⟨11396896195267033112525341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15195861593689377483367121 11396896195267033112525341)
                    ·
                      refine ⟨4273836073225137417197003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11396896195267033112525341 4273836073225137417197003)
                      ·
                        rfl

theorem cell23_8323266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_8323266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8323266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8323266 prefixEnd_8323266 := by exact prefixLift 8323266
  have htrace : WordTrace (prefixWord ++ tailWord_8323266) baseStart_8323266 baseEnd_8323266 := by
    simpa [prefixWord, tailWord_8323266, baseEnd_8323266] using wordTrace_append hprefix tailTrace_8323266
  have hstable : (prefixWord ++ tailWord_8323266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8323266).length < 2 ^ (prefixWord ++ tailWord_8323266).sum := by decide
  have hdescent : baseEnd_8323266 < baseStart_8323266 := by decide
  rcases family_descends (prefixWord ++ tailWord_8323266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8323288 : List Nat := [2, 1, 2, 2, 4, 1, 1, 1, 1, 3, 5]
def baseStart_8323288 : Nat := 118140960795 + 8323288 * 2 ^ 59
def prefixEnd_8323288 : Nat := 4983230072969 + 3 ^ 40 * 8323288 * 2
def baseEnd_8323288 : Nat := 4273847369799536331121901

theorem tailTrace_8323288 : CollatzResearch.WordTrace tailWord_8323288 prefixEnd_8323288 4273847369799536331121901 := by
  unfold tailWord_8323288
  simp only [CollatzResearch.WordTrace]
  refine ⟨151787626535078277631881259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202383502046771036842508345 151787626535078277631881259)
  ·
    refine ⟨227681439802617416447821889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151787626535078277631881259 227681439802617416447821889)
    ·
      refine ⟨170761079851963062335866417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227681439802617416447821889 170761079851963062335866417)
      ·
        refine ⟨128070809888972296751899813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170761079851963062335866417 128070809888972296751899813)
        ·
          refine ⟨24013276854182305640981215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128070809888972296751899813 24013276854182305640981215)
          ·
            refine ⟨36019915281273458461471823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24013276854182305640981215 36019915281273458461471823)
            ·
              refine ⟨54029872921910187692207735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36019915281273458461471823 54029872921910187692207735)
              ·
                refine ⟨81044809382865281538311603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54029872921910187692207735 81044809382865281538311603)
                ·
                  refine ⟨121567214074297922307467405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81044809382865281538311603 121567214074297922307467405)
                  ·
                    refine ⟨45587705277861720865300277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 121567214074297922307467405 45587705277861720865300277)
                    ·
                      refine ⟨4273847369799536331121901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45587705277861720865300277 4273847369799536331121901)
                      ·
                        rfl

theorem cell23_8323288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 1, 1, 3, 5].length) (baseStart_8323288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8323288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8323288 prefixEnd_8323288 := by exact prefixLift 8323288
  have htrace : WordTrace (prefixWord ++ tailWord_8323288) baseStart_8323288 baseEnd_8323288 := by
    simpa [prefixWord, tailWord_8323288, baseEnd_8323288] using wordTrace_append hprefix tailTrace_8323288
  have hstable : (prefixWord ++ tailWord_8323288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8323288).length < 2 ^ (prefixWord ++ tailWord_8323288).sum := by decide
  have hdescent : baseEnd_8323288 < baseStart_8323288 := by decide
  rcases family_descends (prefixWord ++ tailWord_8323288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8323291 : List Nat := [1, 1, 1, 1, 1, 1, 1, 5, 11]
def baseStart_8323291 : Nat := 118140960795 + 8323291 * 2 ^ 59
def prefixEnd_8323291 : Nat := 4983230072969 + 3 ^ 40 * 8323291 * 2
def baseEnd_8323291 : Nat := 474872101137944424376043

theorem tailTrace_8323291 : CollatzResearch.WordTrace tailWord_8323291 prefixEnd_8323291 474872101137944424376043 := by
  unfold tailWord_8323291
  simp only [CollatzResearch.WordTrace]
  refine ⟨303575362489145686776121727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202383574992763791184081151 303575362489145686776121727)
  ·
    refine ⟨455363043733718530164182591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303575362489145686776121727 455363043733718530164182591)
    ·
      refine ⟨683044565600577795246273887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 455363043733718530164182591 683044565600577795246273887)
      ·
        refine ⟨1024566848400866692869410831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 683044565600577795246273887 1024566848400866692869410831)
        ·
          refine ⟨1536850272601300039304116247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1024566848400866692869410831 1536850272601300039304116247)
          ·
            refine ⟨2305275408901950058956174371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1536850272601300039304116247 2305275408901950058956174371)
            ·
              refine ⟨3457913113352925088434261557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2305275408901950058956174371 3457913113352925088434261557)
              ·
                refine ⟨324179354376836727040712021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3457913113352925088434261557 324179354376836727040712021)
                ·
                  refine ⟨474872101137944424376043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 324179354376836727040712021 474872101137944424376043)
                  ·
                    rfl

theorem cell23_8323291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 11].length) (baseStart_8323291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8323291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8323291 prefixEnd_8323291 := by exact prefixLift 8323291
  have htrace : WordTrace (prefixWord ++ tailWord_8323291) baseStart_8323291 baseEnd_8323291 := by
    simpa [prefixWord, tailWord_8323291, baseEnd_8323291] using wordTrace_append hprefix tailTrace_8323291
  have hstable : (prefixWord ++ tailWord_8323291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8323291).length < 2 ^ (prefixWord ++ tailWord_8323291).sum := by decide
  have hdescent : baseEnd_8323291 < baseStart_8323291 := by decide
  rcases family_descends (prefixWord ++ tailWord_8323291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8323338 : List Nat := [3, 1, 2, 2, 1, 1, 2, 3, 1, 7]
def baseStart_8323338 : Nat := 118140960795 + 8323338 * 2 ^ 59
def prefixEnd_8323338 : Nat := 4983230072969 + 3 ^ 40 * 8323338 * 2
def baseEnd_8323338 : Nat := 1424624347944087045165557

theorem tailTrace_8323338 : CollatzResearch.WordTrace tailWord_8323338 prefixEnd_8323338 1424624347944087045165557 := by
  unfold tailWord_8323338
  simp only [CollatzResearch.WordTrace]
  refine ⟨75894269179993853450770667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202384717813316942535388445 75894269179993853450770667)
  ·
    refine ⟨113841403769990780176156001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75894269179993853450770667 113841403769990780176156001)
    ·
      refine ⟨85381052827493085132117001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113841403769990780176156001 85381052827493085132117001)
      ·
        refine ⟨64035789620619813849087751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85381052827493085132117001 64035789620619813849087751)
        ·
          refine ⟨96053684430929720773631627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64035789620619813849087751 96053684430929720773631627)
          ·
            refine ⟨144080526646394581160447441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96053684430929720773631627 144080526646394581160447441)
            ·
              refine ⟨108060394984795935870335581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144080526646394581160447441 108060394984795935870335581)
              ·
                refine ⟨40522648119298475951375843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108060394984795935870335581 40522648119298475951375843)
                ·
                  refine ⟨60783972178947713927063765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40522648119298475951375843 60783972178947713927063765)
                  ·
                    refine ⟨1424624347944087045165557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60783972178947713927063765 1424624347944087045165557)
                    ·
                      rfl

theorem cell23_8323338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 3, 1, 7].length) (baseStart_8323338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8323338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8323338 prefixEnd_8323338 := by exact prefixLift 8323338
  have htrace : WordTrace (prefixWord ++ tailWord_8323338) baseStart_8323338 baseEnd_8323338 := by
    simpa [prefixWord, tailWord_8323338, baseEnd_8323338] using wordTrace_append hprefix tailTrace_8323338
  have hstable : (prefixWord ++ tailWord_8323338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8323338).length < 2 ^ (prefixWord ++ tailWord_8323338).sum := by decide
  have hdescent : baseEnd_8323338 < baseStart_8323338 := by decide
  rcases family_descends (prefixWord ++ tailWord_8323338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8323359 : List Nat := [1, 1, 2, 4, 3, 3, 2, 2, 5]
def baseStart_8323359 : Nat := 118140960795 + 8323359 * 2 ^ 59
def prefixEnd_8323359 : Nat := 4983230072969 + 3 ^ 40 * 8323359 * 2
def baseEnd_8323359 : Nat := 474875980769556172592675

theorem tailTrace_8323359 : CollatzResearch.WordTrace tailWord_8323359 prefixEnd_8323359 474875980769556172592675 := by
  unfold tailWord_8323359
  simp only [CollatzResearch.WordTrace]
  refine ⟨303577842652899334389597131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202385228435266222926398087 303577842652899334389597131)
  ·
    refine ⟨455366763979349001584395697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303577842652899334389597131 455366763979349001584395697)
    ·
      refine ⟨341525072984511751188296773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 455366763979349001584395697 341525072984511751188296773)
      ·
        refine ⟨64035951184595953347805645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 341525072984511751188296773 64035951184595953347805645)
        ·
          refine ⟨24013481694223482505427117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64035951184595953347805645 24013481694223482505427117)
          ·
            refine ⟨9005055635333805939535169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24013481694223482505427117 9005055635333805939535169)
            ·
              refine ⟨6753791726500354454651377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9005055635333805939535169 6753791726500354454651377)
              ·
                refine ⟨5065343794875265840988533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6753791726500354454651377 5065343794875265840988533)
                ·
                  refine ⟨474875980769556172592675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5065343794875265840988533 474875980769556172592675)
                  ·
                    rfl

theorem cell23_8323359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 2, 2, 5].length) (baseStart_8323359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8323359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8323359 prefixEnd_8323359 := by exact prefixLift 8323359
  have htrace : WordTrace (prefixWord ++ tailWord_8323359) baseStart_8323359 baseEnd_8323359 := by
    simpa [prefixWord, tailWord_8323359, baseEnd_8323359] using wordTrace_append hprefix tailTrace_8323359
  have hstable : (prefixWord ++ tailWord_8323359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8323359).length < 2 ^ (prefixWord ++ tailWord_8323359).sum := by decide
  have hdescent : baseEnd_8323359 < baseStart_8323359 := by decide
  rcases family_descends (prefixWord ++ tailWord_8323359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8323362 : List Nat := [3, 3, 1, 1, 3, 1, 1, 1, 2, 5, 2]
def baseStart_8323362 : Nat := 118140960795 + 8323362 * 2 ^ 59
def prefixEnd_8323362 : Nat := 4983230072969 + 3 ^ 40 * 8323362 * 2
def baseEnd_8323362 : Nat := 4273885367367969041596561

theorem tailTrace_8323362 : CollatzResearch.WordTrace tailWord_8323362 prefixEnd_8323362 4273885367367969041596561 := by
  unfold tailWord_8323362
  simp only [CollatzResearch.WordTrace]
  refine ⟨75894488017972116475489085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202385301381258977267970893 75894488017972116475489085)
  ·
    refine ⟨28460433006739543678308407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75894488017972116475489085 28460433006739543678308407)
    ·
      refine ⟨42690649510109315517462611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28460433006739543678308407 42690649510109315517462611)
      ·
        refine ⟨64035974265163973276193917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42690649510109315517462611 64035974265163973276193917)
        ·
          refine ⟨24013490349436489978572719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64035974265163973276193917 24013490349436489978572719)
          ·
            refine ⟨36020235524154734967859079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24013490349436489978572719 36020235524154734967859079)
            ·
              refine ⟨54030353286232102451788619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36020235524154734967859079 54030353286232102451788619)
              ·
                refine ⟨81045529929348153677682929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54030353286232102451788619 81045529929348153677682929)
                ·
                  refine ⟨60784147447011115258262197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81045529929348153677682929 60784147447011115258262197)
                  ·
                    refine ⟨5698513823157292055462081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60784147447011115258262197 5698513823157292055462081)
                    ·
                      refine ⟨4273885367367969041596561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5698513823157292055462081 4273885367367969041596561)
                      ·
                        rfl

theorem cell23_8323362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 1, 2, 5, 2].length) (baseStart_8323362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8323362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8323362 prefixEnd_8323362 := by exact prefixLift 8323362
  have htrace : WordTrace (prefixWord ++ tailWord_8323362) baseStart_8323362 baseEnd_8323362 := by
    simpa [prefixWord, tailWord_8323362, baseEnd_8323362] using wordTrace_append hprefix tailTrace_8323362
  have hstable : (prefixWord ++ tailWord_8323362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8323362).length < 2 ^ (prefixWord ++ tailWord_8323362).sum := by decide
  have hdescent : baseEnd_8323362 < baseStart_8323362 := by decide
  rcases family_descends (prefixWord ++ tailWord_8323362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8323375 : List Nat := [1, 1, 2, 1, 2, 1, 5, 1, 1, 6, 2]
def baseStart_8323375 : Nat := 118140960795 + 8323375 * 2 ^ 59
def prefixEnd_8323375 : Nat := 4983230072969 + 3 ^ 40 * 8323375 * 2
def baseEnd_8323375 : Nat := 4273892042616477490734001

theorem tailTrace_8323375 : CollatzResearch.WordTrace tailWord_8323375 prefixEnd_8323375 4273892042616477490734001 := by
  unfold tailWord_8323375
  simp only [CollatzResearch.WordTrace]
  refine ⟨303578426220841369122179579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202385617480560912748119719 303578426220841369122179579)
  ·
    refine ⟨455367639331262053683269369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303578426220841369122179579 455367639331262053683269369)
    ·
      refine ⟨341525729498446540262452027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 455367639331262053683269369 341525729498446540262452027)
      ·
        refine ⟨512288594247669810393678041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341525729498446540262452027 512288594247669810393678041)
        ·
          refine ⟨384216445685752357795258531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 512288594247669810393678041 384216445685752357795258531)
          ·
            refine ⟨576324668528628536692887797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 384216445685752357795258531 576324668528628536692887797)
            ·
              refine ⟨54030437674558925314958231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 576324668528628536692887797 54030437674558925314958231)
              ·
                refine ⟨81045656511838387972437347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54030437674558925314958231 81045656511838387972437347)
                ·
                  refine ⟨121568484767757581958656021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81045656511838387972437347 121568484767757581958656021)
                  ·
                    refine ⟨5698522723488636654312001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 121568484767757581958656021 5698522723488636654312001)
                    ·
                      refine ⟨4273892042616477490734001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5698522723488636654312001 4273892042616477490734001)
                      ·
                        rfl

theorem cell23_8323375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 1, 1, 6, 2].length) (baseStart_8323375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8323375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8323375 prefixEnd_8323375 := by exact prefixLift 8323375
  have htrace : WordTrace (prefixWord ++ tailWord_8323375) baseStart_8323375 baseEnd_8323375 := by
    simpa [prefixWord, tailWord_8323375, baseEnd_8323375] using wordTrace_append hprefix tailTrace_8323375
  have hstable : (prefixWord ++ tailWord_8323375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8323375).length < 2 ^ (prefixWord ++ tailWord_8323375).sum := by decide
  have hdescent : baseEnd_8323375 < baseStart_8323375 := by decide
  rcases family_descends (prefixWord ++ tailWord_8323375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8323496 : List Nat := [2, 1, 6, 1, 1, 3, 1, 2, 1, 5]
def baseStart_8323496 : Nat := 118140960795 + 8323496 * 2 ^ 59
def prefixEnd_8323496 : Nat := 4983230072969 + 3 ^ 40 * 8323496 * 2
def baseEnd_8323496 : Nat := 1424651391258557172440315

theorem tailTrace_8323496 : CollatzResearch.WordTrace tailWord_8323496 prefixEnd_8323496 1424651391258557172440315 := by
  unfold tailWord_8323496
  simp only [CollatzResearch.WordTrace]
  refine ⟨151791419726701503393667171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202388559635602004524889561 151791419726701503393667171)
  ·
    refine ⟨227687129590052255090500757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151791419726701503393667171 227687129590052255090500757)
    ·
      refine ⟨10672834199533699457367223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 227687129590052255090500757 10672834199533699457367223)
      ·
        refine ⟨16009251299300549186050835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10672834199533699457367223 16009251299300549186050835)
        ·
          refine ⟨24013876948950823779076253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16009251299300549186050835 24013876948950823779076253)
          ·
            refine ⟨9005203855856558917153595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24013876948950823779076253 9005203855856558917153595)
            ·
              refine ⟨13507805783784838375730393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9005203855856558917153595 13507805783784838375730393)
              ·
                refine ⟨10130854337838628781797795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13507805783784838375730393 10130854337838628781797795)
                ·
                  refine ⟨15196281506757943172696693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10130854337838628781797795 15196281506757943172696693)
                  ·
                    refine ⟨1424651391258557172440315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15196281506757943172696693 1424651391258557172440315)
                    ·
                      rfl

theorem cell23_8323496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_8323496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8323496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8323496 prefixEnd_8323496 := by exact prefixLift 8323496
  have htrace : WordTrace (prefixWord ++ tailWord_8323496) baseStart_8323496 baseEnd_8323496 := by
    simpa [prefixWord, tailWord_8323496, baseEnd_8323496] using wordTrace_append hprefix tailTrace_8323496
  have hstable : (prefixWord ++ tailWord_8323496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8323496).length < 2 ^ (prefixWord ++ tailWord_8323496).sum := by decide
  have hdescent : baseEnd_8323496 < baseStart_8323496 := by decide
  rcases family_descends (prefixWord ++ tailWord_8323496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8323505 : List Nat := [1, 2, 2, 4, 1, 2, 2, 9]
def baseStart_8323505 : Nat := 118140960795 + 8323505 * 2 ^ 59
def prefixEnd_8323505 : Nat := 4983230072969 + 3 ^ 40 * 8323505 * 2
def baseEnd_8323505 : Nat := 158294770188946740078089

theorem tailTrace_8323505 : CollatzResearch.WordTrace tailWord_8323505 prefixEnd_8323505 158294770188946740078089 := by
  unfold tailWord_8323505
  simp only [CollatzResearch.WordTrace]
  refine ⟨303583167710370401324411969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202388778473580267549607979 303583167710370401324411969)
  ·
    refine ⟨227687375782777800993308977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303583167710370401324411969 227687375782777800993308977)
    ·
      refine ⟨170765531837083350744981733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227687375782777800993308977 170765531837083350744981733)
      ·
        refine ⟨32018537219453128264684075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 170765531837083350744981733 32018537219453128264684075)
        ·
          refine ⟨48027805829179692397026113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32018537219453128264684075 48027805829179692397026113)
          ·
            refine ⟨36020854371884769297769585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48027805829179692397026113 36020854371884769297769585)
            ·
              refine ⟨27015640778913576973327189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36020854371884769297769585 27015640778913576973327189)
              ·
                refine ⟨158294770188946740078089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 27015640778913576973327189 158294770188946740078089)
                ·
                  rfl

theorem cell23_8323505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 9].length) (baseStart_8323505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8323505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8323505 prefixEnd_8323505 := by exact prefixLift 8323505
  have htrace : WordTrace (prefixWord ++ tailWord_8323505) baseStart_8323505 baseEnd_8323505 := by
    simpa [prefixWord, tailWord_8323505, baseEnd_8323505] using wordTrace_append hprefix tailTrace_8323505
  have hstable : (prefixWord ++ tailWord_8323505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8323505).length < 2 ^ (prefixWord ++ tailWord_8323505).sum := by decide
  have hdescent : baseEnd_8323505 < baseStart_8323505 := by decide
  rcases family_descends (prefixWord ++ tailWord_8323505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8323516 : List Nat := [2, 2, 2, 4, 1, 2, 3, 1, 1, 1, 4]
def baseStart_8323516 : Nat := 118140960795 + 8323516 * 2 ^ 59
def prefixEnd_8323516 : Nat := 4983230072969 + 3 ^ 40 * 8323516 * 2
def baseEnd_8323516 : Nat := 4273964443388761439070853

theorem tailTrace_8323516 : CollatzResearch.WordTrace tailWord_8323516 prefixEnd_8323516 4273964443388761439070853 := by
  unfold tailWord_8323516
  simp only [CollatzResearch.WordTrace]
  refine ⟨151791784456665275101531201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202389045942220366802041601 151791784456665275101531201)
  ·
    refine ⟨113843838342498956326148401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151791784456665275101531201 113843838342498956326148401)
    ·
      refine ⟨85382878756874217244611301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113843838342498956326148401 85382878756874217244611301)
      ·
        refine ⟨16009289766913915733364619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85382878756874217244611301 16009289766913915733364619)
        ·
          refine ⟨24013934650370873600046929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16009289766913915733364619 24013934650370873600046929)
          ·
            refine ⟨18010450987778155200035197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24013934650370873600046929 18010450987778155200035197)
            ·
              refine ⟨6753919120416808200013199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18010450987778155200035197 6753919120416808200013199)
              ·
                refine ⟨10130878680625212300019799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6753919120416808200013199 10130878680625212300019799)
                ·
                  refine ⟨15196318020937818450029699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10130878680625212300019799 15196318020937818450029699)
                  ·
                    refine ⟨22794477031406727675044549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15196318020937818450029699 22794477031406727675044549)
                    ·
                      refine ⟨4273964443388761439070853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22794477031406727675044549 4273964443388761439070853)
                      ·
                        rfl

theorem cell23_8323516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 3, 1, 1, 1, 4].length) (baseStart_8323516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8323516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8323516 prefixEnd_8323516 := by exact prefixLift 8323516
  have htrace : WordTrace (prefixWord ++ tailWord_8323516) baseStart_8323516 baseEnd_8323516 := by
    simpa [prefixWord, tailWord_8323516, baseEnd_8323516] using wordTrace_append hprefix tailTrace_8323516
  have hstable : (prefixWord ++ tailWord_8323516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8323516).length < 2 ^ (prefixWord ++ tailWord_8323516).sum := by decide
  have hdescent : baseEnd_8323516 < baseStart_8323516 := by decide
  rcases family_descends (prefixWord ++ tailWord_8323516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8323549 : List Nat := [1, 4, 3, 1, 1, 1, 4, 1, 1, 3, 3]
def baseStart_8323549 : Nat := 118140960795 + 8323549 * 2 ^ 59
def prefixEnd_8323549 : Nat := 4983230072969 + 3 ^ 40 * 8323549 * 2
def baseEnd_8323549 : Nat := 4273981388250359809958201

theorem tailTrace_8323549 : CollatzResearch.WordTrace tailWord_8323549 prefixEnd_8323549 4273981388250359809958201 := by
  unfold tailWord_8323549
  simp only [CollatzResearch.WordTrace]
  refine ⟨303584772522210996839013701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202389848348140664559342467 303584772522210996839013701)
  ·
    refine ⟨56922144847914561907315069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 303584772522210996839013701 56922144847914561907315069)
    ·
      refine ⟨21345804317967960715243151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56922144847914561907315069 21345804317967960715243151)
      ·
        refine ⟨32018706476951941072864727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21345804317967960715243151 32018706476951941072864727)
        ·
          refine ⟨48028059715427911609297091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32018706476951941072864727 48028059715427911609297091)
          ·
            refine ⟨72042089573141867413945637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48028059715427911609297091 72042089573141867413945637)
            ·
              refine ⟨13507891794964100140114807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72042089573141867413945637 13507891794964100140114807)
              ·
                refine ⟨20261837692446150210172211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13507891794964100140114807 20261837692446150210172211)
                ·
                  refine ⟨30392756538669225315258317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20261837692446150210172211 30392756538669225315258317)
                  ·
                    refine ⟨11397283702000959493221869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30392756538669225315258317 11397283702000959493221869)
                    ·
                      refine ⟨4273981388250359809958201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11397283702000959493221869 4273981388250359809958201)
                      ·
                        rfl

theorem cell23_8323549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 4, 1, 1, 3, 3].length) (baseStart_8323549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8323549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8323549 prefixEnd_8323549 := by exact prefixLift 8323549
  have htrace : WordTrace (prefixWord ++ tailWord_8323549) baseStart_8323549 baseEnd_8323549 := by
    simpa [prefixWord, tailWord_8323549, baseEnd_8323549] using wordTrace_append hprefix tailTrace_8323549
  have hstable : (prefixWord ++ tailWord_8323549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8323549).length < 2 ^ (prefixWord ++ tailWord_8323549).sum := by decide
  have hdescent : baseEnd_8323549 < baseStart_8323549 := by decide
  rcases family_descends (prefixWord ++ tailWord_8323549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8323559 : List Nat := [1, 1, 5, 2, 1, 1, 1, 3, 3, 3, 2]
def baseStart_8323559 : Nat := 118140960795 + 8323559 * 2 ^ 59
def prefixEnd_8323559 : Nat := 4983230072969 + 3 ^ 40 * 8323559 * 2
def baseEnd_8323559 : Nat := 4273986523056904770833155

theorem tailTrace_8323559 : CollatzResearch.WordTrace tailWord_8323559 prefixEnd_8323559 4273986523056904770833155 := by
  unfold tailWord_8323559
  simp only [CollatzResearch.WordTrace]
  refine ⟨303585137252174768546877731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202390091501449845697918487 303585137252174768546877731)
  ·
    refine ⟨455377705878262152820316597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303585137252174768546877731 455377705878262152820316597)
    ·
      refine ⟨42691659926087076826904681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 455377705878262152820316597 42691659926087076826904681)
      ·
        refine ⟨32018744944565307620178511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42691659926087076826904681 32018744944565307620178511)
        ·
          refine ⟨48028117416847961430267767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32018744944565307620178511 48028117416847961430267767)
          ·
            refine ⟨72042176125271942145401651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48028117416847961430267767 72042176125271942145401651)
            ·
              refine ⟨108063264187907913218102477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72042176125271942145401651 108063264187907913218102477)
              ·
                refine ⟨40523724070465467456788429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108063264187907913218102477 40523724070465467456788429)
                ·
                  refine ⟨15196396526424550296295661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40523724070465467456788429 15196396526424550296295661)
                  ·
                    refine ⟨5698648697409206361110873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15196396526424550296295661 5698648697409206361110873)
                    ·
                      refine ⟨4273986523056904770833155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5698648697409206361110873 4273986523056904770833155)
                      ·
                        rfl

theorem cell23_8323559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 3, 3, 3, 2].length) (baseStart_8323559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8323559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8323559 prefixEnd_8323559 := by exact prefixLift 8323559
  have htrace : WordTrace (prefixWord ++ tailWord_8323559) baseStart_8323559 baseEnd_8323559 := by
    simpa [prefixWord, tailWord_8323559, baseEnd_8323559] using wordTrace_append hprefix tailTrace_8323559
  have hstable : (prefixWord ++ tailWord_8323559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8323559).length < 2 ^ (prefixWord ++ tailWord_8323559).sum := by decide
  have hdescent : baseEnd_8323559 < baseStart_8323559 := by decide
  rcases family_descends (prefixWord ++ tailWord_8323559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8323570 : List Nat := [3, 2, 1, 4, 3, 1, 2, 1, 1, 2, 3]
def baseStart_8323570 : Nat := 118140960795 + 8323570 * 2 ^ 59
def prefixEnd_8323570 : Nat := 4983230072969 + 3 ^ 40 * 8323570 * 2
def baseEnd_8323570 : Nat := 4273992171344104227795605

theorem tailTrace_8323570 : CollatzResearch.WordTrace tailWord_8323570 prefixEnd_8323570 4273992171344104227795605 := by
  unfold tailWord_8323570
  simp only [CollatzResearch.WordTrace]
  refine ⟨75896384613783729356382041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202390358970089944950352109 75896384613783729356382041)
  ·
    refine ⟨56922288460337797017286531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75896384613783729356382041 56922288460337797017286531)
    ·
      refine ⟨85383432690506695525929797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56922288460337797017286531 85383432690506695525929797)
      ·
        refine ⟨16009393629470005411111837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85383432690506695525929797 16009393629470005411111837)
        ·
          refine ⟨6003522611051252029166939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16009393629470005411111837 6003522611051252029166939)
          ·
            refine ⟨9005283916576878043750409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6003522611051252029166939 9005283916576878043750409)
            ·
              refine ⟨6753962937432658532812807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9005283916576878043750409 6753962937432658532812807)
              ·
                refine ⟨10130944406148987799219211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6753962937432658532812807 10130944406148987799219211)
                ·
                  refine ⟨15196416609223481698828817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10130944406148987799219211 15196416609223481698828817)
                  ·
                    refine ⟨11397312456917611274121613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15196416609223481698828817 11397312456917611274121613)
                    ·
                      refine ⟨4273992171344104227795605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11397312456917611274121613 4273992171344104227795605)
                      ·
                        rfl

theorem cell23_8323570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 2, 1, 1, 2, 3].length) (baseStart_8323570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8323570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8323570 prefixEnd_8323570 := by exact prefixLift 8323570
  have htrace : WordTrace (prefixWord ++ tailWord_8323570) baseStart_8323570 baseEnd_8323570 := by
    simpa [prefixWord, tailWord_8323570, baseEnd_8323570] using wordTrace_append hprefix tailTrace_8323570
  have hstable : (prefixWord ++ tailWord_8323570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8323570).length < 2 ^ (prefixWord ++ tailWord_8323570).sum := by decide
  have hdescent : baseEnd_8323570 < baseStart_8323570 := by decide
  rcases family_descends (prefixWord ++ tailWord_8323570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8323575 : List Nat := [1, 1, 3, 1, 1, 1, 1, 2, 6, 1, 5]
def baseStart_8323575 : Nat := 118140960795 + 8323575 * 2 ^ 59
def prefixEnd_8323575 : Nat := 4983230072969 + 3 ^ 40 * 8323575 * 2
def baseEnd_8323575 : Nat := 4273994738747376708233081

theorem tailTrace_8323575 : CollatzResearch.WordTrace tailWord_8323575 prefixEnd_8323575 4273994738747376708233081 := by
  unfold tailWord_8323575
  simp only [CollatzResearch.WordTrace]
  refine ⟨303585720820116803279460179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202390480546744535519640119 303585720820116803279460179)
  ·
    refine ⟨455378581230175204919190269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303585720820116803279460179 455378581230175204919190269)
    ·
      refine ⟨170766967961315701844696351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 455378581230175204919190269 170766967961315701844696351)
      ·
        refine ⟨256150451941973552767044527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170766967961315701844696351 256150451941973552767044527)
        ·
          refine ⟨384225677912960329150566791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256150451941973552767044527 384225677912960329150566791)
          ·
            refine ⟨576338516869440493725850187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 384225677912960329150566791 576338516869440493725850187)
            ·
              refine ⟨864507775304160740588775281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 576338516869440493725850187 864507775304160740588775281)
              ·
                refine ⟨648380831478120555441581461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 864507775304160740588775281 648380831478120555441581461)
                ·
                  refine ⟨30392851475536901036324131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 648380831478120555441581461 30392851475536901036324131)
                  ·
                    refine ⟨45589277213305351554486197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30392851475536901036324131 45589277213305351554486197)
                    ·
                      refine ⟨4273994738747376708233081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45589277213305351554486197 4273994738747376708233081)
                      ·
                        rfl

theorem cell23_8323575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 6, 1, 5].length) (baseStart_8323575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8323575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8323575 prefixEnd_8323575 := by exact prefixLift 8323575
  have htrace : WordTrace (prefixWord ++ tailWord_8323575) baseStart_8323575 baseEnd_8323575 := by
    simpa [prefixWord, tailWord_8323575, baseEnd_8323575] using wordTrace_append hprefix tailTrace_8323575
  have hstable : (prefixWord ++ tailWord_8323575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8323575).length < 2 ^ (prefixWord ++ tailWord_8323575).sum := by decide
  have hdescent : baseEnd_8323575 < baseStart_8323575 := by decide
  rcases family_descends (prefixWord ++ tailWord_8323575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8323612 : List Nat := [2, 2, 3, 1, 2, 2, 2, 2, 7]
def baseStart_8323612 : Nat := 118140960795 + 8323612 * 2 ^ 59
def prefixEnd_8323612 : Nat := 4983230072969 + 3 ^ 40 * 8323612 * 2
def baseEnd_8323612 : Nat := 474890415281288118163379

theorem tailTrace_8323612 : CollatzResearch.WordTrace tailWord_8323612 prefixEnd_8323612 474890415281288118163379 := by
  unfold tailWord_8323612
  simp only [CollatzResearch.WordTrace]
  refine ⟨151793535160491379299278545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202391380213988505732371393 151793535160491379299278545)
  ·
    refine ⟨113845151370368534474458909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151793535160491379299278545 113845151370368534474458909)
    ·
      refine ⟨42691931763888200427922091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113845151370368534474458909 42691931763888200427922091)
      ·
        refine ⟨64037897645832300641883137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42691931763888200427922091 64037897645832300641883137)
        ·
          refine ⟨48028423234374225481412353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64037897645832300641883137 48028423234374225481412353)
          ·
            refine ⟨36021317425780669111059265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48028423234374225481412353 36021317425780669111059265)
            ·
              refine ⟨27015988069335501833294449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36021317425780669111059265 27015988069335501833294449)
              ·
                refine ⟨20261991052001626374970837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27015988069335501833294449 20261991052001626374970837)
                ·
                  refine ⟨474890415281288118163379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20261991052001626374970837 474890415281288118163379)
                  ·
                    rfl

theorem cell23_8323612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 2, 7].length) (baseStart_8323612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8323612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8323612 prefixEnd_8323612 := by exact prefixLift 8323612
  have htrace : WordTrace (prefixWord ++ tailWord_8323612) baseStart_8323612 baseEnd_8323612 := by
    simpa [prefixWord, tailWord_8323612, baseEnd_8323612] using wordTrace_append hprefix tailTrace_8323612
  have hstable : (prefixWord ++ tailWord_8323612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8323612).length < 2 ^ (prefixWord ++ tailWord_8323612).sum := by decide
  have hdescent : baseEnd_8323612 < baseStart_8323612 := by decide
  rcases family_descends (prefixWord ++ tailWord_8323612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8323642 : List Nat := [3, 1, 1, 1, 3, 3, 1, 1, 4, 5]
def baseStart_8323642 : Nat := 118140960795 + 8323642 * 2 ^ 59
def prefixEnd_8323642 : Nat := 4983230072969 + 3 ^ 40 * 8323642 * 2
def baseEnd_8323642 : Nat := 1424676380650409315365091

theorem tailTrace_8323642 : CollatzResearch.WordTrace tailWord_8323642 prefixEnd_8323642 1424676380650409315365091 := by
  unfold tailWord_8323642
  simp only [CollatzResearch.WordTrace]
  refine ⟨75897041127718518430537295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202392109673916049148099453 75897041127718518430537295)
  ·
    refine ⟨113845561691577777645805943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75897041127718518430537295 113845561691577777645805943)
    ·
      refine ⟨170768342537366666468708915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113845561691577777645805943 170768342537366666468708915)
      ·
        refine ⟨256152513806049999703063373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170768342537366666468708915 256152513806049999703063373)
        ·
          refine ⟨96057192677268749888648765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 256152513806049999703063373 96057192677268749888648765)
          ·
            refine ⟨36021447253975781208243287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96057192677268749888648765 36021447253975781208243287)
            ·
              refine ⟨54032170880963671812364931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36021447253975781208243287 54032170880963671812364931)
              ·
                refine ⟨81048256321445507718547397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54032170880963671812364931 81048256321445507718547397)
                ·
                  refine ⟨15196548060271032697227637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81048256321445507718547397 15196548060271032697227637)
                  ·
                    refine ⟨1424676380650409315365091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15196548060271032697227637 1424676380650409315365091)
                    ·
                      rfl

theorem cell23_8323642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 1, 4, 5].length) (baseStart_8323642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8323642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8323642 prefixEnd_8323642 := by exact prefixLift 8323642
  have htrace : WordTrace (prefixWord ++ tailWord_8323642) baseStart_8323642 baseEnd_8323642 := by
    simpa [prefixWord, tailWord_8323642, baseEnd_8323642] using wordTrace_append hprefix tailTrace_8323642
  have hstable : (prefixWord ++ tailWord_8323642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8323642).length < 2 ^ (prefixWord ++ tailWord_8323642).sum := by decide
  have hdescent : baseEnd_8323642 < baseStart_8323642 := by decide
  rcases family_descends (prefixWord ++ tailWord_8323642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8323662 : List Nat := [4, 1, 1, 1, 1, 2, 2, 1, 3, 3, 4]
def baseStart_8323662 : Nat := 118140960795 + 8323662 * 2 ^ 59
def prefixEnd_8323662 : Nat := 4983230072969 + 3 ^ 40 * 8323662 * 2
def baseEnd_8323662 : Nat := 4274039411564317867845181

theorem tailTrace_8323662 : CollatzResearch.WordTrace tailWord_8323662 prefixEnd_8323662 4274039411564317867845181 := by
  unfold tailWord_8323662
  simp only [CollatzResearch.WordTrace]
  refine ⟨37948611746350202142234655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202392595980534411425251493 37948611746350202142234655)
  ·
    refine ⟨56922917619525303213351983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37948611746350202142234655 56922917619525303213351983)
    ·
      refine ⟨85384376429287954820027975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56922917619525303213351983 85384376429287954820027975)
      ·
        refine ⟨128076564643931932230041963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85384376429287954820027975 128076564643931932230041963)
        ·
          refine ⟨192114846965897898345062945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128076564643931932230041963 192114846965897898345062945)
          ·
            refine ⟨144086135224423423758797209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192114846965897898345062945 144086135224423423758797209)
            ·
              refine ⟨108064601418317567819097907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144086135224423423758797209 108064601418317567819097907)
              ·
                refine ⟨162096902127476351728646861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108064601418317567819097907 162096902127476351728646861)
                ·
                  refine ⟨60786338297803631898242573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 162096902127476351728646861 60786338297803631898242573)
                  ·
                    refine ⟨22794876861676361961840965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60786338297803631898242573 22794876861676361961840965)
                    ·
                      refine ⟨4274039411564317867845181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22794876861676361961840965 4274039411564317867845181)
                      ·
                        rfl

theorem cell23_8323662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 3, 3, 4].length) (baseStart_8323662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8323662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8323662 prefixEnd_8323662 := by exact prefixLift 8323662
  have htrace : WordTrace (prefixWord ++ tailWord_8323662) baseStart_8323662 baseEnd_8323662 := by
    simpa [prefixWord, tailWord_8323662, baseEnd_8323662] using wordTrace_append hprefix tailTrace_8323662
  have hstable : (prefixWord ++ tailWord_8323662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8323662).length < 2 ^ (prefixWord ++ tailWord_8323662).sum := by decide
  have hdescent : baseEnd_8323662 < baseStart_8323662 := by decide
  rcases family_descends (prefixWord ++ tailWord_8323662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8323676 : List Nat := [2, 2, 4, 1, 3, 1, 2, 1, 2, 5]
def baseStart_8323676 : Nat := 118140960795 + 8323676 * 2 ^ 59
def prefixEnd_8323676 : Nat := 4983230072969 + 3 ^ 40 * 8323676 * 2
def baseEnd_8323676 : Nat := 1424682200097826937690039

theorem tailTrace_8323676 : CollatzResearch.WordTrace tailWord_8323676 prefixEnd_8323676 1424682200097826937690039 := by
  unfold tailWord_8323676
  simp only [CollatzResearch.WordTrace]
  refine ⟨151794702296375448764443441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202392936395167265019257921 151794702296375448764443441)
  ·
    refine ⟨113846026722281586573332581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151794702296375448764443441 113846026722281586573332581)
    ·
      refine ⟨21346130010427797482499859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113846026722281586573332581 21346130010427797482499859)
      ·
        refine ⟨32019195015641696223749789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21346130010427797482499859 32019195015641696223749789)
        ·
          refine ⟨12007198130865636083906171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32019195015641696223749789 12007198130865636083906171)
          ·
            refine ⟨18010797196298454125859257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12007198130865636083906171 18010797196298454125859257)
            ·
              refine ⟨13508097897223840594394443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18010797196298454125859257 13508097897223840594394443)
              ·
                refine ⟨20262146845835760891591665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13508097897223840594394443 20262146845835760891591665)
                ·
                  refine ⟨15196610134376820668693749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20262146845835760891591665 15196610134376820668693749)
                  ·
                    refine ⟨1424682200097826937690039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15196610134376820668693749 1424682200097826937690039)
                    ·
                      rfl

theorem cell23_8323676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 2, 1, 2, 5].length) (baseStart_8323676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8323676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8323676 prefixEnd_8323676 := by exact prefixLift 8323676
  have htrace : WordTrace (prefixWord ++ tailWord_8323676) baseStart_8323676 baseEnd_8323676 := by
    simpa [prefixWord, tailWord_8323676, baseEnd_8323676] using wordTrace_append hprefix tailTrace_8323676
  have hstable : (prefixWord ++ tailWord_8323676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8323676).length < 2 ^ (prefixWord ++ tailWord_8323676).sum := by decide
  have hdescent : baseEnd_8323676 < baseStart_8323676 := by decide
  rcases family_descends (prefixWord ++ tailWord_8323676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8323763 : List Nat := [1, 1, 1, 2, 3, 4, 2, 4, 1, 1, 3]
def baseStart_8323763 : Nat := 118140960795 + 8323763 * 2 ^ 59
def prefixEnd_8323763 : Nat := 4983230072969 + 3 ^ 40 * 8323763 * 2
def baseEnd_8323763 : Nat := 4274091273110421972682217

theorem tailTrace_8323763 : CollatzResearch.WordTrace tailWord_8323763 prefixEnd_8323763 4274091273110421972682217 := by
  unfold tailWord_8323763
  simp only [CollatzResearch.WordTrace]
  refine ⟨303592577743435711387303943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202395051828957140924869295 303592577743435711387303943)
  ·
    refine ⟨455388866615153567080955915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303592577743435711387303943 455388866615153567080955915)
    ·
      refine ⟨683083299922730350621433873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 455388866615153567080955915 683083299922730350621433873)
      ·
        refine ⟨512312474942047762966075405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 683083299922730350621433873 512312474942047762966075405)
        ·
          refine ⟨192117178103267911112278277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 512312474942047762966075405 192117178103267911112278277)
          ·
            refine ⟨36021970894362733333552177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 192117178103267911112278277 36021970894362733333552177)
            ·
              refine ⟨27016478170772050000164133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36021970894362733333552177 27016478170772050000164133)
              ·
                refine ⟨5065589657019759375030775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27016478170772050000164133 5065589657019759375030775)
                ·
                  refine ⟨7598384485529639062546163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5065589657019759375030775 7598384485529639062546163)
                  ·
                    refine ⟨11397576728294458593819245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7598384485529639062546163 11397576728294458593819245)
                    ·
                      refine ⟨4274091273110421972682217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11397576728294458593819245 4274091273110421972682217)
                      ·
                        rfl

theorem cell23_8323763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 4, 1, 1, 3].length) (baseStart_8323763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8323763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8323763 prefixEnd_8323763 := by exact prefixLift 8323763
  have htrace : WordTrace (prefixWord ++ tailWord_8323763) baseStart_8323763 baseEnd_8323763 := by
    simpa [prefixWord, tailWord_8323763, baseEnd_8323763] using wordTrace_append hprefix tailTrace_8323763
  have hstable : (prefixWord ++ tailWord_8323763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8323763).length < 2 ^ (prefixWord ++ tailWord_8323763).sum := by decide
  have hdescent : baseEnd_8323763 < baseStart_8323763 := by decide
  rcases family_descends (prefixWord ++ tailWord_8323763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8323786 : List Nat := [3, 1, 2, 1, 4, 1, 1, 4, 1, 1, 4]
def baseStart_8323786 : Nat := 118140960795 + 8323786 * 2 ^ 59
def prefixEnd_8323786 : Nat := 4983230072969 + 3 ^ 40 * 8323786 * 2
def baseEnd_8323786 : Nat := 4274103083165475382694611

theorem tailTrace_8323786 : CollatzResearch.WordTrace tailWord_8323786 prefixEnd_8323786 4274103083165475382694611 := by
  unfold tailWord_8323786
  simp only [CollatzResearch.WordTrace]
  refine ⟨75898354155588096578847803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202395611081568257543594141 75898354155588096578847803)
  ·
    refine ⟨113847531233382144868271705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75898354155588096578847803 113847531233382144868271705)
    ·
      refine ⟨85385648425036608651203779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113847531233382144868271705 85385648425036608651203779)
      ·
        refine ⟨128078472637554912976805669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85385648425036608651203779 128078472637554912976805669)
        ·
          refine ⟨24014713619541546183151063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128078472637554912976805669 24014713619541546183151063)
          ·
            refine ⟨36022070429312319274726595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24014713619541546183151063 36022070429312319274726595)
            ·
              refine ⟨54033105643968478912089893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36022070429312319274726595 54033105643968478912089893)
              ·
                refine ⟨10131207308244089796016855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54033105643968478912089893 10131207308244089796016855)
                ·
                  refine ⟨15196810962366134694025283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10131207308244089796016855 15196810962366134694025283)
                  ·
                    refine ⟨22795216443549202041037925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15196810962366134694025283 22795216443549202041037925)
                    ·
                      refine ⟨4274103083165475382694611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22795216443549202041037925 4274103083165475382694611)
                      ·
                        rfl

theorem cell23_8323786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 4, 1, 1, 4].length) (baseStart_8323786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8323786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8323786 prefixEnd_8323786 := by exact prefixLift 8323786
  have htrace : WordTrace (prefixWord ++ tailWord_8323786) baseStart_8323786 baseEnd_8323786 := by
    simpa [prefixWord, tailWord_8323786, baseEnd_8323786] using wordTrace_append hprefix tailTrace_8323786
  have hstable : (prefixWord ++ tailWord_8323786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8323786).length < 2 ^ (prefixWord ++ tailWord_8323786).sum := by decide
  have hdescent : baseEnd_8323786 < baseStart_8323786 := by decide
  rcases family_descends (prefixWord ++ tailWord_8323786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8323809 : List Nat := [1, 2, 3, 1, 4, 3, 9]
def baseStart_8323809 : Nat := 118140960795 + 8323809 * 2 ^ 59
def prefixEnd_8323809 : Nat := 4983230072969 + 3 ^ 40 * 8323809 * 2
def baseEnd_8323809 : Nat := 52766850533586775218605

theorem tailTrace_8323809 : CollatzResearch.WordTrace tailWord_8323809 prefixEnd_8323809 52766850533586775218605 := by
  unfold tailWord_8323809
  simp only [CollatzResearch.WordTrace]
  refine ⟨303594255501269061243478481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202396170334179374162318987 303594255501269061243478481)
  ·
    refine ⟨227695691625951795932608861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303594255501269061243478481 227695691625951795932608861)
    ·
      refine ⟨85385884359731923474728323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227695691625951795932608861 85385884359731923474728323)
      ·
        refine ⟨128078826539597885212092485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85385884359731923474728323 128078826539597885212092485)
        ·
          refine ⟨24014779976174603477267341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128078826539597885212092485 24014779976174603477267341)
          ·
            refine ⟨9005542491065476303975253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24014779976174603477267341 9005542491065476303975253)
            ·
              refine ⟨52766850533586775218605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 9005542491065476303975253 52766850533586775218605)
              ·
                rfl

theorem cell23_8323809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 9].length) (baseStart_8323809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8323809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8323809 prefixEnd_8323809 := by exact prefixLift 8323809
  have htrace : WordTrace (prefixWord ++ tailWord_8323809) baseStart_8323809 baseEnd_8323809 := by
    simpa [prefixWord, tailWord_8323809, baseEnd_8323809] using wordTrace_append hprefix tailTrace_8323809
  have hstable : (prefixWord ++ tailWord_8323809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8323809).length < 2 ^ (prefixWord ++ tailWord_8323809).sum := by decide
  have hdescent : baseEnd_8323809 < baseStart_8323809 := by decide
  rcases family_descends (prefixWord ++ tailWord_8323809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8323886 : List Nat := [4, 1, 3, 2, 1, 1, 1, 1, 1, 8]
def baseStart_8323886 : Nat := 118140960795 + 8323886 * 2 ^ 59
def prefixEnd_8323886 : Nat := 4983230072969 + 3 ^ 40 * 8323886 * 2
def baseEnd_8323886 : Nat := 1424718143743641663814717

theorem tailTrace_8323886 : CollatzResearch.WordTrace tailWord_8323886 prefixEnd_8323886 1424718143743641663814717 := by
  unfold tailWord_8323886
  simp only [CollatzResearch.WordTrace]
  refine ⟨37949632990248762924253939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202398042614660068929354341 37949632990248762924253939)
  ·
    refine ⟨56924449485373144386380909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37949632990248762924253939 56924449485373144386380909)
    ·
      refine ⟨21346668557014929144892841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56924449485373144386380909 21346668557014929144892841)
      ·
        refine ⟨16010001417761196858669631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21346668557014929144892841 16010001417761196858669631)
        ·
          refine ⟨24015002126641795288004447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16010001417761196858669631 24015002126641795288004447)
          ·
            refine ⟨36022503189962692932006671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24015002126641795288004447 36022503189962692932006671)
            ·
              refine ⟨54033754784944039398010007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36022503189962692932006671 54033754784944039398010007)
              ·
                refine ⟨81050632177416059097015011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54033754784944039398010007 81050632177416059097015011)
                ·
                  refine ⟨121575948266124088645522517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81050632177416059097015011 121575948266124088645522517)
                  ·
                    refine ⟨1424718143743641663814717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 121575948266124088645522517 1424718143743641663814717)
                    ·
                      rfl

theorem cell23_8323886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 1, 1, 8].length) (baseStart_8323886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8323886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8323886 prefixEnd_8323886 := by exact prefixLift 8323886
  have htrace : WordTrace (prefixWord ++ tailWord_8323886) baseStart_8323886 baseEnd_8323886 := by
    simpa [prefixWord, tailWord_8323886, baseEnd_8323886] using wordTrace_append hprefix tailTrace_8323886
  have hstable : (prefixWord ++ tailWord_8323886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8323886).length < 2 ^ (prefixWord ++ tailWord_8323886).sum := by decide
  have hdescent : baseEnd_8323886 < baseStart_8323886 := by decide
  rcases family_descends (prefixWord ++ tailWord_8323886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8323893 : List Nat := [1, 3, 3, 1, 3, 1, 1, 3, 1, 4, 2]
def baseStart_8323893 : Nat := 118140960795 + 8323893 * 2 ^ 59
def prefixEnd_8323893 : Nat := 4983230072969 + 3 ^ 40 * 8323893 * 2
def baseEnd_8323893 : Nat := 4274158025595506464056619

theorem tailTrace_8323893 : CollatzResearch.WordTrace tailWord_8323893 prefixEnd_8323893 4274158025595506464056619 := by
  unfold tailWord_8323893
  simp only [CollatzResearch.WordTrace]
  refine ⟨303597319232964743589536333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202398212821976495726357555 303597319232964743589536333)
  ·
    refine ⟨113848994712361778846076125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 303597319232964743589536333 113848994712361778846076125)
    ·
      refine ⟨42693373017135667067278547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113848994712361778846076125 42693373017135667067278547)
      ·
        refine ⟨64040059525703500600917821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42693373017135667067278547 64040059525703500600917821)
        ·
          refine ⟨24015022322138812725344183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64040059525703500600917821 24015022322138812725344183)
          ·
            refine ⟨36022533483208219088016275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24015022322138812725344183 36022533483208219088016275)
            ·
              refine ⟨54033800224812328632024413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36022533483208219088016275 54033800224812328632024413)
              ·
                refine ⟨20262675084304623237009155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54033800224812328632024413 20262675084304623237009155)
                ·
                  refine ⟨30394012626456934855513733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20262675084304623237009155 30394012626456934855513733)
                  ·
                    refine ⟨5698877367460675285408825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30394012626456934855513733 5698877367460675285408825)
                    ·
                      refine ⟨4274158025595506464056619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5698877367460675285408825 4274158025595506464056619)
                      ·
                        rfl

theorem cell23_8323893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 3, 1, 4, 2].length) (baseStart_8323893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8323893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8323893 prefixEnd_8323893 := by exact prefixLift 8323893
  have htrace : WordTrace (prefixWord ++ tailWord_8323893) baseStart_8323893 baseEnd_8323893 := by
    simpa [prefixWord, tailWord_8323893, baseEnd_8323893] using wordTrace_append hprefix tailTrace_8323893
  have hstable : (prefixWord ++ tailWord_8323893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8323893).length < 2 ^ (prefixWord ++ tailWord_8323893).sum := by decide
  have hdescent : baseEnd_8323893 < baseStart_8323893 := by decide
  rcases family_descends (prefixWord ++ tailWord_8323893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8323927 : List Nat := [1, 1, 3, 2, 4, 3, 1, 2, 2, 2, 2]
def baseStart_8323927 : Nat := 118140960795 + 8323927 * 2 ^ 59
def prefixEnd_8323927 : Nat := 4983230072969 + 3 ^ 40 * 8323927 * 2
def baseEnd_8323927 : Nat := 4274175483937759331031463

theorem tailTrace_8323927 : CollatzResearch.WordTrace tailWord_8323927 prefixEnd_8323927 4274175483937759331031463 := by
  unfold tailWord_8323927
  simp only [CollatzResearch.WordTrace]
  refine ⟨303598559314841567396274035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202399039543227711597516023 303598559314841567396274035)
  ·
    refine ⟨455397838972262351094411053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303598559314841567396274035 455397838972262351094411053)
    ·
      refine ⟨170774189614598381660404145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 455397838972262351094411053 170774189614598381660404145)
      ·
        refine ⟨128080642210948786245303109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170774189614598381660404145 128080642210948786245303109)
        ·
          refine ⟨24015120414552897420994333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128080642210948786245303109 24015120414552897420994333)
          ·
            refine ⟨9005670155457336532872875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24015120414552897420994333 9005670155457336532872875)
            ·
              refine ⟨13508505233186004799309313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9005670155457336532872875 13508505233186004799309313)
              ·
                refine ⟨10131378924889503599481985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13508505233186004799309313 10131378924889503599481985)
                ·
                  refine ⟨7598534193667127699611489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10131378924889503599481985 7598534193667127699611489)
                  ·
                    refine ⟨5698900645250345774708617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7598534193667127699611489 5698900645250345774708617)
                    ·
                      refine ⟨4274175483937759331031463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5698900645250345774708617 4274175483937759331031463)
                      ·
                        rfl

theorem cell23_8323927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 1, 2, 2, 2, 2].length) (baseStart_8323927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8323927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8323927 prefixEnd_8323927 := by exact prefixLift 8323927
  have htrace : WordTrace (prefixWord ++ tailWord_8323927) baseStart_8323927 baseEnd_8323927 := by
    simpa [prefixWord, tailWord_8323927, baseEnd_8323927] using wordTrace_append hprefix tailTrace_8323927
  have hstable : (prefixWord ++ tailWord_8323927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8323927).length < 2 ^ (prefixWord ++ tailWord_8323927).sum := by decide
  have hdescent : baseEnd_8323927 < baseStart_8323927 := by decide
  rcases family_descends (prefixWord ++ tailWord_8323927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8323979 : List Nat := [1, 1, 1, 1, 4, 2, 2, 1, 1, 3, 6]
def baseStart_8323979 : Nat := 118140960795 + 8323979 * 2 ^ 59
def prefixEnd_8323979 : Nat := 4983230072969 + 3 ^ 40 * 8323979 * 2
def baseEnd_8323979 : Nat := 4274202184931793127581223

theorem tailTrace_8323979 : CollatzResearch.WordTrace tailWord_8323979 prefixEnd_8323979 4274202184931793127581223 := by
  unfold tailWord_8323979
  simp only [CollatzResearch.WordTrace]
  refine ⟨303600455910653180277166991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202400303940435453518111327 303600455910653180277166991)
  ·
    refine ⟨455400683865979770415750487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303600455910653180277166991 455400683865979770415750487)
    ·
      refine ⟨683101025798969655623625731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 455400683865979770415750487 683101025798969655623625731)
      ·
        refine ⟨1024651538698454483435438597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 683101025798969655623625731 1024651538698454483435438597)
        ·
          refine ⟨192122163505960215644144737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1024651538698454483435438597 192122163505960215644144737)
          ·
            refine ⟨144091622629470161733108553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192122163505960215644144737 144091622629470161733108553)
            ·
              refine ⟨108068716972102621299831415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144091622629470161733108553 108068716972102621299831415)
              ·
                refine ⟨162103075458153931949747123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108068716972102621299831415 162103075458153931949747123)
                ·
                  refine ⟨243154613187230897924620685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 162103075458153931949747123 243154613187230897924620685)
                  ·
                    refine ⟨91182979945211586721732757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 243154613187230897924620685 91182979945211586721732757)
                    ·
                      refine ⟨4274202184931793127581223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91182979945211586721732757 4274202184931793127581223)
                      ·
                        rfl

theorem cell23_8323979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 3, 6].length) (baseStart_8323979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8323979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8323979 prefixEnd_8323979 := by exact prefixLift 8323979
  have htrace : WordTrace (prefixWord ++ tailWord_8323979) baseStart_8323979 baseEnd_8323979 := by
    simpa [prefixWord, tailWord_8323979, baseEnd_8323979] using wordTrace_append hprefix tailTrace_8323979
  have hstable : (prefixWord ++ tailWord_8323979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8323979).length < 2 ^ (prefixWord ++ tailWord_8323979).sum := by decide
  have hdescent : baseEnd_8323979 < baseStart_8323979 := by decide
  rcases family_descends (prefixWord ++ tailWord_8323979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8323990 : List Nat := [5, 3, 1, 1, 1, 1, 1, 1, 1, 1, 7]
def baseStart_8323990 : Nat := 118140960795 + 8323990 * 2 ^ 59
def prefixEnd_8323990 : Nat := 4983230072969 + 3 ^ 40 * 8323990 * 2
def baseEnd_8323990 : Nat := 4274207833218992584543673

theorem tailTrace_8323990 : CollatzResearch.WordTrace tailWord_8323990 prefixEnd_8323990 4274207833218992584543673 := by
  unfold tailWord_8323990
  simp only [CollatzResearch.WordTrace]
  refine ⟨18975053569600833072238589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 202400571409075552770544949 18975053569600833072238589)
  ·
    refine ⟨7115645088600312402089471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18975053569600833072238589 7115645088600312402089471)
    ·
      refine ⟨10673467632900468603134207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7115645088600312402089471 10673467632900468603134207)
      ·
        refine ⟨16010201449350702904701311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10673467632900468603134207 16010201449350702904701311)
        ·
          refine ⟨24015302174026054357051967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16010201449350702904701311 24015302174026054357051967)
          ·
            refine ⟨36022953261039081535577951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24015302174026054357051967 36022953261039081535577951)
            ·
              refine ⟨54034429891558622303366927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36022953261039081535577951 54034429891558622303366927)
              ·
                refine ⟨81051644837337933455050391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54034429891558622303366927 81051644837337933455050391)
                ·
                  refine ⟨121577467256006900182575587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81051644837337933455050391 121577467256006900182575587)
                  ·
                    refine ⟨182366200884010350273863381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 121577467256006900182575587 182366200884010350273863381)
                    ·
                      refine ⟨4274207833218992584543673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 182366200884010350273863381 4274207833218992584543673)
                      ·
                        rfl

theorem cell23_8323990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_8323990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8323990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8323990 prefixEnd_8323990 := by exact prefixLift 8323990
  have htrace : WordTrace (prefixWord ++ tailWord_8323990) baseStart_8323990 baseEnd_8323990 := by
    simpa [prefixWord, tailWord_8323990, baseEnd_8323990] using wordTrace_append hprefix tailTrace_8323990
  have hstable : (prefixWord ++ tailWord_8323990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8323990).length < 2 ^ (prefixWord ++ tailWord_8323990).sum := by decide
  have hdescent : baseEnd_8323990 < baseStart_8323990 := by decide
  rcases family_descends (prefixWord ++ tailWord_8323990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8324107 : List Nat := [1, 1, 1, 1, 6, 3, 2, 1, 3, 2, 2]
def baseStart_8324107 : Nat := 118140960795 + 8324107 * 2 ^ 59
def prefixEnd_8324107 : Nat := 4983230072969 + 3 ^ 40 * 8324107 * 2
def baseEnd_8324107 : Nat := 4274267910455568626780635

theorem tailTrace_8324107 : CollatzResearch.WordTrace tailWord_8324107 prefixEnd_8324107 4274267910455568626780635 := by
  unfold tailWord_8324107
  simp only [CollatzResearch.WordTrace]
  refine ⟨303605124454189458137826575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202403416302792972091884383 303605124454189458137826575)
  ·
    refine ⟨455407686681284187206739863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303605124454189458137826575 455407686681284187206739863)
    ·
      refine ⟨683111530021926280810109795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 455407686681284187206739863 683111530021926280810109795)
      ·
        refine ⟨1024667295032889421215164693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 683111530021926280810109795 1024667295032889421215164693)
        ·
          refine ⟨48031279454666691619460845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 1024667295032889421215164693 48031279454666691619460845)
          ·
            refine ⟨18011729795500009357297817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48031279454666691619460845 18011729795500009357297817)
            ·
              refine ⟨13508797346625007017973363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18011729795500009357297817 13508797346625007017973363)
              ·
                refine ⟨20263196019937510526960045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13508797346625007017973363 20263196019937510526960045)
                ·
                  refine ⟨7598698507476566447610017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20263196019937510526960045 7598698507476566447610017)
                  ·
                    refine ⟨5699023880607424835707513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7598698507476566447610017 5699023880607424835707513)
                    ·
                      refine ⟨4274267910455568626780635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5699023880607424835707513 4274267910455568626780635)
                      ·
                        rfl

theorem cell23_8324107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 2, 1, 3, 2, 2].length) (baseStart_8324107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8324107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8324107 prefixEnd_8324107 := by exact prefixLift 8324107
  have htrace : WordTrace (prefixWord ++ tailWord_8324107) baseStart_8324107 baseEnd_8324107 := by
    simpa [prefixWord, tailWord_8324107, baseEnd_8324107] using wordTrace_append hprefix tailTrace_8324107
  have hstable : (prefixWord ++ tailWord_8324107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8324107).length < 2 ^ (prefixWord ++ tailWord_8324107).sum := by decide
  have hdescent : baseEnd_8324107 < baseStart_8324107 := by decide
  rcases family_descends (prefixWord ++ tailWord_8324107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8324117 : List Nat := [1, 3, 2, 1, 4, 2, 3, 1, 2, 4]
def baseStart_8324117 : Nat := 118140960795 + 8324117 * 2 ^ 59
def prefixEnd_8324117 : Nat := 4983230072969 + 3 ^ 40 * 8324117 * 2
def baseEnd_8324117 : Nat := 1424757681754037862551863

theorem tailTrace_8324117 : CollatzResearch.WordTrace tailWord_8324117 prefixEnd_8324117 1424757681754037862551863 := by
  unfold tailWord_8324117
  simp only [CollatzResearch.WordTrace]
  refine ⟨303605489184153229845690605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202403659456102153230460403 303605489184153229845690605)
  ·
    refine ⟨113852058444057461192133977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 303605489184153229845690605 113852058444057461192133977)
    ·
      refine ⟨85389043833043095894100483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113852058444057461192133977 85389043833043095894100483)
      ·
        refine ⟨128083565749564643841150725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85389043833043095894100483 128083565749564643841150725)
        ·
          refine ⟨24015668578043370720215761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128083565749564643841150725 24015668578043370720215761)
          ·
            refine ⟨18011751433532528040161821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24015668578043370720215761 18011751433532528040161821)
            ·
              refine ⟨6754406787574698015060683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18011751433532528040161821 6754406787574698015060683)
              ·
                refine ⟨10131610181362047022591025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6754406787574698015060683 10131610181362047022591025)
                ·
                  refine ⟨7598707636021535266943269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10131610181362047022591025 7598707636021535266943269)
                  ·
                    refine ⟨1424757681754037862551863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7598707636021535266943269 1424757681754037862551863)
                    ·
                      rfl

theorem cell23_8324117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 3, 1, 2, 4].length) (baseStart_8324117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8324117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8324117 prefixEnd_8324117 := by exact prefixLift 8324117
  have htrace : WordTrace (prefixWord ++ tailWord_8324117) baseStart_8324117 baseEnd_8324117 := by
    simpa [prefixWord, tailWord_8324117, baseEnd_8324117] using wordTrace_append hprefix tailTrace_8324117
  have hstable : (prefixWord ++ tailWord_8324117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8324117).length < 2 ^ (prefixWord ++ tailWord_8324117).sum := by decide
  have hdescent : baseEnd_8324117 < baseStart_8324117 := by decide
  rcases family_descends (prefixWord ++ tailWord_8324117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8324120 : List Nat := [2, 1, 2, 3, 2, 4, 1, 1, 1, 2, 4]
def baseStart_8324120 : Nat := 118140960795 + 8324120 * 2 ^ 59
def prefixEnd_8324120 : Nat := 4983230072969 + 3 ^ 40 * 8324120 * 2
def baseEnd_8324120 : Nat := 4274274585704077075918075

theorem tailTrace_8324120 : CollatzResearch.WordTrace tailWord_8324120 prefixEnd_8324120 4274274585704077075918075 := by
  unfold tailWord_8324120
  simp only [CollatzResearch.WordTrace]
  refine ⟨151802799301571180679024907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202403732402094907572033209 151802799301571180679024907)
  ·
    refine ⟨227704198952356771018537361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151802799301571180679024907 227704198952356771018537361)
    ·
      refine ⟨170778149214267578263903021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227704198952356771018537361 170778149214267578263903021)
      ·
        refine ⟨64041805955350341848963633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170778149214267578263903021 64041805955350341848963633)
        ·
          refine ⟨48031354466512756386722725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64041805955350341848963633 48031354466512756386722725)
          ·
            refine ⟨9005878962471141822510511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48031354466512756386722725 9005878962471141822510511)
            ·
              refine ⟨13508818443706712733765767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9005878962471141822510511 13508818443706712733765767)
              ·
                refine ⟨20263227665560069100648651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13508818443706712733765767 20263227665560069100648651)
                ·
                  refine ⟨30394841498340103650972977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20263227665560069100648651 30394841498340103650972977)
                  ·
                    refine ⟨22796131123755077738229733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30394841498340103650972977 22796131123755077738229733)
                    ·
                      refine ⟨4274274585704077075918075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22796131123755077738229733 4274274585704077075918075)
                      ·
                        rfl

theorem cell23_8324120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 1, 1, 1, 2, 4].length) (baseStart_8324120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8324120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8324120 prefixEnd_8324120 := by exact prefixLift 8324120
  have htrace : WordTrace (prefixWord ++ tailWord_8324120) baseStart_8324120 baseEnd_8324120 := by
    simpa [prefixWord, tailWord_8324120, baseEnd_8324120] using wordTrace_append hprefix tailTrace_8324120
  have hstable : (prefixWord ++ tailWord_8324120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8324120).length < 2 ^ (prefixWord ++ tailWord_8324120).sum := by decide
  have hdescent : baseEnd_8324120 < baseStart_8324120 := by decide
  rcases family_descends (prefixWord ++ tailWord_8324120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8324130 : List Nat := [3, 3, 1, 1, 1, 5, 2, 7]
def baseStart_8324130 : Nat := 118140960795 + 8324130 * 2 ^ 59
def prefixEnd_8324130 : Nat := 4983230072969 + 3 ^ 40 * 8324130 * 2
def baseEnd_8324130 : Nat := 158306656315208223584927

theorem tailTrace_8324130 : CollatzResearch.WordTrace tailWord_8324130 prefixEnd_8324130 158306656315208223584927 := by
  unfold tailWord_8324130
  simp only [CollatzResearch.WordTrace]
  refine ⟨75901490833276533266478461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202403975555404088710609229 75901490833276533266478461)
  ·
    refine ⟨28463059062478699974929423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75901490833276533266478461 28463059062478699974929423)
    ·
      refine ⟨42694588593718049962394135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28463059062478699974929423 42694588593718049962394135)
      ·
        refine ⟨64041882890577074943591203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42694588593718049962394135 64041882890577074943591203)
        ·
          refine ⟨96062824335865612415386805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64041882890577074943591203 96062824335865612415386805)
          ·
            refine ⟨9005889781487401163942513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 96062824335865612415386805 9005889781487401163942513)
            ·
              refine ⟨6754417336115550872956885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9005889781487401163942513 6754417336115550872956885)
              ·
                refine ⟨158306656315208223584927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6754417336115550872956885 158306656315208223584927)
                ·
                  rfl

theorem cell23_8324130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 2, 7].length) (baseStart_8324130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8324130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8324130 prefixEnd_8324130 := by exact prefixLift 8324130
  have htrace : WordTrace (prefixWord ++ tailWord_8324130) baseStart_8324130 baseEnd_8324130 := by
    simpa [prefixWord, tailWord_8324130, baseEnd_8324130] using wordTrace_append hprefix tailTrace_8324130
  have hstable : (prefixWord ++ tailWord_8324130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8324130).length < 2 ^ (prefixWord ++ tailWord_8324130).sum := by decide
  have hdescent : baseEnd_8324130 < baseStart_8324130 := by decide
  rcases family_descends (prefixWord ++ tailWord_8324130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8324158 : List Nat := [4, 2, 1, 3, 1, 2, 3, 2, 1, 2, 2]
def baseStart_8324158 : Nat := 118140960795 + 8324158 * 2 ^ 59
def prefixEnd_8324158 : Nat := 4983230072969 + 3 ^ 40 * 8324158 * 2
def baseEnd_8324158 : Nat := 4274294097968947927242901

theorem tailTrace_8324158 : CollatzResearch.WordTrace tailWord_8324158 prefixEnd_8324158 4274294097968947927242901 := by
  unfold tailWord_8324158
  simp only [CollatzResearch.WordTrace]
  refine ⟨37950873072125586730991641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202404656384669795898622085 37950873072125586730991641)
  ·
    refine ⟨28463154804094190048243731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37950873072125586730991641 28463154804094190048243731)
    ·
      refine ⟨42694732206141285072365597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28463154804094190048243731 42694732206141285072365597)
      ·
        refine ⟨16010524577302981902137099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42694732206141285072365597 16010524577302981902137099)
        ·
          refine ⟨24015786865954472853205649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16010524577302981902137099 24015786865954472853205649)
          ·
            refine ⟨18011840149465854639904237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24015786865954472853205649 18011840149465854639904237)
            ·
              refine ⟨6754440056049695489964089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18011840149465854639904237 6754440056049695489964089)
              ·
                refine ⟨5065830042037271617473067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6754440056049695489964089 5065830042037271617473067)
                ·
                  refine ⟨7598745063055907426209601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5065830042037271617473067 7598745063055907426209601)
                  ·
                    refine ⟨5699058797291930569657201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7598745063055907426209601 5699058797291930569657201)
                    ·
                      refine ⟨4274294097968947927242901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5699058797291930569657201 4274294097968947927242901)
                      ·
                        rfl

theorem cell23_8324158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 3, 2, 1, 2, 2].length) (baseStart_8324158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8324158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8324158 prefixEnd_8324158 := by exact prefixLift 8324158
  have htrace : WordTrace (prefixWord ++ tailWord_8324158) baseStart_8324158 baseEnd_8324158 := by
    simpa [prefixWord, tailWord_8324158, baseEnd_8324158] using wordTrace_append hprefix tailTrace_8324158
  have hstable : (prefixWord ++ tailWord_8324158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8324158).length < 2 ^ (prefixWord ++ tailWord_8324158).sum := by decide
  have hdescent : baseEnd_8324158 < baseStart_8324158 := by decide
  rcases family_descends (prefixWord ++ tailWord_8324158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8324176 : List Nat := [2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 6]
def baseStart_8324176 : Nat := 118140960795 + 8324176 * 2 ^ 59
def prefixEnd_8324176 : Nat := 4983230072969 + 3 ^ 40 * 8324176 * 2
def baseEnd_8324176 : Nat := 4274303340620728856817817

theorem tailTrace_8324176 : CollatzResearch.WordTrace tailWord_8324176 prefixEnd_8324176 4274303340620728856817817 := by
  unfold tailWord_8324176
  simp only [CollatzResearch.WordTrace]
  refine ⟨151803820545469741461044191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202405094060626321948058921 151803820545469741461044191)
  ·
    refine ⟨227705730818204612191566287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151803820545469741461044191 227705730818204612191566287)
    ·
      refine ⟨341558596227306918287349431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227705730818204612191566287 341558596227306918287349431)
      ·
        refine ⟨512337894340960377431024147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341558596227306918287349431 512337894340960377431024147)
        ·
          refine ⟨768506841511440566146536221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 512337894340960377431024147 768506841511440566146536221)
          ·
            refine ⟨288190065566790212304951083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 768506841511440566146536221 288190065566790212304951083)
            ·
              refine ⟨432285098350185318457426625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 288190065566790212304951083 432285098350185318457426625)
              ·
                refine ⟨324213823762638988843069969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 432285098350185318457426625 324213823762638988843069969)
                ·
                  refine ⟨243160367821979241632302477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 324213823762638988843069969 243160367821979241632302477)
                  ·
                    refine ⟨91185137933242215612113429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 243160367821979241632302477 91185137933242215612113429)
                    ·
                      refine ⟨4274303340620728856817817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91185137933242215612113429 4274303340620728856817817)
                      ·
                        rfl

theorem cell23_8324176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 6].length) (baseStart_8324176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8324176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8324176 prefixEnd_8324176 := by exact prefixLift 8324176
  have htrace : WordTrace (prefixWord ++ tailWord_8324176) baseStart_8324176 baseEnd_8324176 := by
    simpa [prefixWord, tailWord_8324176, baseEnd_8324176] using wordTrace_append hprefix tailTrace_8324176
  have hstable : (prefixWord ++ tailWord_8324176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8324176).length < 2 ^ (prefixWord ++ tailWord_8324176).sum := by decide
  have hdescent : baseEnd_8324176 < baseStart_8324176 := by decide
  rcases family_descends (prefixWord ++ tailWord_8324176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8324220 : List Nat := [2, 2, 2, 1, 1, 3, 3, 4, 5]
def baseStart_8324220 : Nat := 118140960795 + 8324220 * 2 ^ 59
def prefixEnd_8324220 : Nat := 4983230072969 + 3 ^ 40 * 8324220 * 2
def baseEnd_8324220 : Nat := 474925103752169631629735

theorem tailTrace_8324220 : CollatzResearch.WordTrace tailWord_8324220 prefixEnd_8324220 474925103752169631629735 := by
  unfold tailWord_8324220
  simp only [CollatzResearch.WordTrace]
  refine ⟨151804622951390039218345057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202406163935186718957793409 151804622951390039218345057)
  ·
    refine ⟨113853467213542529413758793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151804622951390039218345057 113853467213542529413758793)
    ·
      refine ⟨85390100410156897060319095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113853467213542529413758793 85390100410156897060319095)
      ·
        refine ⟨128085150615235345590478643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85390100410156897060319095 128085150615235345590478643)
        ·
          refine ⟨192127725922853018385717965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128085150615235345590478643 192127725922853018385717965)
          ·
            refine ⟨72047897221069881894644237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 192127725922853018385717965 72047897221069881894644237)
            ·
              refine ⟨27017961457901205710491589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72047897221069881894644237 27017961457901205710491589)
              ·
                refine ⟨5065867773356476070717173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27017961457901205710491589 5065867773356476070717173)
                ·
                  refine ⟨474925103752169631629735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5065867773356476070717173 474925103752169631629735)
                  ·
                    rfl

theorem cell23_8324220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 4, 5].length) (baseStart_8324220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8324220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8324220 prefixEnd_8324220 := by exact prefixLift 8324220
  have htrace : WordTrace (prefixWord ++ tailWord_8324220) baseStart_8324220 baseEnd_8324220 := by
    simpa [prefixWord, tailWord_8324220, baseEnd_8324220] using wordTrace_append hprefix tailTrace_8324220
  have hstable : (prefixWord ++ tailWord_8324220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8324220).length < 2 ^ (prefixWord ++ tailWord_8324220).sum := by decide
  have hdescent : baseEnd_8324220 < baseStart_8324220 := by decide
  rcases family_descends (prefixWord ++ tailWord_8324220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8324250 : List Nat := [3, 1, 1, 5, 1, 2, 1, 1, 1, 7]
def baseStart_8324250 : Nat := 118140960795 + 8324250 * 2 ^ 59
def prefixEnd_8324250 : Nat := 4983230072969 + 3 ^ 40 * 8324250 * 2
def baseEnd_8324250 : Nat := 1424780446063053855764159

theorem tailTrace_8324250 : CollatzResearch.WordTrace tailWord_8324250 prefixEnd_8324250 1424780446063053855764159 := by
  unfold tailWord_8324250
  simp only [CollatzResearch.WordTrace]
  refine ⟨75902585023167848390070551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202406893395114262373521469 75902585023167848390070551)
  ·
    refine ⟨113853877534751772585105827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75902585023167848390070551 113853877534751772585105827)
    ·
      refine ⟨170780816302127658877658741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113853877534751772585105827 170780816302127658877658741)
      ·
        refine ⟨16010701528324468019780507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 170780816302127658877658741 16010701528324468019780507)
        ·
          refine ⟨24016052292486702029670761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16010701528324468019780507 24016052292486702029670761)
          ·
            refine ⟨18012039219365026522253071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24016052292486702029670761 18012039219365026522253071)
            ·
              refine ⟨27018058829047539783379607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18012039219365026522253071 27018058829047539783379607)
              ·
                refine ⟨40527088243571309675069411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27018058829047539783379607 40527088243571309675069411)
                ·
                  refine ⟨60790632365356964512604117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40527088243571309675069411 60790632365356964512604117)
                  ·
                    refine ⟨1424780446063053855764159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60790632365356964512604117 1424780446063053855764159)
                    ·
                      rfl

theorem cell23_8324250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 1, 1, 7].length) (baseStart_8324250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8324250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8324250 prefixEnd_8324250 := by exact prefixLift 8324250
  have htrace : WordTrace (prefixWord ++ tailWord_8324250) baseStart_8324250 baseEnd_8324250 := by
    simpa [prefixWord, tailWord_8324250, baseEnd_8324250] using wordTrace_append hprefix tailTrace_8324250
  have hstable : (prefixWord ++ tailWord_8324250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8324250).length < 2 ^ (prefixWord ++ tailWord_8324250).sum := by decide
  have hdescent : baseEnd_8324250 < baseStart_8324250 := by decide
  rcases family_descends (prefixWord ++ tailWord_8324250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8324254 : List Nat := [4, 3, 1, 1, 2, 2, 2, 3, 5]
def baseStart_8324254 : Nat := 118140960795 + 8324254 * 2 ^ 59
def prefixEnd_8324254 : Nat := 4983230072969 + 3 ^ 40 * 8324254 * 2
def baseEnd_8324254 : Nat := 474927043567975505738051

theorem tailTrace_8324254 : CollatzResearch.WordTrace tailWord_8324254 prefixEnd_8324254 474927043567975505738051 := by
  unfold tailWord_8324254
  simp only [CollatzResearch.WordTrace]
  refine ⟨37951310748082112780428477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202406990656437934828951877 37951310748082112780428477)
  ·
    refine ⟨14231741530530792292660679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37951310748082112780428477 14231741530530792292660679)
    ·
      refine ⟨21347612295796188438991019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14231741530530792292660679 21347612295796188438991019)
      ·
        refine ⟨32021418443694282658486529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21347612295796188438991019 32021418443694282658486529)
        ·
          refine ⟨24016063832770711993864897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32021418443694282658486529 24016063832770711993864897)
          ·
            refine ⟨18012047874578033995398673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24016063832770711993864897 18012047874578033995398673)
            ·
              refine ⟨13509035905933525496549005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18012047874578033995398673 13509035905933525496549005)
              ·
                refine ⟨5065888464725072061205877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13509035905933525496549005 5065888464725072061205877)
                ·
                  refine ⟨474927043567975505738051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5065888464725072061205877 474927043567975505738051)
                  ·
                    rfl

theorem cell23_8324254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 2, 3, 5].length) (baseStart_8324254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8324254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8324254 prefixEnd_8324254 := by exact prefixLift 8324254
  have htrace : WordTrace (prefixWord ++ tailWord_8324254) baseStart_8324254 baseEnd_8324254 := by
    simpa [prefixWord, tailWord_8324254, baseEnd_8324254] using wordTrace_append hprefix tailTrace_8324254
  have hstable : (prefixWord ++ tailWord_8324254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8324254).length < 2 ^ (prefixWord ++ tailWord_8324254).sum := by decide
  have hdescent : baseEnd_8324254 < baseStart_8324254 := by decide
  rcases family_descends (prefixWord ++ tailWord_8324254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8324364 : List Nat := [2, 2, 1, 2, 2, 4, 2, 1, 2, 3, 2]
def baseStart_8324364 : Nat := 118140960795 + 8324364 * 2 ^ 59
def prefixEnd_8324364 : Nat := 4983230072969 + 3 ^ 40 * 8324364 * 2
def baseEnd_8324364 : Nat := 4274399874983774121266953

theorem tailTrace_8324364 : CollatzResearch.WordTrace tailWord_8324364 prefixEnd_8324364 4274399874983774121266953 := by
  unfold tailWord_8324364
  simp only [CollatzResearch.WordTrace]
  refine ⟨151807249007129195514966073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202409665342838927353288097 151807249007129195514966073)
  ·
    refine ⟨113855436755346896636224555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151807249007129195514966073 113855436755346896636224555)
    ·
      refine ⟨170783155133020344954336833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113855436755346896636224555 170783155133020344954336833)
      ·
        refine ⟨128087366349765258715752625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170783155133020344954336833 128087366349765258715752625)
        ·
          refine ⟨96065524762323944036814469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128087366349765258715752625 96065524762323944036814469)
          ·
            refine ⟨18012285892935739506902713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96065524762323944036814469 18012285892935739506902713)
            ·
              refine ⟨13509214419701804630177035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18012285892935739506902713 13509214419701804630177035)
              ·
                refine ⟨20263821629552706945265553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13509214419701804630177035 20263821629552706945265553)
                ·
                  refine ⟨15197866222164530208949165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20263821629552706945265553 15197866222164530208949165)
                  ·
                    refine ⟨5699199833311698828355937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15197866222164530208949165 5699199833311698828355937)
                    ·
                      refine ⟨4274399874983774121266953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5699199833311698828355937 4274399874983774121266953)
                      ·
                        rfl

theorem cell23_8324364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 2, 1, 2, 3, 2].length) (baseStart_8324364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8324364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8324364 prefixEnd_8324364 := by exact prefixLift 8324364
  have htrace : WordTrace (prefixWord ++ tailWord_8324364) baseStart_8324364 baseEnd_8324364 := by
    simpa [prefixWord, tailWord_8324364, baseEnd_8324364] using wordTrace_append hprefix tailTrace_8324364
  have hstable : (prefixWord ++ tailWord_8324364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8324364).length < 2 ^ (prefixWord ++ tailWord_8324364).sum := by decide
  have hdescent : baseEnd_8324364 < baseStart_8324364 := by decide
  rcases family_descends (prefixWord ++ tailWord_8324364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8324382 : List Nat := [4, 3, 2, 1, 3, 1, 2, 2, 1, 4]
def baseStart_8324382 : Nat := 118140960795 + 8324382 * 2 ^ 59
def prefixEnd_8324382 : Nat := 4983230072969 + 3 ^ 40 * 8324382 * 2
def baseEnd_8324382 : Nat := 1424803039211851683613957

theorem tailTrace_8324382 : CollatzResearch.WordTrace tailWord_8324382 prefixEnd_8324382 1424803039211851683613957 := by
  unfold tailWord_8324382
  simp only [CollatzResearch.WordTrace]
  refine ⟨37951894316024147513010925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202410103018795453402724933 37951894316024147513010925)
  ·
    refine ⟨14231960368509055317379097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37951894316024147513010925 14231960368509055317379097)
    ·
      refine ⟨10673970276381791488034323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14231960368509055317379097 10673970276381791488034323)
      ·
        refine ⟨16010955414572687232051485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10673970276381791488034323 16010955414572687232051485)
        ·
          refine ⟨6004108280464757712019307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16010955414572687232051485 6004108280464757712019307)
          ·
            refine ⟨9006162420697136568028961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6004108280464757712019307 9006162420697136568028961)
            ·
              refine ⟨6754621815522852426021721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9006162420697136568028961 6754621815522852426021721)
              ·
                refine ⟨5065966361642139319516291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6754621815522852426021721 5065966361642139319516291)
                ·
                  refine ⟨7598949542463208979274437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5065966361642139319516291 7598949542463208979274437)
                  ·
                    refine ⟨1424803039211851683613957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7598949542463208979274437 1424803039211851683613957)
                    ·
                      rfl

theorem cell23_8324382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_8324382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8324382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8324382 prefixEnd_8324382 := by exact prefixLift 8324382
  have htrace : WordTrace (prefixWord ++ tailWord_8324382) baseStart_8324382 baseEnd_8324382 := by
    simpa [prefixWord, tailWord_8324382, baseEnd_8324382] using wordTrace_append hprefix tailTrace_8324382
  have hstable : (prefixWord ++ tailWord_8324382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8324382).length < 2 ^ (prefixWord ++ tailWord_8324382).sum := by decide
  have hdescent : baseEnd_8324382 < baseStart_8324382 := by decide
  rcases family_descends (prefixWord ++ tailWord_8324382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8324383 : List Nat := [1, 1, 2, 4, 15]
def baseStart_8324383 : Nat := 118140960795 + 8324383 * 2 ^ 59
def prefixEnd_8324383 : Nat := 4983230072969 + 3 ^ 40 * 8324383 * 2
def baseEnd_8324383 : Nat := 5863387697004402670685

theorem tailTrace_8324383 : CollatzResearch.WordTrace tailWord_8324383 prefixEnd_8324383 5863387697004402670685 := by
  unfold tailWord_8324383
  simp only [CollatzResearch.WordTrace]
  refine ⟨303615191001189557274873803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202410127334126371516582535 303615191001189557274873803)
  ·
    refine ⟨455422786501784335912310705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303615191001189557274873803 455422786501784335912310705)
    ·
      refine ⟨341567089876338251934233029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 455422786501784335912310705 341567089876338251934233029)
      ·
        refine ⟨64043829351813422237668693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 341567089876338251934233029 64043829351813422237668693)
        ·
          refine ⟨5863387697004402670685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 15 64043829351813422237668693 5863387697004402670685)
          ·
            rfl

theorem cell23_8324383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 15].length) (baseStart_8324383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8324383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8324383 prefixEnd_8324383 := by exact prefixLift 8324383
  have htrace : WordTrace (prefixWord ++ tailWord_8324383) baseStart_8324383 baseEnd_8324383 := by
    simpa [prefixWord, tailWord_8324383, baseEnd_8324383] using wordTrace_append hprefix tailTrace_8324383
  have hstable : (prefixWord ++ tailWord_8324383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8324383).length < 2 ^ (prefixWord ++ tailWord_8324383).sum := by decide
  have hdescent : baseEnd_8324383 < baseStart_8324383 := by decide
  rcases family_descends (prefixWord ++ tailWord_8324383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8324387 : List Nat := [1, 1, 1, 4, 2, 3, 1, 4, 2, 4]
def baseStart_8324387 : Nat := 118140960795 + 8324387 * 2 ^ 59
def prefixEnd_8324387 : Nat := 4983230072969 + 3 ^ 40 * 8324387 * 2
def baseEnd_8324387 : Nat := 1424803895012942510426449

theorem tailTrace_8324387 : CollatzResearch.WordTrace tailWord_8324387 prefixEnd_8324387 1424803895012942510426449 := by
  unfold tailWord_8324387
  simp only [CollatzResearch.WordTrace]
  refine ⟨303615336893175065958019415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202410224595450043972012943 303615336893175065958019415)
  ·
    refine ⟨455423005339762598937029123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303615336893175065958019415 455423005339762598937029123)
    ·
      refine ⟨683134508009643898405543685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 455423005339762598937029123 683134508009643898405543685)
      ·
        refine ⟨128087720251808230951039441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 683134508009643898405543685 128087720251808230951039441)
        ·
          refine ⟨96065790188856173213279581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128087720251808230951039441 96065790188856173213279581)
          ·
            refine ⟨36024671320821064954979843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96065790188856173213279581 36024671320821064954979843)
            ·
              refine ⟨54037006981231597432469765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36024671320821064954979843 54037006981231597432469765)
              ·
                refine ⟨10131938808980924518588081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54037006981231597432469765 10131938808980924518588081)
                ·
                  refine ⟨7598954106735693388941061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10131938808980924518588081 7598954106735693388941061)
                  ·
                    refine ⟨1424803895012942510426449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7598954106735693388941061 1424803895012942510426449)
                    ·
                      rfl

theorem cell23_8324387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 4, 2, 4].length) (baseStart_8324387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8324387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8324387 prefixEnd_8324387 := by exact prefixLift 8324387
  have htrace : WordTrace (prefixWord ++ tailWord_8324387) baseStart_8324387 baseEnd_8324387 := by
    simpa [prefixWord, tailWord_8324387, baseEnd_8324387] using wordTrace_append hprefix tailTrace_8324387
  have hstable : (prefixWord ++ tailWord_8324387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8324387).length < 2 ^ (prefixWord ++ tailWord_8324387).sum := by decide
  have hdescent : baseEnd_8324387 < baseStart_8324387 := by decide
  rcases family_descends (prefixWord ++ tailWord_8324387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8324404 : List Nat := [2, 5, 1, 1, 1, 1, 1, 5, 2, 4]
def baseStart_8324404 : Nat := 118140960795 + 8324404 * 2 ^ 59
def prefixEnd_8324404 : Nat := 4983230072969 + 3 ^ 40 * 8324404 * 2
def baseEnd_8324404 : Nat := 1424806804736651321588923

theorem tailTrace_8324404 : CollatzResearch.WordTrace tailWord_8324404 prefixEnd_8324404 1424806804736651321588923 := by
  unfold tailWord_8324404
  simp only [CollatzResearch.WordTrace]
  refine ⟨151807978467056738930694133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202410637956075651907592177 151807978467056738930694133)
  ·
    refine ⟨14231997981286569274752575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 151807978467056738930694133 14231997981286569274752575)
    ·
      refine ⟨21347996971929853912128863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14231997981286569274752575 21347996971929853912128863)
      ·
        refine ⟨32021995457894780868193295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21347996971929853912128863 32021995457894780868193295)
        ·
          refine ⟨48032993186842171302289943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32021995457894780868193295 48032993186842171302289943)
          ·
            refine ⟨72049489780263256953434915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48032993186842171302289943 72049489780263256953434915)
            ·
              refine ⟨108074234670394885430152373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72049489780263256953434915 108074234670394885430152373)
              ·
                refine ⟨10131959500349520509076785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 108074234670394885430152373 10131959500349520509076785)
                ·
                  refine ⟨7598969625262140381807589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10131959500349520509076785 7598969625262140381807589)
                  ·
                    refine ⟨1424806804736651321588923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7598969625262140381807589 1424806804736651321588923)
                    ·
                      rfl

theorem cell23_8324404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 5, 2, 4].length) (baseStart_8324404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8324404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8324404 prefixEnd_8324404 := by exact prefixLift 8324404
  have htrace : WordTrace (prefixWord ++ tailWord_8324404) baseStart_8324404 baseEnd_8324404 := by
    simpa [prefixWord, tailWord_8324404, baseEnd_8324404] using wordTrace_append hprefix tailTrace_8324404
  have hstable : (prefixWord ++ tailWord_8324404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8324404).length < 2 ^ (prefixWord ++ tailWord_8324404).sum := by decide
  have hdescent : baseEnd_8324404 < baseStart_8324404 := by decide
  rcases family_descends (prefixWord ++ tailWord_8324404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8324414 : List Nat := [4, 2, 1, 2, 1, 1, 2, 4, 1, 2, 3]
def baseStart_8324414 : Nat := 118140960795 + 8324414 * 2 ^ 59
def prefixEnd_8324414 : Nat := 4983230072969 + 3 ^ 40 * 8324414 * 2
def baseEnd_8324414 : Nat := 4274425549016498925641723

theorem tailTrace_8324414 : CollatzResearch.WordTrace tailWord_8324414 prefixEnd_8324414 4274425549016498925641723 := by
  unfold tailWord_8324414
  simp only [CollatzResearch.WordTrace]
  refine ⟨37952040208009656196156537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202410881109384833046168197 37952040208009656196156537)
  ·
    refine ⟨28464030156007242147117403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37952040208009656196156537 28464030156007242147117403)
    ·
      refine ⟨42696045234010863220676105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28464030156007242147117403 42696045234010863220676105)
      ·
        refine ⟨32022033925508147415507079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42696045234010863220676105 32022033925508147415507079)
        ·
          refine ⟨48033050888262221123260619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32022033925508147415507079 48033050888262221123260619)
          ·
            refine ⟨72049576332393331684890929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48033050888262221123260619 72049576332393331684890929)
            ·
              refine ⟨54037182249294998763668197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72049576332393331684890929 54037182249294998763668197)
              ·
                refine ⟨10131971671742812268187787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54037182249294998763668197 10131971671742812268187787)
                ·
                  refine ⟨15197957507614218402281681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10131971671742812268187787 15197957507614218402281681)
                  ·
                    refine ⟨11398468130710663801711261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15197957507614218402281681 11398468130710663801711261)
                    ·
                      refine ⟨4274425549016498925641723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11398468130710663801711261 4274425549016498925641723)
                      ·
                        rfl

theorem cell23_8324414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 4, 1, 2, 3].length) (baseStart_8324414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8324414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8324414 prefixEnd_8324414 := by exact prefixLift 8324414
  have htrace : WordTrace (prefixWord ++ tailWord_8324414) baseStart_8324414 baseEnd_8324414 := by
    simpa [prefixWord, tailWord_8324414, baseEnd_8324414] using wordTrace_append hprefix tailTrace_8324414
  have hstable : (prefixWord ++ tailWord_8324414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8324414).length < 2 ^ (prefixWord ++ tailWord_8324414).sum := by decide
  have hdescent : baseEnd_8324414 < baseStart_8324414 := by decide
  rcases family_descends (prefixWord ++ tailWord_8324414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8324422 : List Nat := [6, 1, 1, 3, 1, 1, 2, 3, 1, 1, 3]
def baseStart_8324422 : Nat := 118140960795 + 8324422 * 2 ^ 59
def prefixEnd_8324422 : Nat := 4983230072969 + 3 ^ 40 * 8324422 * 2
def baseEnd_8324422 : Nat := 4274429656861734894341687

theorem tailTrace_8324422 : CollatzResearch.WordTrace tailWord_8324422 prefixEnd_8324422 4274429656861734894341687 := by
  unfold tailWord_8324422
  simp only [CollatzResearch.WordTrace]
  refine ⟨9488019170251508341735735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 202411075632032177957029013 9488019170251508341735735)
  ·
    refine ⟨14232028755377262512603603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9488019170251508341735735 14232028755377262512603603)
    ·
      refine ⟨21348043133065893768905405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14232028755377262512603603 21348043133065893768905405)
      ·
        refine ⟨8005516174899710163339527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21348043133065893768905405 8005516174899710163339527)
        ·
          refine ⟨12008274262349565245009291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8005516174899710163339527 12008274262349565245009291)
          ·
            refine ⟨18012411393524347867513937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12008274262349565245009291 18012411393524347867513937)
            ·
              refine ⟨13509308545143260900635453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18012411393524347867513937 13509308545143260900635453)
              ·
                refine ⟨5065990704428722837738295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13509308545143260900635453 5065990704428722837738295)
                ·
                  refine ⟨7598986056643084256607443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5065990704428722837738295 7598986056643084256607443)
                  ·
                    refine ⟨11398479084964626384911165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7598986056643084256607443 11398479084964626384911165)
                    ·
                      refine ⟨4274429656861734894341687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11398479084964626384911165 4274429656861734894341687)
                      ·
                        rfl

theorem cell23_8324422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_8324422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8324422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8324422 prefixEnd_8324422 := by exact prefixLift 8324422
  have htrace : WordTrace (prefixWord ++ tailWord_8324422) baseStart_8324422 baseEnd_8324422 := by
    simpa [prefixWord, tailWord_8324422, baseEnd_8324422] using wordTrace_append hprefix tailTrace_8324422
  have hstable : (prefixWord ++ tailWord_8324422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8324422).length < 2 ^ (prefixWord ++ tailWord_8324422).sum := by decide
  have hdescent : baseEnd_8324422 < baseStart_8324422 := by decide
  rcases family_descends (prefixWord ++ tailWord_8324422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8324428 : List Nat := [2, 2, 1, 3, 2, 3, 2, 3, 1, 2, 2]
def baseStart_8324428 : Nat := 118140960795 + 8324428 * 2 ^ 59
def prefixEnd_8324428 : Nat := 4983230072969 + 3 ^ 40 * 8324428 * 2
def baseEnd_8324428 : Nat := 4274432737745661870866659

theorem tailTrace_8324428 : CollatzResearch.WordTrace tailWord_8324428 prefixEnd_8324428 4274432737745661870866659 := by
  unfold tailWord_8324428
  simp only [CollatzResearch.WordTrace]
  refine ⟨151808416143013264980130969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202411221524017686640174625 151808416143013264980130969)
  ·
    refine ⟨113856312107259948735098227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151808416143013264980130969 113856312107259948735098227)
    ·
      refine ⟨170784468160889923102647341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113856312107259948735098227 170784468160889923102647341)
      ·
        refine ⟨64044175560333721163492753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170784468160889923102647341 64044175560333721163492753)
        ·
          refine ⟨48033131670250290872619565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64044175560333721163492753 48033131670250290872619565)
          ·
            refine ⟨18012424376343859077232337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48033131670250290872619565 18012424376343859077232337)
            ·
              refine ⟨13509318282257894307924253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18012424376343859077232337 13509318282257894307924253)
              ·
                refine ⟨5065994355846710365471595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13509318282257894307924253 5065994355846710365471595)
                ·
                  refine ⟨7598991533770065548207393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5065994355846710365471595 7598991533770065548207393)
                  ·
                    refine ⟨5699243650327549161155545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7598991533770065548207393 5699243650327549161155545)
                    ·
                      refine ⟨4274432737745661870866659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5699243650327549161155545 4274432737745661870866659)
                      ·
                        rfl

theorem cell23_8324428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 2, 3, 1, 2, 2].length) (baseStart_8324428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8324428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8324428 prefixEnd_8324428 := by exact prefixLift 8324428
  have htrace : WordTrace (prefixWord ++ tailWord_8324428) baseStart_8324428 baseEnd_8324428 := by
    simpa [prefixWord, tailWord_8324428, baseEnd_8324428] using wordTrace_append hprefix tailTrace_8324428
  have hstable : (prefixWord ++ tailWord_8324428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8324428).length < 2 ^ (prefixWord ++ tailWord_8324428).sum := by decide
  have hdescent : baseEnd_8324428 < baseStart_8324428 := by decide
  rcases family_descends (prefixWord ++ tailWord_8324428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8324480 : List Nat := [2, 1, 1, 2, 1, 2, 1, 4, 1, 4, 4]
def baseStart_8324480 : Nat := 118140960795 + 8324480 * 2 ^ 59
def prefixEnd_8324480 : Nat := 4983230072969 + 3 ^ 40 * 8324480 * 2
def baseEnd_8324480 : Nat := 4274459438739695667416419

theorem tailTrace_8324480 : CollatzResearch.WordTrace tailWord_8324480 prefixEnd_8324480 4274459438739695667416419 := by
  unfold tailWord_8324480
  simp only [CollatzResearch.WordTrace]
  refine ⟨151809364440919071420577447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202412485921225428560769929 151809364440919071420577447)
  ·
    refine ⟨227714046661378607130866171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151809364440919071420577447 227714046661378607130866171)
    ·
      refine ⟨341571069992067910696299257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227714046661378607130866171 341571069992067910696299257)
      ·
        refine ⟨256178302494050933022224443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 341571069992067910696299257 256178302494050933022224443)
        ·
          refine ⟨384267453741076399533336665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256178302494050933022224443 384267453741076399533336665)
          ·
            refine ⟨288200590305807299650002499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 384267453741076399533336665 288200590305807299650002499)
            ·
              refine ⟨432300885458710949475003749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 288200590305807299650002499 432300885458710949475003749)
              ·
                refine ⟨81056416023508303026563203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 432300885458710949475003749 81056416023508303026563203)
                ·
                  refine ⟨121584624035262454539844805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81056416023508303026563203 121584624035262454539844805)
                  ·
                    refine ⟨22797117006611710226220901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 121584624035262454539844805 22797117006611710226220901)
                    ·
                      refine ⟨4274459438739695667416419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22797117006611710226220901 4274459438739695667416419)
                      ·
                        rfl

theorem cell23_8324480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 4, 1, 4, 4].length) (baseStart_8324480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8324480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8324480 prefixEnd_8324480 := by exact prefixLift 8324480
  have htrace : WordTrace (prefixWord ++ tailWord_8324480) baseStart_8324480 baseEnd_8324480 := by
    simpa [prefixWord, tailWord_8324480, baseEnd_8324480] using wordTrace_append hprefix tailTrace_8324480
  have hstable : (prefixWord ++ tailWord_8324480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8324480).length < 2 ^ (prefixWord ++ tailWord_8324480).sum := by decide
  have hdescent : baseEnd_8324480 < baseStart_8324480 := by decide
  rcases family_descends (prefixWord ++ tailWord_8324480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8324487 : List Nat := [1, 1, 4, 2, 2, 3, 1, 1, 2, 1, 5]
def baseStart_8324487 : Nat := 118140960795 + 8324487 * 2 ^ 59
def prefixEnd_8324487 : Nat := 4983230072969 + 3 ^ 40 * 8324487 * 2
def baseEnd_8324487 : Nat := 4274463033104277140028887

theorem tailTrace_8324487 : CollatzResearch.WordTrace tailWord_8324487 prefixEnd_8324487 4274463033104277140028887 := by
  unfold tailWord_8324487
  simp only [CollatzResearch.WordTrace]
  refine ⟨303618984192812783036659715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202412656128541855357773143 303618984192812783036659715)
  ·
    refine ⟨455428476289219174554989573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303618984192812783036659715 455428476289219174554989573)
    ·
      refine ⟨85392839304228595229060545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 455428476289219174554989573 85392839304228595229060545)
      ·
        refine ⟨64044629478171446421795409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85392839304228595229060545 64044629478171446421795409)
        ·
          refine ⟨48033472108628584816346557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64044629478171446421795409 48033472108628584816346557)
          ·
            refine ⟨18012552040735719306129959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48033472108628584816346557 18012552040735719306129959)
            ·
              refine ⟨27018828061103578959194939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18012552040735719306129959 27018828061103578959194939)
              ·
                refine ⟨40528242091655368438792409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27018828061103578959194939 40528242091655368438792409)
                ·
                  refine ⟨30396181568741526329094307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40528242091655368438792409 30396181568741526329094307)
                  ·
                    refine ⟨45594272353112289493641461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30396181568741526329094307 45594272353112289493641461)
                    ·
                      refine ⟨4274463033104277140028887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45594272353112289493641461 4274463033104277140028887)
                      ·
                        rfl

theorem cell23_8324487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 1, 2, 1, 5].length) (baseStart_8324487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8324487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8324487 prefixEnd_8324487 := by exact prefixLift 8324487
  have htrace : WordTrace (prefixWord ++ tailWord_8324487) baseStart_8324487 baseEnd_8324487 := by
    simpa [prefixWord, tailWord_8324487, baseEnd_8324487] using wordTrace_append hprefix tailTrace_8324487
  have hstable : (prefixWord ++ tailWord_8324487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8324487).length < 2 ^ (prefixWord ++ tailWord_8324487).sum := by decide
  have hdescent : baseEnd_8324487 < baseStart_8324487 := by decide
  rcases family_descends (prefixWord ++ tailWord_8324487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8324567 : List Nat := [1, 1, 3, 2, 1, 1, 1, 2, 7, 4]
def baseStart_8324567 : Nat := 118140960795 + 8324567 * 2 ^ 59
def prefixEnd_8324567 : Nat := 4983230072969 + 3 ^ 40 * 8324567 * 2
def baseEnd_8324567 : Nat := 1424834703852212275676173

theorem tailTrace_8324567 : CollatzResearch.WordTrace tailWord_8324567 prefixEnd_8324567 1424834703852212275676173 := by
  unfold tailWord_8324567
  simp only [CollatzResearch.WordTrace]
  refine ⟨303621902032522956699571955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202414601355015304466381303 303621902032522956699571955)
  ·
    refine ⟨455432853048784435049357933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303621902032522956699571955 455432853048784435049357933)
    ·
      refine ⟨170787319893294163143509225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 455432853048784435049357933 170787319893294163143509225)
      ·
        refine ⟨128090489919970622357631919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170787319893294163143509225 128090489919970622357631919)
        ·
          refine ⟨192135734879955933536447879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128090489919970622357631919 192135734879955933536447879)
          ·
            refine ⟨288203602319933900304671819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192135734879955933536447879 288203602319933900304671819)
            ·
              refine ⟨432305403479900850457007729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 288203602319933900304671819 432305403479900850457007729)
              ·
                refine ⟨324229052609925637842755797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 432305403479900850457007729 324229052609925637842755797)
                ·
                  refine ⟨7599118420545132136939589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 324229052609925637842755797 7599118420545132136939589)
                  ·
                    refine ⟨1424834703852212275676173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7599118420545132136939589 1424834703852212275676173)
                    ·
                      rfl

theorem cell23_8324567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 7, 4].length) (baseStart_8324567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8324567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8324567 prefixEnd_8324567 := by exact prefixLift 8324567
  have htrace : WordTrace (prefixWord ++ tailWord_8324567) baseStart_8324567 baseEnd_8324567 := by
    simpa [prefixWord, tailWord_8324567, baseEnd_8324567] using wordTrace_append hprefix tailTrace_8324567
  have hstable : (prefixWord ++ tailWord_8324567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8324567).length < 2 ^ (prefixWord ++ tailWord_8324567).sum := by decide
  have hdescent : baseEnd_8324567 < baseStart_8324567 := by decide
  rcases family_descends (prefixWord ++ tailWord_8324567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8324584 : List Nat := [2, 1, 4, 1, 1, 2, 3, 2, 3, 4]
def baseStart_8324584 : Nat := 118140960795 + 8324584 * 2 ^ 59
def prefixEnd_8324584 : Nat := 4983230072969 + 3 ^ 40 * 8324584 * 2
def baseEnd_8324584 : Nat := 1424837613575921086838647

theorem tailTrace_8324584 : CollatzResearch.WordTrace tailWord_8324584 prefixEnd_8324584 1424837613575921086838647 := by
  unfold tailWord_8324584
  simp only [CollatzResearch.WordTrace]
  refine ⟨151811261036730684301470403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202415014715640912401960537 151811261036730684301470403)
  ·
    refine ⟨227716891555096026452205605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151811261036730684301470403 227716891555096026452205605)
    ·
      refine ⟨42696917166580504959788551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 227716891555096026452205605 42696917166580504959788551)
      ·
        refine ⟨64045375749870757439682827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42696917166580504959788551 64045375749870757439682827)
        ·
          refine ⟨96068063624806136159524241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64045375749870757439682827 96068063624806136159524241)
          ·
            refine ⟨72051047718604602119643181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96068063624806136159524241 72051047718604602119643181)
            ·
              refine ⟨27019142894476725794866193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72051047718604602119643181 27019142894476725794866193)
              ·
                refine ⟨20264357170857544346149645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27019142894476725794866193 20264357170857544346149645)
                ·
                  refine ⟨7599133939071579129806117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20264357170857544346149645 7599133939071579129806117)
                  ·
                    refine ⟨1424837613575921086838647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7599133939071579129806117 1424837613575921086838647)
                    ·
                      rfl

theorem cell23_8324584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 2, 3, 4].length) (baseStart_8324584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8324584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8324584 prefixEnd_8324584 := by exact prefixLift 8324584
  have htrace : WordTrace (prefixWord ++ tailWord_8324584) baseStart_8324584 baseEnd_8324584 := by
    simpa [prefixWord, tailWord_8324584, baseEnd_8324584] using wordTrace_append hprefix tailTrace_8324584
  have hstable : (prefixWord ++ tailWord_8324584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8324584).length < 2 ^ (prefixWord ++ tailWord_8324584).sum := by decide
  have hdescent : baseEnd_8324584 < baseStart_8324584 := by decide
  rcases family_descends (prefixWord ++ tailWord_8324584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8324641 : List Nat := [1, 2, 3, 2, 2, 2, 2, 2, 3, 1, 3]
def baseStart_8324641 : Nat := 118140960795 + 8324641 * 2 ^ 59
def prefixEnd_8324641 : Nat := 4983230072969 + 3 ^ 40 * 8324641 * 2
def baseEnd_8324641 : Nat := 4274542109125069537503179

theorem tailTrace_8324641 : CollatzResearch.WordTrace tailWord_8324641 prefixEnd_8324641 4274542109125069537503179 := by
  unfold tailWord_8324641
  simp only [CollatzResearch.WordTrace]
  refine ⟨303624601034254867337765777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202416400689503244891843851 303624601034254867337765777)
  ·
    refine ⟨227718450775691150503324333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303624601034254867337765777 227718450775691150503324333)
    ·
      refine ⟨85394419040884181438746625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227718450775691150503324333 85394419040884181438746625)
      ·
        refine ⟨64045814280663136079059969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85394419040884181438746625 64045814280663136079059969)
        ·
          refine ⟨48034360710497352059294977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64045814280663136079059969 48034360710497352059294977)
          ·
            refine ⟨36025770532873014044471233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48034360710497352059294977 36025770532873014044471233)
            ·
              refine ⟨27019327899654760533353425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36025770532873014044471233 27019327899654760533353425)
              ·
                refine ⟨20264495924741070400015069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27019327899654760533353425 20264495924741070400015069)
                ·
                  refine ⟨7599185971777901400005651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20264495924741070400015069 7599185971777901400005651)
                  ·
                    refine ⟨11398778957666852100008477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7599185971777901400005651 11398778957666852100008477)
                    ·
                      refine ⟨4274542109125069537503179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11398778957666852100008477 4274542109125069537503179)
                      ·
                        rfl

theorem cell23_8324641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 2, 3, 1, 3].length) (baseStart_8324641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8324641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8324641 prefixEnd_8324641 := by exact prefixLift 8324641
  have htrace : WordTrace (prefixWord ++ tailWord_8324641) baseStart_8324641 baseEnd_8324641 := by
    simpa [prefixWord, tailWord_8324641, baseEnd_8324641] using wordTrace_append hprefix tailTrace_8324641
  have hstable : (prefixWord ++ tailWord_8324641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8324641).length < 2 ^ (prefixWord ++ tailWord_8324641).sum := by decide
  have hdescent : baseEnd_8324641 < baseStart_8324641 := by decide
  rcases family_descends (prefixWord ++ tailWord_8324641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8324657 : List Nat := [1, 2, 2, 3, 1, 1, 1, 3, 3, 6]
def baseStart_8324657 : Nat := 118140960795 + 8324657 * 2 ^ 59
def prefixEnd_8324657 : Nat := 4983230072969 + 3 ^ 40 * 8324657 * 2
def baseEnd_8324657 : Nat := 1424850108271847158301035

theorem tailTrace_8324657 : CollatzResearch.WordTrace tailWord_8324657 prefixEnd_8324657 1424850108271847158301035 := by
  unfold tailWord_8324657
  simp only [CollatzResearch.WordTrace]
  refine ⟨303625184602196902070348225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202416789734797934713565483 303625184602196902070348225)
  ·
    refine ⟨227718888451647676552761169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303625184602196902070348225 227718888451647676552761169)
    ·
      refine ⟨170789166338735757414570877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227718888451647676552761169 170789166338735757414570877)
      ·
        refine ⟨64045937377025909030464079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170789166338735757414570877 64045937377025909030464079)
        ·
          refine ⟨96068906065538863545696119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64045937377025909030464079 96068906065538863545696119)
          ·
            refine ⟨144103359098308295318544179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96068906065538863545696119 144103359098308295318544179)
            ·
              refine ⟨216155038647462442977816269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144103359098308295318544179 216155038647462442977816269)
              ·
                refine ⟨81058139492798416116681101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 216155038647462442977816269 81058139492798416116681101)
                ·
                  refine ⟨30396802309799406043755413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81058139492798416116681101 30396802309799406043755413)
                  ·
                    refine ⟨1424850108271847158301035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30396802309799406043755413 1424850108271847158301035)
                    ·
                      rfl

theorem cell23_8324657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 3, 3, 6].length) (baseStart_8324657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8324657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8324657 prefixEnd_8324657 := by exact prefixLift 8324657
  have htrace : WordTrace (prefixWord ++ tailWord_8324657) baseStart_8324657 baseEnd_8324657 := by
    simpa [prefixWord, tailWord_8324657, baseEnd_8324657] using wordTrace_append hprefix tailTrace_8324657
  have hstable : (prefixWord ++ tailWord_8324657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8324657).length < 2 ^ (prefixWord ++ tailWord_8324657).sum := by decide
  have hdescent : baseEnd_8324657 < baseStart_8324657 := by decide
  rcases family_descends (prefixWord ++ tailWord_8324657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8324668 : List Nat := [2, 2, 2, 2, 4, 1, 1, 2, 2, 3, 2]
def baseStart_8324668 : Nat := 118140960795 + 8324668 * 2 ^ 59
def prefixEnd_8324668 : Nat := 4983230072969 + 3 ^ 40 * 8324668 * 2
def baseEnd_8324668 : Nat := 4274555973102740931865555

theorem tailTrace_8324668 : CollatzResearch.WordTrace tailWord_8324668 prefixEnd_8324668 4274555973102740931865555 := by
  unfold tailWord_8324668
  simp only [CollatzResearch.WordTrace]
  refine ⟨151812792902578525474499329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202417057203438033965999105 151812792902578525474499329)
  ·
    refine ⟨113859594676933894105874497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151812792902578525474499329 113859594676933894105874497)
    ·
      refine ⟨85394696007700420579405873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113859594676933894105874497 85394696007700420579405873)
      ·
        refine ⟨64046022005775315434554405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85394696007700420579405873 64046022005775315434554405)
        ·
          refine ⟨12008629126082871643978951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64046022005775315434554405 12008629126082871643978951)
          ·
            refine ⟨18012943689124307465968427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12008629126082871643978951 18012943689124307465968427)
            ·
              refine ⟨27019415533686461198952641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18012943689124307465968427 27019415533686461198952641)
              ·
                refine ⟨20264561650264845899214481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27019415533686461198952641 20264561650264845899214481)
                ·
                  refine ⟨15198421237698634424410861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20264561650264845899214481 15198421237698634424410861)
                  ·
                    refine ⟨5699407964136987909154073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15198421237698634424410861 5699407964136987909154073)
                    ·
                      refine ⟨4274555973102740931865555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5699407964136987909154073 4274555973102740931865555)
                      ·
                        rfl

theorem cell23_8324668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 2, 2, 3, 2].length) (baseStart_8324668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8324668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8324668 prefixEnd_8324668 := by exact prefixLift 8324668
  have htrace : WordTrace (prefixWord ++ tailWord_8324668) baseStart_8324668 baseEnd_8324668 := by
    simpa [prefixWord, tailWord_8324668, baseEnd_8324668] using wordTrace_append hprefix tailTrace_8324668
  have hstable : (prefixWord ++ tailWord_8324668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8324668).length < 2 ^ (prefixWord ++ tailWord_8324668).sum := by decide
  have hdescent : baseEnd_8324668 < baseStart_8324668 := by decide
  rcases family_descends (prefixWord ++ tailWord_8324668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8324677 : List Nat := [1, 3, 1, 1, 1, 4, 1, 1, 3, 1, 6]
def baseStart_8324677 : Nat := 118140960795 + 8324677 * 2 ^ 59
def prefixEnd_8324677 : Nat := 4983230072969 + 3 ^ 40 * 8324677 * 2
def baseEnd_8324677 : Nat := 4274560594428631396653013

theorem tailTrace_8324677 : CollatzResearch.WordTrace tailWord_8324677 prefixEnd_8324677 4274560594428631396653013 := by
  unfold tailWord_8324677
  simp only [CollatzResearch.WordTrace]
  refine ⟨303625914062124445486076285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202417276041416296990717523 303625914062124445486076285)
  ·
    refine ⟨113859717773296667057278607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 303625914062124445486076285 113859717773296667057278607)
    ·
      refine ⟨170789576659945000585917911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113859717773296667057278607 170789576659945000585917911)
      ·
        refine ⟨256184364989917500878876867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170789576659945000585917911 256184364989917500878876867)
        ·
          refine ⟨384276547484876251318315301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256184364989917500878876867 384276547484876251318315301)
          ·
            refine ⟨72051852653414297122184119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 384276547484876251318315301 72051852653414297122184119)
            ·
              refine ⟨108077778980121445683276179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72051852653414297122184119 108077778980121445683276179)
              ·
                refine ⟨162116668470182168524914269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108077778980121445683276179 162116668470182168524914269)
                ·
                  refine ⟨60793750676318313196842851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 162116668470182168524914269 60793750676318313196842851)
                  ·
                    refine ⟨91190626014477469795264277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60793750676318313196842851 91190626014477469795264277)
                    ·
                      refine ⟨4274560594428631396653013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91190626014477469795264277 4274560594428631396653013)
                      ·
                        rfl

theorem cell23_8324677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 3, 1, 6].length) (baseStart_8324677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8324677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8324677 prefixEnd_8324677 := by exact prefixLift 8324677
  have htrace : WordTrace (prefixWord ++ tailWord_8324677) baseStart_8324677 baseEnd_8324677 := by
    simpa [prefixWord, tailWord_8324677, baseEnd_8324677] using wordTrace_append hprefix tailTrace_8324677
  have hstable : (prefixWord ++ tailWord_8324677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8324677).length < 2 ^ (prefixWord ++ tailWord_8324677).sum := by decide
  have hdescent : baseEnd_8324677 < baseStart_8324677 := by decide
  rcases family_descends (prefixWord ++ tailWord_8324677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8324684 : List Nat := [2, 2, 1, 3, 1, 3, 2, 2, 1, 1, 5]
def baseStart_8324684 : Nat := 118140960795 + 8324684 * 2 ^ 59
def prefixEnd_8324684 : Nat := 4983230072969 + 3 ^ 40 * 8324684 * 2
def baseEnd_8324684 : Nat := 4274564188793212869265481

theorem tailTrace_8324684 : CollatzResearch.WordTrace tailWord_8324684 prefixEnd_8324684 4274564188793212869265481 := by
  unfold tailWord_8324684
  simp only [CollatzResearch.WordTrace]
  refine ⟨151813084686549542840790553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202417446248732723787720737 151813084686549542840790553)
  ·
    refine ⟨113859813514912157130592915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151813084686549542840790553 113859813514912157130592915)
    ·
      refine ⟨170789720272368235695889373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113859813514912157130592915 170789720272368235695889373)
      ·
        refine ⟨64046145102138088385958515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170789720272368235695889373 64046145102138088385958515)
        ·
          refine ⟨96069217653207132578937773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64046145102138088385958515 96069217653207132578937773)
          ·
            refine ⟨36025956619952674717101665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96069217653207132578937773 36025956619952674717101665)
            ·
              refine ⟨27019467464964506037826249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36025956619952674717101665 27019467464964506037826249)
              ·
                refine ⟨20264600598723379528369687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27019467464964506037826249 20264600598723379528369687)
                ·
                  refine ⟨30396900898085069292554531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20264600598723379528369687 30396900898085069292554531)
                  ·
                    refine ⟨45595351347127603938831797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30396900898085069292554531 45595351347127603938831797)
                    ·
                      refine ⟨4274564188793212869265481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45595351347127603938831797 4274564188793212869265481)
                      ·
                        rfl

theorem cell23_8324684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 2, 1, 1, 5].length) (baseStart_8324684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8324684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8324684 prefixEnd_8324684 := by exact prefixLift 8324684
  have htrace : WordTrace (prefixWord ++ tailWord_8324684) baseStart_8324684 baseEnd_8324684 := by
    simpa [prefixWord, tailWord_8324684, baseEnd_8324684] using wordTrace_append hprefix tailTrace_8324684
  have hstable : (prefixWord ++ tailWord_8324684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8324684).length < 2 ^ (prefixWord ++ tailWord_8324684).sum := by decide
  have hdescent : baseEnd_8324684 < baseStart_8324684 := by decide
  rcases family_descends (prefixWord ++ tailWord_8324684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8324718 : List Nat := [4, 1, 2, 2, 3, 2, 1, 1, 1, 1, 5]
def baseStart_8324718 : Nat := 118140960795 + 8324718 * 2 ^ 59
def prefixEnd_8324718 : Nat := 4983230072969 + 3 ^ 40 * 8324718 * 2
def baseEnd_8324718 : Nat := 4274581647135465736240325

theorem tailTrace_8324718 : CollatzResearch.WordTrace tailWord_8324718 prefixEnd_8324718 4274581647135465736240325 := by
  unfold tailWord_8324718
  simp only [CollatzResearch.WordTrace]
  refine ⟨37953426181871988686039851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202418272969983939658879205 37953426181871988686039851)
  ·
    refine ⟨56930139272807983029059777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37953426181871988686039851 56930139272807983029059777)
    ·
      refine ⟨42697604454605987271794833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56930139272807983029059777 42697604454605987271794833)
      ·
        refine ⟨32023203340954490453846125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42697604454605987271794833 32023203340954490453846125)
        ·
          refine ⟨12008701252857933920192297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32023203340954490453846125 12008701252857933920192297)
          ·
            refine ⟨9006525939643450440144223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12008701252857933920192297 9006525939643450440144223)
            ·
              refine ⟨13509788909465175660216335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9006525939643450440144223 13509788909465175660216335)
              ·
                refine ⟨20264683364197763490324503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13509788909465175660216335 20264683364197763490324503)
                ·
                  refine ⟨30397025046296645235486755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20264683364197763490324503 30397025046296645235486755)
                  ·
                    refine ⟨45595537569444967853230133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30397025046296645235486755 45595537569444967853230133)
                    ·
                      refine ⟨4274581647135465736240325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45595537569444967853230133 4274581647135465736240325)
                      ·
                        rfl

theorem cell23_8324718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 1, 1, 1, 1, 5].length) (baseStart_8324718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8324718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8324718 prefixEnd_8324718 := by exact prefixLift 8324718
  have htrace : WordTrace (prefixWord ++ tailWord_8324718) baseStart_8324718 baseEnd_8324718 := by
    simpa [prefixWord, tailWord_8324718, baseEnd_8324718] using wordTrace_append hprefix tailTrace_8324718
  have hstable : (prefixWord ++ tailWord_8324718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8324718).length < 2 ^ (prefixWord ++ tailWord_8324718).sum := by decide
  have hdescent : baseEnd_8324718 < baseStart_8324718 := by decide
  rcases family_descends (prefixWord ++ tailWord_8324718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8324741 : List Nat := [1, 3, 1, 1, 4, 1, 1, 1, 5, 3, 2]
def baseStart_8324741 : Nat := 118140960795 + 8324741 * 2 ^ 59
def prefixEnd_8324741 : Nat := 4983230072969 + 3 ^ 40 * 8324741 * 2
def baseEnd_8324741 : Nat := 4274593457190519146252719

theorem tailTrace_8324741 : CollatzResearch.WordTrace tailWord_8324741 prefixEnd_8324741 4274593457190519146252719 := by
  unfold tailWord_8324741
  simp only [CollatzResearch.WordTrace]
  refine ⟨303628248333892584416406077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202418832222595056277604051 303628248333892584416406077)
  ·
    refine ⟨113860593125209719156152279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 303628248333892584416406077 113860593125209719156152279)
    ·
      refine ⟨170790889687814578734228419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113860593125209719156152279 170790889687814578734228419)
      ·
        refine ⟨256186334531721868101342629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170790889687814578734228419 256186334531721868101342629)
        ·
          refine ⟨48034937724697850269001743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 256186334531721868101342629 48034937724697850269001743)
          ·
            refine ⟨72052406587046775403502615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48034937724697850269001743 72052406587046775403502615)
            ·
              refine ⟨108078609880570163105253923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72052406587046775403502615 108078609880570163105253923)
              ·
                refine ⟨162117914820855244657880885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108078609880570163105253923 162117914820855244657880885)
                ·
                  refine ⟨15198554514455179186676333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 162117914820855244657880885 15198554514455179186676333)
                  ·
                    refine ⟨5699457942920692195003625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15198554514455179186676333 5699457942920692195003625)
                    ·
                      refine ⟨4274593457190519146252719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5699457942920692195003625 4274593457190519146252719)
                      ·
                        rfl

theorem cell23_8324741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 5, 3, 2].length) (baseStart_8324741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8324741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8324741 prefixEnd_8324741 := by exact prefixLift 8324741
  have htrace : WordTrace (prefixWord ++ tailWord_8324741) baseStart_8324741 baseEnd_8324741 := by
    simpa [prefixWord, tailWord_8324741, baseEnd_8324741] using wordTrace_append hprefix tailTrace_8324741
  have hstable : (prefixWord ++ tailWord_8324741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8324741).length < 2 ^ (prefixWord ++ tailWord_8324741).sum := by decide
  have hdescent : baseEnd_8324741 < baseStart_8324741 := by decide
  rcases family_descends (prefixWord ++ tailWord_8324741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8324771 : List Nat := [1, 1, 1, 4, 1, 1, 3, 4, 1, 4, 2]
def baseStart_8324771 : Nat := 118140960795 + 8324771 * 2 ^ 59
def prefixEnd_8324771 : Nat := 4983230072969 + 3 ^ 40 * 8324771 * 2
def baseEnd_8324771 : Nat := 4274608861610154028877581

theorem tailTrace_8324771 : CollatzResearch.WordTrace tailWord_8324771 prefixEnd_8324771 4274608861610154028877581 := by
  unfold tailWord_8324771
  simp only [CollatzResearch.WordTrace]
  refine ⟨303629342523783899539998167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202419561682522599693332111 303629342523783899539998167)
  ·
    refine ⟨455444013785675849309997251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303629342523783899539998167 455444013785675849309997251)
    ·
      refine ⟨683166020678513773964995877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 455444013785675849309997251 683166020678513773964995877)
      ·
        refine ⟨128093628877221332618436727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 683166020678513773964995877 128093628877221332618436727)
        ·
          refine ⟨192140443315831998927655091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128093628877221332618436727 192140443315831998927655091)
          ·
            refine ⟨288210664973747998391482637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192140443315831998927655091 288210664973747998391482637)
            ·
              refine ⟨108078999365155499396805989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 288210664973747998391482637 108078999365155499396805989)
              ·
                refine ⟨20264812380966656136901123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 108078999365155499396805989 20264812380966656136901123)
                ·
                  refine ⟨30397218571449984205351685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20264812380966656136901123 30397218571449984205351685)
                  ·
                    refine ⟨5699478482146872038503441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30397218571449984205351685 5699478482146872038503441)
                    ·
                      refine ⟨4274608861610154028877581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5699478482146872038503441 4274608861610154028877581)
                      ·
                        rfl

theorem cell23_8324771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 4, 1, 4, 2].length) (baseStart_8324771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8324771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8324771 prefixEnd_8324771 := by exact prefixLift 8324771
  have htrace : WordTrace (prefixWord ++ tailWord_8324771) baseStart_8324771 baseEnd_8324771 := by
    simpa [prefixWord, tailWord_8324771, baseEnd_8324771] using wordTrace_append hprefix tailTrace_8324771
  have hstable : (prefixWord ++ tailWord_8324771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8324771).length < 2 ^ (prefixWord ++ tailWord_8324771).sum := by decide
  have hdescent : baseEnd_8324771 < baseStart_8324771 := by decide
  rcases family_descends (prefixWord ++ tailWord_8324771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8324784 : List Nat := [2, 1, 1, 1, 2, 1, 5, 2, 2, 2, 4]
def baseStart_8324784 : Nat := 118140960795 + 8324784 * 2 ^ 59
def prefixEnd_8324784 : Nat := 4983230072969 + 3 ^ 40 * 8324784 * 2
def baseEnd_8324784 : Nat := 4274615536858662478015021

theorem tailTrace_8324784 : CollatzResearch.WordTrace tailWord_8324784 prefixEnd_8324784 4274615536858662478015021 := by
  unfold tailWord_8324784
  simp only [CollatzResearch.WordTrace]
  refine ⟨151814908336368401380110703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202419877781824535173480937 151814908336368401380110703)
  ·
    refine ⟨227722362504552602070166055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151814908336368401380110703 227722362504552602070166055)
    ·
      refine ⟨341583543756828903105249083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227722362504552602070166055 341583543756828903105249083)
      ·
        refine ⟨512375315635243354657873625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341583543756828903105249083 512375315635243354657873625)
        ·
          refine ⟨384281486726432515993405219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 512375315635243354657873625 384281486726432515993405219)
          ·
            refine ⟨576422230089648773990107829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 384281486726432515993405219 576422230089648773990107829)
            ·
              refine ⟨54039584070904572561572609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 576422230089648773990107829 54039584070904572561572609)
              ·
                refine ⟨40529688053178429421179457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54039584070904572561572609 40529688053178429421179457)
                ·
                  refine ⟨30397266039883822065884593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40529688053178429421179457 30397266039883822065884593)
                  ·
                    refine ⟨22797949529912866549413445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30397266039883822065884593 22797949529912866549413445)
                    ·
                      refine ⟨4274615536858662478015021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22797949529912866549413445 4274615536858662478015021)
                      ·
                        rfl

theorem cell23_8324784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 2, 2, 2, 4].length) (baseStart_8324784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8324784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8324784 prefixEnd_8324784 := by exact prefixLift 8324784
  have htrace : WordTrace (prefixWord ++ tailWord_8324784) baseStart_8324784 baseEnd_8324784 := by
    simpa [prefixWord, tailWord_8324784, baseEnd_8324784] using wordTrace_append hprefix tailTrace_8324784
  have hstable : (prefixWord ++ tailWord_8324784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8324784).length < 2 ^ (prefixWord ++ tailWord_8324784).sum := by decide
  have hdescent : baseEnd_8324784 < baseStart_8324784 := by decide
  rcases family_descends (prefixWord ++ tailWord_8324784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8324794 : List Nat := [3, 1, 1, 1, 2, 4, 1, 3, 7]
def baseStart_8324794 : Nat := 118140960795 + 8324794 * 2 ^ 59
def prefixEnd_8324794 : Nat := 4983230072969 + 3 ^ 40 * 8324794 * 2
def baseEnd_8324794 : Nat := 474957852407245270987775

theorem tailTrace_8324794 : CollatzResearch.WordTrace tailWord_8324794 prefixEnd_8324794 474957852407245270987775 := by
  unfold tailWord_8324794
  simp only [CollatzResearch.WordTrace]
  refine ⟨75907545350675143617021359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202420120935133716312056957 75907545350675143617021359)
  ·
    refine ⟨113861318026012715425532039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75907545350675143617021359 113861318026012715425532039)
    ·
      refine ⟨170791977039019073138298059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113861318026012715425532039 170791977039019073138298059)
      ·
        refine ⟨256187965558528609707447089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170791977039019073138298059 256187965558528609707447089)
        ·
          refine ⟨192140974168896457280585317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256187965558528609707447089 192140974168896457280585317)
          ·
            refine ⟨36026432656668085740109747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 192140974168896457280585317 36026432656668085740109747)
            ·
              refine ⟨54039648985002128610164621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36026432656668085740109747 54039648985002128610164621)
              ·
                refine ⟨20264868369375798228811733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54039648985002128610164621 20264868369375798228811733)
                ·
                  refine ⟨474957852407245270987775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20264868369375798228811733 474957852407245270987775)
                  ·
                    rfl

theorem cell23_8324794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 3, 7].length) (baseStart_8324794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8324794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8324794 prefixEnd_8324794 := by exact prefixLift 8324794
  have htrace : WordTrace (prefixWord ++ tailWord_8324794) baseStart_8324794 baseEnd_8324794 := by
    simpa [prefixWord, tailWord_8324794, baseEnd_8324794] using wordTrace_append hprefix tailTrace_8324794
  have hstable : (prefixWord ++ tailWord_8324794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8324794).length < 2 ^ (prefixWord ++ tailWord_8324794).sum := by decide
  have hdescent : baseEnd_8324794 < baseStart_8324794 := by decide
  rcases family_descends (prefixWord ++ tailWord_8324794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8324824 : List Nat := [2, 1, 2, 2, 3, 1, 1, 3, 1, 7]
def baseStart_8324824 : Nat := 118140960795 + 8324824 * 2 ^ 59
def prefixEnd_8324824 : Nat := 4983230072969 + 3 ^ 40 * 8324824 * 2
def baseEnd_8324824 : Nat := 1424878692028280773838279

theorem tailTrace_8324824 : CollatzResearch.WordTrace tailWord_8324824 prefixEnd_8324824 1424878692028280773838279 := by
  unfold tailWord_8324824
  simp only [CollatzResearch.WordTrace]
  refine ⟨151815637796295944795838763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202420850395061259727785017 151815637796295944795838763)
  ·
    refine ⟨227723456694443917193758145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151815637796295944795838763 227723456694443917193758145)
    ·
      refine ⟨170792592520832937895318609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227723456694443917193758145 170792592520832937895318609)
      ·
        refine ⟨128094444390624703421488957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170792592520832937895318609 128094444390624703421488957)
        ·
          refine ⟨48035416646484263783058359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128094444390624703421488957 48035416646484263783058359)
          ·
            refine ⟨72053124969726395674587539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48035416646484263783058359 72053124969726395674587539)
            ·
              refine ⟨108079687454589593511881309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72053124969726395674587539 108079687454589593511881309)
              ·
                refine ⟨40529882795471097566955491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108079687454589593511881309 40529882795471097566955491)
                ·
                  refine ⟨60794824193206646350433237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40529882795471097566955491 60794824193206646350433237)
                  ·
                    refine ⟨1424878692028280773838279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60794824193206646350433237 1424878692028280773838279)
                    ·
                      rfl

theorem cell23_8324824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 3, 1, 7].length) (baseStart_8324824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8324824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8324824 prefixEnd_8324824 := by exact prefixLift 8324824
  have htrace : WordTrace (prefixWord ++ tailWord_8324824) baseStart_8324824 baseEnd_8324824 := by
    simpa [prefixWord, tailWord_8324824, baseEnd_8324824] using wordTrace_append hprefix tailTrace_8324824
  have hstable : (prefixWord ++ tailWord_8324824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8324824).length < 2 ^ (prefixWord ++ tailWord_8324824).sum := by decide
  have hdescent : baseEnd_8324824 < baseStart_8324824 := by decide
  rcases family_descends (prefixWord ++ tailWord_8324824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8324845 : List Nat := [1, 5, 1, 2, 1, 3, 3, 2, 5]
def baseStart_8324845 : Nat := 118140960795 + 8324845 * 2 ^ 59
def prefixEnd_8324845 : Nat := 4983230072969 + 3 ^ 40 * 8324845 * 2
def baseEnd_8324845 : Nat := 474960762130954082150249

theorem tailTrace_8324845 : CollatzResearch.WordTrace tailWord_8324845 prefixEnd_8324845 474960762130954082150249 := by
  unfold tailWord_8324845
  simp only [CollatzResearch.WordTrace]
  refine ⟨303632041525515810178191989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202421361017010540118794659 303632041525515810178191989)
  ·
    refine ⟨28465503893017107204205499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 303632041525515810178191989 28465503893017107204205499)
    ·
      refine ⟨42698255839525660806308249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28465503893017107204205499 42698255839525660806308249)
      ·
        refine ⟨32023691879644245604731187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42698255839525660806308249 32023691879644245604731187)
        ·
          refine ⟨48035537819466368407096781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32023691879644245604731187 48035537819466368407096781)
          ·
            refine ⟨18013326682299888152661293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48035537819466368407096781 18013326682299888152661293)
            ·
              refine ⟨6754997505862458057247985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18013326682299888152661293 6754997505862458057247985)
              ·
                refine ⟨5066248129396843542935989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6754997505862458057247985 5066248129396843542935989)
                ·
                  refine ⟨474960762130954082150249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5066248129396843542935989 474960762130954082150249)
                  ·
                    rfl

theorem cell23_8324845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 3, 2, 5].length) (baseStart_8324845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8324845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8324845 prefixEnd_8324845 := by exact prefixLift 8324845
  have htrace : WordTrace (prefixWord ++ tailWord_8324845) baseStart_8324845 baseEnd_8324845 := by
    simpa [prefixWord, tailWord_8324845, baseEnd_8324845] using wordTrace_append hprefix tailTrace_8324845
  have hstable : (prefixWord ++ tailWord_8324845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8324845).length < 2 ^ (prefixWord ++ tailWord_8324845).sum := by decide
  have hdescent : baseEnd_8324845 < baseStart_8324845 := by decide
  rcases family_descends (prefixWord ++ tailWord_8324845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8324898 : List Nat := [3, 3, 1, 1, 2, 1, 1, 4, 2, 2, 3]
def baseStart_8324898 : Nat := 118140960795 + 8324898 * 2 ^ 59
def prefixEnd_8324898 : Nat := 4983230072969 + 3 ^ 40 * 8324898 * 2
def baseEnd_8324898 : Nat := 4274674073653275031989497

theorem tailTrace_8324898 : CollatzResearch.WordTrace tailWord_8324898 prefixEnd_8324898 4274674073653275031989497 := by
  unfold tailWord_8324898
  simp only [CollatzResearch.WordTrace]
  refine ⟨75908493648580950057467837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202422649729549200153247565 75908493648580950057467837)
  ·
    refine ⟨28465685118217856271550439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75908493648580950057467837 28465685118217856271550439)
    ·
      refine ⟨42698527677326784407325659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28465685118217856271550439 42698527677326784407325659)
      ·
        refine ⟨64047791515990176610988489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42698527677326784407325659 64047791515990176610988489)
        ·
          refine ⟨48035843636992632458241367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64047791515990176610988489 48035843636992632458241367)
          ·
            refine ⟨72053765455488948687362051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48035843636992632458241367 72053765455488948687362051)
            ·
              refine ⟨108080648183233423031043077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72053765455488948687362051 108080648183233423031043077)
              ·
                refine ⟨20265121534356266818320577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 108080648183233423031043077 20265121534356266818320577)
                ·
                  refine ⟨15198841150767200113740433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20265121534356266818320577 15198841150767200113740433)
                  ·
                    refine ⟨11399130863075400085305325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15198841150767200113740433 11399130863075400085305325)
                    ·
                      refine ⟨4274674073653275031989497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11399130863075400085305325 4274674073653275031989497)
                      ·
                        rfl

theorem cell23_8324898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 4, 2, 2, 3].length) (baseStart_8324898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8324898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8324898 prefixEnd_8324898 := by exact prefixLift 8324898
  have htrace : WordTrace (prefixWord ++ tailWord_8324898) baseStart_8324898 baseEnd_8324898 := by
    simpa [prefixWord, tailWord_8324898, baseEnd_8324898] using wordTrace_append hprefix tailTrace_8324898
  have hstable : (prefixWord ++ tailWord_8324898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8324898).length < 2 ^ (prefixWord ++ tailWord_8324898).sum := by decide
  have hdescent : baseEnd_8324898 < baseStart_8324898 := by decide
  rcases family_descends (prefixWord ++ tailWord_8324898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8324901 : List Nat := [1, 3, 1, 2, 3, 2, 1, 4, 6]
def baseStart_8324901 : Nat := 118140960795 + 8324901 * 2 ^ 59
def prefixEnd_8324901 : Nat := 4983230072969 + 3 ^ 40 * 8324901 * 2
def baseEnd_8324901 : Nat := 474963957121693168916887

theorem tailTrace_8324901 : CollatzResearch.WordTrace tailWord_8324901 prefixEnd_8324901 474963957121693168916887 := by
  unfold tailWord_8324901
  simp only [CollatzResearch.WordTrace]
  refine ⟨303634084013312931742230557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202422722675541954494820371 303634084013312931742230557)
  ·
    refine ⟨113862781504992349403336459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 303634084013312931742230557 113862781504992349403336459)
    ·
      refine ⟨170794172257488524105004689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113862781504992349403336459 170794172257488524105004689)
      ·
        refine ⟨128095629193116393078753517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170794172257488524105004689 128095629193116393078753517)
        ·
          refine ⟨48035860947418647404532569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128095629193116393078753517 48035860947418647404532569)
          ·
            refine ⟨36026895710563985553399427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48035860947418647404532569 36026895710563985553399427)
            ·
              refine ⟨54040343565845978330099141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36026895710563985553399427 54040343565845978330099141)
              ·
                refine ⟨10132564418596120936893589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54040343565845978330099141 10132564418596120936893589)
                ·
                  refine ⟨474963957121693168916887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10132564418596120936893589 474963957121693168916887)
                  ·
                    rfl

theorem cell23_8324901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 4, 6].length) (baseStart_8324901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8324901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8324901 prefixEnd_8324901 := by exact prefixLift 8324901
  have htrace : WordTrace (prefixWord ++ tailWord_8324901) baseStart_8324901 baseEnd_8324901 := by
    simpa [prefixWord, tailWord_8324901, baseEnd_8324901] using wordTrace_append hprefix tailTrace_8324901
  have hstable : (prefixWord ++ tailWord_8324901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8324901).length < 2 ^ (prefixWord ++ tailWord_8324901).sum := by decide
  have hdescent : baseEnd_8324901 < baseStart_8324901 := by decide
  rcases family_descends (prefixWord ++ tailWord_8324901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8324931 : List Nat := [1, 1, 1, 3, 1, 5, 2, 1, 3, 5]
def baseStart_8324931 : Nat := 118140960795 + 8324931 * 2 ^ 59
def prefixEnd_8324931 : Nat := 4983230072969 + 3 ^ 40 * 8324931 * 2
def baseEnd_8324931 : Nat := 1424897006171624467625615

theorem tailTrace_8324931 : CollatzResearch.WordTrace tailWord_8324931 prefixEnd_8324931 1424897006171624467625615 := by
  unfold tailWord_8324931
  simp only [CollatzResearch.WordTrace]
  refine ⟨303635178203204246865822647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202423452135469497910548431 303635178203204246865822647)
  ·
    refine ⟨455452767304806370298733971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303635178203204246865822647 455452767304806370298733971)
    ·
      refine ⟨683179150957209555448100957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 455452767304806370298733971 683179150957209555448100957)
      ·
        refine ⟨256192181608953583293037859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 683179150957209555448100957 256192181608953583293037859)
        ·
          refine ⟨384288272413430374939556789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256192181608953583293037859 384288272413430374939556789)
          ·
            refine ⟨36027025538759097650583449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 384288272413430374939556789 36027025538759097650583449)
            ·
              refine ⟨27020269154069323237937587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36027025538759097650583449 27020269154069323237937587)
              ·
                refine ⟨40530403731103984856906381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27020269154069323237937587 40530403731103984856906381)
                ·
                  refine ⟨15198901399163994321339893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40530403731103984856906381 15198901399163994321339893)
                  ·
                    refine ⟨1424897006171624467625615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15198901399163994321339893 1424897006171624467625615)
                    ·
                      rfl

theorem cell23_8324931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 1, 3, 5].length) (baseStart_8324931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8324931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8324931 prefixEnd_8324931 := by exact prefixLift 8324931
  have htrace : WordTrace (prefixWord ++ tailWord_8324931) baseStart_8324931 baseEnd_8324931 := by
    simpa [prefixWord, tailWord_8324931, baseEnd_8324931] using wordTrace_append hprefix tailTrace_8324931
  have hstable : (prefixWord ++ tailWord_8324931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8324931).length < 2 ^ (prefixWord ++ tailWord_8324931).sum := by decide
  have hdescent : baseEnd_8324931 < baseStart_8324931 := by decide
  rcases family_descends (prefixWord ++ tailWord_8324931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8324938 : List Nat := [3, 1, 2, 1, 1, 1, 5, 1, 1, 5, 2]
def baseStart_8324938 : Nat := 118140960795 + 8324938 * 2 ^ 59
def prefixEnd_8324938 : Nat := 4983230072969 + 3 ^ 40 * 8324938 * 2
def baseEnd_8324938 : Nat := 4274694612879454875489313

theorem tailTrace_8324938 : CollatzResearch.WordTrace tailWord_8324938 prefixEnd_8324938 4274694612879454875489313 := by
  unfold tailWord_8324938
  simp only [CollatzResearch.WordTrace]
  refine ⟨75908858378544721765331867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202423622342785924707551645 75908858378544721765331867)
  ·
    refine ⟨113863287567817082647997801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75908858378544721765331867 113863287567817082647997801)
    ·
      refine ⟨85397465675862811985998351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113863287567817082647997801 85397465675862811985998351)
      ·
        refine ⟨128096198513794217978997527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85397465675862811985998351 128096198513794217978997527)
        ·
          refine ⟨192144297770691326968496291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128096198513794217978997527 192144297770691326968496291)
          ·
            refine ⟨288216446656036990452744437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192144297770691326968496291 288216446656036990452744437)
            ·
              refine ⟨27020291874003467854944791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 288216446656036990452744437 27020291874003467854944791)
              ·
                refine ⟨40530437811005201782417187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27020291874003467854944791 40530437811005201782417187)
                ·
                  refine ⟨60795656716507802673625781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40530437811005201782417187 60795656716507802673625781)
                  ·
                    refine ⟨5699592817172606500652417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60795656716507802673625781 5699592817172606500652417)
                    ·
                      refine ⟨4274694612879454875489313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5699592817172606500652417 4274694612879454875489313)
                      ·
                        rfl

theorem cell23_8324938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 1, 1, 5, 2].length) (baseStart_8324938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8324938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8324938 prefixEnd_8324938 := by exact prefixLift 8324938
  have htrace : WordTrace (prefixWord ++ tailWord_8324938) baseStart_8324938 baseEnd_8324938 := by
    simpa [prefixWord, tailWord_8324938, baseEnd_8324938] using wordTrace_append hprefix tailTrace_8324938
  have hstable : (prefixWord ++ tailWord_8324938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8324938).length < 2 ^ (prefixWord ++ tailWord_8324938).sum := by decide
  have hdescent : baseEnd_8324938 < baseStart_8324938 := by decide
  rcases family_descends (prefixWord ++ tailWord_8324938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8324962 : List Nat := [3, 3, 2, 1, 2, 2, 2, 1, 3, 1, 3]
def baseStart_8324962 : Nat := 118140960795 + 8324962 * 2 ^ 59
def prefixEnd_8324962 : Nat := 4983230072969 + 3 ^ 40 * 8324962 * 2
def baseEnd_8324962 : Nat := 4274706936415162781589203

theorem tailTrace_8324962 : CollatzResearch.WordTrace tailWord_8324962 prefixEnd_8324962 4274706936415162781589203 := by
  unfold tailWord_8324962
  simp only [CollatzResearch.WordTrace]
  refine ⟨75909077216522984790050285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202424205910727959440134093 75909077216522984790050285)
  ·
    refine ⟨28465903956196119296268857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75909077216522984790050285 28465903956196119296268857)
    ·
      refine ⟨21349427967147089472201643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28465903956196119296268857 21349427967147089472201643)
      ·
        refine ⟨32024141950720634208302465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21349427967147089472201643 32024141950720634208302465)
        ·
          refine ⟨24018106463040475656226849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32024141950720634208302465 24018106463040475656226849)
          ·
            refine ⟨18013579847280356742170137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24018106463040475656226849 18013579847280356742170137)
            ·
              refine ⟨13510184885460267556627603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18013579847280356742170137 13510184885460267556627603)
              ·
                refine ⟨20265277328190401334941405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13510184885460267556627603 20265277328190401334941405)
                ·
                  refine ⟨7599478998071400500603027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20265277328190401334941405 7599478998071400500603027)
                  ·
                    refine ⟨11399218497107100750904541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7599478998071400500603027 11399218497107100750904541)
                    ·
                      refine ⟨4274706936415162781589203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11399218497107100750904541 4274706936415162781589203)
                      ·
                        rfl

theorem cell23_8324962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 2, 1, 3, 1, 3].length) (baseStart_8324962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8324962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8324962 prefixEnd_8324962 := by exact prefixLift 8324962
  have htrace : WordTrace (prefixWord ++ tailWord_8324962) baseStart_8324962 baseEnd_8324962 := by
    simpa [prefixWord, tailWord_8324962, baseEnd_8324962] using wordTrace_append hprefix tailTrace_8324962
  have hstable : (prefixWord ++ tailWord_8324962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8324962).length < 2 ^ (prefixWord ++ tailWord_8324962).sum := by decide
  have hdescent : baseEnd_8324962 < baseStart_8324962 := by decide
  rcases family_descends (prefixWord ++ tailWord_8324962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8324982 : List Nat := [5, 1, 1, 3, 2, 1, 2, 2, 1, 5]
def baseStart_8324982 : Nat := 118140960795 + 8324982 * 2 ^ 59
def prefixEnd_8324982 : Nat := 4983230072969 + 3 ^ 40 * 8324982 * 2
def baseEnd_8324982 : Nat := 1424905735342750901113037

theorem tailTrace_8324982 : CollatzResearch.WordTrace tailWord_8324982 prefixEnd_8324982 1424905735342750901113037 := by
  unfold tailWord_8324982
  simp only [CollatzResearch.WordTrace]
  refine ⟨18977314895376217660995575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 202424692217346321717286133 18977314895376217660995575)
  ·
    refine ⟨28465972343064326491493363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18977314895376217660995575 28465972343064326491493363)
    ·
      refine ⟨42698958514596489737240045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28465972343064326491493363 42698958514596489737240045)
      ·
        refine ⟨16012109442973683651465017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42698958514596489737240045 16012109442973683651465017)
        ·
          refine ⟨12009082082230262738598763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16012109442973683651465017 12009082082230262738598763)
          ·
            refine ⟨18013623123345394107898145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12009082082230262738598763 18013623123345394107898145)
            ·
              refine ⟨13510217342509045580923609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18013623123345394107898145 13510217342509045580923609)
              ·
                refine ⟨10132663006881784185692707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13510217342509045580923609 10132663006881784185692707)
                ·
                  refine ⟨15198994510322676278539061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10132663006881784185692707 15198994510322676278539061)
                  ·
                    refine ⟨1424905735342750901113037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15198994510322676278539061 1424905735342750901113037)
                    ·
                      rfl

theorem cell23_8324982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 2, 2, 1, 5].length) (baseStart_8324982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8324982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8324982 prefixEnd_8324982 := by exact prefixLift 8324982
  have htrace : WordTrace (prefixWord ++ tailWord_8324982) baseStart_8324982 baseEnd_8324982 := by
    simpa [prefixWord, tailWord_8324982, baseEnd_8324982] using wordTrace_append hprefix tailTrace_8324982
  have hstable : (prefixWord ++ tailWord_8324982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8324982).length < 2 ^ (prefixWord ++ tailWord_8324982).sum := by decide
  have hdescent : baseEnd_8324982 < baseStart_8324982 := by decide
  rcases family_descends (prefixWord ++ tailWord_8324982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8324985 : List Nat := [1, 2, 1, 3, 2, 2, 1, 4, 3, 2, 2]
def baseStart_8324985 : Nat := 118140960795 + 8324985 * 2 ^ 59
def prefixEnd_8324985 : Nat := 4983230072969 + 3 ^ 40 * 8324985 * 2
def baseEnd_8324985 : Nat := 4274718746470216191601597

theorem tailTrace_8324985 : CollatzResearch.WordTrace tailWord_8324985 prefixEnd_8324985 4274718746470216191601597 := by
  unfold tailWord_8324985
  simp only [CollatzResearch.WordTrace]
  refine ⟨303637147745008614088288409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202424765163339076058858939 303637147745008614088288409)
  ·
    refine ⟨227727860808756460566216307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303637147745008614088288409 227727860808756460566216307)
    ·
      refine ⟨341591791213134690849324461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227727860808756460566216307 341591791213134690849324461)
      ·
        refine ⟨128096921704925509068496673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 341591791213134690849324461 128096921704925509068496673)
        ·
          refine ⟨96072691278694131801372505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128096921704925509068496673 96072691278694131801372505)
          ·
            refine ⟨72054518459020598851029379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96072691278694131801372505 72054518459020598851029379)
            ·
              refine ⟨108081777688530898276544069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72054518459020598851029379 108081777688530898276544069)
              ·
                refine ⟨20265333316599543426852013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 108081777688530898276544069 20265333316599543426852013)
                ·
                  refine ⟨7599499993724828785069505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20265333316599543426852013 7599499993724828785069505)
                  ·
                    refine ⟨5699624995293621588802129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7599499993724828785069505 5699624995293621588802129)
                    ·
                      refine ⟨4274718746470216191601597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5699624995293621588802129 4274718746470216191601597)
                      ·
                        rfl

theorem cell23_8324985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 4, 3, 2, 2].length) (baseStart_8324985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8324985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8324985 prefixEnd_8324985 := by exact prefixLift 8324985
  have htrace : WordTrace (prefixWord ++ tailWord_8324985) baseStart_8324985 baseEnd_8324985 := by
    simpa [prefixWord, tailWord_8324985, baseEnd_8324985] using wordTrace_append hprefix tailTrace_8324985
  have hstable : (prefixWord ++ tailWord_8324985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8324985).length < 2 ^ (prefixWord ++ tailWord_8324985).sum := by decide
  have hdescent : baseEnd_8324985 < baseStart_8324985 := by decide
  rcases family_descends (prefixWord ++ tailWord_8324985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8325052 : List Nat := [2, 2, 2, 5, 1, 1, 1, 2, 1, 3, 3]
def baseStart_8325052 : Nat := 118140960795 + 8325052 * 2 ^ 59
def prefixEnd_8325052 : Nat := 4983230072969 + 3 ^ 40 * 8325052 * 2
def baseEnd_8325052 : Nat := 4274753149674067429463789

theorem tailTrace_8325052 : CollatzResearch.WordTrace tailWord_8325052 prefixEnd_8325052 4274753149674067429463789 := by
  unfold tailWord_8325052
  simp only [CollatzResearch.WordTrace]
  refine ⟨151819795717882942265488705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202426394290510589687318273 151819795717882942265488705)
  ·
    refine ⟨113864846788412206699116529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151819795717882942265488705 113864846788412206699116529)
    ·
      refine ⟨85398635091309155024337397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113864846788412206699116529 85398635091309155024337397)
      ·
        refine ⟨8006122039810233283531631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 85398635091309155024337397 8006122039810233283531631)
        ·
          refine ⟨12009183059715349925297447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8006122039810233283531631 12009183059715349925297447)
          ·
            refine ⟨18013774589573024887946171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12009183059715349925297447 18013774589573024887946171)
            ·
              refine ⟨27020661884359537331919257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18013774589573024887946171 27020661884359537331919257)
              ·
                refine ⟨20265496413269652998939443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27020661884359537331919257 20265496413269652998939443)
                ·
                  refine ⟨30398244619904479498409165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20265496413269652998939443 30398244619904479498409165)
                  ·
                    refine ⟨11399341732464179811903437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30398244619904479498409165 11399341732464179811903437)
                    ·
                      refine ⟨4274753149674067429463789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11399341732464179811903437 4274753149674067429463789)
                      ·
                        rfl

theorem cell23_8325052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_8325052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8325052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8325052 prefixEnd_8325052 := by exact prefixLift 8325052
  have htrace : WordTrace (prefixWord ++ tailWord_8325052) baseStart_8325052 baseEnd_8325052 := by
    simpa [prefixWord, tailWord_8325052, baseEnd_8325052] using wordTrace_append hprefix tailTrace_8325052
  have hstable : (prefixWord ++ tailWord_8325052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8325052).length < 2 ^ (prefixWord ++ tailWord_8325052).sum := by decide
  have hdescent : baseEnd_8325052 < baseStart_8325052 := by decide
  rcases family_descends (prefixWord ++ tailWord_8325052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8325061 : List Nat := [1, 3, 1, 1, 1, 1, 1, 5, 1, 3, 5]
def baseStart_8325061 : Nat := 118140960795 + 8325061 * 2 ^ 59
def prefixEnd_8325061 : Nat := 4983230072969 + 3 ^ 40 * 8325061 * 2
def baseEnd_8325061 : Nat := 4274757770999957894251247

theorem tailTrace_8325061 : CollatzResearch.WordTrace tailWord_8325061 prefixEnd_8325061 4274757770999957894251247 := by
  unfold tailWord_8325061
  simp only [CollatzResearch.WordTrace]
  refine ⟨303639919692733279068055037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202426613128488852712036691 303639919692733279068055037)
  ·
    refine ⟨113864969884774979650520639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 303639919692733279068055037 113864969884774979650520639)
    ·
      refine ⟨170797454827162469475780959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113864969884774979650520639 170797454827162469475780959)
      ·
        refine ⟨256196182240743704213671439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170797454827162469475780959 256196182240743704213671439)
        ·
          refine ⟨384294273361115556320507159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256196182240743704213671439 384294273361115556320507159)
          ·
            refine ⟨576441410041673334480760739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 384294273361115556320507159 576441410041673334480760739)
            ·
              refine ⟨864662115062510001721141109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 576441410041673334480760739 864662115062510001721141109)
              ·
                refine ⟨81062073287110312661356979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 864662115062510001721141109 81062073287110312661356979)
                ·
                  refine ⟨121593109930665468992035469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81062073287110312661356979 121593109930665468992035469)
                  ·
                    refine ⟨45597416223999550872013301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 121593109930665468992035469 45597416223999550872013301)
                    ·
                      refine ⟨4274757770999957894251247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45597416223999550872013301 4274757770999957894251247)
                      ·
                        rfl

theorem cell23_8325061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 5, 1, 3, 5].length) (baseStart_8325061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8325061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8325061 prefixEnd_8325061 := by exact prefixLift 8325061
  have htrace : WordTrace (prefixWord ++ tailWord_8325061) baseStart_8325061 baseEnd_8325061 := by
    simpa [prefixWord, tailWord_8325061, baseEnd_8325061] using wordTrace_append hprefix tailTrace_8325061
  have hstable : (prefixWord ++ tailWord_8325061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8325061).length < 2 ^ (prefixWord ++ tailWord_8325061).sum := by decide
  have hdescent : baseEnd_8325061 < baseStart_8325061 := by decide
  rcases family_descends (prefixWord ++ tailWord_8325061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8325085 : List Nat := [1, 4, 3, 1, 3, 1, 1, 1, 2, 6]
def baseStart_8325085 : Nat := 118140960795 + 8325085 * 2 ^ 59
def prefixEnd_8325085 : Nat := 4983230072969 + 3 ^ 40 * 8325085 * 2
def baseEnd_8325085 : Nat := 1424923364845221933450379

theorem tailTrace_8325085 : CollatzResearch.WordTrace tailWord_8325085 prefixEnd_8325085 1424923364845221933450379 := by
  unfold tailWord_8325085
  simp only [CollatzResearch.WordTrace]
  refine ⟨303640795044646331166928709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202427196696430887444619139 303640795044646331166928709)
  ·
    refine ⟨56932649070871187093799133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 303640795044646331166928709 56932649070871187093799133)
    ·
      refine ⟨21349743401576695160174675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56932649070871187093799133 21349743401576695160174675)
      ·
        refine ⟨32024615102365042740262013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21349743401576695160174675 32024615102365042740262013)
        ·
          refine ⟨12009230663386891027598255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32024615102365042740262013 12009230663386891027598255)
          ·
            refine ⟨18013845995080336541397383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12009230663386891027598255 18013845995080336541397383)
            ·
              refine ⟨27020768992620504812096075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18013845995080336541397383 27020768992620504812096075)
              ·
                refine ⟨40531153488930757218144113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27020768992620504812096075 40531153488930757218144113)
                ·
                  refine ⟨30398365116698067913608085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40531153488930757218144113 30398365116698067913608085)
                  ·
                    refine ⟨1424923364845221933450379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30398365116698067913608085 1424923364845221933450379)
                    ·
                      rfl

theorem cell23_8325085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 1, 2, 6].length) (baseStart_8325085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8325085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8325085 prefixEnd_8325085 := by exact prefixLift 8325085
  have htrace : WordTrace (prefixWord ++ tailWord_8325085) baseStart_8325085 baseEnd_8325085 := by
    simpa [prefixWord, tailWord_8325085, baseEnd_8325085] using wordTrace_append hprefix tailTrace_8325085
  have hstable : (prefixWord ++ tailWord_8325085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8325085).length < 2 ^ (prefixWord ++ tailWord_8325085).sum := by decide
  have hdescent : baseEnd_8325085 < baseStart_8325085 := by decide
  rcases family_descends (prefixWord ++ tailWord_8325085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8325092 : List Nat := [2, 3, 1, 1, 1, 1, 3, 5, 2, 2, 2]
def baseStart_8325092 : Nat := 118140960795 + 8325092 * 2 ^ 59
def prefixEnd_8325092 : Nat := 4983230072969 + 3 ^ 40 * 8325092 * 2
def baseEnd_8325092 : Nat := 4274773688900247272963605

theorem tailTrace_8325092 : CollatzResearch.WordTrace tailWord_8325092 prefixEnd_8325092 4274773688900247272963605 := by
  unfold tailWord_8325092
  simp only [CollatzResearch.WordTrace]
  refine ⟨151820525177810485681216765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202427366903747314241622353 151820525177810485681216765)
  ·
    refine ⟨56932696941678932130456287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151820525177810485681216765 56932696941678932130456287)
    ·
      refine ⟨85399045412518398195684431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56932696941678932130456287 85399045412518398195684431)
      ·
        refine ⟨128098568118777597293526647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85399045412518398195684431 128098568118777597293526647)
        ·
          refine ⟨192147852178166395940289971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128098568118777597293526647 192147852178166395940289971)
          ·
            refine ⟨288221778267249593910434957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192147852178166395940289971 288221778267249593910434957)
            ·
              refine ⟨108083166850218597716413109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 288221778267249593910434957 108083166850218597716413109)
              ·
                refine ⟨10132796892207993535913729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 108083166850218597716413109 10132796892207993535913729)
                ·
                  refine ⟨7599597669155995151935297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10132796892207993535913729 7599597669155995151935297)
                  ·
                    refine ⟨5699698251866996363951473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7599597669155995151935297 5699698251866996363951473)
                    ·
                      refine ⟨4274773688900247272963605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5699698251866996363951473 4274773688900247272963605)
                      ·
                        rfl

theorem cell23_8325092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 5, 2, 2, 2].length) (baseStart_8325092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8325092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8325092 prefixEnd_8325092 := by exact prefixLift 8325092
  have htrace : WordTrace (prefixWord ++ tailWord_8325092) baseStart_8325092 baseEnd_8325092 := by
    simpa [prefixWord, tailWord_8325092, baseEnd_8325092] using wordTrace_append hprefix tailTrace_8325092
  have hstable : (prefixWord ++ tailWord_8325092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8325092).length < 2 ^ (prefixWord ++ tailWord_8325092).sum := by decide
  have hdescent : baseEnd_8325092 < baseStart_8325092 := by decide
  rcases family_descends (prefixWord ++ tailWord_8325092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8325098 : List Nat := [3, 1, 3, 1, 2, 1, 3, 2, 7]
def baseStart_8325098 : Nat := 118140960795 + 8325098 * 2 ^ 59
def prefixEnd_8325098 : Nat := 4983230072969 + 3 ^ 40 * 8325098 * 2
def baseEnd_8325098 : Nat := 474975196642686027720953

theorem tailTrace_8325098 : CollatzResearch.WordTrace tailWord_8325098 prefixEnd_8325098 474975196642686027720953 := by
  unfold tailWord_8325098
  simp only [CollatzResearch.WordTrace]
  refine ⟨75910317298399808596787987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202427512795732822924767965 75910317298399808596787987)
  ·
    refine ⟨113865475947599712895181981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75910317298399808596787987 113865475947599712895181981)
    ·
      refine ⟨42699553480349892335693243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113865475947599712895181981 42699553480349892335693243)
      ·
        refine ⟨64049330220524838503539865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42699553480349892335693243 64049330220524838503539865)
        ·
          refine ⟨48036997665393628877654899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64049330220524838503539865 48036997665393628877654899)
          ·
            refine ⟨72055496498090443316482349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48036997665393628877654899 72055496498090443316482349)
            ·
              refine ⟨27020811186783916243680881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72055496498090443316482349 27020811186783916243680881)
              ·
                refine ⟨20265608390087937182760661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27020811186783916243680881 20265608390087937182760661)
                ·
                  refine ⟨474975196642686027720953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20265608390087937182760661 474975196642686027720953)
                  ·
                    rfl

theorem cell23_8325098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 2, 7].length) (baseStart_8325098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8325098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8325098 prefixEnd_8325098 := by exact prefixLift 8325098
  have htrace : WordTrace (prefixWord ++ tailWord_8325098) baseStart_8325098 baseEnd_8325098 := by
    simpa [prefixWord, tailWord_8325098, baseEnd_8325098] using wordTrace_append hprefix tailTrace_8325098
  have hstable : (prefixWord ++ tailWord_8325098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8325098).length < 2 ^ (prefixWord ++ tailWord_8325098).sum := by decide
  have hdescent : baseEnd_8325098 < baseStart_8325098 := by decide
  rcases family_descends (prefixWord ++ tailWord_8325098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8325128 : List Nat := [2, 1, 3, 2, 1, 2, 2, 1, 4, 5]
def baseStart_8325128 : Nat := 118140960795 + 8325128 * 2 ^ 59
def prefixEnd_8325128 : Nat := 4983230072969 + 3 ^ 40 * 8325128 * 2
def baseEnd_8325128 : Nat := 1424930724734603044037813

theorem tailTrace_8325128 : CollatzResearch.WordTrace tailWord_8325128 prefixEnd_8325128 1424930724734603044037813 := by
  unfold tailWord_8325128
  simp only [CollatzResearch.WordTrace]
  refine ⟨151821181691745274755372019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202428242255660366340496025 151821181691745274755372019)
  ·
    refine ⟨227731772537617912133058029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151821181691745274755372019 227731772537617912133058029)
    ·
      refine ⟨85399414701606717049896761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227731772537617912133058029 85399414701606717049896761)
      ·
        refine ⟨64049561026205037787422571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85399414701606717049896761 64049561026205037787422571)
        ·
          refine ⟨96074341539307556681133857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64049561026205037787422571 96074341539307556681133857)
          ·
            refine ⟨72055756154480667510850393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96074341539307556681133857 72055756154480667510850393)
            ·
              refine ⟨54041817115860500633137795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72055756154480667510850393 54041817115860500633137795)
              ·
                refine ⟨81062725673790750949706693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54041817115860500633137795 81062725673790750949706693)
                ·
                  refine ⟨15199261063835765803070005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81062725673790750949706693 15199261063835765803070005)
                  ·
                    refine ⟨1424930724734603044037813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15199261063835765803070005 1424930724734603044037813)
                    ·
                      rfl

theorem cell23_8325128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 1, 4, 5].length) (baseStart_8325128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8325128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8325128 prefixEnd_8325128 := by exact prefixLift 8325128
  have htrace : WordTrace (prefixWord ++ tailWord_8325128) baseStart_8325128 baseEnd_8325128 := by
    simpa [prefixWord, tailWord_8325128, baseEnd_8325128] using wordTrace_append hprefix tailTrace_8325128
  have hstable : (prefixWord ++ tailWord_8325128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8325128).length < 2 ^ (prefixWord ++ tailWord_8325128).sum := by decide
  have hdescent : baseEnd_8325128 < baseStart_8325128 := by decide
  rcases family_descends (prefixWord ++ tailWord_8325128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8325205 : List Nat := [1, 3, 2, 2, 1, 4, 1, 3, 6]
def baseStart_8325205 : Nat := 118140960795 + 8325205 * 2 ^ 59
def prefixEnd_8325205 : Nat := 4983230072969 + 3 ^ 40 * 8325205 * 2
def baseEnd_8325205 : Nat := 474981301357133925650065

theorem tailTrace_8325205 : CollatzResearch.WordTrace tailWord_8325205 prefixEnd_8325205 474981301357133925650065 := by
  unfold tailWord_8325205
  simp only [CollatzResearch.WordTrace]
  refine ⟨303645171804211591661297069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202430114536141061107531379 303645171804211591661297069)
  ·
    refine ⟨113866939426579346872986401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 303645171804211591661297069 113866939426579346872986401)
    ·
      refine ⟨85400204569934510154739801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113866939426579346872986401 85400204569934510154739801)
      ·
        refine ⟨64050153427450882616054851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85400204569934510154739801 64050153427450882616054851)
        ·
          refine ⟨96075230141176323924082277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64050153427450882616054851 96075230141176323924082277)
          ·
            refine ⟨18014105651470560735765427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96075230141176323924082277 18014105651470560735765427)
            ·
              refine ⟨27021158477205841103648141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18014105651470560735765427 27021158477205841103648141)
              ·
                refine ⟨10132934428952190413868053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27021158477205841103648141 10132934428952190413868053)
                ·
                  refine ⟨474981301357133925650065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10132934428952190413868053 474981301357133925650065)
                  ·
                    rfl

theorem cell23_8325205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 3, 6].length) (baseStart_8325205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8325205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8325205 prefixEnd_8325205 := by exact prefixLift 8325205
  have htrace : WordTrace (prefixWord ++ tailWord_8325205) baseStart_8325205 baseEnd_8325205 := by
    simpa [prefixWord, tailWord_8325205, baseEnd_8325205] using wordTrace_append hprefix tailTrace_8325205
  have hstable : (prefixWord ++ tailWord_8325205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8325205).length < 2 ^ (prefixWord ++ tailWord_8325205).sum := by decide
  have hdescent : baseEnd_8325205 < baseStart_8325205 := by decide
  rcases family_descends (prefixWord ++ tailWord_8325205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8325248 : List Nat := [2, 1, 1, 2, 1, 3, 1, 1, 5, 6]
def baseStart_8325248 : Nat := 118140960795 + 8325248 * 2 ^ 59
def prefixEnd_8325248 : Nat := 4983230072969 + 3 ^ 40 * 8325248 * 2
def baseEnd_8325248 : Nat := 1424951263960782887537629

theorem tailTrace_8325248 : CollatzResearch.WordTrace tailWord_8325248 prefixEnd_8325248 1424951263960782887537629 := by
  unfold tailWord_8325248
  simp only [CollatzResearch.WordTrace]
  refine ⟨151823370071527905002556199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202431160095370540003408265 151823370071527905002556199)
  ·
    refine ⟨227735055107291857503834299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151823370071527905002556199 227735055107291857503834299)
    ·
      refine ⟨341602582660937786255751449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227735055107291857503834299 341602582660937786255751449)
      ·
        refine ⟨256201936995703339691813587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 341602582660937786255751449 256201936995703339691813587)
        ·
          refine ⟨384302905493555009537720381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256201936995703339691813587 384302905493555009537720381)
          ·
            refine ⟨144113589560083128576645143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 384302905493555009537720381 144113589560083128576645143)
            ·
              refine ⟨216170384340124692864967715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144113589560083128576645143 216170384340124692864967715)
              ·
                refine ⟨324255576510187039297451573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 216170384340124692864967715 324255576510187039297451573)
                ·
                  refine ⟨30398960297830034934136085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 324255576510187039297451573 30398960297830034934136085)
                  ·
                    refine ⟨1424951263960782887537629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30398960297830034934136085 1424951263960782887537629)
                    ·
                      rfl

theorem cell23_8325248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 5, 6].length) (baseStart_8325248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8325248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8325248 prefixEnd_8325248 := by exact prefixLift 8325248
  have htrace : WordTrace (prefixWord ++ tailWord_8325248) baseStart_8325248 baseEnd_8325248 := by
    simpa [prefixWord, tailWord_8325248, baseEnd_8325248] using wordTrace_append hprefix tailTrace_8325248
  have hstable : (prefixWord ++ tailWord_8325248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8325248).length < 2 ^ (prefixWord ++ tailWord_8325248).sum := by decide
  have hdescent : baseEnd_8325248 < baseStart_8325248 := by decide
  rcases family_descends (prefixWord ++ tailWord_8325248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8325255 : List Nat := [1, 1, 4, 2, 1, 1, 3, 2, 3, 1, 4]
def baseStart_8325255 : Nat := 118140960795 + 8325255 * 2 ^ 59
def prefixEnd_8325255 : Nat := 4983230072969 + 3 ^ 40 * 8325255 * 2
def baseEnd_8325255 : Nat := 4274857386246930135225355

theorem tailTrace_8325255 : CollatzResearch.WordTrace tailWord_8325255 prefixEnd_8325255 4274857386246930135225355 := by
  unfold tailWord_8325255
  simp only [CollatzResearch.WordTrace]
  refine ⟨303646995454030450200617219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202431330302686966800411479 303646995454030450200617219)
  ·
    refine ⟨455470493181045675300925829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303646995454030450200617219 455470493181045675300925829)
    ·
      refine ⟨85400717471446064118923593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 455470493181045675300925829 85400717471446064118923593)
      ·
        refine ⟨64050538103584548089192695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85400717471446064118923593 64050538103584548089192695)
        ·
          refine ⟨96075807155376822133789043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64050538103584548089192695 96075807155376822133789043)
          ·
            refine ⟨144113710733065233200683565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96075807155376822133789043 144113710733065233200683565)
            ·
              refine ⟨54042641524899462450256337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144113710733065233200683565 54042641524899462450256337)
              ·
                refine ⟨40531981143674596837692253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54042641524899462450256337 40531981143674596837692253)
                ·
                  refine ⟨15199492928877973814134595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40531981143674596837692253 15199492928877973814134595)
                  ·
                    refine ⟨22799239393316960721201893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15199492928877973814134595 22799239393316960721201893)
                    ·
                      refine ⟨4274857386246930135225355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22799239393316960721201893 4274857386246930135225355)
                      ·
                        rfl

theorem cell23_8325255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 2, 3, 1, 4].length) (baseStart_8325255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8325255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8325255 prefixEnd_8325255 := by exact prefixLift 8325255
  have htrace : WordTrace (prefixWord ++ tailWord_8325255) baseStart_8325255 baseEnd_8325255 := by
    simpa [prefixWord, tailWord_8325255, baseEnd_8325255] using wordTrace_append hprefix tailTrace_8325255
  have hstable : (prefixWord ++ tailWord_8325255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8325255).length < 2 ^ (prefixWord ++ tailWord_8325255).sum := by decide
  have hdescent : baseEnd_8325255 < baseStart_8325255 := by decide
  rcases family_descends (prefixWord ++ tailWord_8325255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8325275 : List Nat := [1, 1, 1, 1, 1, 1, 2, 7, 3, 2, 3]
def baseStart_8325275 : Nat := 118140960795 + 8325275 * 2 ^ 59
def prefixEnd_8325275 : Nat := 4983230072969 + 3 ^ 40 * 8325275 * 2
def baseEnd_8325275 : Nat := 4274867655860020056975263

theorem tailTrace_8325275 : CollatzResearch.WordTrace tailWord_8325275 prefixEnd_8325275 4274867655860020056975263 := by
  unfold tailWord_8325275
  simp only [CollatzResearch.WordTrace]
  refine ⟨303647724913957993616345279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202431816609305329077563519 303647724913957993616345279)
  ·
    refine ⟨455471587370936990424517919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303647724913957993616345279 455471587370936990424517919)
    ·
      refine ⟨683207381056405485636776879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 455471587370936990424517919 683207381056405485636776879)
      ·
        refine ⟨1024811071584608228455165319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 683207381056405485636776879 1024811071584608228455165319)
        ·
          refine ⟨1537216607376912342682747979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1024811071584608228455165319 1537216607376912342682747979)
          ·
            refine ⟨2305824911065368514024121969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1537216607376912342682747979 2305824911065368514024121969)
            ·
              refine ⟨1729368683299026385518091477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2305824911065368514024121969 1729368683299026385518091477)
              ·
                refine ⟨40532078514820930910580269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1729368683299026385518091477 40532078514820930910580269)
                ·
                  refine ⟨15199529443057849091467601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40532078514820930910580269 15199529443057849091467601)
                  ·
                    refine ⟨11399647082293386818600701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15199529443057849091467601 11399647082293386818600701)
                    ·
                      refine ⟨4274867655860020056975263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11399647082293386818600701 4274867655860020056975263)
                      ·
                        rfl

theorem cell23_8325275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 7, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 7, 3, 2, 3].length) (baseStart_8325275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8325275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8325275 prefixEnd_8325275 := by exact prefixLift 8325275
  have htrace : WordTrace (prefixWord ++ tailWord_8325275) baseStart_8325275 baseEnd_8325275 := by
    simpa [prefixWord, tailWord_8325275, baseEnd_8325275] using wordTrace_append hprefix tailTrace_8325275
  have hstable : (prefixWord ++ tailWord_8325275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8325275).length < 2 ^ (prefixWord ++ tailWord_8325275).sum := by decide
  have hdescent : baseEnd_8325275 < baseStart_8325275 := by decide
  rcases family_descends (prefixWord ++ tailWord_8325275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8325282 : List Nat := [3, 3, 1, 3, 1, 1, 2, 2, 1, 6]
def baseStart_8325282 : Nat := 118140960795 + 8325282 * 2 ^ 59
def prefixEnd_8325282 : Nat := 4983230072969 + 3 ^ 40 * 8325282 * 2
def baseEnd_8325282 : Nat := 1424957083408200509862577

theorem tailTrace_8325282 : CollatzResearch.WordTrace tailWord_8325282 prefixEnd_8325282 1424957083408200509862577 := by
  unfold tailWord_8325282
  simp only [CollatzResearch.WordTrace]
  refine ⟨75911995056233158452962525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202431986816621755874566733 75911995056233158452962525)
  ·
    refine ⟨28466998146087434419860947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75911995056233158452962525 28466998146087434419860947)
    ·
      refine ⟨42700497219131151629791421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28466998146087434419860947 42700497219131151629791421)
      ·
        refine ⟨16012686457174181861171783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42700497219131151629791421 16012686457174181861171783)
        ·
          refine ⟨24019029685761272791757675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16012686457174181861171783 24019029685761272791757675)
          ·
            refine ⟨36028544528641909187636513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24019029685761272791757675 36028544528641909187636513)
            ·
              refine ⟨27021408396481431890727385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36028544528641909187636513 27021408396481431890727385)
              ·
                refine ⟨20266056297361073918045539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27021408396481431890727385 20266056297361073918045539)
                ·
                  refine ⟨30399084446041610877068309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20266056297361073918045539 30399084446041610877068309)
                  ·
                    refine ⟨1424957083408200509862577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30399084446041610877068309 1424957083408200509862577)
                    ·
                      rfl

theorem cell23_8325282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 2, 1, 6].length) (baseStart_8325282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8325282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8325282 prefixEnd_8325282 := by exact prefixLift 8325282
  have htrace : WordTrace (prefixWord ++ tailWord_8325282) baseStart_8325282 baseEnd_8325282 := by
    simpa [prefixWord, tailWord_8325282, baseEnd_8325282] using wordTrace_append hprefix tailTrace_8325282
  have hstable : (prefixWord ++ tailWord_8325282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8325282).length < 2 ^ (prefixWord ++ tailWord_8325282).sum := by decide
  have hdescent : baseEnd_8325282 < baseStart_8325282 := by decide
  rcases family_descends (prefixWord ++ tailWord_8325282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8325285 : List Nat := [1, 3, 1, 2, 1, 3, 1, 4, 1, 2, 4]
def baseStart_8325285 : Nat := 118140960795 + 8325285 * 2 ^ 59
def prefixEnd_8325285 : Nat := 4983230072969 + 3 ^ 40 * 8325285 * 2
def baseEnd_8325285 : Nat := 4274872790666565017850217

theorem tailTrace_8325285 : CollatzResearch.WordTrace tailWord_8325285 prefixEnd_8325285 4274872790666565017850217 := by
  unfold tailWord_8325285
  simp only [CollatzResearch.WordTrace]
  refine ⟨303648089643921765324209309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202432059762614510216139539 303648089643921765324209309)
  ·
    refine ⟨113868033616470661996578491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 303648089643921765324209309 113868033616470661996578491)
    ·
      refine ⟨170802050424705992994867737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113868033616470661996578491 170802050424705992994867737)
      ·
        refine ⟨128101537818529494746150803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170802050424705992994867737 128101537818529494746150803)
        ·
          refine ⟨192152306727794242119226205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128101537818529494746150803 192152306727794242119226205)
          ·
            refine ⟨72057115022922840794709827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 192152306727794242119226205 72057115022922840794709827)
            ·
              refine ⟨108085672534384261192064741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72057115022922840794709827 108085672534384261192064741)
              ·
                refine ⟨20266063600197048973512139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 108085672534384261192064741 20266063600197048973512139)
                ·
                  refine ⟨30399095400295573460268209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20266063600197048973512139 30399095400295573460268209)
                  ·
                    refine ⟨22799321550221680095201157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30399095400295573460268209 22799321550221680095201157)
                    ·
                      refine ⟨4274872790666565017850217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22799321550221680095201157 4274872790666565017850217)
                      ·
                        rfl

theorem cell23_8325285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 4, 1, 2, 4].length) (baseStart_8325285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8325285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8325285 prefixEnd_8325285 := by exact prefixLift 8325285
  have htrace : WordTrace (prefixWord ++ tailWord_8325285) baseStart_8325285 baseEnd_8325285 := by
    simpa [prefixWord, tailWord_8325285, baseEnd_8325285] using wordTrace_append hprefix tailTrace_8325285
  have hstable : (prefixWord ++ tailWord_8325285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8325285).length < 2 ^ (prefixWord ++ tailWord_8325285).sum := by decide
  have hdescent : baseEnd_8325285 < baseStart_8325285 := by decide
  rcases family_descends (prefixWord ++ tailWord_8325285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8325300 : List Nat := [2, 5, 3, 1, 1, 1, 2, 1, 3, 1, 3]
def baseStart_8325300 : Nat := 118140960795 + 8325300 * 2 ^ 59
def prefixEnd_8325300 : Nat := 4983230072969 + 3 ^ 40 * 8325300 * 2
def baseEnd_8325300 : Nat := 4274880492876382459162649

theorem tailTrace_8325300 : CollatzResearch.WordTrace tailWord_8325300 prefixEnd_8325300 4274880492876382459162649 := by
  unfold tailWord_8325300
  simp only [CollatzResearch.WordTrace]
  refine ⟨151824318369433711443002677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202432424492578281924003569 151824318369433711443002677)
  ·
    refine ⟨14233529847134410447781501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 151824318369433711443002677 14233529847134410447781501)
    ·
      refine ⟨5337573692675403917918063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14233529847134410447781501 5337573692675403917918063)
      ·
        refine ⟨8006360539013105876877095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5337573692675403917918063 8006360539013105876877095)
        ·
          refine ⟨12009540808519658815315643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8006360539013105876877095 12009540808519658815315643)
          ·
            refine ⟨18014311212779488222973465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12009540808519658815315643 18014311212779488222973465)
            ·
              refine ⟨13510733409584616167230099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18014311212779488222973465 13510733409584616167230099)
              ·
                refine ⟨20266100114376924250845149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13510733409584616167230099 20266100114376924250845149)
                ·
                  refine ⟨7599787542891346594066931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20266100114376924250845149 7599787542891346594066931)
                  ·
                    refine ⟨11399681314337019891100397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7599787542891346594066931 11399681314337019891100397)
                    ·
                      refine ⟨4274880492876382459162649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11399681314337019891100397 4274880492876382459162649)
                      ·
                        rfl

theorem cell23_8325300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_8325300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8325300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8325300 prefixEnd_8325300 := by exact prefixLift 8325300
  have htrace : WordTrace (prefixWord ++ tailWord_8325300) baseStart_8325300 baseEnd_8325300 := by
    simpa [prefixWord, tailWord_8325300, baseEnd_8325300] using wordTrace_append hprefix tailTrace_8325300
  have hstable : (prefixWord ++ tailWord_8325300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8325300).length < 2 ^ (prefixWord ++ tailWord_8325300).sum := by decide
  have hdescent : baseEnd_8325300 < baseStart_8325300 := by decide
  rcases family_descends (prefixWord ++ tailWord_8325300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8325306 : List Nat := [3, 1, 1, 1, 2, 2, 4, 4, 1, 2, 2]
def baseStart_8325306 : Nat := 118140960795 + 8325306 * 2 ^ 59
def prefixEnd_8325306 : Nat := 4983230072969 + 3 ^ 40 * 8325306 * 2
def baseEnd_8325306 : Nat := 4274883573760309435687621

theorem tailTrace_8325306 : CollatzResearch.WordTrace tailWord_8325306 prefixEnd_8325306 4274883573760309435687621 := by
  unfold tailWord_8325306
  simp only [CollatzResearch.WordTrace]
  refine ⟨75912213894211421477680943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202432570384563790607149181 75912213894211421477680943)
  ·
    refine ⟨113868320841317132216521415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75912213894211421477680943 113868320841317132216521415)
    ·
      refine ⟨170802481261975698324782123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113868320841317132216521415 170802481261975698324782123)
      ·
        refine ⟨256203721892963547487173185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170802481261975698324782123 256203721892963547487173185)
        ·
          refine ⟨192152791419722660615379889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256203721892963547487173185 192152791419722660615379889)
          ·
            refine ⟨144114593564791995461534917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192152791419722660615379889 144114593564791995461534917)
            ·
              refine ⟨27021486293398499149037797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 144114593564791995461534917 27021486293398499149037797)
              ·
                refine ⟨5066528680012218590444587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27021486293398499149037797 5066528680012218590444587)
                ·
                  refine ⟨7599793020018327885666881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5066528680012218590444587 7599793020018327885666881)
                  ·
                    refine ⟨5699844765013745914250161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7599793020018327885666881 5699844765013745914250161)
                    ·
                      refine ⟨4274883573760309435687621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5699844765013745914250161 4274883573760309435687621)
                      ·
                        rfl

theorem cell23_8325306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 4, 1, 2, 2].length) (baseStart_8325306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8325306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8325306 prefixEnd_8325306 := by exact prefixLift 8325306
  have htrace : WordTrace (prefixWord ++ tailWord_8325306) baseStart_8325306 baseEnd_8325306 := by
    simpa [prefixWord, tailWord_8325306, baseEnd_8325306] using wordTrace_append hprefix tailTrace_8325306
  have hstable : (prefixWord ++ tailWord_8325306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8325306).length < 2 ^ (prefixWord ++ tailWord_8325306).sum := by decide
  have hdescent : baseEnd_8325306 < baseStart_8325306 := by decide
  rcases family_descends (prefixWord ++ tailWord_8325306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8325316 : List Nat := [2, 3, 3, 1, 2, 2, 3, 1, 2, 4]
def baseStart_8325316 : Nat := 118140960795 + 8325316 * 2 ^ 59
def prefixEnd_8325316 : Nat := 4983230072969 + 3 ^ 40 * 8325316 * 2
def baseEnd_8325316 : Nat := 1424962902855618132187525

theorem tailTrace_8325316 : CollatzResearch.WordTrace tailWord_8325316 prefixEnd_8325316 1424962902855618132187525 := by
  unfold tailWord_8325316
  simp only [CollatzResearch.WordTrace]
  refine ⟨151824610153404728809293901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202432813537872971745725201 151824610153404728809293901)
  ·
    refine ⟨56934228807526773303485213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151824610153404728809293901 56934228807526773303485213)
    ·
      refine ⟨21350335802822539988806955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56934228807526773303485213 21350335802822539988806955)
      ·
        refine ⟨32025503704233809983210433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21350335802822539988806955 32025503704233809983210433)
        ·
          refine ⟨24019127778175357487407825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32025503704233809983210433 24019127778175357487407825)
          ·
            refine ⟨18014345833631518115555869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24019127778175357487407825 18014345833631518115555869)
            ·
              refine ⟨6755379687611819293333451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18014345833631518115555869 6755379687611819293333451)
              ·
                refine ⟨10133069531417728940000177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6755379687611819293333451 10133069531417728940000177)
                ·
                  refine ⟨7599802148563296705000133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10133069531417728940000177 7599802148563296705000133)
                  ·
                    refine ⟨1424962902855618132187525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7599802148563296705000133 1424962902855618132187525)
                    ·
                      rfl

theorem cell23_8325316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 3, 1, 2, 4].length) (baseStart_8325316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8325316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8325316 prefixEnd_8325316 := by exact prefixLift 8325316
  have htrace : WordTrace (prefixWord ++ tailWord_8325316) baseStart_8325316 baseEnd_8325316 := by
    simpa [prefixWord, tailWord_8325316, baseEnd_8325316] using wordTrace_append hprefix tailTrace_8325316
  have hstable : (prefixWord ++ tailWord_8325316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8325316).length < 2 ^ (prefixWord ++ tailWord_8325316).sum := by decide
  have hdescent : baseEnd_8325316 < baseStart_8325316 := by decide
  rcases family_descends (prefixWord ++ tailWord_8325316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8325346 : List Nat := [3, 3, 4, 1, 1, 2, 9]
def baseStart_8325346 : Nat := 118140960795 + 8325346 * 2 ^ 59
def prefixEnd_8325346 : Nat := 4983230072969 + 3 ^ 40 * 8325346 * 2
def baseEnd_8325346 : Nat := 52776593987487521965277

theorem tailTrace_8325346 : CollatzResearch.WordTrace tailWord_8325346 prefixEnd_8325346 52776593987487521965277 := by
  unfold tailWord_8325346
  simp only [CollatzResearch.WordTrace]
  refine ⟨75912578624175193185544973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202433542997800515161453261 75912578624175193185544973)
  ·
    refine ⟨28467216984065697444579365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75912578624175193185544973 28467216984065697444579365)
    ·
      refine ⟨5337603184512318270858631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28467216984065697444579365 5337603184512318270858631)
      ·
        refine ⟨8006404776768477406287947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5337603184512318270858631 8006404776768477406287947)
        ·
          refine ⟨12009607165152716109431921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8006404776768477406287947 12009607165152716109431921)
          ·
            refine ⟨9007205373864537082073941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12009607165152716109431921 9007205373864537082073941)
            ·
              refine ⟨52776593987487521965277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 9007205373864537082073941 52776593987487521965277)
              ·
                rfl

theorem cell23_8325346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 9].length) (baseStart_8325346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8325346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8325346 prefixEnd_8325346 := by exact prefixLift 8325346
  have htrace : WordTrace (prefixWord ++ tailWord_8325346) baseStart_8325346 baseEnd_8325346 := by
    simpa [prefixWord, tailWord_8325346, baseEnd_8325346] using wordTrace_append hprefix tailTrace_8325346
  have hstable : (prefixWord ++ tailWord_8325346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8325346).length < 2 ^ (prefixWord ++ tailWord_8325346).sum := by decide
  have hdescent : baseEnd_8325346 < baseStart_8325346 := by decide
  rcases family_descends (prefixWord ++ tailWord_8325346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8325375 : List Nat := [1, 1, 2, 2, 1, 4, 2, 1, 1, 4, 4]
def baseStart_8325375 : Nat := 118140960795 + 8325375 * 2 ^ 59
def prefixEnd_8325375 : Nat := 4983230072969 + 3 ^ 40 * 8325375 * 2
def baseEnd_8325375 : Nat := 4274919003925469665724803

theorem tailTrace_8325375 : CollatzResearch.WordTrace tailWord_8325375 prefixEnd_8325375 4274919003925469665724803 := by
  unfold tailWord_8325375
  simp only [CollatzResearch.WordTrace]
  refine ⟨303651372213595710694985579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202434248142397140463323719 303651372213595710694985579)
  ·
    refine ⟨455477058320393566042478369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303651372213595710694985579 455477058320393566042478369)
    ·
      refine ⟨341607793740295174531858777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 455477058320393566042478369 341607793740295174531858777)
      ·
        refine ⟨256205845305221380898894083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 341607793740295174531858777 256205845305221380898894083)
        ·
          refine ⟨384308767957832071348341125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256205845305221380898894083 384308767957832071348341125)
          ·
            refine ⟨72057893992093513377813961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 384308767957832071348341125 72057893992093513377813961)
            ·
              refine ⟨54043420494070135033360471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72057893992093513377813961 54043420494070135033360471)
              ·
                refine ⟨81065130741105202550040707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54043420494070135033360471 81065130741105202550040707)
                ·
                  refine ⟨121597696111657803825061061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81065130741105202550040707 121597696111657803825061061)
                  ·
                    refine ⟨22799568020935838217198949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 121597696111657803825061061 22799568020935838217198949)
                    ·
                      refine ⟨4274919003925469665724803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22799568020935838217198949 4274919003925469665724803)
                      ·
                        rfl

theorem cell23_8325375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 1, 1, 4, 4].length) (baseStart_8325375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8325375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8325375 prefixEnd_8325375 := by exact prefixLift 8325375
  have htrace : WordTrace (prefixWord ++ tailWord_8325375) baseStart_8325375 baseEnd_8325375 := by
    simpa [prefixWord, tailWord_8325375, baseEnd_8325375] using wordTrace_append hprefix tailTrace_8325375
  have hstable : (prefixWord ++ tailWord_8325375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8325375).length < 2 ^ (prefixWord ++ tailWord_8325375).sum := by decide
  have hdescent : baseEnd_8325375 < baseStart_8325375 := by decide
  rcases family_descends (prefixWord ++ tailWord_8325375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8325413 : List Nat := [1, 3, 1, 2, 5, 1, 2, 2, 2, 2, 2]
def baseStart_8325413 : Nat := 118140960795 + 8325413 * 2 ^ 59
def prefixEnd_8325413 : Nat := 4983230072969 + 3 ^ 40 * 8325413 * 2
def baseEnd_8325413 : Nat := 4274938516190340517049629

theorem tailTrace_8325413 : CollatzResearch.WordTrace tailWord_8325413 prefixEnd_8325413 4274938516190340517049629 := by
  unfold tailWord_8325413
  simp only [CollatzResearch.WordTrace]
  refine ⟨303652758187458043184868893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202435172124972028789912595 303652758187458043184868893)
  ·
    refine ⟨113869784320296766194325835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 303652758187458043184868893 113869784320296766194325835)
    ·
      refine ⟨170804676480445149291488753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113869784320296766194325835 170804676480445149291488753)
      ·
        refine ⟨128103507360333861968616565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170804676480445149291488753 128103507360333861968616565)
        ·
          refine ⟨12009703815031299559557803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 128103507360333861968616565 12009703815031299559557803)
          ·
            refine ⟨18014555722546949339336705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12009703815031299559557803 18014555722546949339336705)
            ·
              refine ⟨13510916791910212004502529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18014555722546949339336705 13510916791910212004502529)
              ·
                refine ⟨10133187593932659003376897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13510916791910212004502529 10133187593932659003376897)
                ·
                  refine ⟨7599890695449494252532673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10133187593932659003376897 7599890695449494252532673)
                  ·
                    refine ⟨5699918021587120689399505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7599890695449494252532673 5699918021587120689399505)
                    ·
                      refine ⟨4274938516190340517049629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5699918021587120689399505 4274938516190340517049629)
                      ·
                        rfl

theorem cell23_8325413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 2, 2, 2, 2, 2].length) (baseStart_8325413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8325413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8325413 prefixEnd_8325413 := by exact prefixLift 8325413
  have htrace : WordTrace (prefixWord ++ tailWord_8325413) baseStart_8325413 baseEnd_8325413 := by
    simpa [prefixWord, tailWord_8325413, baseEnd_8325413] using wordTrace_append hprefix tailTrace_8325413
  have hstable : (prefixWord ++ tailWord_8325413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8325413).length < 2 ^ (prefixWord ++ tailWord_8325413).sum := by decide
  have hdescent : baseEnd_8325413 < baseStart_8325413 := by decide
  rcases family_descends (prefixWord ++ tailWord_8325413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8325452 : List Nat := [2, 2, 1, 3, 2, 1, 3, 1, 1, 3, 4]
def baseStart_8325452 : Nat := 118140960795 + 8325452 * 2 ^ 59
def prefixEnd_8325452 : Nat := 4983230072969 + 3 ^ 40 * 8325452 * 2
def baseEnd_8325452 : Nat := 4274958541935865864461949

theorem tailTrace_8325452 : CollatzResearch.WordTrace tailWord_8325452 prefixEnd_8325452 4274958541935865864461949 := by
  unfold tailWord_8325452
  simp only [CollatzResearch.WordTrace]
  refine ⟨151827090317158376422769305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202436120422877835230359073 151827090317158376422769305)
  ·
    refine ⟨113870317737868782317076979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151827090317158376422769305 113870317737868782317076979)
    ·
      refine ⟨170805476606803173475615469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113870317737868782317076979 170805476606803173475615469)
      ·
        refine ⟨64052053727551190053355801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170805476606803173475615469 64052053727551190053355801)
        ·
          refine ⟨48039040295663392540016851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64052053727551190053355801 48039040295663392540016851)
          ·
            refine ⟨72058560443495088810025277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48039040295663392540016851 72058560443495088810025277)
            ·
              refine ⟨27021960166310658303759479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72058560443495088810025277 27021960166310658303759479)
              ·
                refine ⟨40532940249465987455639219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27021960166310658303759479 40532940249465987455639219)
                ·
                  refine ⟨60799410374198981183458829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40532940249465987455639219 60799410374198981183458829)
                  ·
                    refine ⟨22799778890324617943797061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60799410374198981183458829 22799778890324617943797061)
                    ·
                      refine ⟨4274958541935865864461949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22799778890324617943797061 4274958541935865864461949)
                      ·
                        rfl

theorem cell23_8325452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 1, 1, 3, 4].length) (baseStart_8325452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8325452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8325452 prefixEnd_8325452 := by exact prefixLift 8325452
  have htrace : WordTrace (prefixWord ++ tailWord_8325452) baseStart_8325452 baseEnd_8325452 := by
    simpa [prefixWord, tailWord_8325452, baseEnd_8325452] using wordTrace_append hprefix tailTrace_8325452
  have hstable : (prefixWord ++ tailWord_8325452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8325452).length < 2 ^ (prefixWord ++ tailWord_8325452).sum := by decide
  have hdescent : baseEnd_8325452 < baseStart_8325452 := by decide
  rcases family_descends (prefixWord ++ tailWord_8325452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8325455 : List Nat := [1, 1, 2, 1, 1, 2, 1, 4, 2, 3, 5]
def baseStart_8325455 : Nat := 118140960795 + 8325455 * 2 ^ 59
def prefixEnd_8325455 : Nat := 4983230072969 + 3 ^ 40 * 8325455 * 2
def baseEnd_8325455 : Nat := 4274960082377829352724435

theorem tailTrace_8325455 : CollatzResearch.WordTrace tailWord_8325455 prefixEnd_8325455 4274960082377829352724435 := by
  unfold tailWord_8325455
  simp only [CollatzResearch.WordTrace]
  refine ⟨303654290053305884357897819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202436193368870589571931879 303654290053305884357897819)
  ·
    refine ⟨455481435079958826536846729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303654290053305884357897819 455481435079958826536846729)
    ·
      refine ⟨341611076309969119902635047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 455481435079958826536846729 341611076309969119902635047)
      ·
        refine ⟨512416614464953679853952571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341611076309969119902635047 512416614464953679853952571)
        ·
          refine ⟨768624921697430519780928857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 512416614464953679853952571 768624921697430519780928857)
          ·
            refine ⟨576468691273072889835696643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 768624921697430519780928857 576468691273072889835696643)
            ·
              refine ⟨864703036909609334753544965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 576468691273072889835696643 864703036909609334753544965)
              ·
                refine ⟨162131819420551750266289681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 864703036909609334753544965 162131819420551750266289681)
                ·
                  refine ⟨121598864565413812699717261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 162131819420551750266289681 121598864565413812699717261)
                  ·
                    refine ⟨45599574212030179762393973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 121598864565413812699717261 45599574212030179762393973)
                    ·
                      refine ⟨4274960082377829352724435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45599574212030179762393973 4274960082377829352724435)
                      ·
                        rfl

theorem cell23_8325455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 2, 3, 5].length) (baseStart_8325455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8325455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8325455 prefixEnd_8325455 := by exact prefixLift 8325455
  have htrace : WordTrace (prefixWord ++ tailWord_8325455) baseStart_8325455 baseEnd_8325455 := by
    simpa [prefixWord, tailWord_8325455, baseEnd_8325455] using wordTrace_append hprefix tailTrace_8325455
  have hstable : (prefixWord ++ tailWord_8325455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8325455).length < 2 ^ (prefixWord ++ tailWord_8325455).sum := by decide
  have hdescent : baseEnd_8325455 < baseStart_8325455 := by decide
  rcases family_descends (prefixWord ++ tailWord_8325455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8325470 : List Nat := [4, 4, 2, 1, 1, 1, 2, 1, 7]
def baseStart_8325470 : Nat := 118140960795 + 8325470 * 2 ^ 59
def prefixEnd_8325470 : Nat := 4983230072969 + 3 ^ 40 * 8325470 * 2
def baseEnd_8325470 : Nat := 474996420509738532670763

theorem tailTrace_8325470 : CollatzResearch.WordTrace tailWord_8325470 prefixEnd_8325470 474996420509738532670763 := by
  unfold tailWord_8325470
  simp only [CollatzResearch.WordTrace]
  refine ⟨37956854643531442739961733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202436558098834361279795909 37956854643531442739961733)
  ·
    refine ⟨7116910245662145513742825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37956854643531442739961733 7116910245662145513742825)
    ·
      refine ⟨5337682684246609135307119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7116910245662145513742825 5337682684246609135307119)
      ·
        refine ⟨8006524026369913702960679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5337682684246609135307119 8006524026369913702960679)
        ·
          refine ⟨12009786039554870554441019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8006524026369913702960679 12009786039554870554441019)
          ·
            refine ⟨18014679059332305831661529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12009786039554870554441019 18014679059332305831661529)
            ·
              refine ⟨13511009294499229373746147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18014679059332305831661529 13511009294499229373746147)
              ·
                refine ⟨20266513941748844060619221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13511009294499229373746147 20266513941748844060619221)
                ·
                  refine ⟨474996420509738532670763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20266513941748844060619221 474996420509738532670763)
                  ·
                    rfl

theorem cell23_8325470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 2, 1, 7].length) (baseStart_8325470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8325470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8325470 prefixEnd_8325470 := by exact prefixLift 8325470
  have htrace : WordTrace (prefixWord ++ tailWord_8325470) baseStart_8325470 baseEnd_8325470 := by
    simpa [prefixWord, tailWord_8325470, baseEnd_8325470] using wordTrace_append hprefix tailTrace_8325470
  have hstable : (prefixWord ++ tailWord_8325470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8325470).length < 2 ^ (prefixWord ++ tailWord_8325470).sum := by decide
  have hdescent : baseEnd_8325470 < baseStart_8325470 := by decide
  rcases family_descends (prefixWord ++ tailWord_8325470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8325479 : List Nat := [1, 1, 5, 1, 3, 1, 1, 3, 3, 4]
def baseStart_8325479 : Nat := 118140960795 + 8325479 * 2 ^ 59
def prefixEnd_8325479 : Nat := 4983230072969 + 3 ^ 40 * 8325479 * 2
def baseEnd_8325479 : Nat := 1424990801971179086274775

theorem tailTrace_8325479 : CollatzResearch.WordTrace tailWord_8325479 prefixEnd_8325479 1424990801971179086274775 := by
  unfold tailWord_8325479
  simp only [CollatzResearch.WordTrace]
  refine ⟨303655165405218936456771491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202436776936812624304514327 303655165405218936456771491)
  ·
    refine ⟨455482748107828404685157237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303655165405218936456771491 455482748107828404685157237)
    ·
      refine ⟨42701507635108912939233491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 455482748107828404685157237 42701507635108912939233491)
      ·
        refine ⟨64052261452663369408850237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42701507635108912939233491 64052261452663369408850237)
        ·
          refine ⟨24019598044748763528318839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64052261452663369408850237 24019598044748763528318839)
          ·
            refine ⟨36029397067123145292478259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24019598044748763528318839 36029397067123145292478259)
            ·
              refine ⟨54044095600684717938717389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36029397067123145292478259 54044095600684717938717389)
              ·
                refine ⟨20266535850256769227019021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54044095600684717938717389 20266535850256769227019021)
                ·
                  refine ⟨7599950943846288460132133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20266535850256769227019021 7599950943846288460132133)
                  ·
                    refine ⟨1424990801971179086274775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7599950943846288460132133 1424990801971179086274775)
                    ·
                      rfl

theorem cell23_8325479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 3, 3, 4].length) (baseStart_8325479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8325479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8325479 prefixEnd_8325479 := by exact prefixLift 8325479
  have htrace : WordTrace (prefixWord ++ tailWord_8325479) baseStart_8325479 baseEnd_8325479 := by
    simpa [prefixWord, tailWord_8325479, baseEnd_8325479] using wordTrace_append hprefix tailTrace_8325479
  have hstable : (prefixWord ++ tailWord_8325479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8325479).length < 2 ^ (prefixWord ++ tailWord_8325479).sum := by decide
  have hdescent : baseEnd_8325479 < baseStart_8325479 := by decide
  rcases family_descends (prefixWord ++ tailWord_8325479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8325513 : List Nat := [1, 2, 1, 1, 6, 3, 1, 3, 1, 4]
def baseStart_8325513 : Nat := 118140960795 + 8325513 * 2 ^ 59
def prefixEnd_8325513 : Nat := 4983230072969 + 3 ^ 40 * 8325513 * 2
def baseEnd_8325513 : Nat := 1424996621418596708599723

theorem tailTrace_8325513 : CollatzResearch.WordTrace tailWord_8325513 prefixEnd_8325513 1424996621418596708599723 := by
  unfold tailWord_8325513
  simp only [CollatzResearch.WordTrace]
  refine ⟨303656405487095760263509193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202437603658063840175672795 303656405487095760263509193)
  ·
    refine ⟨227742304115321820197631895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303656405487095760263509193 227742304115321820197631895)
    ·
      refine ⟨341613456172982730296447843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227742304115321820197631895 341613456172982730296447843)
      ·
        refine ⟨512420184259474095444671765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341613456172982730296447843 512420184259474095444671765)
        ·
          refine ⟨24019696137162848223968989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 512420184259474095444671765 24019696137162848223968989)
          ·
            refine ⟨9007386051436068083988371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24019696137162848223968989 9007386051436068083988371)
            ·
              refine ⟨13511079077154102125982557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9007386051436068083988371 13511079077154102125982557)
              ·
                refine ⟨5066654653932788297243459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13511079077154102125982557 5066654653932788297243459)
                ·
                  refine ⟨7599981980899182445865189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5066654653932788297243459 7599981980899182445865189)
                  ·
                    refine ⟨1424996621418596708599723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7599981980899182445865189 1424996621418596708599723)
                    ·
                      rfl

theorem cell23_8325513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 1, 3, 1, 4].length) (baseStart_8325513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8325513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8325513 prefixEnd_8325513 := by exact prefixLift 8325513
  have htrace : WordTrace (prefixWord ++ tailWord_8325513) baseStart_8325513 baseEnd_8325513 := by
    simpa [prefixWord, tailWord_8325513, baseEnd_8325513] using wordTrace_append hprefix tailTrace_8325513
  have hstable : (prefixWord ++ tailWord_8325513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8325513).length < 2 ^ (prefixWord ++ tailWord_8325513).sum := by decide
  have hdescent : baseEnd_8325513 < baseStart_8325513 := by decide
  rcases family_descends (prefixWord ++ tailWord_8325513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8325536 : List Nat := [2, 1, 1, 4, 1, 3, 3, 1, 3, 1, 3]
def baseStart_8325536 : Nat := 118140960795 + 8325536 * 2 ^ 59
def prefixEnd_8325536 : Nat := 4983230072969 + 3 ^ 40 * 8325536 * 2
def baseEnd_8325536 : Nat := 4275001674310843535811563

theorem tailTrace_8325536 : CollatzResearch.WordTrace tailWord_8325536 prefixEnd_8325536 4275001674310843535811563 := by
  unfold tailWord_8325536
  simp only [CollatzResearch.WordTrace]
  refine ⟨151828622183006217595798231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202438162910674956794397641 151828622183006217595798231)
  ·
    refine ⟨227742933274509326393697347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151828622183006217595798231 227742933274509326393697347)
    ·
      refine ⟨341614399911763989590546021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227742933274509326393697347 341614399911763989590546021)
      ·
        refine ⟨64052699983455748048227379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 341614399911763989590546021 64052699983455748048227379)
        ·
          refine ⟨96079049975183622072341069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64052699983455748048227379 96079049975183622072341069)
          ·
            refine ⟨36029643740693858277127901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96079049975183622072341069 36029643740693858277127901)
            ·
              refine ⟨13511116402760196853922963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36029643740693858277127901 13511116402760196853922963)
              ·
                refine ⟨20266674604140295280884445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13511116402760196853922963 20266674604140295280884445)
                ·
                  refine ⟨7600002976552610730331667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20266674604140295280884445 7600002976552610730331667)
                  ·
                    refine ⟨11400004464828916095497501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7600002976552610730331667 11400004464828916095497501)
                    ·
                      refine ⟨4275001674310843535811563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11400004464828916095497501 4275001674310843535811563)
                      ·
                        rfl

theorem cell23_8325536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 3, 1, 3, 1, 3].length) (baseStart_8325536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8325536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8325536 prefixEnd_8325536 := by exact prefixLift 8325536
  have htrace : WordTrace (prefixWord ++ tailWord_8325536) baseStart_8325536 baseEnd_8325536 := by
    simpa [prefixWord, tailWord_8325536, baseEnd_8325536] using wordTrace_append hprefix tailTrace_8325536
  have hstable : (prefixWord ++ tailWord_8325536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8325536).length < 2 ^ (prefixWord ++ tailWord_8325536).sum := by decide
  have hdescent : baseEnd_8325536 < baseStart_8325536 := by decide
  rcases family_descends (prefixWord ++ tailWord_8325536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8325559 : List Nat := [1, 1, 3, 1, 3, 4, 1, 1, 3, 1, 4]
def baseStart_8325559 : Nat := 118140960795 + 8325559 * 2 ^ 59
def prefixEnd_8325559 : Nat := 4983230072969 + 3 ^ 40 * 8325559 * 2
def baseEnd_8325559 : Nat := 4275013484365896945823957

theorem tailTrace_8325559 : CollatzResearch.WordTrace tailWord_8325559 prefixEnd_8325559 4275013484365896945823957 := by
  unfold tailWord_8325559
  simp only [CollatzResearch.WordTrace]
  refine ⟨303658083244929110119683731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202438722163286073413122487 303658083244929110119683731)
  ·
    refine ⟨455487124867393665179525597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303658083244929110119683731 455487124867393665179525597)
    ·
      refine ⟨170807671825272624442322099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 455487124867393665179525597 170807671825272624442322099)
      ·
        refine ⟨256211507737908936663483149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170807671825272624442322099 256211507737908936663483149)
        ·
          refine ⟨96079315401715851248806181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 256211507737908936663483149 96079315401715851248806181)
          ·
            refine ⟨18014871637821722109151159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96079315401715851248806181 18014871637821722109151159)
            ·
              refine ⟨27022307456732583163726739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18014871637821722109151159 27022307456732583163726739)
              ·
                refine ⟨40533461185098874745590109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27022307456732583163726739 40533461185098874745590109)
                ·
                  refine ⟨15200047944412078029596291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40533461185098874745590109 15200047944412078029596291)
                  ·
                    refine ⟨22800071916618117044394437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15200047944412078029596291 22800071916618117044394437)
                    ·
                      refine ⟨4275013484365896945823957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22800071916618117044394437 4275013484365896945823957)
                      ·
                        rfl

theorem cell23_8325559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 1, 3, 1, 4].length) (baseStart_8325559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8325559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8325559 prefixEnd_8325559 := by exact prefixLift 8325559
  have htrace : WordTrace (prefixWord ++ tailWord_8325559) baseStart_8325559 baseEnd_8325559 := by
    simpa [prefixWord, tailWord_8325559, baseEnd_8325559] using wordTrace_append hprefix tailTrace_8325559
  have hstable : (prefixWord ++ tailWord_8325559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8325559).length < 2 ^ (prefixWord ++ tailWord_8325559).sum := by decide
  have hdescent : baseEnd_8325559 < baseStart_8325559 := by decide
  rcases family_descends (prefixWord ++ tailWord_8325559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8325562 : List Nat := [3, 1, 1, 1, 2, 1, 1, 4, 3, 1, 5]
def baseStart_8325562 : Nat := 118140960795 + 8325562 * 2 ^ 59
def prefixEnd_8325562 : Nat := 4983230072969 + 3 ^ 40 * 8325562 * 2
def baseEnd_8325562 : Nat := 4275015024807860434086443

theorem tailTrace_8325562 : CollatzResearch.WordTrace tailWord_8325562 prefixEnd_8325562 4275015024807860434086443 := by
  unfold tailWord_8325562
  simp only [CollatzResearch.WordTrace]
  refine ⟨75914548165979560408010735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202438795109278827754695293 75914548165979560408010735)
  ·
    refine ⟨113871822248969340612016103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75914548165979560408010735 113871822248969340612016103)
    ·
      refine ⟨170807733373454010918024155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113871822248969340612016103 170807733373454010918024155)
      ·
        refine ⟨256211600060181016377036233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170807733373454010918024155 256211600060181016377036233)
        ·
          refine ⟨192158700045135762282777175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256211600060181016377036233 192158700045135762282777175)
          ·
            refine ⟨288238050067703643424165763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192158700045135762282777175 288238050067703643424165763)
            ·
              refine ⟨432357075101555465136248645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 288238050067703643424165763 432357075101555465136248645)
              ·
                refine ⟨81066951581541649713046621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 432357075101555465136248645 81066951581541649713046621)
                ·
                  refine ⟨30400106843078118642392483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81066951581541649713046621 30400106843078118642392483)
                  ·
                    refine ⟨45600160264617177963588725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30400106843078118642392483 45600160264617177963588725)
                    ·
                      refine ⟨4275015024807860434086443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45600160264617177963588725 4275015024807860434086443)
                      ·
                        rfl

theorem cell23_8325562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 4, 3, 1, 5].length) (baseStart_8325562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8325562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8325562 prefixEnd_8325562 := by exact prefixLift 8325562
  have htrace : WordTrace (prefixWord ++ tailWord_8325562) baseStart_8325562 baseEnd_8325562 := by
    simpa [prefixWord, tailWord_8325562, baseEnd_8325562] using wordTrace_append hprefix tailTrace_8325562
  have hstable : (prefixWord ++ tailWord_8325562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8325562).length < 2 ^ (prefixWord ++ tailWord_8325562).sum := by decide
  have hdescent : baseEnd_8325562 < baseStart_8325562 := by decide
  rcases family_descends (prefixWord ++ tailWord_8325562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8325599 : List Nat := [1, 1, 2, 3, 3, 4, 1, 8]
def baseStart_8325599 : Nat := 118140960795 + 8325599 * 2 ^ 59
def prefixEnd_8325599 : Nat := 4983230072969 + 3 ^ 40 * 8325599 * 2
def baseEnd_8325599 : Nat := 158334593466373214419399

theorem tailTrace_8325599 : CollatzResearch.WordTrace tailWord_8325599 prefixEnd_8325599 158334593466373214419399 := by
  unfold tailWord_8325599
  simp only [CollatzResearch.WordTrace]
  refine ⟨303659542164784196951139851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202439694776522797967426567 303659542164784196951139851)
  ·
    refine ⟨455489313247176295426709777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303659542164784196951139851 455489313247176295426709777)
    ·
      refine ⟨341616984935382221570032333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 455489313247176295426709777 341616984935382221570032333)
      ·
        refine ⟨128106369350768333088762125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 341616984935382221570032333 128106369350768333088762125)
        ·
          refine ⟨48039888506538124908285797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128106369350768333088762125 48039888506538124908285797)
          ·
            refine ⟨9007479094975898420303587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48039888506538124908285797 9007479094975898420303587)
            ·
              refine ⟨13511218642463847630455381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9007479094975898420303587 13511218642463847630455381)
              ·
                refine ⟨158334593466373214419399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13511218642463847630455381 158334593466373214419399)
                ·
                  rfl

theorem cell23_8325599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 1, 8].length) (baseStart_8325599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8325599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8325599 prefixEnd_8325599 := by exact prefixLift 8325599
  have htrace : WordTrace (prefixWord ++ tailWord_8325599) baseStart_8325599 baseEnd_8325599 := by
    simpa [prefixWord, tailWord_8325599, baseEnd_8325599] using wordTrace_append hprefix tailTrace_8325599
  have hstable : (prefixWord ++ tailWord_8325599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8325599).length < 2 ^ (prefixWord ++ tailWord_8325599).sum := by decide
  have hdescent : baseEnd_8325599 < baseStart_8325599 := by decide
  rcases family_descends (prefixWord ++ tailWord_8325599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8325612 : List Nat := [2, 2, 1, 1, 2, 1, 3, 2, 2, 7]
def baseStart_8325612 : Nat := 118140960795 + 8325612 * 2 ^ 59
def prefixEnd_8325612 : Nat := 4983230072969 + 3 ^ 40 * 8325612 * 2
def baseEnd_8325612 : Nat := 1425013566280195079487071

theorem tailTrace_8325612 : CollatzResearch.WordTrace tailWord_8325612 prefixEnd_8325612 1425013566280195079487071 := by
  unfold tailWord_8325612
  simp only [CollatzResearch.WordTrace]
  refine ⟨151830008156868550085681545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202440010875824733447575393 151830008156868550085681545)
  ·
    refine ⟨113872506117651412564261159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151830008156868550085681545 113872506117651412564261159)
    ·
      refine ⟨170808759176477118846391739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113872506117651412564261159 170808759176477118846391739)
      ·
        refine ⟨256213138764715678269587609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170808759176477118846391739 256213138764715678269587609)
        ·
          refine ⟨192159854073536758702190707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256213138764715678269587609 192159854073536758702190707)
          ·
            refine ⟨288239781110305138053286061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192159854073536758702190707 288239781110305138053286061)
            ·
              refine ⟨108089917916364426769982273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 288239781110305138053286061 108089917916364426769982273)
              ·
                refine ⟨81067438437273320077486705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108089917916364426769982273 81067438437273320077486705)
                ·
                  refine ⟨60800578827954990058115029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81067438437273320077486705 60800578827954990058115029)
                  ·
                    refine ⟨1425013566280195079487071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60800578827954990058115029 1425013566280195079487071)
                    ·
                      rfl

theorem cell23_8325612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 7].length) (baseStart_8325612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8325612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8325612 prefixEnd_8325612 := by exact prefixLift 8325612
  have htrace : WordTrace (prefixWord ++ tailWord_8325612) baseStart_8325612 baseEnd_8325612 := by
    simpa [prefixWord, tailWord_8325612, baseEnd_8325612] using wordTrace_append hprefix tailTrace_8325612
  have hstable : (prefixWord ++ tailWord_8325612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8325612).length < 2 ^ (prefixWord ++ tailWord_8325612).sum := by decide
  have hdescent : baseEnd_8325612 < baseStart_8325612 := by decide
  rcases family_descends (prefixWord ++ tailWord_8325612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8325643 : List Nat := [1, 1, 1, 1, 7, 1, 3, 2, 2, 1, 3]
def baseStart_8325643 : Nat := 118140960795 + 8325643 * 2 ^ 59
def prefixEnd_8325643 : Nat := 4983230072969 + 3 ^ 40 * 8325643 * 2
def baseEnd_8325643 : Nat := 4275056616740874617173571

theorem tailTrace_8325643 : CollatzResearch.WordTrace tailWord_8325643 prefixEnd_8325643 4275056616740874617173571 := by
  unfold tailWord_8325643
  simp only [CollatzResearch.WordTrace]
  refine ⟨303661146976624792465741583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202440764651083194977161055 303661146976624792465741583)
  ·
    refine ⟨455491720464937188698612375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303661146976624792465741583 455491720464937188698612375)
    ·
      refine ⟨683237580697405783047918563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 455491720464937188698612375 683237580697405783047918563)
      ·
        refine ⟨1024856371046108674571877845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 683237580697405783047918563 1024856371046108674571877845)
        ·
          refine ⟨24020071196393172060278387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 1024856371046108674571877845 24020071196393172060278387)
          ·
            refine ⟨36030106794589758090417581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24020071196393172060278387 36030106794589758090417581)
            ·
              refine ⟨13511290047971159283906593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36030106794589758090417581 13511290047971159283906593)
              ·
                refine ⟨10133467535978369462929945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13511290047971159283906593 10133467535978369462929945)
                ·
                  refine ⟨7600100651983777097197459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10133467535978369462929945 7600100651983777097197459)
                  ·
                    refine ⟨11400150977975665645796189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7600100651983777097197459 11400150977975665645796189)
                    ·
                      refine ⟨4275056616740874617173571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11400150977975665645796189 4275056616740874617173571)
                      ·
                        rfl

theorem cell23_8325643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 3, 2, 2, 1, 3].length) (baseStart_8325643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8325643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8325643 prefixEnd_8325643 := by exact prefixLift 8325643
  have htrace : WordTrace (prefixWord ++ tailWord_8325643) baseStart_8325643 baseEnd_8325643 := by
    simpa [prefixWord, tailWord_8325643, baseEnd_8325643] using wordTrace_append hprefix tailTrace_8325643
  have hstable : (prefixWord ++ tailWord_8325643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8325643).length < 2 ^ (prefixWord ++ tailWord_8325643).sum := by decide
  have hdescent : baseEnd_8325643 < baseStart_8325643 := by decide
  rcases family_descends (prefixWord ++ tailWord_8325643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8325660 : List Nat := [2, 2, 3, 1, 2, 3, 3, 1, 2, 1, 3]
def baseStart_8325660 : Nat := 118140960795 + 8325660 * 2 ^ 59
def prefixEnd_8325660 : Nat := 4983230072969 + 3 ^ 40 * 8325660 * 2
def baseEnd_8325660 : Nat := 4275065345912001050660993

theorem tailTrace_8325660 : CollatzResearch.WordTrace tailWord_8325660 prefixEnd_8325660 4275065345912001050660993 := by
  unfold tailWord_8325660
  simp only [CollatzResearch.WordTrace]
  refine ⟨151830883508781602184555217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202441178011708802912740289 151830883508781602184555217)
  ·
    refine ⟨113873162631586201638416413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151830883508781602184555217 113873162631586201638416413)
    ·
      refine ⟨42702435986844825614406155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113873162631586201638416413 42702435986844825614406155)
      ·
        refine ⟨64053653980267238421609233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42702435986844825614406155 64053653980267238421609233)
        ·
          refine ⟨48040240485200428816206925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64053653980267238421609233 48040240485200428816206925)
          ·
            refine ⟨18015090181950160806077597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48040240485200428816206925 18015090181950160806077597)
            ·
              refine ⟨6755658818231310302279099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18015090181950160806077597 6755658818231310302279099)
              ·
                refine ⟨10133488227346965453418649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6755658818231310302279099 10133488227346965453418649)
                ·
                  refine ⟨7600116170510224090063987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10133488227346965453418649 7600116170510224090063987)
                  ·
                    refine ⟨11400174255765336135095981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7600116170510224090063987 11400174255765336135095981)
                    ·
                      refine ⟨4275065345912001050660993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11400174255765336135095981 4275065345912001050660993)
                      ·
                        rfl

theorem cell23_8325660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 3, 1, 2, 1, 3].length) (baseStart_8325660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8325660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8325660 prefixEnd_8325660 := by exact prefixLift 8325660
  have htrace : WordTrace (prefixWord ++ tailWord_8325660) baseStart_8325660 baseEnd_8325660 := by
    simpa [prefixWord, tailWord_8325660, baseEnd_8325660] using wordTrace_append hprefix tailTrace_8325660
  have hstable : (prefixWord ++ tailWord_8325660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8325660).length < 2 ^ (prefixWord ++ tailWord_8325660).sum := by decide
  have hdescent : baseEnd_8325660 < baseStart_8325660 := by decide
  rcases family_descends (prefixWord ++ tailWord_8325660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8325669 : List Nat := [1, 3, 1, 2, 2, 1, 2, 2, 2, 4, 3]
def baseStart_8325669 : Nat := 118140960795 + 8325669 * 2 ^ 59
def prefixEnd_8325669 : Nat := 4983230072969 + 3 ^ 40 * 8325669 * 2
def baseEnd_8325669 : Nat := 4275069967237891515448451

theorem tailTrace_8325669 : CollatzResearch.WordTrace tailWord_8325669 prefixEnd_8325669 4275069967237891515448451 := by
  unfold tailWord_8325669
  simp only [CollatzResearch.WordTrace]
  refine ⟨303662095274530598906188061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202441396849687065937458707 303662095274530598906188061)
  ·
    refine ⟨113873285727948974589820523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 303662095274530598906188061 113873285727948974589820523)
    ·
      refine ⟨170809928591923461884730785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113873285727948974589820523 170809928591923461884730785)
      ·
        refine ⟨128107446443942596413548089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170809928591923461884730785 128107446443942596413548089)
        ·
          refine ⟨96080584832956947310161067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128107446443942596413548089 96080584832956947310161067)
          ·
            refine ⟨144120877249435420965241601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96080584832956947310161067 144120877249435420965241601)
            ·
              refine ⟨108090657937076565723931201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144120877249435420965241601 108090657937076565723931201)
              ·
                refine ⟨81067993452807424292948401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108090657937076565723931201 81067993452807424292948401)
                ·
                  refine ⟨60800995089605568219711301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81067993452807424292948401 60800995089605568219711301)
                  ·
                    refine ⟨11400186579301044041195869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60800995089605568219711301 11400186579301044041195869)
                    ·
                      refine ⟨4275069967237891515448451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11400186579301044041195869 4275069967237891515448451)
                      ·
                        rfl

theorem cell23_8325669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 2, 2, 4, 3].length) (baseStart_8325669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8325669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8325669 prefixEnd_8325669 := by exact prefixLift 8325669
  have htrace : WordTrace (prefixWord ++ tailWord_8325669) baseStart_8325669 baseEnd_8325669 := by
    simpa [prefixWord, tailWord_8325669, baseEnd_8325669] using wordTrace_append hprefix tailTrace_8325669
  have hstable : (prefixWord ++ tailWord_8325669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8325669).length < 2 ^ (prefixWord ++ tailWord_8325669).sum := by decide
  have hdescent : baseEnd_8325669 < baseStart_8325669 := by decide
  rcases family_descends (prefixWord ++ tailWord_8325669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8325686 : List Nat := [5, 1, 2, 1, 2, 1, 1, 1, 1, 3, 5]
def baseStart_8325686 : Nat := 118140960795 + 8325686 * 2 ^ 59
def prefixEnd_8325686 : Nat := 4983230072969 + 3 ^ 40 * 8325686 * 2
def baseEnd_8325686 : Nat := 4275078696409017948935873

theorem tailTrace_8325686 : CollatzResearch.WordTrace tailWord_8325686 prefixEnd_8325686 4275078696409017948935873 := by
  unfold tailWord_8325686
  simp only [CollatzResearch.WordTrace]
  refine ⟨18978919707216813175597307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 202441810210312673873037941 18978919707216813175597307)
  ·
    refine ⟨28468379560825219763395961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18978919707216813175597307 28468379560825219763395961)
    ·
      refine ⟨21351284670618914822546971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28468379560825219763395961 21351284670618914822546971)
      ·
        refine ⟨32026927005928372233820457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21351284670618914822546971 32026927005928372233820457)
        ·
          refine ⟨24020195254446279175365343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32026927005928372233820457 24020195254446279175365343)
          ·
            refine ⟨36030292881669418763048015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24020195254446279175365343 36030292881669418763048015)
            ·
              refine ⟨54045439322504128144572023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36030292881669418763048015 54045439322504128144572023)
              ·
                refine ⟨81068158983756192216858035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54045439322504128144572023 81068158983756192216858035)
                ·
                  refine ⟨121602238475634288325287053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81068158983756192216858035 121602238475634288325287053)
                  ·
                    refine ⟨45600839428362858121982645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 121602238475634288325287053 45600839428362858121982645)
                    ·
                      refine ⟨4275078696409017948935873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45600839428362858121982645 4275078696409017948935873)
                      ·
                        rfl

theorem cell23_8325686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_8325686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8325686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8325686 prefixEnd_8325686 := by exact prefixLift 8325686
  have htrace : WordTrace (prefixWord ++ tailWord_8325686) baseStart_8325686 baseEnd_8325686 := by
    simpa [prefixWord, tailWord_8325686, baseEnd_8325686] using wordTrace_append hprefix tailTrace_8325686
  have hstable : (prefixWord ++ tailWord_8325686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8325686).length < 2 ^ (prefixWord ++ tailWord_8325686).sum := by decide
  have hdescent : baseEnd_8325686 < baseStart_8325686 := by decide
  rcases family_descends (prefixWord ++ tailWord_8325686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8325699 : List Nat := [1, 1, 1, 3, 1, 2, 1, 3, 4, 3, 3]
def baseStart_8325699 : Nat := 118140960795 + 8325699 * 2 ^ 59
def prefixEnd_8325699 : Nat := 4983230072969 + 3 ^ 40 * 8325699 * 2
def baseEnd_8325699 : Nat := 4275085371657526398073313

theorem tailTrace_8325699 : CollatzResearch.WordTrace tailWord_8325699 prefixEnd_8325699 4275085371657526398073313 := by
  unfold tailWord_8325699
  simp only [CollatzResearch.WordTrace]
  refine ⟨303663189464421914029780151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202442126309614609353186767 303663189464421914029780151)
  ·
    refine ⟨455494784196632871044670227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303663189464421914029780151 455494784196632871044670227)
    ·
      refine ⟨683242176294949306567005341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 455494784196632871044670227 683242176294949306567005341)
      ·
        refine ⟨256215816110605989962627003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 683242176294949306567005341 256215816110605989962627003)
        ·
          refine ⟨384323724165908984943940505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256215816110605989962627003 384323724165908984943940505)
          ·
            refine ⟨288242793124431738707955379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 384323724165908984943940505 288242793124431738707955379)
            ·
              refine ⟨432364189686647608061933069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 288242793124431738707955379 432364189686647608061933069)
              ·
                refine ⟨162136571132492853023224901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 432364189686647608061933069 162136571132492853023224901)
                ·
                  refine ⟨30400607087342409941854669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 162136571132492853023224901 30400607087342409941854669)
                  ·
                    refine ⟨11400227657753403728195501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30400607087342409941854669 11400227657753403728195501)
                    ·
                      refine ⟨4275085371657526398073313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11400227657753403728195501 4275085371657526398073313)
                      ·
                        rfl

theorem cell23_8325699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 4, 3, 3].length) (baseStart_8325699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8325699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8325699 prefixEnd_8325699 := by exact prefixLift 8325699
  have htrace : WordTrace (prefixWord ++ tailWord_8325699) baseStart_8325699 baseEnd_8325699 := by
    simpa [prefixWord, tailWord_8325699, baseEnd_8325699] using wordTrace_append hprefix tailTrace_8325699
  have hstable : (prefixWord ++ tailWord_8325699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8325699).length < 2 ^ (prefixWord ++ tailWord_8325699).sum := by decide
  have hdescent : baseEnd_8325699 < baseStart_8325699 := by decide
  rcases family_descends (prefixWord ++ tailWord_8325699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8325706 : List Nat := [3, 1, 2, 1, 1, 6, 1, 1, 7]
def baseStart_8325706 : Nat := 118140960795 + 8325706 * 2 ^ 59
def prefixEnd_8325706 : Nat := 4983230072969 + 3 ^ 40 * 8325706 * 2
def baseEnd_8325706 : Nat := 475009885113567541187309

theorem tailTrace_8325706 : CollatzResearch.WordTrace tailWord_8325706 prefixEnd_8325706 475009885113567541187309 := by
  unfold tailWord_8325706
  simp only [CollatzResearch.WordTrace]
  refine ⟨75915861193849138556321243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202442296516931036150189981 75915861193849138556321243)
  ·
    refine ⟨113873791790773707834481865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75915861193849138556321243 113873791790773707834481865)
    ·
      refine ⟨85405343843080280875861399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113873791790773707834481865 85405343843080280875861399)
      ·
        refine ⟨128108015764620421313792099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85405343843080280875861399 128108015764620421313792099)
        ·
          refine ⟨192162023646930631970688149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128108015764620421313792099 192162023646930631970688149)
          ·
            refine ⟨9007594858449873373626007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 192162023646930631970688149 9007594858449873373626007)
            ·
              refine ⟨13511392287674810060439011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9007594858449873373626007 13511392287674810060439011)
              ·
                refine ⟨20267088431512215090658517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13511392287674810060439011 20267088431512215090658517)
                ·
                  refine ⟨475009885113567541187309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20267088431512215090658517 475009885113567541187309)
                  ·
                    rfl

theorem cell23_8325706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 1, 1, 7].length) (baseStart_8325706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8325706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8325706 prefixEnd_8325706 := by exact prefixLift 8325706
  have htrace : WordTrace (prefixWord ++ tailWord_8325706) baseStart_8325706 baseEnd_8325706 := by
    simpa [prefixWord, tailWord_8325706, baseEnd_8325706] using wordTrace_append hprefix tailTrace_8325706
  have hstable : (prefixWord ++ tailWord_8325706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8325706).length < 2 ^ (prefixWord ++ tailWord_8325706).sum := by decide
  have hdescent : baseEnd_8325706 < baseStart_8325706 := by decide
  rcases family_descends (prefixWord ++ tailWord_8325706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8325719 : List Nat := [1, 1, 3, 2, 2, 2, 1, 2, 4, 5]
def baseStart_8325719 : Nat := 118140960795 + 8325719 * 2 ^ 59
def prefixEnd_8325719 : Nat := 4983230072969 + 3 ^ 40 * 8325719 * 2
def baseEnd_8325719 : Nat := 1425031880423538773274407

theorem tailTrace_8325719 : CollatzResearch.WordTrace tailWord_8325719 prefixEnd_8325719 1425031880423538773274407 := by
  unfold tailWord_8325719
  simp only [CollatzResearch.WordTrace]
  refine ⟨303663918924349457445508211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202442612616232971630338807 303663918924349457445508211)
  ·
    refine ⟨455495878386524186168262317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303663918924349457445508211 455495878386524186168262317)
    ·
      refine ⟨170810954394946569813098369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 455495878386524186168262317 170810954394946569813098369)
      ·
        refine ⟨128108215796209927359823777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170810954394946569813098369 128108215796209927359823777)
        ·
          refine ⟨96081161847157445519867833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128108215796209927359823777 96081161847157445519867833)
          ·
            refine ⟨72060871385368084139900875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96081161847157445519867833 72060871385368084139900875)
            ·
              refine ⟨108091307078052126209851313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72060871385368084139900875 108091307078052126209851313)
              ·
                refine ⟨81068480308539094657388485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108091307078052126209851313 81068480308539094657388485)
                ·
                  refine ⟨15200340057851080248260341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81068480308539094657388485 15200340057851080248260341)
                  ·
                    refine ⟨1425031880423538773274407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15200340057851080248260341 1425031880423538773274407)
                    ·
                      rfl

theorem cell23_8325719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 2, 4, 5].length) (baseStart_8325719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8325719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8325719 prefixEnd_8325719 := by exact prefixLift 8325719
  have htrace : WordTrace (prefixWord ++ tailWord_8325719) baseStart_8325719 baseEnd_8325719 := by
    simpa [prefixWord, tailWord_8325719, baseEnd_8325719] using wordTrace_append hprefix tailTrace_8325719
  have hstable : (prefixWord ++ tailWord_8325719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8325719).length < 2 ^ (prefixWord ++ tailWord_8325719).sum := by decide
  have hdescent : baseEnd_8325719 < baseStart_8325719 := by decide
  rcases family_descends (prefixWord ++ tailWord_8325719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8325756 : List Nat := [2, 2, 2, 1, 1, 2, 4, 2, 2, 1, 4]
def baseStart_8325756 : Nat := 118140960795 + 8325756 * 2 ^ 59
def prefixEnd_8325756 : Nat := 4983230072969 + 3 ^ 40 * 8325756 * 2
def baseEnd_8325756 : Nat := 4275114640054832675060551

theorem tailTrace_8325756 : CollatzResearch.WordTrace tailWord_8325756 prefixEnd_8325756 4275114640054832675060551 := by
  unfold tailWord_8325756
  simp only [CollatzResearch.WordTrace]
  refine ⟨151832634212607706382302561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202443512283476941843070081 151832634212607706382302561)
  ·
    refine ⟨113874475659455779786726921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151832634212607706382302561 113874475659455779786726921)
    ·
      refine ⟨85405856744591834840045191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113874475659455779786726921 85405856744591834840045191)
      ·
        refine ⟨128108785116887752260067787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85405856744591834840045191 128108785116887752260067787)
        ·
          refine ⟨192163177675331628390101681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128108785116887752260067787 192163177675331628390101681)
          ·
            refine ⟨144122383256498721292576261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192163177675331628390101681 144122383256498721292576261)
            ·
              refine ⟨27022946860593510242358049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 144122383256498721292576261 27022946860593510242358049)
              ·
                refine ⟨20267210145445132681768537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27022946860593510242358049 20267210145445132681768537)
                ·
                  refine ⟨15200407609083849511326403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20267210145445132681768537 15200407609083849511326403)
                  ·
                    refine ⟨22800611413625774266989605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15200407609083849511326403 22800611413625774266989605)
                    ·
                      refine ⟨4275114640054832675060551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22800611413625774266989605 4275114640054832675060551)
                      ·
                        rfl

theorem cell23_8325756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 2, 2, 1, 4].length) (baseStart_8325756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8325756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8325756 prefixEnd_8325756 := by exact prefixLift 8325756
  have htrace : WordTrace (prefixWord ++ tailWord_8325756) baseStart_8325756 baseEnd_8325756 := by
    simpa [prefixWord, tailWord_8325756, baseEnd_8325756] using wordTrace_append hprefix tailTrace_8325756
  have hstable : (prefixWord ++ tailWord_8325756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8325756).length < 2 ^ (prefixWord ++ tailWord_8325756).sum := by decide
  have hdescent : baseEnd_8325756 < baseStart_8325756 := by decide
  rcases family_descends (prefixWord ++ tailWord_8325756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8325757 : List Nat := [1, 4, 1, 1, 6, 1, 2, 2, 5]
def baseStart_8325757 : Nat := 118140960795 + 8325757 * 2 ^ 59
def prefixEnd_8325757 : Nat := 4983230072969 + 3 ^ 40 * 8325757 * 2
def baseEnd_8325757 : Nat := 475012794837276352349783

theorem tailTrace_8325757 : CollatzResearch.WordTrace tailWord_8325757 prefixEnd_8325757 475012794837276352349783 := by
  unfold tailWord_8325757
  simp only [CollatzResearch.WordTrace]
  refine ⟨303665304898211789935391525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202443536598807859956927683 303665304898211789935391525)
  ·
    refine ⟨56937244668414710612885911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 303665304898211789935391525 56937244668414710612885911)
    ·
      refine ⟨85405867002622065919328867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56937244668414710612885911 85405867002622065919328867)
      ·
        refine ⟨128108800503933098878993301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85405867002622065919328867 128108800503933098878993301)
        ·
          refine ⟨6005100023621864009952811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 128108800503933098878993301 6005100023621864009952811)
          ·
            refine ⟨9007650035432796014929217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6005100023621864009952811 9007650035432796014929217)
            ·
              refine ⟨6755737526574597011196913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9007650035432796014929217 6755737526574597011196913)
              ·
                refine ⟨5066803144930947758397685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6755737526574597011196913 5066803144930947758397685)
                ·
                  refine ⟨475012794837276352349783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5066803144930947758397685 475012794837276352349783)
                  ·
                    rfl

theorem cell23_8325757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 2, 2, 5].length) (baseStart_8325757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8325757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8325757 prefixEnd_8325757 := by exact prefixLift 8325757
  have htrace : WordTrace (prefixWord ++ tailWord_8325757) baseStart_8325757 baseEnd_8325757 := by
    simpa [prefixWord, tailWord_8325757, baseEnd_8325757] using wordTrace_append hprefix tailTrace_8325757
  have hstable : (prefixWord ++ tailWord_8325757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8325757).length < 2 ^ (prefixWord ++ tailWord_8325757).sum := by decide
  have hdescent : baseEnd_8325757 < baseStart_8325757 := by decide
  rcases family_descends (prefixWord ++ tailWord_8325757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8325769 : List Nat := [1, 2, 1, 1, 4, 1, 1, 2, 2, 4, 4]
def baseStart_8325769 : Nat := 118140960795 + 8325769 * 2 ^ 59
def prefixEnd_8325769 : Nat := 4983230072969 + 3 ^ 40 * 8325769 * 2
def baseEnd_8325769 : Nat := 4275121315303341124197991

theorem tailTrace_8325769 : CollatzResearch.WordTrace tailWord_8325769 prefixEnd_8325769 4275121315303341124197991 := by
  unfold tailWord_8325769
  simp only [CollatzResearch.WordTrace]
  refine ⟨303665742574168315984828361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202443828382778877323218907 303665742574168315984828361)
  ·
    refine ⟨227749306930626236988621271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303665742574168315984828361 227749306930626236988621271)
    ·
      refine ⟨341623960395939355482931907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227749306930626236988621271 341623960395939355482931907)
      ·
        refine ⟨512435940593909033224397861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341623960395939355482931907 512435940593909033224397861)
        ·
          refine ⟨96081738861357943729574599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 512435940593909033224397861 96081738861357943729574599)
          ·
            refine ⟨144122608292036915594361899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96081738861357943729574599 144122608292036915594361899)
            ·
              refine ⟨216183912438055373391542849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144122608292036915594361899 216183912438055373391542849)
              ·
                refine ⟨162137934328541530043657137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 216183912438055373391542849 162137934328541530043657137)
                ·
                  refine ⟨121603450746406147532742853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 162137934328541530043657137 121603450746406147532742853)
                  ·
                    refine ⟨22800647014951152662389285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 121603450746406147532742853 22800647014951152662389285)
                    ·
                      refine ⟨4275121315303341124197991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22800647014951152662389285 4275121315303341124197991)
                      ·
                        rfl

theorem cell23_8325769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 2, 4, 4].length) (baseStart_8325769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8325769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8325769 prefixEnd_8325769 := by exact prefixLift 8325769
  have htrace : WordTrace (prefixWord ++ tailWord_8325769) baseStart_8325769 baseEnd_8325769 := by
    simpa [prefixWord, tailWord_8325769, baseEnd_8325769] using wordTrace_append hprefix tailTrace_8325769
  have hstable : (prefixWord ++ tailWord_8325769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8325769).length < 2 ^ (prefixWord ++ tailWord_8325769).sum := by decide
  have hdescent : baseEnd_8325769 < baseStart_8325769 := by decide
  rcases family_descends (prefixWord ++ tailWord_8325769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8325793 : List Nat := [1, 2, 3, 3, 3, 1, 1, 1, 1, 4, 3]
def baseStart_8325793 : Nat := 118140960795 + 8325793 * 2 ^ 59
def prefixEnd_8325793 : Nat := 4983230072969 + 3 ^ 40 * 8325793 * 2
def baseEnd_8325793 : Nat := 4275133638839049030297881

theorem tailTrace_8325793 : CollatzResearch.WordTrace tailWord_8325793 prefixEnd_8325793 4275133638839049030297881 := by
  unfold tailWord_8325793
  simp only [CollatzResearch.WordTrace]
  refine ⟨303666617926081368083702033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202444411950720912055801355 303666617926081368083702033)
  ·
    refine ⟨227749963444561026062776525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303666617926081368083702033 227749963444561026062776525)
    ·
      refine ⟨85406236291710384773541197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227749963444561026062776525 85406236291710384773541197)
      ·
        refine ⟨32027338609391394290077949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85406236291710384773541197 32027338609391394290077949)
        ·
          refine ⟨12010251978521772858779231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32027338609391394290077949 12010251978521772858779231)
          ·
            refine ⟨18015377967782659288168847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12010251978521772858779231 18015377967782659288168847)
            ·
              refine ⟨27023066951673988932253271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18015377967782659288168847 27023066951673988932253271)
              ·
                refine ⟨40534600427510983398379907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27023066951673988932253271 40534600427510983398379907)
                ·
                  refine ⟨60801900641266475097569861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40534600427510983398379907 60801900641266475097569861)
                  ·
                    refine ⟨11400356370237464080794349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60801900641266475097569861 11400356370237464080794349)
                    ·
                      refine ⟨4275133638839049030297881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11400356370237464080794349 4275133638839049030297881)
                      ·
                        rfl

theorem cell23_8325793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 1, 1, 4, 3].length) (baseStart_8325793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8325793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8325793 prefixEnd_8325793 := by exact prefixLift 8325793
  have htrace : WordTrace (prefixWord ++ tailWord_8325793) baseStart_8325793 baseEnd_8325793 := by
    simpa [prefixWord, tailWord_8325793, baseEnd_8325793] using wordTrace_append hprefix tailTrace_8325793
  have hstable : (prefixWord ++ tailWord_8325793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8325793).length < 2 ^ (prefixWord ++ tailWord_8325793).sum := by decide
  have hdescent : baseEnd_8325793 < baseStart_8325793 := by decide
  rcases family_descends (prefixWord ++ tailWord_8325793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8325813 : List Nat := [1, 3, 3, 3, 1, 1, 3, 2, 6]
def baseStart_8325813 : Nat := 118140960795 + 8325813 * 2 ^ 59
def prefixEnd_8325813 : Nat := 4983230072969 + 3 ^ 40 * 8325813 * 2
def baseEnd_8325813 : Nat := 475015989828015439116421

theorem tailTrace_8325813 : CollatzResearch.WordTrace tailWord_8325813 prefixEnd_8325813 475015989828015439116421 := by
  unfold tailWord_8325813
  simp only [CollatzResearch.WordTrace]
  refine ⟨303667347386008911499430093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202444898257339274332953395 303667347386008911499430093)
  ·
    refine ⟨113875255269753341812286285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 303667347386008911499430093 113875255269753341812286285)
    ·
      refine ⟨42703220726157503179607357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113875255269753341812286285 42703220726157503179607357)
      ·
        refine ⟨16013707772309063692352759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42703220726157503179607357 16013707772309063692352759)
        ·
          refine ⟨24020561658463595538529139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16013707772309063692352759 24020561658463595538529139)
          ·
            refine ⟨36030842487695393307793709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24020561658463595538529139 36030842487695393307793709)
            ·
              refine ⟨13511565932885772490422641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36030842487695393307793709 13511565932885772490422641)
              ·
                refine ⟨10133674449664329367816981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13511565932885772490422641 10133674449664329367816981)
                ·
                  refine ⟨475015989828015439116421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10133674449664329367816981 475015989828015439116421)
                  ·
                    rfl

theorem cell23_8325813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 3, 2, 6].length) (baseStart_8325813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8325813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8325813 prefixEnd_8325813 := by exact prefixLift 8325813
  have htrace : WordTrace (prefixWord ++ tailWord_8325813) baseStart_8325813 baseEnd_8325813 := by
    simpa [prefixWord, tailWord_8325813, baseEnd_8325813] using wordTrace_append hprefix tailTrace_8325813
  have hstable : (prefixWord ++ tailWord_8325813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8325813).length < 2 ^ (prefixWord ++ tailWord_8325813).sum := by decide
  have hdescent : baseEnd_8325813 < baseStart_8325813 := by decide
  rcases family_descends (prefixWord ++ tailWord_8325813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8325823 : List Nat := [1, 1, 2, 2, 2, 4, 1, 3, 3, 1, 3]
def baseStart_8325823 : Nat := 118140960795 + 8325823 * 2 ^ 59
def prefixEnd_8325823 : Nat := 4983230072969 + 3 ^ 40 * 8325823 * 2
def baseEnd_8325823 : Nat := 4275149043258683912922743

theorem tailTrace_8325823 : CollatzResearch.WordTrace tailWord_8325823 prefixEnd_8325823 4275149043258683912922743 := by
  unfold tailWord_8325823
  simp only [CollatzResearch.WordTrace]
  refine ⟨303667712115972683207294123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202445141410648455471529415 303667712115972683207294123)
  ·
    refine ⟨455501568173959024810941185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303667712115972683207294123 455501568173959024810941185)
    ·
      refine ⟨341626176130469268608205889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 455501568173959024810941185 341626176130469268608205889)
      ·
        refine ⟨256219632097851951456154417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 341626176130469268608205889 256219632097851951456154417)
        ·
          refine ⟨192164724073388963592115813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256219632097851951456154417 192164724073388963592115813)
          ·
            refine ⟨36030885763760430673521715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 192164724073388963592115813 36030885763760430673521715)
            ·
              refine ⟨54046328645640646010282573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36030885763760430673521715 54046328645640646010282573)
              ·
                refine ⟨20267373242115242253855965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54046328645640646010282573 20267373242115242253855965)
                ·
                  refine ⟨7600264965793215845195987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20267373242115242253855965 7600264965793215845195987)
                  ·
                    refine ⟨11400397448689823767793981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7600264965793215845195987 11400397448689823767793981)
                    ·
                      refine ⟨4275149043258683912922743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11400397448689823767793981 4275149043258683912922743)
                      ·
                        rfl

theorem cell23_8325823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 3, 3, 1, 3].length) (baseStart_8325823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8325823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8325823 prefixEnd_8325823 := by exact prefixLift 8325823
  have htrace : WordTrace (prefixWord ++ tailWord_8325823) baseStart_8325823 baseEnd_8325823 := by
    simpa [prefixWord, tailWord_8325823, baseEnd_8325823] using wordTrace_append hprefix tailTrace_8325823
  have hstable : (prefixWord ++ tailWord_8325823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8325823).length < 2 ^ (prefixWord ++ tailWord_8325823).sum := by decide
  have hdescent : baseEnd_8325823 < baseStart_8325823 := by decide
  rcases family_descends (prefixWord ++ tailWord_8325823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8325857 : List Nat := [1, 2, 3, 1, 4, 1, 3, 3, 1, 1, 3]
def baseStart_8325857 : Nat := 118140960795 + 8325857 * 2 ^ 59
def prefixEnd_8325857 : Nat := 4983230072969 + 3 ^ 40 * 8325857 * 2
def baseEnd_8325857 : Nat := 4275166501600936779897587

theorem tailTrace_8325857 : CollatzResearch.WordTrace tailWord_8325857 prefixEnd_8325857 4275166501600936779897587 := by
  unfold tailWord_8325857
  simp only [CollatzResearch.WordTrace]
  refine ⟨303668952197849507014031825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202445968131899671342687883 303668952197849507014031825)
  ·
    refine ⟨227751714148387130260523869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303668952197849507014031825 227751714148387130260523869)
    ·
      refine ⟨85406892805645173847696451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227751714148387130260523869 85406892805645173847696451)
      ·
        refine ⟨128110339208467760771544677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85406892805645173847696451 128110339208467760771544677)
        ·
          refine ⟨24020688601587705144664627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128110339208467760771544677 24020688601587705144664627)
          ·
            refine ⟨36031032902381557716996941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24020688601587705144664627 36031032902381557716996941)
            ·
              refine ⟨13511637338393084143873853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36031032902381557716996941 13511637338393084143873853)
              ·
                refine ⟨5066864001897406553952695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13511637338393084143873853 5066864001897406553952695)
                ·
                  refine ⟨7600296002846109830929043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5066864001897406553952695 7600296002846109830929043)
                  ·
                    refine ⟨11400444004269164746393565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7600296002846109830929043 11400444004269164746393565)
                    ·
                      refine ⟨4275166501600936779897587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11400444004269164746393565 4275166501600936779897587)
                      ·
                        rfl

theorem cell23_8325857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 3, 3, 1, 1, 3].length) (baseStart_8325857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8325857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8325857 prefixEnd_8325857 := by exact prefixLift 8325857
  have htrace : WordTrace (prefixWord ++ tailWord_8325857) baseStart_8325857 baseEnd_8325857 := by
    simpa [prefixWord, tailWord_8325857, baseEnd_8325857] using wordTrace_append hprefix tailTrace_8325857
  have hstable : (prefixWord ++ tailWord_8325857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8325857).length < 2 ^ (prefixWord ++ tailWord_8325857).sum := by decide
  have hdescent : baseEnd_8325857 < baseStart_8325857 := by decide
  rcases family_descends (prefixWord ++ tailWord_8325857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8325873 : List Nat := [1, 2, 2, 2, 2, 2, 2, 4, 2, 4]
def baseStart_8325873 : Nat := 118140960795 + 8325873 * 2 ^ 59
def prefixEnd_8325873 : Nat := 4983230072969 + 3 ^ 40 * 8325873 * 2
def baseEnd_8325873 : Nat := 1425058239097136239099171

theorem tailTrace_8325873 : CollatzResearch.WordTrace tailWord_8325873 prefixEnd_8325873 1425058239097136239099171 := by
  unfold tailWord_8325873
  simp only [CollatzResearch.WordTrace]
  refine ⟨303669535765791541746614273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202446357177194361164409515 303669535765791541746614273)
  ·
    refine ⟨227752151824343656309960705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303669535765791541746614273 227752151824343656309960705)
    ·
      refine ⟨170814113868257742232470529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227752151824343656309960705 170814113868257742232470529)
      ·
        refine ⟨128110585401193306674352897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170814113868257742232470529 128110585401193306674352897)
        ·
          refine ⟨96082939050894980005764673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128110585401193306674352897 96082939050894980005764673)
          ·
            refine ⟨72062204288171235004323505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96082939050894980005764673 72062204288171235004323505)
            ·
              refine ⟨54046653216128426253242629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72062204288171235004323505 54046653216128426253242629)
              ·
                refine ⟨10133747478024079922482993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54046653216128426253242629 10133747478024079922482993)
                ·
                  refine ⟨7600310608518059941862245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10133747478024079922482993 7600310608518059941862245)
                  ·
                    refine ⟨1425058239097136239099171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7600310608518059941862245 1425058239097136239099171)
                    ·
                      rfl

theorem cell23_8325873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 4, 2, 4].length) (baseStart_8325873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8325873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8325873 prefixEnd_8325873 := by exact prefixLift 8325873
  have htrace : WordTrace (prefixWord ++ tailWord_8325873) baseStart_8325873 baseEnd_8325873 := by
    simpa [prefixWord, tailWord_8325873, baseEnd_8325873] using wordTrace_append hprefix tailTrace_8325873
  have hstable : (prefixWord ++ tailWord_8325873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8325873).length < 2 ^ (prefixWord ++ tailWord_8325873).sum := by decide
  have hdescent : baseEnd_8325873 < baseStart_8325873 := by decide
  rcases family_descends (prefixWord ++ tailWord_8325873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8325874 : List Nat := [3, 2, 1, 3, 1, 3, 3, 2, 1, 1, 3]
def baseStart_8325874 : Nat := 118140960795 + 8325874 * 2 ^ 59
def prefixEnd_8325874 : Nat := 4983230072969 + 3 ^ 40 * 8325874 * 2
def baseEnd_8325874 : Nat := 4275175230772063213385009

theorem tailTrace_8325874 : CollatzResearch.WordTrace tailWord_8325874 prefixEnd_8325874 4275175230772063213385009 := by
  unfold tailWord_8325874
  simp only [CollatzResearch.WordTrace]
  refine ⟨75917393059696979729350169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202446381492525279278267117 75917393059696979729350169)
  ·
    refine ⟨56938044794772734797012627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75917393059696979729350169 56938044794772734797012627)
    ·
      refine ⟨85407067192159102195518941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56938044794772734797012627 85407067192159102195518941)
      ·
        refine ⟨32027650197059663323319603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85407067192159102195518941 32027650197059663323319603)
        ·
          refine ⟨48041475295589494984979405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32027650197059663323319603 48041475295589494984979405)
          ·
            refine ⟨18015553235846060619367277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48041475295589494984979405 18015553235846060619367277)
            ·
              refine ⟨6755832463442272732262729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18015553235846060619367277 6755832463442272732262729)
              ·
                refine ⟨5066874347581704549197047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6755832463442272732262729 5066874347581704549197047)
                ·
                  refine ⟨7600311521372556823795571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5066874347581704549197047 7600311521372556823795571)
                  ·
                    refine ⟨11400467282058835235693357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7600311521372556823795571 11400467282058835235693357)
                    ·
                      refine ⟨4275175230772063213385009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11400467282058835235693357 4275175230772063213385009)
                      ·
                        rfl

theorem cell23_8325874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 3, 2, 1, 1, 3].length) (baseStart_8325874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8325874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8325874 prefixEnd_8325874 := by exact prefixLift 8325874
  have htrace : WordTrace (prefixWord ++ tailWord_8325874) baseStart_8325874 baseEnd_8325874 := by
    simpa [prefixWord, tailWord_8325874, baseEnd_8325874] using wordTrace_append hprefix tailTrace_8325874
  have hstable : (prefixWord ++ tailWord_8325874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8325874).length < 2 ^ (prefixWord ++ tailWord_8325874).sum := by decide
  have hdescent : baseEnd_8325874 < baseStart_8325874 := by decide
  rcases family_descends (prefixWord ++ tailWord_8325874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8325913 : List Nat := [1, 2, 1, 2, 1, 1, 1, 6, 4, 1, 3]
def baseStart_8325913 : Nat := 118140960795 + 8325913 * 2 ^ 59
def prefixEnd_8325913 : Nat := 4983230072969 + 3 ^ 40 * 8325913 * 2
def baseEnd_8325913 : Nat := 4275195256517588560797329

theorem tailTrace_8325913 : CollatzResearch.WordTrace tailWord_8325913 prefixEnd_8325913 4275195256517588560797329 := by
  unfold tailWord_8325913
  simp only [CollatzResearch.WordTrace]
  refine ⟨303670994685646628578070393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202447329790431085718713595 303670994685646628578070393)
  ·
    refine ⟨227753246014234971433552795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303670994685646628578070393 227753246014234971433552795)
    ·
      refine ⟨341629869021352457150329193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227753246014234971433552795 341629869021352457150329193)
      ·
        refine ⟨256222401766014342862746895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 341629869021352457150329193 256222401766014342862746895)
        ·
          refine ⟨384333602649021514294120343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256222401766014342862746895 384333602649021514294120343)
          ·
            refine ⟨576500403973532271441180515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 384333602649021514294120343 576500403973532271441180515)
            ·
              refine ⟨864750605960298407161770773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 576500403973532271441180515 864750605960298407161770773)
              ·
                refine ⟨40535184654388987835708005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 864750605960298407161770773 40535184654388987835708005)
                ·
                  refine ⟨7600347122697935219195251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40535184654388987835708005 7600347122697935219195251)
                  ·
                    refine ⟨11400520684046902828792877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7600347122697935219195251 11400520684046902828792877)
                    ·
                      refine ⟨4275195256517588560797329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11400520684046902828792877 4275195256517588560797329)
                      ·
                        rfl

theorem cell23_8325913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 6, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 6, 4, 1, 3].length) (baseStart_8325913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8325913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8325913 prefixEnd_8325913 := by exact prefixLift 8325913
  have htrace : WordTrace (prefixWord ++ tailWord_8325913) baseStart_8325913 baseEnd_8325913 := by
    simpa [prefixWord, tailWord_8325913, baseEnd_8325913] using wordTrace_append hprefix tailTrace_8325913
  have hstable : (prefixWord ++ tailWord_8325913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8325913).length < 2 ^ (prefixWord ++ tailWord_8325913).sum := by decide
  have hdescent : baseEnd_8325913 < baseStart_8325913 := by decide
  rcases family_descends (prefixWord ++ tailWord_8325913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8325917 : List Nat := [1, 4, 2, 4, 1, 2, 1, 1, 1, 1, 5]
def baseStart_8325917 : Nat := 118140960795 + 8325917 * 2 ^ 59
def prefixEnd_8325917 : Nat := 4983230072969 + 3 ^ 40 * 8325917 * 2
def baseEnd_8325917 : Nat := 4275197310440206545147311

theorem tailTrace_8325917 : CollatzResearch.WordTrace tailWord_8325917 prefixEnd_8325917 4275197310440206545147311 := by
  unfold tailWord_8325917
  simp only [CollatzResearch.WordTrace]
  refine ⟨303671140577632137261216005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202447427051754758174144003 303671140577632137261216005)
  ·
    refine ⟨56938338858306025736478001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 303671140577632137261216005 56938338858306025736478001)
    ·
      refine ⟨42703754143729519302358501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56938338858306025736478001 42703754143729519302358501)
      ·
        refine ⟨8006953901949284869192219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42703754143729519302358501 8006953901949284869192219)
        ·
          refine ⟨12010430852923927303788329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8006953901949284869192219 12010430852923927303788329)
          ·
            refine ⟨9007823139692945477841247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12010430852923927303788329 9007823139692945477841247)
            ·
              refine ⟨13511734709539418216761871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9007823139692945477841247 13511734709539418216761871)
              ·
                refine ⟨20267602064309127325142807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13511734709539418216761871 20267602064309127325142807)
                ·
                  refine ⟨30401403096463690987714211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20267602064309127325142807 30401403096463690987714211)
                  ·
                    refine ⟨45602104644695536481571317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30401403096463690987714211 45602104644695536481571317)
                    ·
                      refine ⟨4275197310440206545147311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45602104644695536481571317 4275197310440206545147311)
                      ·
                        rfl

theorem cell23_8325917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_8325917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8325917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8325917 prefixEnd_8325917 := by exact prefixLift 8325917
  have htrace : WordTrace (prefixWord ++ tailWord_8325917) baseStart_8325917 baseEnd_8325917 := by
    simpa [prefixWord, tailWord_8325917, baseEnd_8325917] using wordTrace_append hprefix tailTrace_8325917
  have hstable : (prefixWord ++ tailWord_8325917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8325917).length < 2 ^ (prefixWord ++ tailWord_8325917).sum := by decide
  have hdescent : baseEnd_8325917 < baseStart_8325917 := by decide
  rcases family_descends (prefixWord ++ tailWord_8325917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8325970 : List Nat := [3, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2]
def baseStart_8325970 : Nat := 118140960795 + 8325970 * 2 ^ 59
def prefixEnd_8325970 : Nat := 4983230072969 + 3 ^ 40 * 8325970 * 2
def baseEnd_8325970 : Nat := 4275224524914894837784567

theorem tailTrace_8325970 : CollatzResearch.WordTrace tailWord_8325970 prefixEnd_8325970 4275224524914894837784567 := by
  unfold tailWord_8325970
  simp only [CollatzResearch.WordTrace]
  refine ⟨75918268411610031828223841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202448715764293418208596909 75918268411610031828223841)
  ·
    refine ⟨56938701308707523871167881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75918268411610031828223841 56938701308707523871167881)
    ·
      refine ⟨42704025981530642903375911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56938701308707523871167881 42704025981530642903375911)
      ·
        refine ⟨64056038972295964355063867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42704025981530642903375911 64056038972295964355063867)
        ·
          refine ⟨96084058458443946532595801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64056038972295964355063867 96084058458443946532595801)
          ·
            refine ⟨72063043843832959899446851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96084058458443946532595801 72063043843832959899446851)
            ·
              refine ⟨108094565765749439849170277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72063043843832959899446851 108094565765749439849170277)
              ·
                refine ⟨20267731081078019971719427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 108094565765749439849170277 20267731081078019971719427)
                ·
                  refine ⟨30401596621617029957579141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20267731081078019971719427 30401596621617029957579141)
                  ·
                    refine ⟨5700299366553193117046089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30401596621617029957579141 5700299366553193117046089)
                    ·
                      refine ⟨4275224524914894837784567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5700299366553193117046089 4275224524914894837784567)
                      ·
                        rfl

theorem cell23_8325970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2].length) (baseStart_8325970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8325970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8325970 prefixEnd_8325970 := by exact prefixLift 8325970
  have htrace : WordTrace (prefixWord ++ tailWord_8325970) baseStart_8325970 baseEnd_8325970 := by
    simpa [prefixWord, tailWord_8325970, baseEnd_8325970] using wordTrace_append hprefix tailTrace_8325970
  have hstable : (prefixWord ++ tailWord_8325970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8325970).length < 2 ^ (prefixWord ++ tailWord_8325970).sum := by decide
  have hdescent : baseEnd_8325970 < baseStart_8325970 := by decide
  rcases family_descends (prefixWord ++ tailWord_8325970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8325987 : List Nat := [1, 1, 1, 5, 3, 2, 1, 1, 4, 2, 2]
def baseStart_8325987 : Nat := 118140960795 + 8325987 * 2 ^ 59
def prefixEnd_8325987 : Nat := 4983230072969 + 3 ^ 40 * 8325987 * 2
def baseEnd_8325987 : Nat := 4275233254086021271271989

theorem tailTrace_8325987 : CollatzResearch.WordTrace tailWord_8325987 prefixEnd_8325987 4275233254086021271271989 := by
  unfold tailWord_8325987
  simp only [CollatzResearch.WordTrace]
  refine ⟨303673693687378539216264215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202449129124919026144176143 303673693687378539216264215)
  ·
    refine ⟨455510540531067808824396323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303673693687378539216264215 455510540531067808824396323)
    ·
      refine ⟨683265810796601713236594485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 455510540531067808824396323 683265810796601713236594485)
      ·
        refine ⟨64056169762181410615930733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 683265810796601713236594485 64056169762181410615930733)
        ·
          refine ⟨24021063660818028980974025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64056169762181410615930733 24021063660818028980974025)
          ·
            refine ⟨18015797745613521735730519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24021063660818028980974025 18015797745613521735730519)
            ·
              refine ⟨27023696618420282603595779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18015797745613521735730519 27023696618420282603595779)
              ·
                refine ⟨40535544927630423905393669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27023696618420282603595779 40535544927630423905393669)
                ·
                  refine ⟨7600414673930704482261313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40535544927630423905393669 7600414673930704482261313)
                  ·
                    refine ⟨5700311005448028361695985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7600414673930704482261313 5700311005448028361695985)
                    ·
                      refine ⟨4275233254086021271271989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5700311005448028361695985 4275233254086021271271989)
                      ·
                        rfl

theorem cell23_8325987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 1, 4, 2, 2].length) (baseStart_8325987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8325987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8325987 prefixEnd_8325987 := by exact prefixLift 8325987
  have htrace : WordTrace (prefixWord ++ tailWord_8325987) baseStart_8325987 baseEnd_8325987 := by
    simpa [prefixWord, tailWord_8325987, baseEnd_8325987] using wordTrace_append hprefix tailTrace_8325987
  have hstable : (prefixWord ++ tailWord_8325987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8325987).length < 2 ^ (prefixWord ++ tailWord_8325987).sum := by decide
  have hdescent : baseEnd_8325987 < baseStart_8325987 := by decide
  rcases family_descends (prefixWord ++ tailWord_8325987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8326003 : List Nat := [1, 1, 1, 2, 2, 1, 6, 1, 2, 3, 3]
def baseStart_8326003 : Nat := 118140960795 + 8326003 * 2 ^ 59
def prefixEnd_8326003 : Nat := 4983230072969 + 3 ^ 40 * 8326003 * 2
def baseEnd_8326003 : Nat := 4275241469776493208671915

theorem tailTrace_8326003 : CollatzResearch.WordTrace tailWord_8326003 prefixEnd_8326003 4275241469776493208671915 := by
  unfold tailWord_8326003
  simp only [CollatzResearch.WordTrace]
  refine ⟨303674277255320573948846663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202449518170213715965897775 303674277255320573948846663)
  ·
    refine ⟨455511415882980860923269995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303674277255320573948846663 455511415882980860923269995)
    ·
      refine ⟨683267123824471291384904993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 455511415882980860923269995 683267123824471291384904993)
      ·
        refine ⟨512450342868353468538678745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 683267123824471291384904993 512450342868353468538678745)
        ·
          refine ⟨384337757151265101404009059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 512450342868353468538678745 384337757151265101404009059)
          ·
            refine ⟨576506635726897652106013589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 384337757151265101404009059 576506635726897652106013589)
            ·
              refine ⟨27023748549698327442469387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 576506635726897652106013589 27023748549698327442469387)
              ·
                refine ⟨40535622824547491163704081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27023748549698327442469387 40535622824547491163704081)
                ·
                  refine ⟨30401717118410618372778061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40535622824547491163704081 30401717118410618372778061)
                  ·
                    refine ⟨11400643919403981889791773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30401717118410618372778061 11400643919403981889791773)
                    ·
                      refine ⟨4275241469776493208671915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11400643919403981889791773 4275241469776493208671915)
                      ·
                        rfl

theorem cell23_8326003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 1, 2, 3, 3].length) (baseStart_8326003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8326003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8326003 prefixEnd_8326003 := by exact prefixLift 8326003
  have htrace : WordTrace (prefixWord ++ tailWord_8326003) baseStart_8326003 baseEnd_8326003 := by
    simpa [prefixWord, tailWord_8326003, baseEnd_8326003] using wordTrace_append hprefix tailTrace_8326003
  have hstable : (prefixWord ++ tailWord_8326003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8326003).length < 2 ^ (prefixWord ++ tailWord_8326003).sum := by decide
  have hdescent : baseEnd_8326003 < baseStart_8326003 := by decide
  rcases family_descends (prefixWord ++ tailWord_8326003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8326016 : List Nat := [2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 7]
def baseStart_8326016 : Nat := 118140960795 + 8326016 * 2 ^ 59
def prefixEnd_8326016 : Nat := 4983230072969 + 3 ^ 40 * 8326016 * 2
def baseEnd_8326016 : Nat := 4275248145025001657809355

theorem tailTrace_8326016 : CollatzResearch.WordTrace tailWord_8326016 prefixEnd_8326016 4275248145025001657809355 := by
  unfold tailWord_8326016
  simp only [CollatzResearch.WordTrace]
  refine ⟨151837375702136738584534951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202449834269515651446046601 151837375702136738584534951)
  ·
    refine ⟨227756063553205107876802427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151837375702136738584534951 227756063553205107876802427)
    ·
      refine ⟨341634095329807661815203641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227756063553205107876802427 341634095329807661815203641)
      ·
        refine ⟨256225571497355746361402731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 341634095329807661815203641 256225571497355746361402731)
        ·
          refine ⟨384338357246033619542104097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256225571497355746361402731 384338357246033619542104097)
          ·
            refine ⟨288253767934525214656578073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 384338357246033619542104097 288253767934525214656578073)
            ·
              refine ⟨216190325950893910992433555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 288253767934525214656578073 216190325950893910992433555)
              ·
                refine ⟨324285488926340866488650333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 216190325950893910992433555 324285488926340866488650333)
                ·
                  refine ⟨121607058347377824933243875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 324285488926340866488650333 121607058347377824933243875)
                  ·
                    refine ⟨182410587521066737399865813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 121607058347377824933243875 182410587521066737399865813)
                    ·
                      refine ⟨4275248145025001657809355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 182410587521066737399865813 4275248145025001657809355)
                      ·
                        rfl

theorem cell23_8326016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 7].length) (baseStart_8326016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8326016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8326016 prefixEnd_8326016 := by exact prefixLift 8326016
  have htrace : WordTrace (prefixWord ++ tailWord_8326016) baseStart_8326016 baseEnd_8326016 := by
    simpa [prefixWord, tailWord_8326016, baseEnd_8326016] using wordTrace_append hprefix tailTrace_8326016
  have hstable : (prefixWord ++ tailWord_8326016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8326016).length < 2 ^ (prefixWord ++ tailWord_8326016).sum := by decide
  have hdescent : baseEnd_8326016 < baseStart_8326016 := by decide
  rcases family_descends (prefixWord ++ tailWord_8326016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8326023 : List Nat := [1, 1, 4, 2, 3, 1, 2, 1, 1, 7]
def baseStart_8326023 : Nat := 118140960795 + 8326023 * 2 ^ 59
def prefixEnd_8326023 : Nat := 4983230072969 + 3 ^ 40 * 8326023 * 2
def baseEnd_8326023 : Nat := 1425083913129861043473941

theorem tailTrace_8326023 : CollatzResearch.WordTrace tailWord_8326023 prefixEnd_8326023 1425083913129861043473941 := by
  unfold tailWord_8326023
  simp only [CollatzResearch.WordTrace]
  refine ⟨303675006715248117364574723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202450004476832078243049815 303675006715248117364574723)
  ·
    refine ⟨455512510072872176046862085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303675006715248117364574723 455512510072872176046862085)
    ·
      refine ⟨85408595638663533008786641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 455512510072872176046862085 85408595638663533008786641)
      ·
        refine ⟨64056446728997649756589981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85408595638663533008786641 64056446728997649756589981)
        ·
          refine ⟨24021167523374118658721243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64056446728997649756589981 24021167523374118658721243)
          ·
            refine ⟨36031751285061177988081865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24021167523374118658721243 36031751285061177988081865)
            ·
              refine ⟨27023813463795883491061399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36031751285061177988081865 27023813463795883491061399)
              ·
                refine ⟨40535720195693825236592099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27023813463795883491061399 40535720195693825236592099)
                ·
                  refine ⟨60803580293540737854888149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40535720195693825236592099 60803580293540737854888149)
                  ·
                    refine ⟨1425083913129861043473941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60803580293540737854888149 1425083913129861043473941)
                    ·
                      rfl

theorem cell23_8326023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 1, 1, 7].length) (baseStart_8326023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8326023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8326023 prefixEnd_8326023 := by exact prefixLift 8326023
  have htrace : WordTrace (prefixWord ++ tailWord_8326023) baseStart_8326023 baseEnd_8326023 := by
    simpa [prefixWord, tailWord_8326023, baseEnd_8326023] using wordTrace_append hprefix tailTrace_8326023
  have hstable : (prefixWord ++ tailWord_8326023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8326023).length < 2 ^ (prefixWord ++ tailWord_8326023).sum := by decide
  have hdescent : baseEnd_8326023 < baseStart_8326023 := by decide
  rcases family_descends (prefixWord ++ tailWord_8326023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8326044 : List Nat := [2, 2, 3, 3, 2, 1, 3, 2, 5]
def baseStart_8326044 : Nat := 118140960795 + 8326044 * 2 ^ 59
def prefixEnd_8326044 : Nat := 4983230072969 + 3 ^ 40 * 8326044 * 2
def baseEnd_8326044 : Nat := 475029169164814172028803

theorem tailTrace_8326044 : CollatzResearch.WordTrace tailWord_8326044 prefixEnd_8326044 475029169164814172028803 := by
  unfold tailWord_8326044
  simp only [CollatzResearch.WordTrace]
  refine ⟨151837886324086018975544593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202450515098781358634059457 151837886324086018975544593)
  ·
    refine ⟨113878414743064514231658445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151837886324086018975544593 113878414743064514231658445)
    ·
      refine ⟨42704405528649192836871917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113878414743064514231658445 42704405528649192836871917)
      ·
        refine ⟨16014152073243447313826969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42704405528649192836871917 16014152073243447313826969)
        ·
          refine ⟨12010614054932585485370227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16014152073243447313826969 12010614054932585485370227)
          ·
            refine ⟨18015921082398878228055341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12010614054932585485370227 18015921082398878228055341)
            ·
              refine ⟨6755970405899579335520753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18015921082398878228055341 6755970405899579335520753)
              ·
                refine ⟨5066977804424684501640565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6755970405899579335520753 5066977804424684501640565)
                ·
                  refine ⟨475029169164814172028803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5066977804424684501640565 475029169164814172028803)
                  ·
                    rfl

theorem cell23_8326044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 3, 2, 5].length) (baseStart_8326044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8326044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8326044 prefixEnd_8326044 := by exact prefixLift 8326044
  have htrace : WordTrace (prefixWord ++ tailWord_8326044) baseStart_8326044 baseEnd_8326044 := by
    simpa [prefixWord, tailWord_8326044, baseEnd_8326044] using wordTrace_append hprefix tailTrace_8326044
  have hstable : (prefixWord ++ tailWord_8326044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8326044).length < 2 ^ (prefixWord ++ tailWord_8326044).sum := by decide
  have hdescent : baseEnd_8326044 < baseStart_8326044 := by decide
  rcases family_descends (prefixWord ++ tailWord_8326044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8326050 : List Nat := [3, 3, 1, 2, 2, 2, 1, 1, 1, 2, 5]
def baseStart_8326050 : Nat := 118140960795 + 8326050 * 2 ^ 59
def prefixEnd_8326050 : Nat := 4983230072969 + 3 ^ 40 * 8326050 * 2
def baseEnd_8326050 : Nat := 4275265603367254524784199

theorem tailTrace_8326050 : CollatzResearch.WordTrace tailWord_8326050 prefixEnd_8326050 4275265603367254524784199 := by
  unfold tailWord_8326050
  simp only [CollatzResearch.WordTrace]
  refine ⟨75918997871537575243951901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202450660990766867317205069 75918997871537575243951901)
  ·
    refine ⟨28469624201826590716481963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75918997871537575243951901 28469624201826590716481963)
    ·
      refine ⟨42704436302739886074722945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28469624201826590716481963 42704436302739886074722945)
      ·
        refine ⟨32028327227054914556042209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42704436302739886074722945 32028327227054914556042209)
        ·
          refine ⟨24021245420291185917031657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32028327227054914556042209 24021245420291185917031657)
          ·
            refine ⟨18015934065218389437773743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24021245420291185917031657 18015934065218389437773743)
            ·
              refine ⟨27023901097827584156660615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18015934065218389437773743 27023901097827584156660615)
              ·
                refine ⟨40535851646741376234990923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27023901097827584156660615 40535851646741376234990923)
                ·
                  refine ⟨60803777470112064352486385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40535851646741376234990923 60803777470112064352486385)
                  ·
                    refine ⟨45602833102584048264364789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60803777470112064352486385 45602833102584048264364789)
                    ·
                      refine ⟨4275265603367254524784199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45602833102584048264364789 4275265603367254524784199)
                      ·
                        rfl

theorem cell23_8326050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_8326050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8326050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8326050 prefixEnd_8326050 := by exact prefixLift 8326050
  have htrace : WordTrace (prefixWord ++ tailWord_8326050) baseStart_8326050 baseEnd_8326050 := by
    simpa [prefixWord, tailWord_8326050, baseEnd_8326050] using wordTrace_append hprefix tailTrace_8326050
  have hstable : (prefixWord ++ tailWord_8326050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8326050).length < 2 ^ (prefixWord ++ tailWord_8326050).sum := by decide
  have hdescent : baseEnd_8326050 < baseStart_8326050 := by decide
  rcases family_descends (prefixWord ++ tailWord_8326050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8326063 : List Nat := [1, 1, 2, 1, 2, 2, 2, 4, 1, 4, 3]
def baseStart_8326063 : Nat := 118140960795 + 8326063 * 2 ^ 59
def prefixEnd_8326063 : Nat := 4983230072969 + 3 ^ 40 * 8326063 * 2
def baseEnd_8326063 : Nat := 4275272278615762973921639

theorem tailTrace_8326063 : CollatzResearch.WordTrace tailWord_8326063 prefixEnd_8326063 4275272278615762973921639 := by
  unfold tailWord_8326063
  simp only [CollatzResearch.WordTrace]
  refine ⟨303676465635103204196030843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202450977090068802797353895 303676465635103204196030843)
  ·
    refine ⟨455514698452654806294046265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303676465635103204196030843 455514698452654806294046265)
    ·
      refine ⟨341636023839491104720534699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 455514698452654806294046265 341636023839491104720534699)
      ·
        refine ⟨512454035759236657080802049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341636023839491104720534699 512454035759236657080802049)
        ·
          refine ⟨384340526819427492810601537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 512454035759236657080802049 384340526819427492810601537)
          ·
            refine ⟨288255395114570619607951153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 384340526819427492810601537 288255395114570619607951153)
            ·
              refine ⟨216191546335927964705963365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 288255395114570619607951153 216191546335927964705963365)
              ·
                refine ⟨40535914937986493382368131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 216191546335927964705963365 40535914937986493382368131)
                ·
                  refine ⟨60803872406979740073552197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40535914937986493382368131 60803872406979740073552197)
                  ·
                    refine ⟨11400726076308701263791037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60803872406979740073552197 11400726076308701263791037)
                    ·
                      refine ⟨4275272278615762973921639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11400726076308701263791037 4275272278615762973921639)
                      ·
                        rfl

theorem cell23_8326063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 4, 1, 4, 3].length) (baseStart_8326063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8326063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8326063 prefixEnd_8326063 := by exact prefixLift 8326063
  have htrace : WordTrace (prefixWord ++ tailWord_8326063) baseStart_8326063 baseEnd_8326063 := by
    simpa [prefixWord, tailWord_8326063, baseEnd_8326063] using wordTrace_append hprefix tailTrace_8326063
  have hstable : (prefixWord ++ tailWord_8326063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8326063).length < 2 ^ (prefixWord ++ tailWord_8326063).sum := by decide
  have hdescent : baseEnd_8326063 < baseStart_8326063 := by decide
  rcases family_descends (prefixWord ++ tailWord_8326063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8326077 : List Nat := [1, 4, 1, 2, 4, 1, 2, 1, 2, 1, 4]
def baseStart_8326077 : Nat := 118140960795 + 8326077 * 2 ^ 59
def prefixEnd_8326077 : Nat := 4983230072969 + 3 ^ 40 * 8326077 * 2
def baseEnd_8326077 : Nat := 4275279467344925919146575

theorem tailTrace_8326077 : CollatzResearch.WordTrace tailWord_8326077 prefixEnd_8326077 4275279467344925919146575 := by
  unfold tailWord_8326077
  simp only [CollatzResearch.WordTrace]
  refine ⟨303676976257052484587040485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202451317504701656391360323 303676976257052484587040485)
  ·
    refine ⟨56939433048197340860070091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 303676976257052484587040485 56939433048197340860070091)
    ·
      refine ⟨85409149572296011290105137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56939433048197340860070091 85409149572296011290105137)
      ·
        refine ⟨64056862179222008467578853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85409149572296011290105137 64056862179222008467578853)
        ·
          refine ⟨12010661658604126587671035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64056862179222008467578853 12010661658604126587671035)
          ·
            refine ⟨18015992487906189881506553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12010661658604126587671035 18015992487906189881506553)
            ·
              refine ⟨13511994365929642411129915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18015992487906189881506553 13511994365929642411129915)
              ·
                refine ⟨20267991548894463616694873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13511994365929642411129915 20267991548894463616694873)
                ·
                  refine ⟨15200993661670847712521155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20267991548894463616694873 15200993661670847712521155)
                  ·
                    refine ⟨22801490492506271568781733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15200993661670847712521155 22801490492506271568781733)
                    ·
                      refine ⟨4275279467344925919146575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22801490492506271568781733 4275279467344925919146575)
                      ·
                        rfl

theorem cell23_8326077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 2, 1, 2, 1, 4].length) (baseStart_8326077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8326077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8326077 prefixEnd_8326077 := by exact prefixLift 8326077
  have htrace : WordTrace (prefixWord ++ tailWord_8326077) baseStart_8326077 baseEnd_8326077 := by
    simpa [prefixWord, tailWord_8326077, baseEnd_8326077] using wordTrace_append hprefix tailTrace_8326077
  have hstable : (prefixWord ++ tailWord_8326077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8326077).length < 2 ^ (prefixWord ++ tailWord_8326077).sum := by decide
  have hdescent : baseEnd_8326077 < baseStart_8326077 := by decide
  rcases family_descends (prefixWord ++ tailWord_8326077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8326080 : List Nat := [2, 1, 1, 2, 3, 3, 1, 3, 2, 2, 3]
def baseStart_8326080 : Nat := 118140960795 + 8326080 * 2 ^ 59
def prefixEnd_8326080 : Nat := 4983230072969 + 3 ^ 40 * 8326080 * 2
def baseEnd_8326080 : Nat := 4275281007786889407409061

theorem tailTrace_8326080 : CollatzResearch.WordTrace tailWord_8326080 prefixEnd_8326080 4275281007786889407409061 := by
  unfold tailWord_8326080
  simp only [CollatzResearch.WordTrace]
  refine ⟨151838542838020808049699847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202451390450694410732933129 151838542838020808049699847)
  ·
    refine ⟨227757814257031212074549771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151838542838020808049699847 227757814257031212074549771)
    ·
      refine ⟨341636721385546818111824657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227757814257031212074549771 341636721385546818111824657)
      ·
        refine ⟨256227541039160113583868493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 341636721385546818111824657 256227541039160113583868493)
        ·
          refine ⟨96085327889685042593950685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 256227541039160113583868493 96085327889685042593950685)
          ·
            refine ⟨36031997958631890972731507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96085327889685042593950685 36031997958631890972731507)
            ·
              refine ⟨54047996937947836459097261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36031997958631890972731507 54047996937947836459097261)
              ·
                refine ⟨20267998851730438672161473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54047996937947836459097261 20267998851730438672161473)
                ·
                  refine ⟨15200999138797829004121105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20267998851730438672161473 15200999138797829004121105)
                  ·
                    refine ⟨11400749354098371753090829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15200999138797829004121105 11400749354098371753090829)
                    ·
                      refine ⟨4275281007786889407409061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11400749354098371753090829 4275281007786889407409061)
                      ·
                        rfl

theorem cell23_8326080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 3, 2, 2, 3].length) (baseStart_8326080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8326080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8326080 prefixEnd_8326080 := by exact prefixLift 8326080
  have htrace : WordTrace (prefixWord ++ tailWord_8326080) baseStart_8326080 baseEnd_8326080 := by
    simpa [prefixWord, tailWord_8326080, baseEnd_8326080] using wordTrace_append hprefix tailTrace_8326080
  have hstable : (prefixWord ++ tailWord_8326080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8326080).length < 2 ^ (prefixWord ++ tailWord_8326080).sum := by decide
  have hdescent : baseEnd_8326080 < baseStart_8326080 := by decide
  rcases family_descends (prefixWord ++ tailWord_8326080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8326100 : List Nat := [2, 4, 1, 2, 1, 2, 1, 4, 6]
def baseStart_8326100 : Nat := 118140960795 + 8326100 * 2 ^ 59
def prefixEnd_8326100 : Nat := 4983230072969 + 3 ^ 40 * 8326100 * 2
def baseEnd_8326100 : Nat := 475032364155553258795441

theorem tailTrace_8326100 : CollatzResearch.WordTrace tailWord_8326100 prefixEnd_8326100 475032364155553258795441 := by
  unfold tailWord_8326100
  simp only [CollatzResearch.WordTrace]
  refine ⟨151838907567984579757563877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202451876757312773010085169 151838907567984579757563877)
  ·
    refine ⟨28469795168997108704543227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151838907567984579757563877 28469795168997108704543227)
    ·
      refine ⟨42704692753495663056814841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28469795168997108704543227 42704692753495663056814841)
      ·
        refine ⟨32028519565121747292611131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42704692753495663056814841 32028519565121747292611131)
        ·
          refine ⟨48042779347682620938916697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32028519565121747292611131 48042779347682620938916697)
          ·
            refine ⟨36032084510761965704187523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48042779347682620938916697 36032084510761965704187523)
            ·
              refine ⟨54048126766142948556281285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36032084510761965704187523 54048126766142948556281285)
              ·
                refine ⟨10134023768651802854302741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54048126766142948556281285 10134023768651802854302741)
                ·
                  refine ⟨475032364155553258795441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10134023768651802854302741 475032364155553258795441)
                  ·
                    rfl

theorem cell23_8326100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 4, 6].length) (baseStart_8326100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8326100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8326100 prefixEnd_8326100 := by exact prefixLift 8326100
  have htrace : WordTrace (prefixWord ++ tailWord_8326100) baseStart_8326100 baseEnd_8326100 := by
    simpa [prefixWord, tailWord_8326100, baseEnd_8326100] using wordTrace_append hprefix tailTrace_8326100
  have hstable : (prefixWord ++ tailWord_8326100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8326100).length < 2 ^ (prefixWord ++ tailWord_8326100).sum := by decide
  have hdescent : baseEnd_8326100 < baseStart_8326100 := by decide
  rcases family_descends (prefixWord ++ tailWord_8326100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8326104 : List Nat := [2, 1, 2, 2, 2, 3, 4, 2, 1, 4]
def baseStart_8326104 : Nat := 118140960795 + 8326104 * 2 ^ 59
def prefixEnd_8326104 : Nat := 4983230072969 + 3 ^ 40 * 8326104 * 2
def baseEnd_8326104 : Nat := 1425097777107532437836317

theorem tailTrace_8326104 : CollatzResearch.WordTrace tailWord_8326104 prefixEnd_8326104 1425097777107532437836317 := by
  unfold tailWord_8326104
  simp only [CollatzResearch.WordTrace]
  refine ⟨151838980513977334099136683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202451974018636445465515577 151838980513977334099136683)
  ·
    refine ⟨227758470770966001148705025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151838980513977334099136683 227758470770966001148705025)
    ·
      refine ⟨170818853078224500861528769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227758470770966001148705025 170818853078224500861528769)
      ·
        refine ⟨128114139808668375646146577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170818853078224500861528769 128114139808668375646146577)
        ·
          refine ⟨96085604856501281734609933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128114139808668375646146577 96085604856501281734609933)
          ·
            refine ⟨36032101821187980650478725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96085604856501281734609933 36032101821187980650478725)
            ·
              refine ⟨6756019091472746371964761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36032101821187980650478725 6756019091472746371964761)
              ·
                refine ⟨5067014318604559778973571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6756019091472746371964761 5067014318604559778973571)
                ·
                  refine ⟨7600521477906839668460357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5067014318604559778973571 7600521477906839668460357)
                  ·
                    refine ⟨1425097777107532437836317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7600521477906839668460357 1425097777107532437836317)
                    ·
                      rfl

theorem cell23_8326104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 4, 2, 1, 4].length) (baseStart_8326104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8326104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8326104 prefixEnd_8326104 := by exact prefixLift 8326104
  have htrace : WordTrace (prefixWord ++ tailWord_8326104) baseStart_8326104 baseEnd_8326104 := by
    simpa [prefixWord, tailWord_8326104, baseEnd_8326104] using wordTrace_append hprefix tailTrace_8326104
  have hstable : (prefixWord ++ tailWord_8326104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8326104).length < 2 ^ (prefixWord ++ tailWord_8326104).sum := by decide
  have hdescent : baseEnd_8326104 < baseStart_8326104 := by decide
  rcases family_descends (prefixWord ++ tailWord_8326104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8326127 : List Nat := [1, 1, 2, 1, 4, 4, 1, 2, 3, 1, 3]
def baseStart_8326127 : Nat := 118140960795 + 8326127 * 2 ^ 59
def prefixEnd_8326127 : Nat := 4983230072969 + 3 ^ 40 * 8326127 * 2
def baseEnd_8326127 : Nat := 4275305141377650723521345

theorem tailTrace_8326127 : CollatzResearch.WordTrace tailWord_8326127 prefixEnd_8326127 4275305141377650723521345 := by
  unfold tailWord_8326127
  simp only [CollatzResearch.WordTrace]
  refine ⟨303678799906871343126360635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202452533271247562084240423 303678799906871343126360635)
  ·
    refine ⟨455518199860307014689540953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303678799906871343126360635 455518199860307014689540953)
    ·
      refine ⟨341638649895230261017155715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 455518199860307014689540953 341638649895230261017155715)
      ·
        refine ⟨512457974842845391525733573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341638649895230261017155715 512457974842845391525733573)
        ·
          refine ⟨96085870283033510911075045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 512457974842845391525733573 96085870283033510911075045)
          ·
            refine ⟨18016100678068783295826571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96085870283033510911075045 18016100678068783295826571)
            ·
              refine ⟨27024151017103174943739857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18016100678068783295826571 27024151017103174943739857)
              ·
                refine ⟨20268113262827381207804893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27024151017103174943739857 20268113262827381207804893)
                ·
                  refine ⟨7600542473560267952926835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20268113262827381207804893 7600542473560267952926835)
                  ·
                    refine ⟨11400813710340401929390253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7600542473560267952926835 11400813710340401929390253)
                    ·
                      refine ⟨4275305141377650723521345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11400813710340401929390253 4275305141377650723521345)
                      ·
                        rfl

theorem cell23_8326127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 2, 3, 1, 3].length) (baseStart_8326127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8326127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8326127 prefixEnd_8326127 := by exact prefixLift 8326127
  have htrace : WordTrace (prefixWord ++ tailWord_8326127) baseStart_8326127 baseEnd_8326127 := by
    simpa [prefixWord, tailWord_8326127, baseEnd_8326127] using wordTrace_append hprefix tailTrace_8326127
  have hstable : (prefixWord ++ tailWord_8326127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8326127).length < 2 ^ (prefixWord ++ tailWord_8326127).sum := by decide
  have hdescent : baseEnd_8326127 < baseStart_8326127 := by decide
  rcases family_descends (prefixWord ++ tailWord_8326127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8326153 : List Nat := [1, 2, 1, 1, 3, 1, 1, 2, 5, 1, 5]
def baseStart_8326153 : Nat := 118140960795 + 8326153 * 2 ^ 59
def prefixEnd_8326153 : Nat := 4983230072969 + 3 ^ 40 * 8326153 * 2
def baseEnd_8326153 : Nat := 4275318491874667621796225

theorem tailTrace_8326153 : CollatzResearch.WordTrace tailWord_8326153 prefixEnd_8326153 4275318491874667621796225 := by
  unfold tailWord_8326153
  simp only [CollatzResearch.WordTrace]
  refine ⟨303679748204777149566807113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202453165469851433044538075 303679748204777149566807113)
  ·
    refine ⟨227759811153582862175105335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303679748204777149566807113 227759811153582862175105335)
    ·
      refine ⟨341639716730374293262658003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227759811153582862175105335 341639716730374293262658003)
      ·
        refine ⟨512459575095561439893987005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341639716730374293262658003 512459575095561439893987005)
        ·
          refine ⟨192172340660835539960245127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 512459575095561439893987005 192172340660835539960245127)
          ·
            refine ⟨288258510991253309940367691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192172340660835539960245127 288258510991253309940367691)
            ·
              refine ⟨432387766486879964910551537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 288258510991253309940367691 432387766486879964910551537)
              ·
                refine ⟨324290824865159973682913653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 432387766486879964910551537 324290824865159973682913653)
                ·
                  refine ⟨30402264831108747532773155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 324290824865159973682913653 30402264831108747532773155)
                  ·
                    refine ⟨45603397246663121299159733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30402264831108747532773155 45603397246663121299159733)
                    ·
                      refine ⟨4275318491874667621796225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45603397246663121299159733 4275318491874667621796225)
                      ·
                        rfl

theorem cell23_8326153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 5, 1, 5].length) (baseStart_8326153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8326153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8326153 prefixEnd_8326153 := by exact prefixLift 8326153
  have htrace : WordTrace (prefixWord ++ tailWord_8326153) baseStart_8326153 baseEnd_8326153 := by
    simpa [prefixWord, tailWord_8326153, baseEnd_8326153] using wordTrace_append hprefix tailTrace_8326153
  have hstable : (prefixWord ++ tailWord_8326153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8326153).length < 2 ^ (prefixWord ++ tailWord_8326153).sum := by decide
  have hdescent : baseEnd_8326153 < baseStart_8326153 := by decide
  rcases family_descends (prefixWord ++ tailWord_8326153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8326163 : List Nat := [1, 1, 1, 2, 1, 4, 1, 4, 1, 1, 6]
def baseStart_8326163 : Nat := 118140960795 + 8326163 * 2 ^ 59
def prefixEnd_8326163 : Nat := 4983230072969 + 3 ^ 40 * 8326163 * 2
def baseEnd_8326163 : Nat := 4275323626681212582671179

theorem tailTrace_8326163 : CollatzResearch.WordTrace tailWord_8326163 prefixEnd_8326163 4275323626681212582671179 := by
  unfold tailWord_8326163
  simp only [CollatzResearch.WordTrace]
  refine ⟨303680112934740921274671143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202453408623160614183114095 303680112934740921274671143)
  ·
    refine ⟨455520169402111381912006715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303680112934740921274671143 455520169402111381912006715)
    ·
      refine ⟨683280254103167072868010073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 455520169402111381912006715 683280254103167072868010073)
      ·
        refine ⟨512460190577375304651007555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 683280254103167072868010073 512460190577375304651007555)
        ·
          refine ⟨768690285866062956976511333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 512460190577375304651007555 768690285866062956976511333)
          ·
            refine ⟨144129428599886804433095875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 768690285866062956976511333 144129428599886804433095875)
            ·
              refine ⟨216194142899830206649643813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144129428599886804433095875 216194142899830206649643813)
              ·
                refine ⟨40536401793718163746808215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 216194142899830206649643813 40536401793718163746808215)
                ·
                  refine ⟨60804602690577245620212323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40536401793718163746808215 60804602690577245620212323)
                  ·
                    refine ⟨91206904035865868430318485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60804602690577245620212323 91206904035865868430318485)
                    ·
                      refine ⟨4275323626681212582671179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91206904035865868430318485 4275323626681212582671179)
                      ·
                        rfl

theorem cell23_8326163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 4, 1, 1, 6].length) (baseStart_8326163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8326163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8326163 prefixEnd_8326163 := by exact prefixLift 8326163
  have htrace : WordTrace (prefixWord ++ tailWord_8326163) baseStart_8326163 baseEnd_8326163 := by
    simpa [prefixWord, tailWord_8326163, baseEnd_8326163] using wordTrace_append hprefix tailTrace_8326163
  have hstable : (prefixWord ++ tailWord_8326163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8326163).length < 2 ^ (prefixWord ++ tailWord_8326163).sum := by decide
  have hdescent : baseEnd_8326163 < baseStart_8326163 := by decide
  rcases family_descends (prefixWord ++ tailWord_8326163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8326170 : List Nat := [3, 1, 1, 3, 1, 2, 3, 2, 1, 1, 5]
def baseStart_8326170 : Nat := 118140960795 + 8326170 * 2 ^ 59
def prefixEnd_8326170 : Nat := 4983230072969 + 3 ^ 40 * 8326170 * 2
def baseEnd_8326170 : Nat := 4275327221045794055283647

theorem tailTrace_8326170 : CollatzResearch.WordTrace tailWord_8326170 prefixEnd_8326170 4275327221045794055283647 := by
  unfold tailWord_8326170
  simp only [CollatzResearch.WordTrace]
  refine ⟨75920092061428890367543991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202453578830477040980117309 75920092061428890367543991)
  ·
    refine ⟨113880138092143335551315987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75920092061428890367543991 113880138092143335551315987)
    ·
      refine ⟨170820207138215003326973981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113880138092143335551315987 170820207138215003326973981)
      ·
        refine ⟨64057577676830626247615243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170820207138215003326973981 64057577676830626247615243)
        ·
          refine ⟨96086366515245939371422865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64057577676830626247615243 96086366515245939371422865)
          ·
            refine ⟨72064774886434454528567149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96086366515245939371422865 72064774886434454528567149)
            ·
              refine ⟨27024290582412920448212681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72064774886434454528567149 27024290582412920448212681)
              ·
                refine ⟨20268217936809690336159511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27024290582412920448212681 20268217936809690336159511)
                ·
                  refine ⟨30402326905214535504239267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20268217936809690336159511 30402326905214535504239267)
                  ·
                    refine ⟨45603490357821803256358901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30402326905214535504239267 45603490357821803256358901)
                    ·
                      refine ⟨4275327221045794055283647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45603490357821803256358901 4275327221045794055283647)
                      ·
                        rfl

theorem cell23_8326170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 2, 1, 1, 5].length) (baseStart_8326170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8326170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8326170 prefixEnd_8326170 := by exact prefixLift 8326170
  have htrace : WordTrace (prefixWord ++ tailWord_8326170) baseStart_8326170 baseEnd_8326170 := by
    simpa [prefixWord, tailWord_8326170, baseEnd_8326170] using wordTrace_append hprefix tailTrace_8326170
  have hstable : (prefixWord ++ tailWord_8326170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8326170).length < 2 ^ (prefixWord ++ tailWord_8326170).sum := by decide
  have hdescent : baseEnd_8326170 < baseStart_8326170 := by decide
  rcases family_descends (prefixWord ++ tailWord_8326170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8326177 : List Nat := [1, 2, 3, 2, 3, 3, 1, 1, 1, 6]
def baseStart_8326177 : Nat := 118140960795 + 8326177 * 2 ^ 59
def prefixEnd_8326177 : Nat := 4983230072969 + 3 ^ 40 * 8326177 * 2
def baseEnd_8326177 : Nat := 1425110271803458509298705

theorem tailTrace_8326177 : CollatzResearch.WordTrace tailWord_8326177 prefixEnd_8326177 1425110271803458509298705 := by
  unfold tailWord_8326177
  simp only [CollatzResearch.WordTrace]
  refine ⟨303680623556690201665680785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202453749037793467777120523 303680623556690201665680785)
  ·
    refine ⟨227760467667517651249260589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303680623556690201665680785 227760467667517651249260589)
    ·
      refine ⟨85410175375319119218472721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227760467667517651249260589 85410175375319119218472721)
      ·
        refine ⟨64057631531489339413854541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85410175375319119218472721 64057631531489339413854541)
        ·
          refine ⟨24021611824308502280195453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64057631531489339413854541 24021611824308502280195453)
          ·
            refine ⟨9008104434115688355073295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24021611824308502280195453 9008104434115688355073295)
            ·
              refine ⟨13512156651173532532609943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9008104434115688355073295 13512156651173532532609943)
              ·
                refine ⟨20268234976760298798914915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13512156651173532532609943 20268234976760298798914915)
                ·
                  refine ⟨30402352465140448198372373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20268234976760298798914915 30402352465140448198372373)
                  ·
                    refine ⟨1425110271803458509298705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30402352465140448198372373 1425110271803458509298705)
                    ·
                      rfl

theorem cell23_8326177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 1, 1, 1, 6].length) (baseStart_8326177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8326177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8326177 prefixEnd_8326177 := by exact prefixLift 8326177
  have htrace : WordTrace (prefixWord ++ tailWord_8326177) baseStart_8326177 baseEnd_8326177 := by
    simpa [prefixWord, tailWord_8326177, baseEnd_8326177] using wordTrace_append hprefix tailTrace_8326177
  have hstable : (prefixWord ++ tailWord_8326177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8326177).length < 2 ^ (prefixWord ++ tailWord_8326177).sum := by decide
  have hdescent : baseEnd_8326177 < baseStart_8326177 := by decide
  rcases family_descends (prefixWord ++ tailWord_8326177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8326187 : List Nat := [1, 1, 1, 1, 2, 1, 8, 2, 1, 2, 3]
def baseStart_8326187 : Nat := 118140960795 + 8326187 * 2 ^ 59
def prefixEnd_8326187 : Nat := 4983230072969 + 3 ^ 40 * 8326187 * 2
def baseEnd_8326187 : Nat := 4275335950216920488771069

theorem tailTrace_8326187 : CollatzResearch.WordTrace tailWord_8326187 prefixEnd_8326187 4275335950216920488771069 := by
  unfold tailWord_8326187
  simp only [CollatzResearch.WordTrace]
  refine ⟨303680988286653973373544815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202453992191102648915696543 303680988286653973373544815)
  ·
    refine ⟨455521482429980960060317223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303680988286653973373544815 455521482429980960060317223)
    ·
      refine ⟨683282223644971440090475835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 455521482429980960060317223 683282223644971440090475835)
      ·
        refine ⟨1024923335467457160135713753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 683282223644971440090475835 1024923335467457160135713753)
        ·
          refine ⟨768692501600592870101785315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1024923335467457160135713753 768692501600592870101785315)
          ·
            refine ⟨1153038752400889305152677973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 768692501600592870101785315 1153038752400889305152677973)
            ·
              refine ⟨13512172879697921544757945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1153038752400889305152677973 13512172879697921544757945)
              ·
                refine ⟨10134129659773441158568459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13512172879697921544757945 10134129659773441158568459)
                ·
                  refine ⟨15201194489660161737852689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10134129659773441158568459 15201194489660161737852689)
                  ·
                    refine ⟨11400895867245121303389517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15201194489660161737852689 11400895867245121303389517)
                    ·
                      refine ⟨4275335950216920488771069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11400895867245121303389517 4275335950216920488771069)
                      ·
                        rfl

theorem cell23_8326187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 8, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 8, 2, 1, 2, 3].length) (baseStart_8326187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8326187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8326187 prefixEnd_8326187 := by exact prefixLift 8326187
  have htrace : WordTrace (prefixWord ++ tailWord_8326187) baseStart_8326187 baseEnd_8326187 := by
    simpa [prefixWord, tailWord_8326187, baseEnd_8326187] using wordTrace_append hprefix tailTrace_8326187
  have hstable : (prefixWord ++ tailWord_8326187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8326187).length < 2 ^ (prefixWord ++ tailWord_8326187).sum := by decide
  have hdescent : baseEnd_8326187 < baseStart_8326187 := by decide
  rcases family_descends (prefixWord ++ tailWord_8326187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8326190 : List Nat := [4, 1, 3, 1, 1, 1, 3, 9]
def baseStart_8326190 : Nat := 118140960795 + 8326190 * 2 ^ 59
def prefixEnd_8326190 : Nat := 4983230072969 + 3 ^ 40 * 8326190 * 2
def baseEnd_8326190 : Nat := 158345832987366073223465

theorem tailTrace_8326190 : CollatzResearch.WordTrace tailWord_8326190 prefixEnd_8326190 158345832987366073223465 := by
  unfold tailWord_8326190
  simp only [CollatzResearch.WordTrace]
  refine ⟨37960137213205388110738003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202454065137095403257269349 37960137213205388110738003)
  ·
    refine ⟨56940205819808082166107005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37960137213205388110738003 56940205819808082166107005)
    ·
      refine ⟨21352577182428030812290127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56940205819808082166107005 21352577182428030812290127)
      ·
        refine ⟨32028865773642046218435191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21352577182428030812290127 32028865773642046218435191)
        ·
          refine ⟨48043298660463069327652787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32028865773642046218435191 48043298660463069327652787)
          ·
            refine ⟨72064947990694603991479181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48043298660463069327652787 72064947990694603991479181)
            ·
              refine ⟨27024355496510476496804693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72064947990694603991479181 27024355496510476496804693)
              ·
                refine ⟨158345832987366073223465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 27024355496510476496804693 158345832987366073223465)
                ·
                  rfl

theorem cell23_8326190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 9].length) (baseStart_8326190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8326190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8326190 prefixEnd_8326190 := by exact prefixLift 8326190
  have htrace : WordTrace (prefixWord ++ tailWord_8326190) baseStart_8326190 baseEnd_8326190 := by
    simpa [prefixWord, tailWord_8326190, baseEnd_8326190] using wordTrace_append hprefix tailTrace_8326190
  have hstable : (prefixWord ++ tailWord_8326190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8326190).length < 2 ^ (prefixWord ++ tailWord_8326190).sum := by decide
  have hdescent : baseEnd_8326190 < baseStart_8326190 := by decide
  rcases family_descends (prefixWord ++ tailWord_8326190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8326238 : List Nat := [4, 4, 1, 1, 1, 1, 3, 2, 1, 2, 3]
def baseStart_8326238 : Nat := 118140960795 + 8326238 * 2 ^ 59
def prefixEnd_8326238 : Nat := 4983230072969 + 3 ^ 40 * 8326238 * 2
def baseEnd_8326238 : Nat := 4275362137730299789233335

theorem tailTrace_8326238 : CollatzResearch.WordTrace tailWord_8326238 prefixEnd_8326238 4275362137730299789233335 := by
  unfold tailWord_8326238
  simp only [CollatzResearch.WordTrace]
  refine ⟨37960356051183651135456421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202455232272979472722434245 37960356051183651135456421)
  ·
    refine ⟨7117566759596934587898079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37960356051183651135456421 7117566759596934587898079)
    ·
      refine ⟨10676350139395401881847119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7117566759596934587898079 10676350139395401881847119)
      ·
        refine ⟨16014525209093102822770679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10676350139395401881847119 16014525209093102822770679)
        ·
          refine ⟨24021787813639654234156019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16014525209093102822770679 24021787813639654234156019)
          ·
            refine ⟨36032681720459481351234029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24021787813639654234156019 36032681720459481351234029)
            ·
              refine ⟨13512255645172305506712761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36032681720459481351234029 13512255645172305506712761)
              ·
                refine ⟨10134191733879229130034571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13512255645172305506712761 10134191733879229130034571)
                ·
                  refine ⟨15201287600818843695051857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10134191733879229130034571 15201287600818843695051857)
                  ·
                    refine ⟨11400965700614132771288893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15201287600818843695051857 11400965700614132771288893)
                    ·
                      refine ⟨4275362137730299789233335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11400965700614132771288893 4275362137730299789233335)
                      ·
                        rfl

theorem cell23_8326238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_8326238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8326238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8326238 prefixEnd_8326238 := by exact prefixLift 8326238
  have htrace : WordTrace (prefixWord ++ tailWord_8326238) baseStart_8326238 baseEnd_8326238 := by
    simpa [prefixWord, tailWord_8326238, baseEnd_8326238] using wordTrace_append hprefix tailTrace_8326238
  have hstable : (prefixWord ++ tailWord_8326238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8326238).length < 2 ^ (prefixWord ++ tailWord_8326238).sum := by decide
  have hdescent : baseEnd_8326238 < baseStart_8326238 := by decide
  rcases family_descends (prefixWord ++ tailWord_8326238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8326342 : List Nat := [6, 1, 2, 2, 1, 2, 1, 1, 1, 4, 2]
def baseStart_8326342 : Nat := 118140960795 + 8326342 * 2 ^ 59
def prefixEnd_8326342 : Nat := 4983230072969 + 3 ^ 40 * 8326342 * 2
def baseEnd_8326342 : Nat := 4275415539718367382332857

theorem tailTrace_8326342 : CollatzResearch.WordTrace tailWord_8326342 prefixEnd_8326342 4275415539718367382332857 := by
  unfold tailWord_8326342
  simp only [CollatzResearch.WordTrace]
  refine ⟨9490207550034138588919915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 202457761067394956563624853 9490207550034138588919915)
  ·
    refine ⟨14235311325051207883379873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9490207550034138588919915 14235311325051207883379873)
    ·
      refine ⟨10676483493788405912534905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14235311325051207883379873 10676483493788405912534905)
      ·
        refine ⟨8007362620341304434401179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10676483493788405912534905 8007362620341304434401179)
        ·
          refine ⟨12011043930511956651601769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8007362620341304434401179 12011043930511956651601769)
          ·
            refine ⟨9008282947883967488701327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12011043930511956651601769 9008282947883967488701327)
            ·
              refine ⟨13512424421825951233051991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9008282947883967488701327 13512424421825951233051991)
              ·
                refine ⟨20268636632738926849577987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13512424421825951233051991 20268636632738926849577987)
                ·
                  refine ⟨30402954949108390274366981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20268636632738926849577987 30402954949108390274366981)
                  ·
                    refine ⟨5700554052957823176443809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30402954949108390274366981 5700554052957823176443809)
                    ·
                      refine ⟨4275415539718367382332857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5700554052957823176443809 4275415539718367382332857)
                      ·
                        rfl

theorem cell23_8326342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_8326342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8326342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8326342 prefixEnd_8326342 := by exact prefixLift 8326342
  have htrace : WordTrace (prefixWord ++ tailWord_8326342) baseStart_8326342 baseEnd_8326342 := by
    simpa [prefixWord, tailWord_8326342, baseEnd_8326342] using wordTrace_append hprefix tailTrace_8326342
  have hstable : (prefixWord ++ tailWord_8326342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8326342).length < 2 ^ (prefixWord ++ tailWord_8326342).sum := by decide
  have hdescent : baseEnd_8326342 < baseStart_8326342 := by decide
  rcases family_descends (prefixWord ++ tailWord_8326342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8326347 : List Nat := [1, 1, 1, 1, 3, 2, 2, 3, 1, 6, 2]
def baseStart_8326347 : Nat := 118140960795 + 8326347 * 2 ^ 59
def prefixEnd_8326347 : Nat := 4983230072969 + 3 ^ 40 * 8326347 * 2
def baseEnd_8326347 : Nat := 4275418107121639862770333

theorem tailTrace_8326347 : CollatzResearch.WordTrace tailWord_8326347 prefixEnd_8326347 4275418107121639862770333 := by
  unfold tailWord_8326347
  simp only [CollatzResearch.WordTrace]
  refine ⟨303686823966074320699369295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202457882644049547132912863 303686823966074320699369295)
  ·
    refine ⟨455530235949111481049053943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303686823966074320699369295 455530235949111481049053943)
    ·
      refine ⟨683295353923667221573580915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 455530235949111481049053943 683295353923667221573580915)
      ·
        refine ⟨1024943030885500832360371373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 683295353923667221573580915 1024943030885500832360371373)
        ·
          refine ⟨384353636582062812135139265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1024943030885500832360371373 384353636582062812135139265)
          ·
            refine ⟨288265227436547109101354449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 384353636582062812135139265 288265227436547109101354449)
            ·
              refine ⟨216198920577410331826015837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 288265227436547109101354449 216198920577410331826015837)
              ·
                refine ⟨81074595216528874434755939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 216198920577410331826015837 81074595216528874434755939)
                ·
                  refine ⟨121611892824793311652133909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81074595216528874434755939 121611892824793311652133909)
                  ·
                    refine ⟨5700557476162186483693777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 121611892824793311652133909 5700557476162186483693777)
                    ·
                      refine ⟨4275418107121639862770333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5700557476162186483693777 4275418107121639862770333)
                      ·
                        rfl

theorem cell23_8326347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 3, 1, 6, 2].length) (baseStart_8326347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8326347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8326347 prefixEnd_8326347 := by exact prefixLift 8326347
  have htrace : WordTrace (prefixWord ++ tailWord_8326347) baseStart_8326347 baseEnd_8326347 := by
    simpa [prefixWord, tailWord_8326347, baseEnd_8326347] using wordTrace_append hprefix tailTrace_8326347
  have hstable : (prefixWord ++ tailWord_8326347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8326347).length < 2 ^ (prefixWord ++ tailWord_8326347).sum := by decide
  have hdescent : baseEnd_8326347 < baseStart_8326347 := by decide
  rcases family_descends (prefixWord ++ tailWord_8326347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8326367 : List Nat := [1, 1, 2, 3, 2, 1, 4, 1, 1, 4, 3]
def baseStart_8326367 : Nat := 118140960795 + 8326367 * 2 ^ 59
def prefixEnd_8326367 : Nat := 4983230072969 + 3 ^ 40 * 8326367 * 2
def baseEnd_8326367 : Nat := 4275428376734729784520241

theorem tailTrace_8326367 : CollatzResearch.WordTrace tailWord_8326367 prefixEnd_8326367 4275428376734729784520241 := by
  unfold tailWord_8326367
  simp only [CollatzResearch.WordTrace]
  refine ⟨303687553426001864115097355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202458368950667909410064903 303687553426001864115097355)
  ·
    refine ⟨455531330139002796172646033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303687553426001864115097355 455531330139002796172646033)
    ·
      refine ⟨341648497604252097129484525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 455531330139002796172646033 341648497604252097129484525)
      ·
        refine ⟨128118186601594536423556697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 341648497604252097129484525 128118186601594536423556697)
        ·
          refine ⟨96088639951195902317667523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128118186601594536423556697 96088639951195902317667523)
          ·
            refine ⟨144132959926793853476501285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96088639951195902317667523 144132959926793853476501285)
            ·
              refine ⟨27024929986273847526843991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 144132959926793853476501285 27024929986273847526843991)
              ·
                refine ⟨40537394979410771290265987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27024929986273847526843991 40537394979410771290265987)
                ·
                  refine ⟨60806092469116156935398981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40537394979410771290265987 60806092469116156935398981)
                  ·
                    refine ⟨11401142337959279425387309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60806092469116156935398981 11401142337959279425387309)
                    ·
                      refine ⟨4275428376734729784520241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11401142337959279425387309 4275428376734729784520241)
                      ·
                        rfl

theorem cell23_8326367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 1, 1, 4, 3].length) (baseStart_8326367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8326367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8326367 prefixEnd_8326367 := by exact prefixLift 8326367
  have htrace : WordTrace (prefixWord ++ tailWord_8326367) baseStart_8326367 baseEnd_8326367 := by
    simpa [prefixWord, tailWord_8326367, baseEnd_8326367] using wordTrace_append hprefix tailTrace_8326367
  have hstable : (prefixWord ++ tailWord_8326367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8326367).length < 2 ^ (prefixWord ++ tailWord_8326367).sum := by decide
  have hdescent : baseEnd_8326367 < baseStart_8326367 := by decide
  rcases family_descends (prefixWord ++ tailWord_8326367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8326388 : List Nat := [2, 6, 1, 2, 1, 1, 1, 1, 1, 2, 5]
def baseStart_8326388 : Nat := 118140960795 + 8326388 * 2 ^ 59
def prefixEnd_8326388 : Nat := 4983230072969 + 3 ^ 40 * 8326388 * 2
def baseEnd_8326388 : Nat := 4275439159828474202357645

theorem tailTrace_8326388 : CollatzResearch.WordTrace tailWord_8326388 prefixEnd_8326388 4275439159828474202357645 := by
  unfold tailWord_8326388
  simp only [CollatzResearch.WordTrace]
  refine ⟨151844159679462892350805909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202458879572617189801074545 151844159679462892350805909)
  ·
    refine ⟨7117694984974823078944027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 151844159679462892350805909 7117694984974823078944027)
    ·
      refine ⟨10676542477462234618416041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7117694984974823078944027 10676542477462234618416041)
      ·
        refine ⟨8007406858096675963812031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10676542477462234618416041 8007406858096675963812031)
        ·
          refine ⟨12011110287145013945718047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8007406858096675963812031 12011110287145013945718047)
          ·
            refine ⟨18016665430717520918577071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12011110287145013945718047 18016665430717520918577071)
            ·
              refine ⟨27024998146076281377865607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18016665430717520918577071 27024998146076281377865607)
              ·
                refine ⟨40537497219114422066798411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27024998146076281377865607 40537497219114422066798411)
                ·
                  refine ⟨60806245828671633100197617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40537497219114422066798411 60806245828671633100197617)
                  ·
                    refine ⟨45604684371503724825148213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60806245828671633100197617 45604684371503724825148213)
                    ·
                      refine ⟨4275439159828474202357645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45604684371503724825148213 4275439159828474202357645)
                      ·
                        rfl

theorem cell23_8326388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_8326388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8326388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8326388 prefixEnd_8326388 := by exact prefixLift 8326388
  have htrace : WordTrace (prefixWord ++ tailWord_8326388) baseStart_8326388 baseEnd_8326388 := by
    simpa [prefixWord, tailWord_8326388, baseEnd_8326388] using wordTrace_append hprefix tailTrace_8326388
  have hstable : (prefixWord ++ tailWord_8326388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8326388).length < 2 ^ (prefixWord ++ tailWord_8326388).sum := by decide
  have hdescent : baseEnd_8326388 < baseStart_8326388 := by decide
  rcases family_descends (prefixWord ++ tailWord_8326388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8326400 : List Nat := [2, 1, 1, 2, 1, 1, 3, 1, 2, 9]
def baseStart_8326400 : Nat := 118140960795 + 8326400 * 2 ^ 59
def prefixEnd_8326400 : Nat := 4983230072969 + 3 ^ 40 * 8326400 * 2
def baseEnd_8326400 : Nat := 1425148440532109385135863

theorem tailTrace_8326400 : CollatzResearch.WordTrace tailWord_8326400 prefixEnd_8326400 1425148440532109385135863 := by
  unfold tailWord_8326400
  simp only [CollatzResearch.WordTrace]
  refine ⟨151844378517441155375524327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202459171356588207167365769 151844378517441155375524327)
  ·
    refine ⟨227766567776161733063286491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151844378517441155375524327 227766567776161733063286491)
    ·
      refine ⟨341649851664242599594929737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227766567776161733063286491 341649851664242599594929737)
      ·
        refine ⟨256237388748181949696197303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 341649851664242599594929737 256237388748181949696197303)
        ·
          refine ⟨384356083122272924544295955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256237388748181949696197303 384356083122272924544295955)
          ·
            refine ⟨576534124683409386816443933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 384356083122272924544295955 576534124683409386816443933)
            ·
              refine ⟨216200296756278520056166475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 576534124683409386816443933 216200296756278520056166475)
              ·
                refine ⟨324300445134417780084249713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 216200296756278520056166475 324300445134417780084249713)
                ·
                  refine ⟨243225333850813335063187285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 324300445134417780084249713 243225333850813335063187285)
                  ·
                    refine ⟨1425148440532109385135863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 243225333850813335063187285 1425148440532109385135863)
                    ·
                      rfl

theorem cell23_8326400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 2, 9].length) (baseStart_8326400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8326400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8326400 prefixEnd_8326400 := by exact prefixLift 8326400
  have htrace : WordTrace (prefixWord ++ tailWord_8326400) baseStart_8326400 baseEnd_8326400 := by
    simpa [prefixWord, tailWord_8326400, baseEnd_8326400] using wordTrace_append hprefix tailTrace_8326400
  have hstable : (prefixWord ++ tailWord_8326400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8326400).length < 2 ^ (prefixWord ++ tailWord_8326400).sum := by decide
  have hdescent : baseEnd_8326400 < baseStart_8326400 := by decide
  rcases family_descends (prefixWord ++ tailWord_8326400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8326404 : List Nat := [2, 3, 2, 2, 2, 2, 1, 3, 6]
def baseStart_8326404 : Nat := 118140960795 + 8326404 * 2 ^ 59
def prefixEnd_8326404 : Nat := 4983230072969 + 3 ^ 40 * 8326404 * 2
def baseEnd_8326404 : Nat := 475049708390994015528619

theorem tailTrace_8326404 : CollatzResearch.WordTrace tailWord_8326404 prefixEnd_8326404 475049708390994015528619 := by
  unfold tailWord_8326404
  simp only [CollatzResearch.WordTrace]
  refine ⟨151844451463433909717097133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202459268617911879622796177 151844451463433909717097133)
  ·
    refine ⟨56941669298787716143911425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151844451463433909717097133 56941669298787716143911425)
    ·
      refine ⟨42706251974090787107933569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56941669298787716143911425 42706251974090787107933569)
      ·
        refine ⟨32029688980568090330950177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42706251974090787107933569 32029688980568090330950177)
        ·
          refine ⟨24022266735426067748212633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32029688980568090330950177 24022266735426067748212633)
          ·
            refine ⟨18016700051569550811159475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24022266735426067748212633 18016700051569550811159475)
            ·
              refine ⟨27025050077354326216739213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18016700051569550811159475 27025050077354326216739213)
              ·
                refine ⟨10134393779007872331277205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27025050077354326216739213 10134393779007872331277205)
                ·
                  refine ⟨475049708390994015528619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10134393779007872331277205 475049708390994015528619)
                  ·
                    rfl

theorem cell23_8326404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 3, 6].length) (baseStart_8326404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8326404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8326404 prefixEnd_8326404 := by exact prefixLift 8326404
  have htrace : WordTrace (prefixWord ++ tailWord_8326404) baseStart_8326404 baseEnd_8326404 := by
    simpa [prefixWord, tailWord_8326404, baseEnd_8326404] using wordTrace_append hprefix tailTrace_8326404
  have hstable : (prefixWord ++ tailWord_8326404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8326404).length < 2 ^ (prefixWord ++ tailWord_8326404).sum := by decide
  have hdescent : baseEnd_8326404 < baseStart_8326404 := by decide
  rcases family_descends (prefixWord ++ tailWord_8326404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8326417 : List Nat := [1, 2, 2, 1, 1, 4, 3, 1, 3, 5]
def baseStart_8326417 : Nat := 118140960795 + 8326417 * 2 ^ 59
def prefixEnd_8326417 : Nat := 4983230072969 + 3 ^ 40 * 8326417 * 2
def baseEnd_8326417 : Nat := 1425151350255818196298337

theorem tailTrace_8326417 : CollatzResearch.WordTrace tailWord_8326417 prefixEnd_8326417 1425151350255818196298337 := by
  unfold tailWord_8326417
  simp only [CollatzResearch.WordTrace]
  refine ⟨303689377075820722654417505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202459584717213815102945003 303689377075820722654417505)
  ·
    refine ⟨227767032806865541990813129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303689377075820722654417505 227767032806865541990813129)
    ·
      refine ⟨170825274605149156493109847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227767032806865541990813129 170825274605149156493109847)
      ·
        refine ⟨256237911907723734739664771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170825274605149156493109847 256237911907723734739664771)
        ·
          refine ⟨384356867861585602109497157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256237911907723734739664771 384356867861585602109497157)
          ·
            refine ⟨72066912724047300395530717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 384356867861585602109497157 72066912724047300395530717)
            ·
              refine ⟨27025092271517737648324019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72066912724047300395530717 27025092271517737648324019)
              ·
                refine ⟨40537638407276606472486029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27025092271517737648324019 40537638407276606472486029)
                ·
                  refine ⟨15201614402728727427182261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40537638407276606472486029 15201614402728727427182261)
                  ·
                    refine ⟨1425151350255818196298337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15201614402728727427182261 1425151350255818196298337)
                    ·
                      rfl

theorem cell23_8326417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 5].length) (baseStart_8326417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8326417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8326417 prefixEnd_8326417 := by exact prefixLift 8326417
  have htrace : WordTrace (prefixWord ++ tailWord_8326417) baseStart_8326417 baseEnd_8326417 := by
    simpa [prefixWord, tailWord_8326417, baseEnd_8326417] using wordTrace_append hprefix tailTrace_8326417
  have hstable : (prefixWord ++ tailWord_8326417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8326417).length < 2 ^ (prefixWord ++ tailWord_8326417).sum := by decide
  have hdescent : baseEnd_8326417 < baseStart_8326417 := by decide
  rcases family_descends (prefixWord ++ tailWord_8326417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8326464 : List Nat := [2, 1, 1, 2, 2, 1, 3, 5, 2, 4]
def baseStart_8326464 : Nat := 118140960795 + 8326464 * 2 ^ 59
def prefixEnd_8326464 : Nat := 4983230072969 + 3 ^ 40 * 8326464 * 2
def baseEnd_8326464 : Nat := 1425159394786071968335765

theorem tailTrace_8326464 : CollatzResearch.WordTrace tailWord_8326464 prefixEnd_8326464 1425159394786071968335765 := by
  unfold tailWord_8326464
  simp only [CollatzResearch.WordTrace]
  refine ⟨151845545653325224840689223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202460727537766966454252297 151845545653325224840689223)
  ·
    refine ⟨227768318479987837261033835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151845545653325224840689223 227768318479987837261033835)
    ·
      refine ⟨341652477719981755891550753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227768318479987837261033835 341652477719981755891550753)
      ·
        refine ⟨256239358289986316918663065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 341652477719981755891550753 256239358289986316918663065)
        ·
          refine ⟨192179518717489737688997299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256239358289986316918663065 192179518717489737688997299)
          ·
            refine ⟨288269278076234606533495949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192179518717489737688997299 288269278076234606533495949)
            ·
              refine ⟨108100979278587977450060981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 288269278076234606533495949 108100979278587977450060981)
              ·
                refine ⟨10134466807367622885943217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 108100979278587977450060981 10134466807367622885943217)
                ·
                  refine ⟨7600850105525717164457413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10134466807367622885943217 7600850105525717164457413)
                  ·
                    refine ⟨1425159394786071968335765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7600850105525717164457413 1425159394786071968335765)
                    ·
                      rfl

theorem cell23_8326464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 5, 2, 4].length) (baseStart_8326464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8326464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8326464 prefixEnd_8326464 := by exact prefixLift 8326464
  have htrace : WordTrace (prefixWord ++ tailWord_8326464) baseStart_8326464 baseEnd_8326464 := by
    simpa [prefixWord, tailWord_8326464, baseEnd_8326464] using wordTrace_append hprefix tailTrace_8326464
  have hstable : (prefixWord ++ tailWord_8326464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8326464).length < 2 ^ (prefixWord ++ tailWord_8326464).sum := by decide
  have hdescent : baseEnd_8326464 < baseStart_8326464 := by decide
  rcases family_descends (prefixWord ++ tailWord_8326464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8326471 : List Nat := [1, 1, 4, 1, 2, 3, 1, 1, 5, 2, 2]
def baseStart_8326471 : Nat := 118140960795 + 8326471 * 2 ^ 59
def prefixEnd_8326471 : Nat := 4983230072969 + 3 ^ 40 * 8326471 * 2
def baseEnd_8326471 : Nat := 4275481778722797377619763

theorem tailTrace_8326471 : CollatzResearch.WordTrace tailWord_8326471 prefixEnd_8326471 4275481778722797377619763 := by
  unfold tailWord_8326471
  simp only [CollatzResearch.WordTrace]
  refine ⟨303691346617625089876883267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202460897745083393251255511 303691346617625089876883267)
  ·
    refine ⟨455537019926437634815324901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303691346617625089876883267 455537019926437634815324901)
    ·
      refine ⟨85413191236207056527873419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 455537019926437634815324901 85413191236207056527873419)
      ·
        refine ⟨128119786854310584791810129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85413191236207056527873419 128119786854310584791810129)
        ·
          refine ⟨96089840140732938593857597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128119786854310584791810129 96089840140732938593857597)
          ·
            refine ⟨36033690052774851972696599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96089840140732938593857597 36033690052774851972696599)
            ·
              refine ⟨54050535079162277959044899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36033690052774851972696599 54050535079162277959044899)
              ·
                refine ⟨81075802618743416938567349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54050535079162277959044899 81075802618743416938567349)
                ·
                  refine ⟨7600856495507195337990689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 81075802618743416938567349 7600856495507195337990689)
                  ·
                    refine ⟨5700642371630396503493017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7600856495507195337990689 5700642371630396503493017)
                    ·
                      refine ⟨4275481778722797377619763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5700642371630396503493017 4275481778722797377619763)
                      ·
                        rfl

theorem cell23_8326471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 1, 5, 2, 2].length) (baseStart_8326471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8326471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8326471 prefixEnd_8326471 := by exact prefixLift 8326471
  have htrace : WordTrace (prefixWord ++ tailWord_8326471) baseStart_8326471 baseEnd_8326471 := by
    simpa [prefixWord, tailWord_8326471, baseEnd_8326471] using wordTrace_append hprefix tailTrace_8326471
  have hstable : (prefixWord ++ tailWord_8326471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8326471).length < 2 ^ (prefixWord ++ tailWord_8326471).sum := by decide
  have hdescent : baseEnd_8326471 < baseStart_8326471 := by decide
  rcases family_descends (prefixWord ++ tailWord_8326471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8326484 : List Nat := [2, 4, 1, 1, 2, 1, 1, 4, 1, 2, 4]
def baseStart_8326484 : Nat := 118140960795 + 8326484 * 2 ^ 59
def prefixEnd_8326484 : Nat := 4983230072969 + 3 ^ 40 * 8326484 * 2
def baseEnd_8326484 : Nat := 4275488453971305826757203

theorem tailTrace_8326484 : CollatzResearch.WordTrace tailWord_8326484 prefixEnd_8326484 4275488453971305826757203 := by
  unfold tailWord_8326484
  simp only [CollatzResearch.WordTrace]
  refine ⟨151845910383288996548553253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202461213844385328731404337 151845910383288996548553253)
  ·
    refine ⟨28471108196866686852853735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151845910383288996548553253 28471108196866686852853735)
    ·
      refine ⟨42706662295300030279280603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28471108196866686852853735 42706662295300030279280603)
      ·
        refine ⟨64059993442950045418920905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42706662295300030279280603 64059993442950045418920905)
        ·
          refine ⟨48044995082212534064190679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64059993442950045418920905 48044995082212534064190679)
          ·
            refine ⟨72067492623318801096286019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48044995082212534064190679 72067492623318801096286019)
            ·
              refine ⟨108101238934978201644429029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72067492623318801096286019 108101238934978201644429029)
              ·
                refine ⟨20268982300308412808330443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 108101238934978201644429029 20268982300308412808330443)
                ·
                  refine ⟨30403473450462619212495665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20268982300308412808330443 30403473450462619212495665)
                  ·
                    refine ⟨22802605087846964409371749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30403473450462619212495665 22802605087846964409371749)
                    ·
                      refine ⟨4275488453971305826757203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22802605087846964409371749 4275488453971305826757203)
                      ·
                        rfl

theorem cell23_8326484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 4, 1, 2, 4].length) (baseStart_8326484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8326484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8326484 prefixEnd_8326484 := by exact prefixLift 8326484
  have htrace : WordTrace (prefixWord ++ tailWord_8326484) baseStart_8326484 baseEnd_8326484 := by
    simpa [prefixWord, tailWord_8326484, baseEnd_8326484] using wordTrace_append hprefix tailTrace_8326484
  have hstable : (prefixWord ++ tailWord_8326484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8326484).length < 2 ^ (prefixWord ++ tailWord_8326484).sum := by decide
  have hdescent : baseEnd_8326484 < baseStart_8326484 := by decide
  rcases family_descends (prefixWord ++ tailWord_8326484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8326521 : List Nat := [1, 2, 1, 3, 2, 1, 2, 5, 2, 1, 3]
def baseStart_8326521 : Nat := 118140960795 + 8326521 * 2 ^ 59
def prefixEnd_8326521 : Nat := 4983230072969 + 3 ^ 40 * 8326521 * 2
def baseEnd_8326521 : Nat := 4275507452755522181994533

theorem tailTrace_8326521 : CollatzResearch.WordTrace tailWord_8326521 prefixEnd_8326521 4275507452755522181994533 := by
  unfold tailWord_8326521
  simp only [CollatzResearch.WordTrace]
  refine ⟨303693170267443948416203417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202462113511629298944135611 303693170267443948416203417)
  ·
    refine ⟨227769877700582961312152563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303693170267443948416203417 227769877700582961312152563)
    ·
      refine ⟨341654816550874441968228845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227769877700582961312152563 341654816550874441968228845)
      ·
        refine ⟨128120556206577915738085817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 341654816550874441968228845 128120556206577915738085817)
        ·
          refine ⟨96090417154933436803564363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128120556206577915738085817 96090417154933436803564363)
          ·
            refine ⟨144135625732400155205346545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96090417154933436803564363 144135625732400155205346545)
            ·
              refine ⟨108101719299300116404009909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144135625732400155205346545 108101719299300116404009909)
              ·
                refine ⟨10134536184309385912875929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 108101719299300116404009909 10134536184309385912875929)
                ·
                  refine ⟨7600902138232039434656947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10134536184309385912875929 7600902138232039434656947)
                  ·
                    refine ⟨11401353207348059151985421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7600902138232039434656947 11401353207348059151985421)
                    ·
                      refine ⟨4275507452755522181994533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11401353207348059151985421 4275507452755522181994533)
                      ·
                        rfl

theorem cell23_8326521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 5, 2, 1, 3].length) (baseStart_8326521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8326521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8326521 prefixEnd_8326521 := by exact prefixLift 8326521
  have htrace : WordTrace (prefixWord ++ tailWord_8326521) baseStart_8326521 baseEnd_8326521 := by
    simpa [prefixWord, tailWord_8326521, baseEnd_8326521] using wordTrace_append hprefix tailTrace_8326521
  have hstable : (prefixWord ++ tailWord_8326521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8326521).length < 2 ^ (prefixWord ++ tailWord_8326521).sum := by decide
  have hdescent : baseEnd_8326521 < baseStart_8326521 := by decide
  rcases family_descends (prefixWord ++ tailWord_8326521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8326564 : List Nat := [2, 3, 1, 2, 1, 1, 1, 3, 2, 4, 3]
def baseStart_8326564 : Nat := 118140960795 + 8326564 * 2 ^ 59
def prefixEnd_8326564 : Nat := 4983230072969 + 3 ^ 40 * 8326564 * 2
def baseEnd_8326564 : Nat := 4275529532423665513756835

theorem tailTrace_8326564 : CollatzResearch.WordTrace tailWord_8326564 prefixEnd_8326564 4275529532423665513756835 := by
  unfold tailWord_8326564
  simp only [CollatzResearch.WordTrace]
  refine ⟨151847369303144083380009373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202463159070858777840012497 151847369303144083380009373)
  ·
    refine ⟨56942763488679031267503515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151847369303144083380009373 56942763488679031267503515)
    ·
      refine ⟨85414145233018546901255273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56942763488679031267503515 85414145233018546901255273)
      ·
        refine ⟨64060608924763910175941455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85414145233018546901255273 64060608924763910175941455)
        ·
          refine ⟨96090913387145865263912183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64060608924763910175941455 96090913387145865263912183)
          ·
            refine ⟨144136370080718797895868275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96090913387145865263912183 144136370080718797895868275)
            ·
              refine ⟨216204555121078196843802413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144136370080718797895868275 216204555121078196843802413)
              ·
                refine ⟨81076708170404323816425905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 216204555121078196843802413 81076708170404323816425905)
                ·
                  refine ⟨60807531127803242862319429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81076708170404323816425905 60807531127803242862319429)
                  ·
                    refine ⟨11401412086463108036684893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60807531127803242862319429 11401412086463108036684893)
                    ·
                      refine ⟨4275529532423665513756835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11401412086463108036684893 4275529532423665513756835)
                      ·
                        rfl

theorem cell23_8326564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 3, 2, 4, 3].length) (baseStart_8326564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8326564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8326564 prefixEnd_8326564 := by exact prefixLift 8326564
  have htrace : WordTrace (prefixWord ++ tailWord_8326564) baseStart_8326564 baseEnd_8326564 := by
    simpa [prefixWord, tailWord_8326564, baseEnd_8326564] using wordTrace_append hprefix tailTrace_8326564
  have hstable : (prefixWord ++ tailWord_8326564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8326564).length < 2 ^ (prefixWord ++ tailWord_8326564).sum := by decide
  have hdescent : baseEnd_8326564 < baseStart_8326564 := by decide
  rcases family_descends (prefixWord ++ tailWord_8326564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8326612 : List Nat := [2, 4, 1, 2, 3, 1, 2, 2, 2, 2, 2]
def baseStart_8326612 : Nat := 118140960795 + 8326612 * 2 ^ 59
def prefixEnd_8326612 : Nat := 4983230072969 + 3 ^ 40 * 8326612 * 2
def baseEnd_8326612 : Nat := 4275554179495081325956615

theorem tailTrace_8326612 : CollatzResearch.WordTrace tailWord_8326612 prefixEnd_8326612 4275554179495081325956615 := by
  unfold tailWord_8326612
  simp only [CollatzResearch.WordTrace]
  refine ⟨151848244655057135478883045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202464326206742847305177393 151848244655057135478883045)
  ·
    refine ⟨28471545872823212902290571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151848244655057135478883045 28471545872823212902290571)
    ·
      refine ⟨42707318809234819353435857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28471545872823212902290571 42707318809234819353435857)
      ·
        refine ⟨32030489106926114515076893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42707318809234819353435857 32030489106926114515076893)
        ·
          refine ⟨12011433415097292943153835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32030489106926114515076893 12011433415097292943153835)
          ·
            refine ⟨18017150122645939414730753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12011433415097292943153835 18017150122645939414730753)
            ·
              refine ⟨13512862591984454561048065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18017150122645939414730753 13512862591984454561048065)
              ·
                refine ⟨10134646943988340920786049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13512862591984454561048065 10134646943988340920786049)
                ·
                  refine ⟨7600985207991255690589537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10134646943988340920786049 7600985207991255690589537)
                  ·
                    refine ⟨5700738905993441767942153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7600985207991255690589537 5700738905993441767942153)
                    ·
                      refine ⟨4275554179495081325956615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5700738905993441767942153 4275554179495081325956615)
                      ·
                        rfl

theorem cell23_8326612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 2, 2, 2, 2, 2].length) (baseStart_8326612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8326612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8326612 prefixEnd_8326612 := by exact prefixLift 8326612
  have htrace : WordTrace (prefixWord ++ tailWord_8326612) baseStart_8326612 baseEnd_8326612 := by
    simpa [prefixWord, tailWord_8326612, baseEnd_8326612] using wordTrace_append hprefix tailTrace_8326612
  have hstable : (prefixWord ++ tailWord_8326612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8326612).length < 2 ^ (prefixWord ++ tailWord_8326612).sum := by decide
  have hdescent : baseEnd_8326612 < baseStart_8326612 := by decide
  rcases family_descends (prefixWord ++ tailWord_8326612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8326618 : List Nat := [3, 1, 1, 2, 3, 2, 4, 2, 5]
def baseStart_8326618 : Nat := 118140960795 + 8326618 * 2 ^ 59
def prefixEnd_8326618 : Nat := 4983230072969 + 3 ^ 40 * 8326618 * 2
def baseEnd_8326618 : Nat := 475061917819889811386843

theorem tailTrace_8326618 : CollatzResearch.WordTrace tailWord_8326618 prefixEnd_8326618 475061917819889811386843 := by
  unfold tailWord_8326618
  simp only [CollatzResearch.WordTrace]
  refine ⟨75924177037023133495621127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202464472098728355988323005 75924177037023133495621127)
  ·
    refine ⟨113886265555534700243431691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75924177037023133495621127 113886265555534700243431691)
    ·
      refine ⟨170829398333302050365147537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113886265555534700243431691 170829398333302050365147537)
      ·
        refine ⟨128122048749976537773860653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170829398333302050365147537 128122048749976537773860653)
        ·
          refine ⟨48045768281241201665197745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128122048749976537773860653 48045768281241201665197745)
          ·
            refine ⟨36034326210930901248898309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48045768281241201665197745 36034326210930901248898309)
            ·
              refine ⟨6756436164549543984168433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36034326210930901248898309 6756436164549543984168433)
              ·
                refine ⟨5067327123412157988126325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6756436164549543984168433 5067327123412157988126325)
                ·
                  refine ⟨475061917819889811386843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5067327123412157988126325 475061917819889811386843)
                  ·
                    rfl

theorem cell23_8326618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 4, 2, 5].length) (baseStart_8326618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8326618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8326618 prefixEnd_8326618 := by exact prefixLift 8326618
  have htrace : WordTrace (prefixWord ++ tailWord_8326618) baseStart_8326618 baseEnd_8326618 := by
    simpa [prefixWord, tailWord_8326618, baseEnd_8326618] using wordTrace_append hprefix tailTrace_8326618
  have hstable : (prefixWord ++ tailWord_8326618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8326618).length < 2 ^ (prefixWord ++ tailWord_8326618).sum := by decide
  have hdescent : baseEnd_8326618 < baseStart_8326618 := by decide
  rcases family_descends (prefixWord ++ tailWord_8326618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8326664 : List Nat := [2, 1, 3, 2, 1, 1, 3, 1, 2, 1, 6]
def baseStart_8326664 : Nat := 118140960795 + 8326664 * 2 ^ 59
def prefixEnd_8326664 : Nat := 4983230072969 + 3 ^ 40 * 8326664 * 2
def baseEnd_8326664 : Nat := 4275580880489115122506375

theorem tailTrace_8326664 : CollatzResearch.WordTrace tailWord_8326664 prefixEnd_8326664 4275580880489115122506375 := by
  unfold tailWord_8326664
  simp only [CollatzResearch.WordTrace]
  refine ⟨151849192952962941919329523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202465590603950589225772697 151849192952962941919329523)
  ·
    refine ⟨227773789429444412878994285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151849192952962941919329523 227773789429444412878994285)
    ·
      refine ⟨85415171036041654829622857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227773789429444412878994285 85415171036041654829622857)
      ·
        refine ⟨64061378277031241122217143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85415171036041654829622857 64061378277031241122217143)
        ·
          refine ⟨96092067415546861683325715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64061378277031241122217143 96092067415546861683325715)
          ·
            refine ⟨144138101123320292524988573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96092067415546861683325715 144138101123320292524988573)
            ·
              refine ⟨54051787921245109696870715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144138101123320292524988573 54051787921245109696870715)
              ·
                refine ⟨81077681881867664545306073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54051787921245109696870715 81077681881867664545306073)
                ·
                  refine ⟨60808261411400748408979555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81077681881867664545306073 60808261411400748408979555)
                  ·
                    refine ⟨91212392117101122613469333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60808261411400748408979555 91212392117101122613469333)
                    ·
                      refine ⟨4275580880489115122506375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91212392117101122613469333 4275580880489115122506375)
                      ·
                        rfl

theorem cell23_8326664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 1, 2, 1, 6].length) (baseStart_8326664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8326664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8326664 prefixEnd_8326664 := by exact prefixLift 8326664
  have htrace : WordTrace (prefixWord ++ tailWord_8326664) baseStart_8326664 baseEnd_8326664 := by
    simpa [prefixWord, tailWord_8326664, baseEnd_8326664] using wordTrace_append hprefix tailTrace_8326664
  have hstable : (prefixWord ++ tailWord_8326664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8326664).length < 2 ^ (prefixWord ++ tailWord_8326664).sum := by decide
  have hdescent : baseEnd_8326664 < baseStart_8326664 := by decide
  rcases family_descends (prefixWord ++ tailWord_8326664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8326741 : List Nat := [1, 3, 2, 2, 1, 1, 1, 4, 3, 1, 4]
def baseStart_8326741 : Nat := 118140960795 + 8326741 * 2 ^ 59
def prefixEnd_8326741 : Nat := 4983230072969 + 3 ^ 40 * 8326741 * 2
def baseEnd_8326741 : Nat := 4275620418499511321243521

theorem tailTrace_8326741 : CollatzResearch.WordTrace tailWord_8326741 prefixEnd_8326741 4275620418499511321243521 := by
  unfold tailWord_8326741
  simp only [CollatzResearch.WordTrace]
  refine ⟨303701194326646925989212077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202467462884431283992808051 303701194326646925989212077)
  ·
    refine ⟨113887947872492597245954529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 303701194326646925989212077 113887947872492597245954529)
    ·
      refine ⟨85415960904369447934465897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113887947872492597245954529 85415960904369447934465897)
      ·
        refine ⟨64061970678277085950849423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85415960904369447934465897 64061970678277085950849423)
        ·
          refine ⟨96092956017415628926274135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64061970678277085950849423 96092956017415628926274135)
          ·
            refine ⟨144139434026123443389411203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96092956017415628926274135 144139434026123443389411203)
            ·
              refine ⟨216209151039185165084116805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144139434026123443389411203 216209151039185165084116805)
              ·
                refine ⟨40539215819847218453271901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 216209151039185165084116805 40539215819847218453271901)
                ·
                  refine ⟨15202205932442706919976963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40539215819847218453271901 15202205932442706919976963)
                  ·
                    refine ⟨22803308898664060379965445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15202205932442706919976963 22803308898664060379965445)
                    ·
                      refine ⟨4275620418499511321243521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22803308898664060379965445 4275620418499511321243521)
                      ·
                        rfl

theorem cell23_8326741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 4, 3, 1, 4].length) (baseStart_8326741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8326741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8326741 prefixEnd_8326741 := by exact prefixLift 8326741
  have htrace : WordTrace (prefixWord ++ tailWord_8326741) baseStart_8326741 baseEnd_8326741 := by
    simpa [prefixWord, tailWord_8326741, baseEnd_8326741] using wordTrace_append hprefix tailTrace_8326741
  have hstable : (prefixWord ++ tailWord_8326741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8326741).length < 2 ^ (prefixWord ++ tailWord_8326741).sum := by decide
  have hdescent : baseEnd_8326741 < baseStart_8326741 := by decide
  rcases family_descends (prefixWord ++ tailWord_8326741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8326742 : List Nat := [5, 2, 2, 2, 1, 1, 1, 3, 6]
def baseStart_8326742 : Nat := 118140960795 + 8326742 * 2 ^ 59
def prefixEnd_8326742 : Nat := 4983230072969 + 3 ^ 40 * 8326742 * 2
def baseEnd_8326742 : Nat := 475068992442240646370113

theorem tailTrace_8326742 : CollatzResearch.WordTrace tailWord_8326742 prefixEnd_8326742 475068992442240646370113 := by
  unfold tailWord_8326742
  simp only [CollatzResearch.WordTrace]
  refine ⟨18981326924977706447499905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 202467487199762202106665653 18981326924977706447499905)
  ·
    refine ⟨14235995193733279835624929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18981326924977706447499905 14235995193733279835624929)
    ·
      refine ⟨10676996395299959876718697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14235995193733279835624929 10676996395299959876718697)
      ·
        refine ⟨8007747296474969907539023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10676996395299959876718697 8007747296474969907539023)
        ·
          refine ⟨12011620944712454861308535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8007747296474969907539023 12011620944712454861308535)
          ·
            refine ⟨18017431417068682291962803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12011620944712454861308535 18017431417068682291962803)
            ·
              refine ⟨27026147125603023437944205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18017431417068682291962803 27026147125603023437944205)
              ·
                refine ⟨10134805172101133789229077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27026147125603023437944205 10134805172101133789229077)
                ·
                  refine ⟨475068992442240646370113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10134805172101133789229077 475068992442240646370113)
                  ·
                    rfl

theorem cell23_8326742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 3, 6].length) (baseStart_8326742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8326742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8326742 prefixEnd_8326742 := by exact prefixLift 8326742
  have htrace : WordTrace (prefixWord ++ tailWord_8326742) baseStart_8326742 baseEnd_8326742 := by
    simpa [prefixWord, tailWord_8326742, baseEnd_8326742] using wordTrace_append hprefix tailTrace_8326742
  have hstable : (prefixWord ++ tailWord_8326742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8326742).length < 2 ^ (prefixWord ++ tailWord_8326742).sum := by decide
  have hdescent : baseEnd_8326742 < baseStart_8326742 := by decide
  rcases family_descends (prefixWord ++ tailWord_8326742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8326785 : List Nat := [1, 2, 4, 2, 1, 3, 2, 2, 2, 4]
def baseStart_8326785 : Nat := 118140960795 + 8326785 * 2 ^ 59
def prefixEnd_8326785 : Nat := 4983230072969 + 3 ^ 40 * 8326785 * 2
def baseEnd_8326785 : Nat := 1425214337216103049697773

theorem tailTrace_8326785 : CollatzResearch.WordTrace tailWord_8326785 prefixEnd_8326785 1425214337216103049697773 := by
  unfold tailWord_8326785
  simp only [CollatzResearch.WordTrace]
  refine ⟨303702799138487521503813809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202468532758991681002542539 303702799138487521503813809)
  ·
    refine ⟨227777099353865641127860357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303702799138487521503813809 227777099353865641127860357)
    ·
      refine ⟨42708206128849807711473817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 227777099353865641127860357 42708206128849807711473817)
      ·
        refine ⟨32031154596637355783605363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42708206128849807711473817 32031154596637355783605363)
        ·
          refine ⟨48046731894956033675408045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32031154596637355783605363 48046731894956033675408045)
          ·
            refine ⟨18017524460608512628278017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48046731894956033675408045 18017524460608512628278017)
            ·
              refine ⟨13513143345456384471208513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18017524460608512628278017 13513143345456384471208513)
              ·
                refine ⟨10134857509092288353406385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13513143345456384471208513 10134857509092288353406385)
                ·
                  refine ⟨7601143131819216265054789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10134857509092288353406385 7601143131819216265054789)
                  ·
                    refine ⟨1425214337216103049697773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7601143131819216265054789 1425214337216103049697773)
                    ·
                      rfl

theorem cell23_8326785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 2, 2, 2, 4].length) (baseStart_8326785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8326785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8326785 prefixEnd_8326785 := by exact prefixLift 8326785
  have htrace : WordTrace (prefixWord ++ tailWord_8326785) baseStart_8326785 baseEnd_8326785 := by
    simpa [prefixWord, tailWord_8326785, baseEnd_8326785] using wordTrace_append hprefix tailTrace_8326785
  have hstable : (prefixWord ++ tailWord_8326785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8326785).length < 2 ^ (prefixWord ++ tailWord_8326785).sum := by decide
  have hdescent : baseEnd_8326785 < baseStart_8326785 := by decide
  rcases family_descends (prefixWord ++ tailWord_8326785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8326798 : List Nat := [4, 1, 1, 3, 1, 4, 1, 8]
def baseStart_8326798 : Nat := 118140960795 + 8326798 * 2 ^ 59
def prefixEnd_8326798 : Nat := 4983230072969 + 3 ^ 40 * 8326798 * 2
def baseEnd_8326798 : Nat := 158357395810993244378917

theorem tailTrace_8326798 : CollatzResearch.WordTrace tailWord_8326798 prefixEnd_8326798 158357395810993244378917 := by
  unfold tailWord_8326798
  simp only [CollatzResearch.WordTrace]
  refine ⟨37962909160930053090504631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202468848858293616482691365 37962909160930053090504631)
  ·
    refine ⟨56944363741395079635756947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37962909160930053090504631 56944363741395079635756947)
    ·
      refine ⟨85416545612092619453635421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56944363741395079635756947 85416545612092619453635421)
      ·
        refine ⟨32031204604534732295113283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85416545612092619453635421 32031204604534732295113283)
        ·
          refine ⟨48046806906802098442669925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32031204604534732295113283 48046806906802098442669925)
          ·
            refine ⟨9008776295025393458000611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48046806906802098442669925 9008776295025393458000611)
            ·
              refine ⟨13513164442538090187000917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9008776295025393458000611 13513164442538090187000917)
              ·
                refine ⟨158357395810993244378917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13513164442538090187000917 158357395810993244378917)
                ·
                  rfl

theorem cell23_8326798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 1, 8].length) (baseStart_8326798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8326798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8326798 prefixEnd_8326798 := by exact prefixLift 8326798
  have htrace : WordTrace (prefixWord ++ tailWord_8326798) baseStart_8326798 baseEnd_8326798 := by
    simpa [prefixWord, tailWord_8326798, baseEnd_8326798] using wordTrace_append hprefix tailTrace_8326798
  have hstable : (prefixWord ++ tailWord_8326798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8326798).length < 2 ^ (prefixWord ++ tailWord_8326798).sum := by decide
  have hdescent : baseEnd_8326798 < baseStart_8326798 := by decide
  rcases family_descends (prefixWord ++ tailWord_8326798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8326808 : List Nat := [2, 1, 2, 4, 1, 2, 1, 3, 1, 3, 3]
def baseStart_8326808 : Nat := 118140960795 + 8326808 * 2 ^ 59
def prefixEnd_8326808 : Nat := 4983230072969 + 3 ^ 40 * 8326808 * 2
def baseEnd_8326808 : Nat := 4275654821703362559105713

theorem tailTrace_8326808 : CollatzResearch.WordTrace tailWord_8326808 prefixEnd_8326808 4275654821703362559105713 := by
  unfold tailWord_8326808
  simp only [CollatzResearch.WordTrace]
  refine ⟨151851819008702098215950539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202469092011602797621267385 151851819008702098215950539)
  ·
    refine ⟨227777728513053147323925809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151851819008702098215950539 227777728513053147323925809)
    ·
      refine ⟨170833296384789860492944357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227777728513053147323925809 170833296384789860492944357)
      ·
        refine ⟨32031243072148098842427067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 170833296384789860492944357 32031243072148098842427067)
        ·
          refine ⟨48046864608222148263640601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32031243072148098842427067 48046864608222148263640601)
          ·
            refine ⟨36035148456166611197730451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48046864608222148263640601 36035148456166611197730451)
            ·
              refine ⟨54052722684249916796595677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36035148456166611197730451 54052722684249916796595677)
              ·
                refine ⟨20269771006593718798723379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54052722684249916796595677 20269771006593718798723379)
                ·
                  refine ⟨30404656509890578198085069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20269771006593718798723379 30404656509890578198085069)
                  ·
                    refine ⟨11401746191208966824281901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30404656509890578198085069 11401746191208966824281901)
                    ·
                      refine ⟨4275654821703362559105713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11401746191208966824281901 4275654821703362559105713)
                      ·
                        rfl

theorem cell23_8326808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 3, 1, 3, 3].length) (baseStart_8326808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8326808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8326808 prefixEnd_8326808 := by exact prefixLift 8326808
  have htrace : WordTrace (prefixWord ++ tailWord_8326808) baseStart_8326808 baseEnd_8326808 := by
    simpa [prefixWord, tailWord_8326808, baseEnd_8326808] using wordTrace_append hprefix tailTrace_8326808
  have hstable : (prefixWord ++ tailWord_8326808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8326808).length < 2 ^ (prefixWord ++ tailWord_8326808).sum := by decide
  have hdescent : baseEnd_8326808 < baseStart_8326808 := by decide
  rcases family_descends (prefixWord ++ tailWord_8326808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8326815 : List Nat := [1, 1, 2, 7, 1, 1, 3, 7]
def baseStart_8326815 : Nat := 118140960795 + 8326815 * 2 ^ 59
def prefixEnd_8326815 : Nat := 4983230072969 + 3 ^ 40 * 8326815 * 2
def baseEnd_8326815 : Nat := 158357719113627556730303

theorem tailTrace_8326815 : CollatzResearch.WordTrace tailWord_8326815 prefixEnd_8326815 158357719113627556730303 := by
  unfold tailWord_8326815
  simp only [CollatzResearch.WordTrace]
  refine ⟨303703893328378836627405899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202469262218919224418270599 303703893328378836627405899)
  ·
    refine ⟨455555839992568254941108849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303703893328378836627405899 455555839992568254941108849)
    ·
      refine ⟨341666879994426191205831637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 455555839992568254941108849 341666879994426191205831637)
      ·
        refine ⟨8007817499869363856386679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 341666879994426191205831637 8007817499869363856386679)
        ·
          refine ⟨12011726249804045784580019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8007817499869363856386679 12011726249804045784580019)
          ·
            refine ⟨18017589374706068676870029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12011726249804045784580019 18017589374706068676870029)
            ·
              refine ⟨6756596015514775753826261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18017589374706068676870029 6756596015514775753826261)
              ·
                refine ⟨158357719113627556730303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6756596015514775753826261 158357719113627556730303)
                ·
                  rfl

theorem cell23_8326815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 3, 7].length) (baseStart_8326815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8326815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8326815 prefixEnd_8326815 := by exact prefixLift 8326815
  have htrace : WordTrace (prefixWord ++ tailWord_8326815) baseStart_8326815 baseEnd_8326815 := by
    simpa [prefixWord, tailWord_8326815, baseEnd_8326815] using wordTrace_append hprefix tailTrace_8326815
  have hstable : (prefixWord ++ tailWord_8326815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8326815).length < 2 ^ (prefixWord ++ tailWord_8326815).sum := by decide
  have hdescent : baseEnd_8326815 < baseStart_8326815 := by decide
  rcases family_descends (prefixWord ++ tailWord_8326815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8326835 : List Nat := [1, 1, 1, 2, 3, 3, 3, 3, 1, 3, 2]
def baseStart_8326835 : Nat := 118140960795 + 8326835 * 2 ^ 59
def prefixEnd_8326835 : Nat := 4983230072969 + 3 ^ 40 * 8326835 * 2
def baseEnd_8326835 : Nat := 4275668685681033953468089

theorem tailTrace_8326835 : CollatzResearch.WordTrace tailWord_8326835 prefixEnd_8326835 4275668685681033953468089 := by
  unfold tailWord_8326835
  simp only [CollatzResearch.WordTrace]
  refine ⟨303704622788306380043133959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202469748525537586695422639 303704622788306380043133959)
  ·
    refine ⟨455556934182459570064700939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303704622788306380043133959 455556934182459570064700939)
    ·
      refine ⟨683335401273689355097051409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 455556934182459570064700939 683335401273689355097051409)
      ·
        refine ⟨512501550955267016322788557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 683335401273689355097051409 512501550955267016322788557)
        ·
          refine ⟨192188081608225131121045709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 512501550955267016322788557 192188081608225131121045709)
          ·
            refine ⟨72070530603084424170392141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 192188081608225131121045709 72070530603084424170392141)
            ·
              refine ⟨27026448976156659063897053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72070530603084424170392141 27026448976156659063897053)
              ·
                refine ⟨10134918366058747148961395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27026448976156659063897053 10134918366058747148961395)
                ·
                  refine ⟨15202377549088120723442093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10134918366058747148961395 15202377549088120723442093)
                  ·
                    refine ⟨5700891580908045271290785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15202377549088120723442093 5700891580908045271290785)
                    ·
                      refine ⟨4275668685681033953468089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5700891580908045271290785 4275668685681033953468089)
                      ·
                        rfl

theorem cell23_8326835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 3, 1, 3, 2].length) (baseStart_8326835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8326835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8326835 prefixEnd_8326835 := by exact prefixLift 8326835
  have htrace : WordTrace (prefixWord ++ tailWord_8326835) baseStart_8326835 baseEnd_8326835 := by
    simpa [prefixWord, tailWord_8326835, baseEnd_8326835] using wordTrace_append hprefix tailTrace_8326835
  have hstable : (prefixWord ++ tailWord_8326835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8326835).length < 2 ^ (prefixWord ++ tailWord_8326835).sum := by decide
  have hdescent : baseEnd_8326835 < baseStart_8326835 := by decide
  rcases family_descends (prefixWord ++ tailWord_8326835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8326841 : List Nat := [1, 2, 1, 4, 1, 1, 3, 2, 2, 6]
def baseStart_8326841 : Nat := 118140960795 + 8326841 * 2 ^ 59
def prefixEnd_8326841 : Nat := 4983230072969 + 3 ^ 40 * 8326841 * 2
def baseEnd_8326841 : Nat := 1425223922188320309997687

theorem tailTrace_8326841 : CollatzResearch.WordTrace tailWord_8326841 prefixEnd_8326841 1425223922188320309997687 := by
  unfold tailWord_8326841
  simp only [CollatzResearch.WordTrace]
  refine ⟨303704841626284643067852377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202469894417523095378568251 303704841626284643067852377)
  ·
    refine ⟨227778631219713482300889283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303704841626284643067852377 227778631219713482300889283)
    ·
      refine ⟨341667946829570223451333925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227778631219713482300889283 341667946829570223451333925)
      ·
        refine ⟨64062740030544416897125111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 341667946829570223451333925 64062740030544416897125111)
        ·
          refine ⟨96094110045816625345687667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64062740030544416897125111 96094110045816625345687667)
          ·
            refine ⟨144141165068724938018531501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96094110045816625345687667 144141165068724938018531501)
            ·
              refine ⟨54052936900771851756949313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144141165068724938018531501 54052936900771851756949313)
              ·
                refine ⟨40539702675578888817711985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54052936900771851756949313 40539702675578888817711985)
                ·
                  refine ⟨30404777006684166613283989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40539702675578888817711985 30404777006684166613283989)
                  ·
                    refine ⟨1425223922188320309997687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30404777006684166613283989 1425223922188320309997687)
                    ·
                      rfl

theorem cell23_8326841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 2, 2, 6].length) (baseStart_8326841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8326841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8326841 prefixEnd_8326841 := by exact prefixLift 8326841
  have htrace : WordTrace (prefixWord ++ tailWord_8326841) baseStart_8326841 baseEnd_8326841 := by
    simpa [prefixWord, tailWord_8326841, baseEnd_8326841] using wordTrace_append hprefix tailTrace_8326841
  have hstable : (prefixWord ++ tailWord_8326841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8326841).length < 2 ^ (prefixWord ++ tailWord_8326841).sum := by decide
  have hdescent : baseEnd_8326841 < baseStart_8326841 := by decide
  rcases family_descends (prefixWord ++ tailWord_8326841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8326842 : List Nat := [3, 1, 1, 1, 2, 6, 1, 2, 2, 1, 3]
def baseStart_8326842 : Nat := 118140960795 + 8326842 * 2 ^ 59
def prefixEnd_8326842 : Nat := 4983230072969 + 3 ^ 40 * 8326842 * 2
def baseEnd_8326842 : Nat := 4275672280045615426080557

theorem tailTrace_8326842 : CollatzResearch.WordTrace tailWord_8326842 prefixEnd_8326842 4275672280045615426080557 := by
  unfold tailWord_8326842
  simp only [CollatzResearch.WordTrace]
  refine ⟨75926219524820255059659695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202469918732854013492425853 75926219524820255059659695)
  ·
    refine ⟨113889329287230382589489543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75926219524820255059659695 113889329287230382589489543)
    ·
      refine ⟨170833993930845573884234315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113889329287230382589489543 170833993930845573884234315)
      ·
        refine ⟨256250990896268360826351473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170833993930845573884234315 256250990896268360826351473)
        ·
          refine ⟨192188243172201270619763605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256250990896268360826351473 192188243172201270619763605)
          ·
            refine ⟨9008823898696934560301419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 192188243172201270619763605 9008823898696934560301419)
            ·
              refine ⟨13513235848045401840452129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9008823898696934560301419 13513235848045401840452129)
              ·
                refine ⟨10134926886034051380339097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13513235848045401840452129 10134926886034051380339097)
                ·
                  refine ⟨7601195164525538535254323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10134926886034051380339097 7601195164525538535254323)
                  ·
                    refine ⟨11401792746788307802881485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7601195164525538535254323 11401792746788307802881485)
                    ·
                      refine ⟨4275672280045615426080557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11401792746788307802881485 4275672280045615426080557)
                      ·
                        rfl

theorem cell23_8326842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 1, 2, 2, 1, 3].length) (baseStart_8326842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8326842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8326842 prefixEnd_8326842 := by exact prefixLift 8326842
  have htrace : WordTrace (prefixWord ++ tailWord_8326842) baseStart_8326842 baseEnd_8326842 := by
    simpa [prefixWord, tailWord_8326842, baseEnd_8326842] using wordTrace_append hprefix tailTrace_8326842
  have hstable : (prefixWord ++ tailWord_8326842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8326842).length < 2 ^ (prefixWord ++ tailWord_8326842).sum := by decide
  have hdescent : baseEnd_8326842 < baseStart_8326842 := by decide
  rcases family_descends (prefixWord ++ tailWord_8326842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8326865 : List Nat := [1, 2, 2, 1, 2, 4, 3, 1, 1, 4, 2]
def baseStart_8326865 : Nat := 118140960795 + 8326865 * 2 ^ 59
def prefixEnd_8326865 : Nat := 4983230072969 + 3 ^ 40 * 8326865 * 2
def baseEnd_8326865 : Nat := 4275684090100668836092951

theorem tailTrace_8326865 : CollatzResearch.WordTrace tailWord_8326865 prefixEnd_8326865 4275684090100668836092951 := by
  unfold tailWord_8326865
  simp only [CollatzResearch.WordTrace]
  refine ⟨303705716978197695166726049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202470477985465130111150699 303705716978197695166726049)
  ·
    refine ⟨227779287733648271375044537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303705716978197695166726049 227779287733648271375044537)
    ·
      refine ⟨170834465800236203531283403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227779287733648271375044537 170834465800236203531283403)
      ·
        refine ⟨256251698700354305296925105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170834465800236203531283403 256251698700354305296925105)
        ·
          refine ⟨192188774025265728972693829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256251698700354305296925105 192188774025265728972693829)
          ·
            refine ⟨36035395129737324182380093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 192188774025265728972693829 36035395129737324182380093)
            ·
              refine ⟨13513273173651496568392535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36035395129737324182380093 13513273173651496568392535)
              ·
                refine ⟨20269909760477244852588803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13513273173651496568392535 20269909760477244852588803)
                ·
                  refine ⟨30404864640715867278883205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20269909760477244852588803 30404864640715867278883205)
                  ·
                    refine ⟨5700912120134225114790601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30404864640715867278883205 5700912120134225114790601)
                    ·
                      refine ⟨4275684090100668836092951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5700912120134225114790601 4275684090100668836092951)
                      ·
                        rfl

theorem cell23_8326865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 3, 1, 1, 4, 2].length) (baseStart_8326865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8326865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8326865 prefixEnd_8326865 := by exact prefixLift 8326865
  have htrace : WordTrace (prefixWord ++ tailWord_8326865) baseStart_8326865 baseEnd_8326865 := by
    simpa [prefixWord, tailWord_8326865, baseEnd_8326865] using wordTrace_append hprefix tailTrace_8326865
  have hstable : (prefixWord ++ tailWord_8326865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8326865).length < 2 ^ (prefixWord ++ tailWord_8326865).sum := by decide
  have hdescent : baseEnd_8326865 < baseStart_8326865 := by decide
  rcases family_descends (prefixWord ++ tailWord_8326865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8326871 : List Nat := [1, 1, 3, 2, 1, 3, 1, 4, 7]
def baseStart_8326871 : Nat := 118140960795 + 8326871 * 2 ^ 59
def prefixEnd_8326871 : Nat := 4983230072969 + 3 ^ 40 * 8326871 * 2
def baseEnd_8326871 : Nat := 475076352331621756957547

theorem tailTrace_8326871 : CollatzResearch.WordTrace tailWord_8326871 prefixEnd_8326871 475076352331621756957547 := by
  unfold tailWord_8326871
  simp only [CollatzResearch.WordTrace]
  refine ⟨303705935816175958191444467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202470623877450638794296311 303705935816175958191444467)
  ·
    refine ⟨455558903724263937287166701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303705935816175958191444467 455558903724263937287166701)
    ·
      refine ⟨170834588896598976482687513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 455558903724263937287166701 170834588896598976482687513)
      ·
        refine ⟨128125941672449232362015635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170834588896598976482687513 128125941672449232362015635)
        ·
          refine ⟨192188912508673848543023453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128125941672449232362015635 192188912508673848543023453)
          ·
            refine ⟨72070842190752693203633795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 192188912508673848543023453 72070842190752693203633795)
            ·
              refine ⟨108106263286129039805450693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72070842190752693203633795 108106263286129039805450693)
              ·
                refine ⟨20269924366149194963522005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 108106263286129039805450693 20269924366149194963522005)
                ·
                  refine ⟨475076352331621756957547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20269924366149194963522005 475076352331621756957547)
                  ·
                    rfl

theorem cell23_8326871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 4, 7].length) (baseStart_8326871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8326871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8326871 prefixEnd_8326871 := by exact prefixLift 8326871
  have htrace : WordTrace (prefixWord ++ tailWord_8326871) baseStart_8326871 baseEnd_8326871 := by
    simpa [prefixWord, tailWord_8326871, baseEnd_8326871] using wordTrace_append hprefix tailTrace_8326871
  have hstable : (prefixWord ++ tailWord_8326871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8326871).length < 2 ^ (prefixWord ++ tailWord_8326871).sum := by decide
  have hdescent : baseEnd_8326871 < baseStart_8326871 := by decide
  rcases family_descends (prefixWord ++ tailWord_8326871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8326911 : List Nat := [1, 1, 2, 2, 1, 3, 3, 1, 1, 1, 7]
def baseStart_8326911 : Nat := 118140960795 + 8326911 * 2 ^ 59
def prefixEnd_8326911 : Nat := 4983230072969 + 3 ^ 40 * 8326911 * 2
def baseEnd_8326911 : Nat := 4275707710210775656117739

theorem tailTrace_8326911 : CollatzResearch.WordTrace tailWord_8326911 prefixEnd_8326911 4275707710210775656117739 := by
  unfold tailWord_8326911
  simp only [CollatzResearch.WordTrace]
  refine ⟨303707394736031045022900587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202471596490687363348600391 303707394736031045022900587)
  ·
    refine ⟨455561092104046567534350881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303707394736031045022900587 455561092104046567534350881)
    ·
      refine ⟨341670819078034925650763161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 455561092104046567534350881 341670819078034925650763161)
      ·
        refine ⟨256253114308526194238072371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 341670819078034925650763161 256253114308526194238072371)
        ·
          refine ⟨384379671462789291357108557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256253114308526194238072371 384379671462789291357108557)
          ·
            refine ⟨144142376798545984258915709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 384379671462789291357108557 144142376798545984258915709)
            ·
              refine ⟨54053391299454744097093391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144142376798545984258915709 54053391299454744097093391)
              ·
                refine ⟨81080086949182116145640087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54053391299454744097093391 81080086949182116145640087)
                ·
                  refine ⟨121620130423773174218460131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81080086949182116145640087 121620130423773174218460131)
                  ·
                    refine ⟨182430195635659761327690197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 121620130423773174218460131 182430195635659761327690197)
                    ·
                      refine ⟨4275707710210775656117739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 182430195635659761327690197 4275707710210775656117739)
                      ·
                        rfl

theorem cell23_8326911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 1, 1, 1, 7].length) (baseStart_8326911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8326911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8326911 prefixEnd_8326911 := by exact prefixLift 8326911
  have htrace : WordTrace (prefixWord ++ tailWord_8326911) baseStart_8326911 baseEnd_8326911 := by
    simpa [prefixWord, tailWord_8326911, baseEnd_8326911] using wordTrace_append hprefix tailTrace_8326911
  have hstable : (prefixWord ++ tailWord_8326911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8326911).length < 2 ^ (prefixWord ++ tailWord_8326911).sum := by decide
  have hdescent : baseEnd_8326911 < baseStart_8326911 := by decide
  rcases family_descends (prefixWord ++ tailWord_8326911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8326916 : List Nat := [2, 3, 2, 2, 1, 4, 2, 1, 2, 2, 2]
def baseStart_8326916 : Nat := 118140960795 + 8326916 * 2 ^ 59
def prefixEnd_8326916 : Nat := 4983230072969 + 3 ^ 40 * 8326916 * 2
def baseEnd_8326916 : Nat := 4275710277614048136555217

theorem tailTrace_8326916 : CollatzResearch.WordTrace tailWord_8326916 prefixEnd_8326916 4275710277614048136555217 := by
  unfold tailWord_8326916
  simp only [CollatzResearch.WordTrace]
  refine ⟨151853788550506465438416301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202471718067341953917888401 151853788550506465438416301)
  ·
    refine ⟨56945170706439924539406113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151853788550506465438416301 56945170706439924539406113)
    ·
      refine ⟨42708878029829943404554585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56945170706439924539406113 42708878029829943404554585)
      ·
        refine ⟨32031658522372457553415939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42708878029829943404554585 32031658522372457553415939)
        ·
          refine ⟨48047487783558686330123909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32031658522372457553415939 48047487783558686330123909)
          ·
            refine ⟨9008903959417253686898233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48047487783558686330123909 9008903959417253686898233)
            ·
              refine ⟨6756677969562940265173675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9008903959417253686898233 6756677969562940265173675)
              ·
                refine ⟨10135016954344410397760513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6756677969562940265173675 10135016954344410397760513)
                ·
                  refine ⟨7601262715758307798320385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10135016954344410397760513 7601262715758307798320385)
                  ·
                    refine ⟨5700947036818730848740289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7601262715758307798320385 5700947036818730848740289)
                    ·
                      refine ⟨4275710277614048136555217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5700947036818730848740289 4275710277614048136555217)
                      ·
                        rfl

theorem cell23_8326916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 2, 1, 2, 2, 2].length) (baseStart_8326916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8326916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8326916 prefixEnd_8326916 := by exact prefixLift 8326916
  have htrace : WordTrace (prefixWord ++ tailWord_8326916) baseStart_8326916 baseEnd_8326916 := by
    simpa [prefixWord, tailWord_8326916, baseEnd_8326916] using wordTrace_append hprefix tailTrace_8326916
  have hstable : (prefixWord ++ tailWord_8326916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8326916).length < 2 ^ (prefixWord ++ tailWord_8326916).sum := by decide
  have hdescent : baseEnd_8326916 < baseStart_8326916 := by decide
  rcases family_descends (prefixWord ++ tailWord_8326916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8326935 : List Nat := [1, 1, 3, 4, 2, 2, 2, 1, 2, 5]
def baseStart_8326935 : Nat := 118140960795 + 8326935 * 2 ^ 59
def prefixEnd_8326935 : Nat := 4983230072969 + 3 ^ 40 * 8326935 * 2
def baseEnd_8326935 : Nat := 1425240011248827854072543

theorem tailTrace_8326935 : CollatzResearch.WordTrace tailWord_8326935 prefixEnd_8326935 1425240011248827854072543 := by
  unfold tailWord_8326935
  simp only [CollatzResearch.WordTrace]
  refine ⟨303708270087944097121774259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202472180058629398081182839 303708270087944097121774259)
  ·
    refine ⟨455562405131916145682661389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303708270087944097121774259 455562405131916145682661389)
    ·
      refine ⟨170835901924468554630998021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 455562405131916145682661389 170835901924468554630998021)
      ·
        refine ⟨32031731610837853993312129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 170835901924468554630998021 32031731610837853993312129)
        ·
          refine ⟨24023798708128390494984097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32031731610837853993312129 24023798708128390494984097)
          ·
            refine ⟨18017849031096292871238073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24023798708128390494984097 18017849031096292871238073)
            ·
              refine ⟨13513386773322219653428555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18017849031096292871238073 13513386773322219653428555)
              ·
                refine ⟨20270080159983329480142833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13513386773322219653428555 20270080159983329480142833)
                ·
                  refine ⟨15202560119987497110107125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20270080159983329480142833 15202560119987497110107125)
                  ·
                    refine ⟨1425240011248827854072543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15202560119987497110107125 1425240011248827854072543)
                    ·
                      rfl

theorem cell23_8326935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 2, 1, 2, 5].length) (baseStart_8326935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8326935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8326935 prefixEnd_8326935 := by exact prefixLift 8326935
  have htrace : WordTrace (prefixWord ++ tailWord_8326935) baseStart_8326935 baseEnd_8326935 := by
    simpa [prefixWord, tailWord_8326935, baseEnd_8326935] using wordTrace_append hprefix tailTrace_8326935
  have hstable : (prefixWord ++ tailWord_8326935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8326935).length < 2 ^ (prefixWord ++ tailWord_8326935).sum := by decide
  have hdescent : baseEnd_8326935 < baseStart_8326935 := by decide
  rcases family_descends (prefixWord ++ tailWord_8326935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8326989 : List Nat := [1, 6, 1, 2, 1, 3, 1, 1, 2, 1, 4]
def baseStart_8326989 : Nat := 118140960795 + 8326989 * 2 ^ 59
def prefixEnd_8326989 : Nat := 4983230072969 + 3 ^ 40 * 8326989 * 2
def baseEnd_8326989 : Nat := 4275747761701826350942381

theorem tailTrace_8326989 : CollatzResearch.WordTrace tailWord_8326989 prefixEnd_8326989 4275747761701826350942381 := by
  unfold tailWord_8326989
  simp only [CollatzResearch.WordTrace]
  refine ⟨303710239629748464344240021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202473493086498976229493347 303710239629748464344240021)
  ·
    refine ⟨14236417482644459266136251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 303710239629748464344240021 14236417482644459266136251)
    ·
      refine ⟨21354626223966688899204377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14236417482644459266136251 21354626223966688899204377)
      ·
        refine ⟨16015969667975016674403283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21354626223966688899204377 16015969667975016674403283)
        ·
          refine ⟨24023954501962525011604925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16015969667975016674403283 24023954501962525011604925)
          ·
            refine ⟨9008982938235946879351847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24023954501962525011604925 9008982938235946879351847)
            ·
              refine ⟨13513474407353920319027771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9008982938235946879351847 13513474407353920319027771)
              ·
                refine ⟨20270211611030880478541657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13513474407353920319027771 20270211611030880478541657)
                ·
                  refine ⟨15202658708273160358906243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20270211611030880478541657 15202658708273160358906243)
                  ·
                    refine ⟨22803988062409740538359365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15202658708273160358906243 22803988062409740538359365)
                    ·
                      refine ⟨4275747761701826350942381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22803988062409740538359365 4275747761701826350942381)
                      ·
                        rfl

theorem cell23_8326989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_8326989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8326989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8326989 prefixEnd_8326989 := by exact prefixLift 8326989
  have htrace : WordTrace (prefixWord ++ tailWord_8326989) baseStart_8326989 baseEnd_8326989 := by
    simpa [prefixWord, tailWord_8326989, baseEnd_8326989] using wordTrace_append hprefix tailTrace_8326989
  have hstable : (prefixWord ++ tailWord_8326989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8326989).length < 2 ^ (prefixWord ++ tailWord_8326989).sum := by decide
  have hdescent : baseEnd_8326989 < baseStart_8326989 := by decide
  rcases family_descends (prefixWord ++ tailWord_8326989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8326999 : List Nat := [1, 1, 3, 2, 5, 1, 2, 3, 1, 4]
def baseStart_8326999 : Nat := 118140960795 + 8326999 * 2 ^ 59
def prefixEnd_8326999 : Nat := 4983230072969 + 3 ^ 40 * 8326999 * 2
def baseEnd_8326999 : Nat := 1425250965502790437272445

theorem tailTrace_8326999 : CollatzResearch.WordTrace tailWord_8326999 prefixEnd_8326999 1425250965502790437272445 := by
  unfold tailWord_8326999
  simp only [CollatzResearch.WordTrace]
  refine ⟨303710604359712236052104051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202473736239808157368069367 303710604359712236052104051)
  ·
    refine ⟨455565906539568354078156077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303710604359712236052104051 455565906539568354078156077)
    ·
      refine ⟨170837214952338132779308529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 455565906539568354078156077 170837214952338132779308529)
      ·
        refine ⟨128127911214253599584481397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170837214952338132779308529 128127911214253599584481397)
        ·
          refine ⟨12011991676336274961045131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 128127911214253599584481397 12011991676336274961045131)
          ·
            refine ⟨18017987514504412441567697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12011991676336274961045131 18017987514504412441567697)
            ·
              refine ⟨13513490635878309331175773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18017987514504412441567697 13513490635878309331175773)
              ·
                refine ⟨5067558988454365999190915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13513490635878309331175773 5067558988454365999190915)
                ·
                  refine ⟨7601338482681548998786373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5067558988454365999190915 7601338482681548998786373)
                  ·
                    refine ⟨1425250965502790437272445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7601338482681548998786373 1425250965502790437272445)
                    ·
                      rfl

theorem cell23_8326999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 2, 3, 1, 4].length) (baseStart_8326999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8326999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8326999 prefixEnd_8326999 := by exact prefixLift 8326999
  have htrace : WordTrace (prefixWord ++ tailWord_8326999) baseStart_8326999 baseEnd_8326999 := by
    simpa [prefixWord, tailWord_8326999, baseEnd_8326999] using wordTrace_append hprefix tailTrace_8326999
  have hstable : (prefixWord ++ tailWord_8326999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8326999).length < 2 ^ (prefixWord ++ tailWord_8326999).sum := by decide
  have hdescent : baseEnd_8326999 < baseStart_8326999 := by decide
  rcases family_descends (prefixWord ++ tailWord_8326999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8327012 : List Nat := [2, 3, 1, 1, 5, 2, 1, 2, 6]
def baseStart_8327012 : Nat := 118140960795 + 8327012 * 2 ^ 59
def prefixEnd_8327012 : Nat := 4983230072969 + 3 ^ 40 * 8327012 * 2
def baseEnd_8327012 : Nat := 475084396861875528994975

theorem tailTrace_8327012 : CollatzResearch.WordTrace tailWord_8327012 prefixEnd_8327012 475084396861875528994975 := by
  unfold tailWord_8327012
  simp only [CollatzResearch.WordTrace]
  refine ⟨151855539254332569636163645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202474052339110092848218193 151855539254332569636163645)
  ·
    refine ⟨56945827220374713613561367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151855539254332569636163645 56945827220374713613561367)
    ·
      refine ⟨85418740830562070420342051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56945827220374713613561367 85418740830562070420342051)
      ·
        refine ⟨128128111245843105630513077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85418740830562070420342051 128128111245843105630513077)
        ·
          refine ⟨12012010429297791152860601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 128128111245843105630513077 12012010429297791152860601)
          ·
            refine ⟨9009007821973343364645451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12012010429297791152860601 9009007821973343364645451)
            ·
              refine ⟨13513511732960015046968177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9009007821973343364645451 13513511732960015046968177)
              ·
                refine ⟨10135133799720011285226133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13513511732960015046968177 10135133799720011285226133)
                ·
                  refine ⟨475084396861875528994975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10135133799720011285226133 475084396861875528994975)
                  ·
                    rfl

theorem cell23_8327012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 1, 2, 6].length) (baseStart_8327012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8327012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8327012 prefixEnd_8327012 := by exact prefixLift 8327012
  have htrace : WordTrace (prefixWord ++ tailWord_8327012) baseStart_8327012 baseEnd_8327012 := by
    simpa [prefixWord, tailWord_8327012, baseEnd_8327012] using wordTrace_append hprefix tailTrace_8327012
  have hstable : (prefixWord ++ tailWord_8327012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8327012).length < 2 ^ (prefixWord ++ tailWord_8327012).sum := by decide
  have hdescent : baseEnd_8327012 < baseStart_8327012 := by decide
  rcases family_descends (prefixWord ++ tailWord_8327012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8327045 : List Nat := [1, 3, 1, 1, 3, 2, 1, 1, 2, 6, 2]
def baseStart_8327045 : Nat := 118140960795 + 8327045 * 2 ^ 59
def prefixEnd_8327045 : Nat := 4983230072969 + 3 ^ 40 * 8327045 * 2
def baseEnd_8327045 : Nat := 4275776516618478131842123

theorem tailTrace_8327045 : CollatzResearch.WordTrace tailWord_8327045 prefixEnd_8327045 4275776516618478131842123 := by
  unfold tailWord_8327045
  simp only [CollatzResearch.WordTrace]
  refine ⟨303712282117545585908278589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202474854745030390605519059 303712282117545585908278589)
  ·
    refine ⟨113892105794079594715604471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 303712282117545585908278589 113892105794079594715604471)
    ·
      refine ⟨170838158691119392073406707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113892105794079594715604471 170838158691119392073406707)
      ·
        refine ⟨256257238036679088110110061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170838158691119392073406707 256257238036679088110110061)
        ·
          refine ⟨96096464263754658041291273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 256257238036679088110110061 96096464263754658041291273)
          ·
            refine ⟨72072348197815993530968455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96096464263754658041291273 72072348197815993530968455)
            ·
              refine ⟨108108522296723990296452683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72072348197815993530968455 108108522296723990296452683)
              ·
                refine ⟨162162783445085985444679025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108108522296723990296452683 162162783445085985444679025)
                ·
                  refine ⟨121622087583814489083509269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 162162783445085985444679025 121622087583814489083509269)
                  ·
                    refine ⟨5701035355491304175789497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 121622087583814489083509269 5701035355491304175789497)
                    ·
                      refine ⟨4275776516618478131842123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5701035355491304175789497 4275776516618478131842123)
                      ·
                        rfl

theorem cell23_8327045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 2, 6, 2].length) (baseStart_8327045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8327045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8327045 prefixEnd_8327045 := by exact prefixLift 8327045
  have htrace : WordTrace (prefixWord ++ tailWord_8327045) baseStart_8327045 baseEnd_8327045 := by
    simpa [prefixWord, tailWord_8327045, baseEnd_8327045] using wordTrace_append hprefix tailTrace_8327045
  have hstable : (prefixWord ++ tailWord_8327045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8327045).length < 2 ^ (prefixWord ++ tailWord_8327045).sum := by decide
  have hdescent : baseEnd_8327045 < baseStart_8327045 := by decide
  rcases family_descends (prefixWord ++ tailWord_8327045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8327073 : List Nat := [1, 2, 3, 4, 2, 1, 3, 2, 1, 1, 3]
def baseStart_8327073 : Nat := 118140960795 + 8327073 * 2 ^ 59
def prefixEnd_8327073 : Nat := 4983230072969 + 3 ^ 40 * 8327073 * 2
def baseEnd_8327073 : Nat := 4275790894076804022291995

theorem tailTrace_8327073 : CollatzResearch.WordTrace tailWord_8327073 prefixEnd_8327073 4275790894076804022291995 := by
  unfold tailWord_8327073
  simp only [CollatzResearch.WordTrace]
  refine ⟨303713303361444146690297873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202475535574296097793531915 303713303361444146690297873)
  ·
    refine ⟨227784977521083110017723405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303713303361444146690297873 227784977521083110017723405)
    ·
      refine ⟨85419366570406166256646277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227784977521083110017723405 85419366570406166256646277)
      ·
        refine ⟨16016131231951156173121177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85419366570406166256646277 16016131231951156173121177)
        ·
          refine ⟨12012098423963367129840883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16016131231951156173121177 12012098423963367129840883)
          ·
            refine ⟨18018147635945050694761325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12012098423963367129840883 18018147635945050694761325)
            ·
              refine ⟨6756805363479394010535497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18018147635945050694761325 6756805363479394010535497)
              ·
                refine ⟨5067604022609545507901623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6756805363479394010535497 5067604022609545507901623)
                ·
                  refine ⟨7601406033914318261852435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5067604022609545507901623 7601406033914318261852435)
                  ·
                    refine ⟨11402109050871477392778653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7601406033914318261852435 11402109050871477392778653)
                    ·
                      refine ⟨4275790894076804022291995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11402109050871477392778653 4275790894076804022291995)
                      ·
                        rfl

theorem cell23_8327073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 3, 2, 1, 1, 3].length) (baseStart_8327073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8327073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8327073 prefixEnd_8327073 := by exact prefixLift 8327073
  have htrace : WordTrace (prefixWord ++ tailWord_8327073) baseStart_8327073 baseEnd_8327073 := by
    simpa [prefixWord, tailWord_8327073, baseEnd_8327073] using wordTrace_append hprefix tailTrace_8327073
  have hstable : (prefixWord ++ tailWord_8327073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8327073).length < 2 ^ (prefixWord ++ tailWord_8327073).sum := by decide
  have hdescent : baseEnd_8327073 < baseStart_8327073 := by decide
  rcases family_descends (prefixWord ++ tailWord_8327073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8327089 : List Nat := [1, 2, 2, 4, 2, 1, 4, 1, 2, 4]
def baseStart_8327089 : Nat := 118140960795 + 8327089 * 2 ^ 59
def prefixEnd_8327089 : Nat := 4983230072969 + 3 ^ 40 * 8327089 * 2
def baseEnd_8327089 : Nat := 1425266369922425319897307

theorem tailTrace_8327089 : CollatzResearch.WordTrace tailWord_8327089 prefixEnd_8327089 1425266369922425319897307 := by
  unfold tailWord_8327089
  simp only [CollatzResearch.WordTrace]
  refine ⟨303713886929386181422880321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202475924619590787615253547 303713886929386181422880321)
  ·
    refine ⟨227785415197039636067160241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303713886929386181422880321 227785415197039636067160241)
    ·
      refine ⟨170839061397779727050370181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227785415197039636067160241 170839061397779727050370181)
      ·
        refine ⟨32032324012083698821944409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 170839061397779727050370181 32032324012083698821944409)
        ·
          refine ⟨24024243009062774116458307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32032324012083698821944409 24024243009062774116458307)
          ·
            refine ⟨36036364513594161174687461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24024243009062774116458307 36036364513594161174687461)
            ·
              refine ⟨6756818346298905220253899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36036364513594161174687461 6756818346298905220253899)
              ·
                refine ⟨10135227519448357830380849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6756818346298905220253899 10135227519448357830380849)
                ·
                  refine ⟨7601420639586268372785637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10135227519448357830380849 7601420639586268372785637)
                  ·
                    refine ⟨1425266369922425319897307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7601420639586268372785637 1425266369922425319897307)
                    ·
                      rfl

theorem cell23_8327089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 4, 1, 2, 4].length) (baseStart_8327089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8327089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8327089 prefixEnd_8327089 := by exact prefixLift 8327089
  have htrace : WordTrace (prefixWord ++ tailWord_8327089) baseStart_8327089 baseEnd_8327089 := by
    simpa [prefixWord, tailWord_8327089, baseEnd_8327089] using wordTrace_append hprefix tailTrace_8327089
  have hstable : (prefixWord ++ tailWord_8327089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8327089).length < 2 ^ (prefixWord ++ tailWord_8327089).sum := by decide
  have hdescent : baseEnd_8327089 < baseStart_8327089 := by decide
  rcases family_descends (prefixWord ++ tailWord_8327089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8327095 : List Nat := [1, 1, 3, 1, 3, 1, 1, 5, 1, 3, 3]
def baseStart_8327095 : Nat := 118140960795 + 8327095 * 2 ^ 59
def prefixEnd_8327095 : Nat := 4983230072969 + 3 ^ 40 * 8327095 * 2
def baseEnd_8327095 : Nat := 4275802190651202936216893

theorem tailTrace_8327095 : CollatzResearch.WordTrace tailWord_8327095 prefixEnd_8327095 4275802190651202936216893 := by
  unfold tailWord_8327095
  simp only [CollatzResearch.WordTrace]
  refine ⟨303714105767364444447598739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202476070511576296298399159 303714105767364444447598739)
  ·
    refine ⟨455571158651046666671398109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303714105767364444447598739 455571158651046666671398109)
    ·
      refine ⟨170839184494142500001774291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 455571158651046666671398109 170839184494142500001774291)
      ·
        refine ⟨256258776741213750002661437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170839184494142500001774291 256258776741213750002661437)
        ·
          refine ⟨96097041277955156250998039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 256258776741213750002661437 96097041277955156250998039)
          ·
            refine ⟨144145561916932734376497059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96097041277955156250998039 144145561916932734376497059)
            ·
              refine ⟨216218342875399101564745589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144145561916932734376497059 216218342875399101564745589)
              ·
                refine ⟨20270469644568665771694899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 216218342875399101564745589 20270469644568665771694899)
                ·
                  refine ⟨30405704466852998657542349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20270469644568665771694899 30405704466852998657542349)
                  ·
                    refine ⟨11402139175069874496578381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30405704466852998657542349 11402139175069874496578381)
                    ·
                      refine ⟨4275802190651202936216893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11402139175069874496578381 4275802190651202936216893)
                      ·
                        rfl

theorem cell23_8327095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 5, 1, 3, 3].length) (baseStart_8327095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8327095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8327095 prefixEnd_8327095 := by exact prefixLift 8327095
  have htrace : WordTrace (prefixWord ++ tailWord_8327095) baseStart_8327095 baseEnd_8327095 := by
    simpa [prefixWord, tailWord_8327095, baseEnd_8327095] using wordTrace_append hprefix tailTrace_8327095
  have hstable : (prefixWord ++ tailWord_8327095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8327095).length < 2 ^ (prefixWord ++ tailWord_8327095).sum := by decide
  have hdescent : baseEnd_8327095 < baseStart_8327095 := by decide
  rcases family_descends (prefixWord ++ tailWord_8327095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8327098 : List Nat := [3, 1, 1, 1, 2, 1, 2, 1, 4, 7]
def baseStart_8327098 : Nat := 118140960795 + 8327098 * 2 ^ 59
def prefixEnd_8327098 : Nat := 4983230072969 + 3 ^ 40 * 8327098 * 2
def baseEnd_8327098 : Nat := 1425267910364388808159793

theorem tailTrace_8327098 : CollatzResearch.WordTrace tailWord_8327098 prefixEnd_8327098 1425267910364388808159793 := by
  unfold tailWord_8327098
  simp only [CollatzResearch.WordTrace]
  refine ⟨75928553796588393989989487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202476143457569050639971965 75928553796588393989989487)
  ·
    refine ⟨113892830694882590984984231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75928553796588393989989487 113892830694882590984984231)
    ·
      refine ⟨170839246042323886477476347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113892830694882590984984231 170839246042323886477476347)
      ·
        refine ⟨256258869063485829716214521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170839246042323886477476347 256258869063485829716214521)
        ·
          refine ⟨192194151797614372287160891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256258869063485829716214521 192194151797614372287160891)
          ·
            refine ⟨288291227696421558430741337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192194151797614372287160891 288291227696421558430741337)
            ·
              refine ⟨216218420772316168823056003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 288291227696421558430741337 216218420772316168823056003)
              ·
                refine ⟨324327631158474253234584005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 216218420772316168823056003 324327631158474253234584005)
                ·
                  refine ⟨60811430842213922481484501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 324327631158474253234584005 60811430842213922481484501)
                  ·
                    refine ⟨1425267910364388808159793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60811430842213922481484501 1425267910364388808159793)
                    ·
                      rfl

theorem cell23_8327098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 4, 7].length) (baseStart_8327098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8327098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8327098 prefixEnd_8327098 := by exact prefixLift 8327098
  have htrace : WordTrace (prefixWord ++ tailWord_8327098) baseStart_8327098 baseEnd_8327098 := by
    simpa [prefixWord, tailWord_8327098, baseEnd_8327098] using wordTrace_append hprefix tailTrace_8327098
  have hstable : (prefixWord ++ tailWord_8327098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8327098).length < 2 ^ (prefixWord ++ tailWord_8327098).sum := by decide
  have hdescent : baseEnd_8327098 < baseStart_8327098 := by decide
  rcases family_descends (prefixWord ++ tailWord_8327098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8327112 : List Nat := [2, 1, 3, 1, 4, 2, 1, 2, 1, 3, 3]
def baseStart_8327112 : Nat := 118140960795 + 8327112 * 2 ^ 59
def prefixEnd_8327112 : Nat := 4983230072969 + 3 ^ 40 * 8327112 * 2
def baseEnd_8327112 : Nat := 4275810919822329369704315

theorem tailTrace_8327112 : CollatzResearch.WordTrace tailWord_8327112 prefixEnd_8327112 4275810919822329369704315 := by
  unfold tailWord_8327112
  simp only [CollatzResearch.WordTrace]
  refine ⟨151857362904151428175483795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202476483872201904233978393 151857362904151428175483795)
  ·
    refine ⟨227786044356227142263225693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151857362904151428175483795 227786044356227142263225693)
    ·
      refine ⟨85419766633585178348709635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227786044356227142263225693 85419766633585178348709635)
      ·
        refine ⟨128129649950377767523064453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85419766633585178348709635 128129649950377767523064453)
        ·
          refine ⟨24024309365695831410574585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128129649950377767523064453 24024309365695831410574585)
          ·
            refine ⟨18018232024271873557930939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24024309365695831410574585 18018232024271873557930939)
            ·
              refine ⟨27027348036407810336896409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18018232024271873557930939 27027348036407810336896409)
              ·
                refine ⟨20270511027305857752672307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27027348036407810336896409 20270511027305857752672307)
                ·
                  refine ⟨30405766540958786629008461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20270511027305857752672307 30405766540958786629008461)
                  ·
                    refine ⟨11402162452859544985878173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30405766540958786629008461 11402162452859544985878173)
                    ·
                      refine ⟨4275810919822329369704315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11402162452859544985878173 4275810919822329369704315)
                      ·
                        rfl

theorem cell23_8327112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 2, 1, 3, 3].length) (baseStart_8327112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8327112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8327112 prefixEnd_8327112 := by exact prefixLift 8327112
  have htrace : WordTrace (prefixWord ++ tailWord_8327112) baseStart_8327112 baseEnd_8327112 := by
    simpa [prefixWord, tailWord_8327112, baseEnd_8327112] using wordTrace_append hprefix tailTrace_8327112
  have hstable : (prefixWord ++ tailWord_8327112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8327112).length < 2 ^ (prefixWord ++ tailWord_8327112).sum := by decide
  have hdescent : baseEnd_8327112 < baseStart_8327112 := by decide
  rcases family_descends (prefixWord ++ tailWord_8327112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8327130 : List Nat := [3, 1, 1, 2, 5, 2, 2, 2, 1, 2, 2]
def baseStart_8327130 : Nat := 118140960795 + 8327130 * 2 ^ 59
def prefixEnd_8327130 : Nat := 4983230072969 + 3 ^ 40 * 8327130 * 2
def baseEnd_8327130 : Nat := 4275820162474110299279233

theorem tailTrace_8327130 : CollatzResearch.WordTrace tailWord_8327130 prefixEnd_8327130 4275820162474110299279233 := by
  unfold tailWord_8327130
  simp only [CollatzResearch.WordTrace]
  refine ⟨75928845580559411356280711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202476921548158430283415229 75928845580559411356280711)
  ·
    refine ⟨113893268370839117034421067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75928845580559411356280711 113893268370839117034421067)
    ·
      refine ⟨170839902556258675551631601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113893268370839117034421067 170839902556258675551631601)
      ·
        refine ⟨128129926917194006663723701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170839902556258675551631601 128129926917194006663723701)
        ·
          refine ⟨12012180648486938124724097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 128129926917194006663723701 12012180648486938124724097)
          ·
            refine ⟨9009135486365203593543073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12012180648486938124724097 9009135486365203593543073)
            ·
              refine ⟨6756851614773902695157305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9009135486365203593543073 6756851614773902695157305)
              ·
                refine ⟨5067638711080427021367979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6756851614773902695157305 5067638711080427021367979)
                ·
                  refine ⟨7601458066620640532051969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5067638711080427021367979 7601458066620640532051969)
                  ·
                    refine ⟨5701093549965480399038977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7601458066620640532051969 5701093549965480399038977)
                    ·
                      refine ⟨4275820162474110299279233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5701093549965480399038977 4275820162474110299279233)
                      ·
                        rfl

theorem cell23_8327130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 2, 2, 1, 2, 2].length) (baseStart_8327130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8327130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8327130 prefixEnd_8327130 := by exact prefixLift 8327130
  have htrace : WordTrace (prefixWord ++ tailWord_8327130) baseStart_8327130 baseEnd_8327130 := by
    simpa [prefixWord, tailWord_8327130, baseEnd_8327130] using wordTrace_append hprefix tailTrace_8327130
  have hstable : (prefixWord ++ tailWord_8327130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8327130).length < 2 ^ (prefixWord ++ tailWord_8327130).sum := by decide
  have hdescent : baseEnd_8327130 < baseStart_8327130 := by decide
  rcases family_descends (prefixWord ++ tailWord_8327130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8327135 : List Nat := [1, 1, 2, 3, 4, 1, 1, 1, 2, 3, 4]
def baseStart_8327135 : Nat := 118140960795 + 8327135 * 2 ^ 59
def prefixEnd_8327135 : Nat := 4983230072969 + 3 ^ 40 * 8327135 * 2
def baseEnd_8327135 : Nat := 4275822729877382779716709

theorem tailTrace_8327135 : CollatzResearch.WordTrace tailWord_8327135 prefixEnd_8327135 4275822729877382779716709 := by
  unfold tailWord_8327135
  simp only [CollatzResearch.WordTrace]
  refine ⟨303715564687219531279054859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202477043124813020852703239 303715564687219531279054859)
  ·
    refine ⟨455573347030829296918582289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303715564687219531279054859 455573347030829296918582289)
    ·
      refine ⟨341680010273121972688936717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 455573347030829296918582289 341680010273121972688936717)
      ·
        refine ⟨128130003852420739758351269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 341680010273121972688936717 128130003852420739758351269)
        ·
          refine ⟨24024375722328888704690863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128130003852420739758351269 24024375722328888704690863)
          ·
            refine ⟨36036563583493333057036295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24024375722328888704690863 36036563583493333057036295)
            ·
              refine ⟨54054845375239999585554443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36036563583493333057036295 54054845375239999585554443)
              ·
                refine ⟨81082268062859999378331665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54054845375239999585554443 81082268062859999378331665)
                ·
                  refine ⟨60811701047144999533748749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81082268062859999378331665 60811701047144999533748749)
                  ·
                    refine ⟨22804387892679374825155781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60811701047144999533748749 22804387892679374825155781)
                    ·
                      refine ⟨4275822729877382779716709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22804387892679374825155781 4275822729877382779716709)
                      ·
                        rfl

theorem cell23_8327135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 2, 3, 4].length) (baseStart_8327135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8327135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8327135 prefixEnd_8327135 := by exact prefixLift 8327135
  have htrace : WordTrace (prefixWord ++ tailWord_8327135) baseStart_8327135 baseEnd_8327135 := by
    simpa [prefixWord, tailWord_8327135, baseEnd_8327135] using wordTrace_append hprefix tailTrace_8327135
  have hstable : (prefixWord ++ tailWord_8327135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8327135).length < 2 ^ (prefixWord ++ tailWord_8327135).sum := by decide
  have hdescent : baseEnd_8327135 < baseStart_8327135 := by decide
  rcases family_descends (prefixWord ++ tailWord_8327135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8327152 : List Nat := [2, 1, 1, 1, 3, 2, 3, 3, 1, 4, 2]
def baseStart_8327152 : Nat := 118140960795 + 8327152 * 2 ^ 59
def prefixEnd_8327152 : Nat := 4983230072969 + 3 ^ 40 * 8327152 * 2
def baseEnd_8327152 : Nat := 4275831459048509213204131

theorem tailTrace_8327152 : CollatzResearch.WordTrace tailWord_8327152 prefixEnd_8327152 4275831459048509213204131 := by
  unfold tailWord_8327152
  simp only [CollatzResearch.WordTrace]
  refine ⟨151858092364078971591211855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202477456485438628788282473 151858092364078971591211855)
  ·
    refine ⟨227787138546118457386817783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151858092364078971591211855 227787138546118457386817783)
    ·
      refine ⟨341680707819177686080226675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227787138546118457386817783 341680707819177686080226675)
      ·
        refine ⟨512521061728766529120340013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341680707819177686080226675 512521061728766529120340013)
        ·
          refine ⟨192195398148287448420127505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 512521061728766529120340013 192195398148287448420127505)
          ·
            refine ⟨144146548611215586315095629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192195398148287448420127505 144146548611215586315095629)
            ·
              refine ⟨54054955729205844868160861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144146548611215586315095629 54054955729205844868160861)
              ·
                refine ⟨20270608398452191825560323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54054955729205844868160861 20270608398452191825560323)
                ·
                  refine ⟨30405912597678287738340485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20270608398452191825560323 30405912597678287738340485)
                  ·
                    refine ⟨5701108612064678950938841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30405912597678287738340485 5701108612064678950938841)
                    ·
                      refine ⟨4275831459048509213204131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5701108612064678950938841 4275831459048509213204131)
                      ·
                        rfl

theorem cell23_8327152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 3, 1, 4, 2].length) (baseStart_8327152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8327152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8327152 prefixEnd_8327152 := by exact prefixLift 8327152
  have htrace : WordTrace (prefixWord ++ tailWord_8327152) baseStart_8327152 baseEnd_8327152 := by
    simpa [prefixWord, tailWord_8327152, baseEnd_8327152] using wordTrace_append hprefix tailTrace_8327152
  have hstable : (prefixWord ++ tailWord_8327152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8327152).length < 2 ^ (prefixWord ++ tailWord_8327152).sum := by decide
  have hdescent : baseEnd_8327152 < baseStart_8327152 := by decide
  rcases family_descends (prefixWord ++ tailWord_8327152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8327169 : List Nat := [1, 2, 4, 1, 2, 1, 2, 2, 4, 2, 2]
def baseStart_8327169 : Nat := 118140960795 + 8327169 * 2 ^ 59
def prefixEnd_8327169 : Nat := 4983230072969 + 3 ^ 40 * 8327169 * 2
def baseEnd_8327169 : Nat := 4275840188219635646691553

theorem tailTrace_8327169 : CollatzResearch.WordTrace tailWord_8327169 prefixEnd_8327169 4275840188219635646691553 := by
  unfold tailWord_8327169
  simp only [CollatzResearch.WordTrace]
  refine ⟨303716804769096355085792561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202477869846064236723861707 303716804769096355085792561)
  ·
    refine ⟨227787603576822266314344421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303716804769096355085792561 227787603576822266314344421)
    ·
      refine ⟨42710175670654174933939579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 227787603576822266314344421 42710175670654174933939579)
      ·
        refine ⟨64065263505981262400909369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42710175670654174933939579 64065263505981262400909369)
        ·
          refine ⟨48048947629485946800682027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64065263505981262400909369 48048947629485946800682027)
          ·
            refine ⟨72073421444228920201023041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48048947629485946800682027 72073421444228920201023041)
            ·
              refine ⟨54055066083171690150767281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72073421444228920201023041 54055066083171690150767281)
              ·
                refine ⟨40541299562378767613075461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54055066083171690150767281 40541299562378767613075461)
                ·
                  refine ⟨7601493667946018927451649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40541299562378767613075461 7601493667946018927451649)
                  ·
                    refine ⟨5701120250959514195588737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7601493667946018927451649 5701120250959514195588737)
                    ·
                      refine ⟨4275840188219635646691553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5701120250959514195588737 4275840188219635646691553)
                      ·
                        rfl

theorem cell23_8327169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 2, 4, 2, 2].length) (baseStart_8327169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8327169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8327169 prefixEnd_8327169 := by exact prefixLift 8327169
  have htrace : WordTrace (prefixWord ++ tailWord_8327169) baseStart_8327169 baseEnd_8327169 := by
    simpa [prefixWord, tailWord_8327169, baseEnd_8327169] using wordTrace_append hprefix tailTrace_8327169
  have hstable : (prefixWord ++ tailWord_8327169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8327169).length < 2 ^ (prefixWord ++ tailWord_8327169).sum := by decide
  have hdescent : baseEnd_8327169 < baseStart_8327169 := by decide
  rcases family_descends (prefixWord ++ tailWord_8327169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8327192 : List Nat := [2, 1, 2, 3, 2, 1, 1, 6, 5]
def baseStart_8327192 : Nat := 118140960795 + 8327192 * 2 ^ 59
def prefixEnd_8327192 : Nat := 4983230072969 + 3 ^ 40 * 8327192 * 2
def baseEnd_8327192 : Nat := 475094666474965450744883

theorem tailTrace_8327192 : CollatzResearch.WordTrace tailWord_8327192 prefixEnd_8327192 475094666474965450744883 := by
  unfold tailWord_8327192
  simp only [CollatzResearch.WordTrace]
  refine ⟨151858821824006515006939915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202478429098675353342586553 151858821824006515006939915)
  ·
    refine ⟨227788232736009772510409873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151858821824006515006939915 227788232736009772510409873)
    ·
      refine ⟨170841174552007329382807405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227788232736009772510409873 170841174552007329382807405)
      ·
        refine ⟨64065440457002748518552777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170841174552007329382807405 64065440457002748518552777)
        ·
          refine ⟨48049080342752061388914583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64065440457002748518552777 48049080342752061388914583)
          ·
            refine ⟨72073620514128092083371875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48049080342752061388914583 72073620514128092083371875)
            ·
              refine ⟨108110430771192138125057813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72073620514128092083371875 108110430771192138125057813)
              ·
                refine ⟨5067676442399631474612085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 108110430771192138125057813 5067676442399631474612085)
                ·
                  refine ⟨475094666474965450744883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5067676442399631474612085 475094666474965450744883)
                  ·
                    rfl

theorem cell23_8327192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 6, 5].length) (baseStart_8327192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8327192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8327192 prefixEnd_8327192 := by exact prefixLift 8327192
  have htrace : WordTrace (prefixWord ++ tailWord_8327192) baseStart_8327192 baseEnd_8327192 := by
    simpa [prefixWord, tailWord_8327192, baseEnd_8327192] using wordTrace_append hprefix tailTrace_8327192
  have hstable : (prefixWord ++ tailWord_8327192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8327192).length < 2 ^ (prefixWord ++ tailWord_8327192).sum := by decide
  have hdescent : baseEnd_8327192 < baseStart_8327192 := by decide
  rcases family_descends (prefixWord ++ tailWord_8327192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8327202 : List Nat := [3, 3, 1, 1, 1, 2, 1, 3, 2, 3, 3]
def baseStart_8327202 : Nat := 118140960795 + 8327202 * 2 ^ 59
def prefixEnd_8327202 : Nat := 4983230072969 + 3 ^ 40 * 8327202 * 2
def baseEnd_8327202 : Nat := 4275857133081234017578901

theorem tailTrace_8327202 : CollatzResearch.WordTrace tailWord_8327202 prefixEnd_8327202 4275857133081234017578901 := by
  unfold tailWord_8327202
  simp only [CollatzResearch.WordTrace]
  refine ⟨75929502094494200430435965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202478672251984534481162573 75929502094494200430435965)
  ·
    refine ⟨28473563285435325161413487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75929502094494200430435965 28473563285435325161413487)
    ·
      refine ⟨42710344928152987742120231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28473563285435325161413487 42710344928152987742120231)
      ·
        refine ⟨64065517392229481613180347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42710344928152987742120231 64065517392229481613180347)
        ·
          refine ⟨96098276088344222419770521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64065517392229481613180347 96098276088344222419770521)
          ·
            refine ⟨72073707066258166814827891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96098276088344222419770521 72073707066258166814827891)
            ·
              refine ⟨108110560599387250222241837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72073707066258166814827891 108110560599387250222241837)
              ·
                refine ⟨40541460224770218833340689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108110560599387250222241837 40541460224770218833340689)
                ·
                  refine ⟨30406095168577664125005517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40541460224770218833340689 30406095168577664125005517)
                  ·
                    refine ⟨11402285688216624046877069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30406095168577664125005517 11402285688216624046877069)
                    ·
                      refine ⟨4275857133081234017578901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11402285688216624046877069 4275857133081234017578901)
                      ·
                        rfl

theorem cell23_8327202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 3, 2, 3, 3].length) (baseStart_8327202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8327202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8327202 prefixEnd_8327202 := by exact prefixLift 8327202
  have htrace : WordTrace (prefixWord ++ tailWord_8327202) baseStart_8327202 baseEnd_8327202 := by
    simpa [prefixWord, tailWord_8327202, baseEnd_8327202] using wordTrace_append hprefix tailTrace_8327202
  have hstable : (prefixWord ++ tailWord_8327202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8327202).length < 2 ^ (prefixWord ++ tailWord_8327202).sum := by decide
  have hdescent : baseEnd_8327202 < baseStart_8327202 := by decide
  rcases family_descends (prefixWord ++ tailWord_8327202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8327205 : List Nat := [1, 3, 1, 2, 2, 3, 1, 2, 1, 7]
def baseStart_8327205 : Nat := 118140960795 + 8327205 * 2 ^ 59
def prefixEnd_8327205 : Nat := 4983230072969 + 3 ^ 40 * 8327205 * 2
def baseEnd_8327205 : Nat := 1425286224507732501947129

theorem tailTrace_8327205 : CollatzResearch.WordTrace tailWord_8327205 prefixEnd_8327205 1425286224507732501947129 := by
  unfold tailWord_8327205
  simp only [CollatzResearch.WordTrace]
  refine ⟨303718117796965933234103069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202478745197977288822735379 303718117796965933234103069)
  ·
    refine ⟨113894294173862224962788651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 303718117796965933234103069 113894294173862224962788651)
    ·
      refine ⟨170841441260793337444182977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113894294173862224962788651 170841441260793337444182977)
      ·
        refine ⟨128131080945595003083137233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170841441260793337444182977 128131080945595003083137233)
        ·
          refine ⟨96098310709196252312352925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128131080945595003083137233 96098310709196252312352925)
          ·
            refine ⟨36036866515948594617132347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96098310709196252312352925 36036866515948594617132347)
            ·
              refine ⟨54055299773922891925698521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36036866515948594617132347 54055299773922891925698521)
              ·
                refine ⟨40541474830442168944273891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54055299773922891925698521 40541474830442168944273891)
                ·
                  refine ⟨60812212245663253416410837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40541474830442168944273891 60812212245663253416410837)
                  ·
                    refine ⟨1425286224507732501947129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60812212245663253416410837 1425286224507732501947129)
                    ·
                      rfl

theorem cell23_8327205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 2, 1, 7].length) (baseStart_8327205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8327205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8327205 prefixEnd_8327205 := by exact prefixLift 8327205
  have htrace : WordTrace (prefixWord ++ tailWord_8327205) baseStart_8327205 baseEnd_8327205 := by
    simpa [prefixWord, tailWord_8327205, baseEnd_8327205] using wordTrace_append hprefix tailTrace_8327205
  have hstable : (prefixWord ++ tailWord_8327205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8327205).length < 2 ^ (prefixWord ++ tailWord_8327205).sum := by decide
  have hdescent : baseEnd_8327205 < baseStart_8327205 := by decide
  rcases family_descends (prefixWord ++ tailWord_8327205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8327222 : List Nat := [5, 1, 2, 1, 1, 1, 1, 3, 1, 7]
def baseStart_8327222 : Nat := 118140960795 + 8327222 * 2 ^ 59
def prefixEnd_8327222 : Nat := 4983230072969 + 3 ^ 40 * 8327222 * 2
def baseEnd_8327222 : Nat := 1425289134231441313109603

theorem tailTrace_8327222 : CollatzResearch.WordTrace tailWord_8327222 prefixEnd_8327222 1425289134231441313109603 := by
  unfold tailWord_8327222
  simp only [CollatzResearch.WordTrace]
  refine ⟨18982421114869021571091995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 202479158558602896758314613 18982421114869021571091995)
  ·
    refine ⟨28473631672303532356637993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18982421114869021571091995 28473631672303532356637993)
    ·
      refine ⟨21355223754227649267478495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28473631672303532356637993 21355223754227649267478495)
      ·
        refine ⟨32032835631341473901217743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21355223754227649267478495 32032835631341473901217743)
        ·
          refine ⟨48049253447012210851826615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32032835631341473901217743 48049253447012210851826615)
          ·
            refine ⟨72073880170518316277739923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48049253447012210851826615 72073880170518316277739923)
            ·
              refine ⟨108110820255777474416609885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72073880170518316277739923 108110820255777474416609885)
              ·
                refine ⟨40541557595916552906228707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108110820255777474416609885 40541557595916552906228707)
                ·
                  refine ⟨60812336393874829359343061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40541557595916552906228707 60812336393874829359343061)
                  ·
                    refine ⟨1425289134231441313109603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60812336393874829359343061 1425289134231441313109603)
                    ·
                      rfl

theorem cell23_8327222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 3, 1, 7].length) (baseStart_8327222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8327222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8327222 prefixEnd_8327222 := by exact prefixLift 8327222
  have htrace : WordTrace (prefixWord ++ tailWord_8327222) baseStart_8327222 baseEnd_8327222 := by
    simpa [prefixWord, tailWord_8327222, baseEnd_8327222] using wordTrace_append hprefix tailTrace_8327222
  have hstable : (prefixWord ++ tailWord_8327222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8327222).length < 2 ^ (prefixWord ++ tailWord_8327222).sum := by decide
  have hdescent : baseEnd_8327222 < baseStart_8327222 := by decide
  rcases family_descends (prefixWord ++ tailWord_8327222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8327255 : List Nat := [1, 1, 3, 2, 2, 1, 2, 2, 2, 1, 6]
def baseStart_8327255 : Nat := 118140960795 + 8327255 * 2 ^ 59
def prefixEnd_8327255 : Nat := 4983230072969 + 3 ^ 40 * 8327255 * 2
def baseEnd_8327255 : Nat := 4275884347555922310216157

theorem tailTrace_8327255 : CollatzResearch.WordTrace tailWord_8327255 prefixEnd_8327255 4275884347555922310216157 := by
  unfold tailWord_8327255
  simp only [CollatzResearch.WordTrace]
  refine ⟨303719941446784791773423219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202479960964523194515615479 303719941446784791773423219)
  ·
    refine ⟨455579912170177187660134829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303719941446784791773423219 455579912170177187660134829)
    ·
      refine ⟨170842467063816445372550561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 455579912170177187660134829 170842467063816445372550561)
      ·
        refine ⟨128131850297862334029412921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170842467063816445372550561 128131850297862334029412921)
        ·
          refine ⟨96098887723396750522059691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128131850297862334029412921 96098887723396750522059691)
          ·
            refine ⟨144148331585095125783089537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96098887723396750522059691 144148331585095125783089537)
            ·
              refine ⟨108111248688821344337317153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144148331585095125783089537 108111248688821344337317153)
              ·
                refine ⟨81083436516616008252987865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108111248688821344337317153 81083436516616008252987865)
                ·
                  refine ⟨60812577387462006189740899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81083436516616008252987865 60812577387462006189740899)
                  ·
                    refine ⟨91218866081193009284611349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60812577387462006189740899 91218866081193009284611349)
                    ·
                      refine ⟨4275884347555922310216157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91218866081193009284611349 4275884347555922310216157)
                      ·
                        rfl

theorem cell23_8327255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 2, 2, 1, 6].length) (baseStart_8327255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8327255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8327255 prefixEnd_8327255 := by exact prefixLift 8327255
  have htrace : WordTrace (prefixWord ++ tailWord_8327255) baseStart_8327255 baseEnd_8327255 := by
    simpa [prefixWord, tailWord_8327255, baseEnd_8327255] using wordTrace_append hprefix tailTrace_8327255
  have hstable : (prefixWord ++ tailWord_8327255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8327255).length < 2 ^ (prefixWord ++ tailWord_8327255).sum := by decide
  have hdescent : baseEnd_8327255 < baseStart_8327255 := by decide
  rcases family_descends (prefixWord ++ tailWord_8327255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8327279 : List Nat := [1, 1, 2, 1, 3, 5, 2, 1, 2, 2, 3]
def baseStart_8327279 : Nat := 118140960795 + 8327279 * 2 ^ 59
def prefixEnd_8327279 : Nat := 4983230072969 + 3 ^ 40 * 8327279 * 2
def baseEnd_8327279 : Nat := 4275896671091630216316047

theorem tailTrace_8327279 : CollatzResearch.WordTrace tailWord_8327279 prefixEnd_8327279 4275896671091630216316047 := by
  unfold tailWord_8327279
  simp only [CollatzResearch.WordTrace]
  refine ⟨303720816798697843872296891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202480544532465229248197927 303720816798697843872296891)
  ·
    refine ⟨455581225198046765808445337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303720816798697843872296891 455581225198046765808445337)
    ·
      refine ⟨341685918898535074356334003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 455581225198046765808445337 341685918898535074356334003)
      ·
        refine ⟨512528878347802611534501005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341685918898535074356334003 512528878347802611534501005)
        ·
          refine ⟨192198329380425979325437877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 512528878347802611534501005 192198329380425979325437877)
          ·
            refine ⟨18018593379414935561759801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 192198329380425979325437877 18018593379414935561759801)
            ·
              refine ⟨13513945034561201671319851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18018593379414935561759801 13513945034561201671319851)
              ·
                refine ⟨20270917551841802506979777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13513945034561201671319851 20270917551841802506979777)
                ·
                  refine ⟨15203188163881351880234833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20270917551841802506979777 15203188163881351880234833)
                  ·
                    refine ⟨11402391122911013910176125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15203188163881351880234833 11402391122911013910176125)
                    ·
                      refine ⟨4275896671091630216316047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11402391122911013910176125 4275896671091630216316047)
                      ·
                        rfl

theorem cell23_8327279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 2, 1, 2, 2, 3].length) (baseStart_8327279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8327279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8327279 prefixEnd_8327279 := by exact prefixLift 8327279
  have htrace : WordTrace (prefixWord ++ tailWord_8327279) baseStart_8327279 baseEnd_8327279 := by
    simpa [prefixWord, tailWord_8327279, baseEnd_8327279] using wordTrace_append hprefix tailTrace_8327279
  have hstable : (prefixWord ++ tailWord_8327279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8327279).length < 2 ^ (prefixWord ++ tailWord_8327279).sum := by decide
  have hdescent : baseEnd_8327279 < baseStart_8327279 := by decide
  rcases family_descends (prefixWord ++ tailWord_8327279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8327352 : List Nat := [2, 1, 2, 1, 2, 1, 4, 3, 1, 1, 5]
def baseStart_8327352 : Nat := 118140960795 + 8327352 * 2 ^ 59
def prefixEnd_8327352 : Nat := 4983230072969 + 3 ^ 40 * 8327352 * 2
def baseEnd_8327352 : Nat := 4275934155179408430703211

theorem tailTrace_8327352 : CollatzResearch.WordTrace tailWord_8327352 prefixEnd_8327352 4275934155179408430703211 := by
  unfold tailWord_8327352
  simp only [CollatzResearch.WordTrace]
  refine ⟨151861739663716688669852155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202482319551622251559802873 151861739663716688669852155)
  ·
    refine ⟨227792609495575033004778233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151861739663716688669852155 227792609495575033004778233)
    ·
      refine ⟨170844457121681274753583675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227792609495575033004778233 170844457121681274753583675)
      ·
        refine ⟨256266685682521912130375513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170844457121681274753583675 256266685682521912130375513)
        ·
          refine ⟨192200014261891434097781635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256266685682521912130375513 192200014261891434097781635)
          ·
            refine ⟨288300021392837151146672453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192200014261891434097781635 288300021392837151146672453)
            ·
              refine ⟨54056254011156965840001085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 288300021392837151146672453 54056254011156965840001085)
              ·
                refine ⟨20271095254183862190000407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54056254011156965840001085 20271095254183862190000407)
                ·
                  refine ⟨30406642881275793285000611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20271095254183862190000407 30406642881275793285000611)
                  ·
                    refine ⟨45609964321913689927500917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30406642881275793285000611 45609964321913689927500917)
                    ·
                      refine ⟨4275934155179408430703211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45609964321913689927500917 4275934155179408430703211)
                      ·
                        rfl

theorem cell23_8327352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 3, 1, 1, 5].length) (baseStart_8327352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8327352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8327352 prefixEnd_8327352 := by exact prefixLift 8327352
  have htrace : WordTrace (prefixWord ++ tailWord_8327352) baseStart_8327352 baseEnd_8327352 := by
    simpa [prefixWord, tailWord_8327352, baseEnd_8327352] using wordTrace_append hprefix tailTrace_8327352
  have hstable : (prefixWord ++ tailWord_8327352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8327352).length < 2 ^ (prefixWord ++ tailWord_8327352).sum := by decide
  have hdescent : baseEnd_8327352 < baseStart_8327352 := by decide
  rcases family_descends (prefixWord ++ tailWord_8327352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8327355 : List Nat := [1, 1, 1, 1, 1, 2, 16]
def baseStart_8327355 : Nat := 118140960795 + 8327355 * 2 ^ 59
def prefixEnd_8327355 : Nat := 4983230072969 + 3 ^ 40 * 8327355 * 2
def baseEnd_8327355 : Nat := 52789329575572492826737

theorem tailTrace_8327355 : CollatzResearch.WordTrace tailWord_8327355 prefixEnd_8327355 52789329575572492826737 := by
  unfold tailWord_8327355
  simp only [CollatzResearch.WordTrace]
  refine ⟨303723588746422508852063519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202482392497615005901375679 303723588746422508852063519)
  ·
    refine ⟨455585383119633763278095279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303723588746422508852063519 455585383119633763278095279)
    ·
      refine ⟨683378074679450644917142919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 455585383119633763278095279 683378074679450644917142919)
      ·
        refine ⟨1025067112019175967375714379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 683378074679450644917142919 1025067112019175967375714379)
        ·
          refine ⟨1537600668028763951063571569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1025067112019175967375714379 1537600668028763951063571569)
          ·
            refine ⟨1153200501021572963297678677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1537600668028763951063571569 1153200501021572963297678677)
            ·
              refine ⟨52789329575572492826737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 16 1153200501021572963297678677 52789329575572492826737)
              ·
                rfl

theorem cell23_8327355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 16].length) (baseStart_8327355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8327355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8327355 prefixEnd_8327355 := by exact prefixLift 8327355
  have htrace : WordTrace (prefixWord ++ tailWord_8327355) baseStart_8327355 baseEnd_8327355 := by
    simpa [prefixWord, tailWord_8327355, baseEnd_8327355] using wordTrace_append hprefix tailTrace_8327355
  have hstable : (prefixWord ++ tailWord_8327355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8327355).length < 2 ^ (prefixWord ++ tailWord_8327355).sum := by decide
  have hdescent : baseEnd_8327355 < baseStart_8327355 := by decide
  rcases family_descends (prefixWord ++ tailWord_8327355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8327389 : List Nat := [1, 4, 3, 2, 1, 2, 1, 9]
def baseStart_8327389 : Nat := 118140960795 + 8327389 * 2 ^ 59
def prefixEnd_8327389 : Nat := 4983230072969 + 3 ^ 40 * 8327389 * 2
def baseEnd_8327389 : Nat := 158368635331986103182983

theorem tailTrace_8327389 : CollatzResearch.WordTrace tailWord_8327389 prefixEnd_8327389 158368635331986103182983 := by
  unfold tailWord_8327389
  simp only [CollatzResearch.WordTrace]
  refine ⟨303724828828299332658801221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202483219218866221772534147 303724828828299332658801221)
  ·
    refine ⟨56948405405306124873525229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 303724828828299332658801221 56948405405306124873525229)
    ·
      refine ⟨21355652026989796827571961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56948405405306124873525229 21355652026989796827571961)
      ·
        refine ⟨16016739020242347620678971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21355652026989796827571961 16016739020242347620678971)
        ·
          refine ⟨24025108530363521431018457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16016739020242347620678971 24025108530363521431018457)
          ·
            refine ⟨18018831397772641073263843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24025108530363521431018457 18018831397772641073263843)
            ·
              refine ⟨27028247096658961609895765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18018831397772641073263843 27028247096658961609895765)
              ·
                refine ⟨158368635331986103182983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 27028247096658961609895765 158368635331986103182983)
                ·
                  rfl

theorem cell23_8327389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 9].length) (baseStart_8327389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8327389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8327389 prefixEnd_8327389 := by exact prefixLift 8327389
  have htrace : WordTrace (prefixWord ++ tailWord_8327389) baseStart_8327389 baseEnd_8327389 := by
    simpa [prefixWord, tailWord_8327389, baseEnd_8327389] using wordTrace_append hprefix tailTrace_8327389
  have hstable : (prefixWord ++ tailWord_8327389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8327389).length < 2 ^ (prefixWord ++ tailWord_8327389).sum := by decide
  have hdescent : baseEnd_8327389 < baseStart_8327389 := by decide
  rcases family_descends (prefixWord ++ tailWord_8327389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8327400 : List Nat := [2, 1, 4, 1, 2, 2, 3, 3, 1, 2, 2]
def baseStart_8327400 : Nat := 118140960795 + 8327400 * 2 ^ 59
def prefixEnd_8327400 : Nat := 4983230072969 + 3 ^ 40 * 8327400 * 2
def baseEnd_8327400 : Nat := 4275958802250824242902991

theorem tailTrace_8327400 : CollatzResearch.WordTrace tailWord_8327400 prefixEnd_8327400 4275958802250824242902991 := by
  unfold tailWord_8327400
  simp only [CollatzResearch.WordTrace]
  refine ⟨151862615015629740768725827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202483486687506321024967769 151862615015629740768725827)
  ·
    refine ⟨227793922523444611153088741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151862615015629740768725827 227793922523444611153088741)
    ·
      refine ⟨42711360473145864591204139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 227793922523444611153088741 42711360473145864591204139)
      ·
        refine ⟨64067040709718796886806209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42711360473145864591204139 64067040709718796886806209)
        ·
          refine ⟨48050280532289097665104657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64067040709718796886806209 48050280532289097665104657)
          ·
            refine ⟨36037710399216823248828493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48050280532289097665104657 36037710399216823248828493)
            ·
              refine ⟨13514141399706308718310685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36037710399216823248828493 13514141399706308718310685)
              ·
                refine ⟨5067803024889865769366507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13514141399706308718310685 5067803024889865769366507)
                ·
                  refine ⟨7601704537334798654049761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5067803024889865769366507 7601704537334798654049761)
                  ·
                    refine ⟨5701278403001098990537321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7601704537334798654049761 5701278403001098990537321)
                    ·
                      refine ⟨4275958802250824242902991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5701278403001098990537321 4275958802250824242902991)
                      ·
                        rfl

theorem cell23_8327400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 3, 3, 1, 2, 2].length) (baseStart_8327400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8327400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8327400 prefixEnd_8327400 := by exact prefixLift 8327400
  have htrace : WordTrace (prefixWord ++ tailWord_8327400) baseStart_8327400 baseEnd_8327400 := by
    simpa [prefixWord, tailWord_8327400, baseEnd_8327400] using wordTrace_append hprefix tailTrace_8327400
  have hstable : (prefixWord ++ tailWord_8327400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8327400).length < 2 ^ (prefixWord ++ tailWord_8327400).sum := by decide
  have hdescent : baseEnd_8327400 < baseStart_8327400 := by decide
  rcases family_descends (prefixWord ++ tailWord_8327400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8327433 : List Nat := [1, 2, 1, 1, 3, 4, 4, 1, 2, 1, 3]
def baseStart_8327433 : Nat := 118140960795 + 8327433 * 2 ^ 59
def prefixEnd_8327433 : Nat := 4983230072969 + 3 ^ 40 * 8327433 * 2
def baseEnd_8327433 : Nat := 4275975747112422613790339

theorem tailTrace_8327433 : CollatzResearch.WordTrace tailWord_8327433 prefixEnd_8327433 4275975747112422613790339 := by
  unfold tailWord_8327433
  simp only [CollatzResearch.WordTrace]
  refine ⟨303726433640139928173402953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202484289093426618782268635 303726433640139928173402953)
  ·
    refine ⟨227794825230104946130052215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303726433640139928173402953 227794825230104946130052215)
    ·
      refine ⟨341692237845157419195078323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227794825230104946130052215 341692237845157419195078323)
      ·
        refine ⟨512538356767736128792617485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341692237845157419195078323 512538356767736128792617485)
        ·
          refine ⟨192201883787901048297231557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 512538356767736128792617485 192201883787901048297231557)
          ·
            refine ⟨36037853210231446555730917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 192201883787901048297231557 36037853210231446555730917)
            ·
              refine ⟨6757097476918396229199547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36037853210231446555730917 6757097476918396229199547)
              ·
                refine ⟨10135646215377594343799321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6757097476918396229199547 10135646215377594343799321)
                ·
                  refine ⟨7601734661533195757849491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10135646215377594343799321 7601734661533195757849491)
                  ·
                    refine ⟨11402601992299793636774237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7601734661533195757849491 11402601992299793636774237)
                    ·
                      refine ⟨4275975747112422613790339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11402601992299793636774237 4275975747112422613790339)
                      ·
                        rfl

theorem cell23_8327433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 4, 1, 2, 1, 3].length) (baseStart_8327433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8327433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8327433 prefixEnd_8327433 := by exact prefixLift 8327433
  have htrace : WordTrace (prefixWord ++ tailWord_8327433) baseStart_8327433 baseEnd_8327433 := by
    simpa [prefixWord, tailWord_8327433, baseEnd_8327433] using wordTrace_append hprefix tailTrace_8327433
  have hstable : (prefixWord ++ tailWord_8327433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8327433).length < 2 ^ (prefixWord ++ tailWord_8327433).sum := by decide
  have hdescent : baseEnd_8327433 < baseStart_8327433 := by decide
  rcases family_descends (prefixWord ++ tailWord_8327433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8327439 : List Nat := [1, 1, 2, 1, 1, 1, 3, 2, 5, 4, 2]
def baseStart_8327439 : Nat := 118140960795 + 8327439 * 2 ^ 59
def prefixEnd_8327439 : Nat := 4983230072969 + 3 ^ 40 * 8327439 * 2
def baseEnd_8327439 : Nat := 4275978827996349590315311

theorem tailTrace_8327439 : CollatzResearch.WordTrace tailWord_8327439 prefixEnd_8327439 4275978827996349590315311 := by
  unfold tailWord_8327439
  simp only [CollatzResearch.WordTrace]
  refine ⟨303726652478118191198121371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202484434985412127465414247 303726652478118191198121371)
  ·
    refine ⟨455589978717177286797182057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303726652478118191198121371 455589978717177286797182057)
    ·
      refine ⟨341692484037882965097886543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 455589978717177286797182057 341692484037882965097886543)
      ·
        refine ⟨512538726056824447646829815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341692484037882965097886543 512538726056824447646829815)
        ·
          refine ⟨768808089085236671470244723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 512538726056824447646829815 768808089085236671470244723)
          ·
            refine ⟨1153212133627855007205367085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 768808089085236671470244723 1153212133627855007205367085)
            ·
              refine ⟨432454550110445627702012657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1153212133627855007205367085 432454550110445627702012657)
              ·
                refine ⟨324340912582834220776509493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 432454550110445627702012657 324340912582834220776509493)
                ·
                  refine ⟨30406960554640708197797765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 324340912582834220776509493 30406960554640708197797765)
                  ·
                    refine ⟨5701305103995132787087081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30406960554640708197797765 5701305103995132787087081)
                    ·
                      refine ⟨4275978827996349590315311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5701305103995132787087081 4275978827996349590315311)
                      ·
                        rfl

theorem cell23_8327439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 5, 4, 2].length) (baseStart_8327439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8327439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8327439 prefixEnd_8327439 := by exact prefixLift 8327439
  have htrace : WordTrace (prefixWord ++ tailWord_8327439) baseStart_8327439 baseEnd_8327439 := by
    simpa [prefixWord, tailWord_8327439, baseEnd_8327439] using wordTrace_append hprefix tailTrace_8327439
  have hstable : (prefixWord ++ tailWord_8327439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8327439).length < 2 ^ (prefixWord ++ tailWord_8327439).sum := by decide
  have hdescent : baseEnd_8327439 < baseStart_8327439 := by decide
  rcases family_descends (prefixWord ++ tailWord_8327439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8327456 : List Nat := [2, 1, 1, 5, 2, 1, 1, 1, 3, 4, 2]
def baseStart_8327456 : Nat := 118140960795 + 8327456 * 2 ^ 59
def prefixEnd_8327456 : Nat := 4983230072969 + 3 ^ 40 * 8327456 * 2
def baseEnd_8327456 : Nat := 4275987557167476023802733

theorem tailTrace_8327456 : CollatzResearch.WordTrace tailWord_8327456 prefixEnd_8327456 4275987557167476023802733 := by
  unfold tailWord_8327456
  simp only [CollatzResearch.WordTrace]
  refine ⟨151863636259528301550745111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202484848346037735400993481 151863636259528301550745111)
  ·
    refine ⟨227795454389292452326117667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151863636259528301550745111 227795454389292452326117667)
    ·
      refine ⟨341693181583938678489176501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227795454389292452326117667 341693181583938678489176501)
      ·
        refine ⟨32033735773494251108360297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 341693181583938678489176501 32033735773494251108360297)
        ·
          refine ⟨24025301830120688331270223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32033735773494251108360297 24025301830120688331270223)
          ·
            refine ⟨36037952745181032496905335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24025301830120688331270223 36037952745181032496905335)
            ·
              refine ⟨54056929117771548745358003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36037952745181032496905335 54056929117771548745358003)
              ·
                refine ⟨81085393676657323118037005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54056929117771548745358003 81085393676657323118037005)
                ·
                  refine ⟨30407022628746496169263877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81085393676657323118037005 30407022628746496169263877)
                  ·
                    refine ⟨5701316742889968031736977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30407022628746496169263877 5701316742889968031736977)
                    ·
                      refine ⟨4275987557167476023802733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5701316742889968031736977 4275987557167476023802733)
                      ·
                        rfl

theorem cell23_8327456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 1, 3, 4, 2].length) (baseStart_8327456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8327456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8327456 prefixEnd_8327456 := by exact prefixLift 8327456
  have htrace : WordTrace (prefixWord ++ tailWord_8327456) baseStart_8327456 baseEnd_8327456 := by
    simpa [prefixWord, tailWord_8327456, baseEnd_8327456] using wordTrace_append hprefix tailTrace_8327456
  have hstable : (prefixWord ++ tailWord_8327456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8327456).length < 2 ^ (prefixWord ++ tailWord_8327456).sum := by decide
  have hdescent : baseEnd_8327456 < baseStart_8327456 := by decide
  rcases family_descends (prefixWord ++ tailWord_8327456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8327460 : List Nat := [2, 3, 1, 3, 1, 3, 3, 1, 1, 3, 2]
def baseStart_8327460 : Nat := 118140960795 + 8327460 * 2 ^ 59
def prefixEnd_8327460 : Nat := 4983230072969 + 3 ^ 40 * 8327460 * 2
def baseEnd_8327460 : Nat := 4275989611090094008152715

theorem tailTrace_8327460 : CollatzResearch.WordTrace tailWord_8327460 prefixEnd_8327460 4275989611090094008152715 := by
  unfold tailWord_8327460
  simp only [CollatzResearch.WordTrace]
  refine ⟨151863709205521055892317917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202484945607361407856423889 151863709205521055892317917)
  ·
    refine ⟨56948890952070395959619219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151863709205521055892317917 56948890952070395959619219)
    ·
      refine ⟨85423336428105593939428829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56948890952070395959619219 85423336428105593939428829)
      ·
        refine ⟨32033751160539597727285811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85423336428105593939428829 32033751160539597727285811)
        ·
          refine ⟨48050626740809396590928717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32033751160539597727285811 48050626740809396590928717)
          ·
            refine ⟨18018985027803523721598269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48050626740809396590928717 18018985027803523721598269)
            ·
              refine ⟨6757119385426321395599351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18018985027803523721598269 6757119385426321395599351)
              ·
                refine ⟨10135679078139482093399027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6757119385426321395599351 10135679078139482093399027)
                ·
                  refine ⟨15203518617209223140098541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10135679078139482093399027 15203518617209223140098541)
                  ·
                    refine ⟨5701319481453458677536953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15203518617209223140098541 5701319481453458677536953)
                    ·
                      refine ⟨4275989611090094008152715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5701319481453458677536953 4275989611090094008152715)
                      ·
                        rfl

theorem cell23_8327460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 3, 1, 1, 3, 2].length) (baseStart_8327460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8327460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8327460 prefixEnd_8327460 := by exact prefixLift 8327460
  have htrace : WordTrace (prefixWord ++ tailWord_8327460) baseStart_8327460 baseEnd_8327460 := by
    simpa [prefixWord, tailWord_8327460, baseEnd_8327460] using wordTrace_append hprefix tailTrace_8327460
  have hstable : (prefixWord ++ tailWord_8327460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8327460).length < 2 ^ (prefixWord ++ tailWord_8327460).sum := by decide
  have hdescent : baseEnd_8327460 < baseStart_8327460 := by decide
  rcases family_descends (prefixWord ++ tailWord_8327460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8327476 : List Nat := [2, 5, 1, 1, 1, 2, 1, 1, 2, 4, 3]
def baseStart_8327476 : Nat := 118140960795 + 8327476 * 2 ^ 59
def prefixEnd_8327476 : Nat := 4983230072969 + 3 ^ 40 * 8327476 * 2
def baseEnd_8327476 : Nat := 4275997826780565945552641

theorem tailTrace_8327476 : CollatzResearch.WordTrace tailWord_8327476 prefixEnd_8327476 4275997826780565945552641 := by
  unfold tailWord_8327476
  simp only [CollatzResearch.WordTrace]
  refine ⟨151864000989492073258609141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202485334652656097678145521 151864000989492073258609141)
  ·
    refine ⟨14237250092764881867994607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 151864000989492073258609141 14237250092764881867994607)
    ·
      refine ⟨21355875139147322801991911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14237250092764881867994607 21355875139147322801991911)
      ·
        refine ⟨32033812708720984202987867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21355875139147322801991911 32033812708720984202987867)
        ·
          refine ⟨48050719063081476304481801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32033812708720984202987867 48050719063081476304481801)
          ·
            refine ⟨36038039297311107228361351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48050719063081476304481801 36038039297311107228361351)
            ·
              refine ⟨54057058945966660842542027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36038039297311107228361351 54057058945966660842542027)
              ·
                refine ⟨81085588418949991263813041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54057058945966660842542027 81085588418949991263813041)
                ·
                  refine ⟨60814191314212493447859781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81085588418949991263813041 60814191314212493447859781)
                  ·
                    refine ⟨11402660871414842521473709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60814191314212493447859781 11402660871414842521473709)
                    ·
                      refine ⟨4275997826780565945552641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11402660871414842521473709 4275997826780565945552641)
                      ·
                        rfl

theorem cell23_8327476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 1, 2, 4, 3].length) (baseStart_8327476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8327476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8327476 prefixEnd_8327476 := by exact prefixLift 8327476
  have htrace : WordTrace (prefixWord ++ tailWord_8327476) baseStart_8327476 baseEnd_8327476 := by
    simpa [prefixWord, tailWord_8327476, baseEnd_8327476] using wordTrace_append hprefix tailTrace_8327476
  have hstable : (prefixWord ++ tailWord_8327476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8327476).length < 2 ^ (prefixWord ++ tailWord_8327476).sum := by decide
  have hdescent : baseEnd_8327476 < baseStart_8327476 := by decide
  rcases family_descends (prefixWord ++ tailWord_8327476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8327486 : List Nat := [4, 2, 1, 2, 1, 3, 1, 1, 2, 2, 4]
def baseStart_8327486 : Nat := 118140960795 + 8327486 * 2 ^ 59
def prefixEnd_8327486 : Nat := 4983230072969 + 3 ^ 40 * 8327486 * 2
def baseEnd_8327486 : Nat := 4276002961587110906427595

theorem tailTrace_8327486 : CollatzResearch.WordTrace tailWord_8327486 prefixEnd_8327486 4276002961587110906427595 := by
  unfold tailWord_8327486
  simp only [CollatzResearch.WordTrace]
  refine ⟨37966045838618489778135289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202485577805965278816721541 37966045838618489778135289)
  ·
    refine ⟨28474534378963867333601467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37966045838618489778135289 28474534378963867333601467)
    ·
      refine ⟨42711801568445801000402201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28474534378963867333601467 42711801568445801000402201)
      ·
        refine ⟨32033851176334350750301651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42711801568445801000402201 32033851176334350750301651)
        ·
          refine ⟨48050776764501526125452477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32033851176334350750301651 48050776764501526125452477)
          ·
            refine ⟨18019041286688072297044679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48050776764501526125452477 18019041286688072297044679)
            ·
              refine ⟨27028561930032108445567019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18019041286688072297044679 27028561930032108445567019)
              ·
                refine ⟨40542842895048162668350529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27028561930032108445567019 40542842895048162668350529)
                ·
                  refine ⟨30407132171286122001262897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40542842895048162668350529 30407132171286122001262897)
                  ·
                    refine ⟨22805349128464591500947173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30407132171286122001262897 22805349128464591500947173)
                    ·
                      refine ⟨4276002961587110906427595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22805349128464591500947173 4276002961587110906427595)
                      ·
                        rfl

theorem cell23_8327486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_8327486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8327486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8327486 prefixEnd_8327486 := by exact prefixLift 8327486
  have htrace : WordTrace (prefixWord ++ tailWord_8327486) baseStart_8327486 baseEnd_8327486 := by
    simpa [prefixWord, tailWord_8327486, baseEnd_8327486] using wordTrace_append hprefix tailTrace_8327486
  have hstable : (prefixWord ++ tailWord_8327486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8327486).length < 2 ^ (prefixWord ++ tailWord_8327486).sum := by decide
  have hdescent : baseEnd_8327486 < baseStart_8327486 := by decide
  rcases family_descends (prefixWord ++ tailWord_8327486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8327518 : List Nat := [4, 4, 2, 1, 2, 1, 1, 2, 2, 1, 3]
def baseStart_8327518 : Nat := 118140960795 + 8327518 * 2 ^ 59
def prefixEnd_8327518 : Nat := 4983230072969 + 3 ^ 40 * 8327518 * 2
def baseEnd_8327518 : Nat := 4276019392968054781227449

theorem tailTrace_8327518 : CollatzResearch.WordTrace tailWord_8327518 prefixEnd_8327518 4276019392968054781227449 := by
  unfold tailWord_8327518
  simp only [CollatzResearch.WordTrace]
  refine ⟨37966191730603998461280901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202486355896554658460164805 37966191730603998461280901)
  ·
    refine ⟨7118660949488249711490169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37966191730603998461280901 7118660949488249711490169)
    ·
      refine ⟨5338995712116187283617627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7118660949488249711490169 5338995712116187283617627)
      ·
        refine ⟨8008493568174280925426441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5338995712116187283617627 8008493568174280925426441)
        ·
          refine ⟨6006370176130710694069831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8008493568174280925426441 6006370176130710694069831)
          ·
            refine ⟨9009555264196066041104747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6006370176130710694069831 9009555264196066041104747)
            ·
              refine ⟨13514332896294099061657121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9009555264196066041104747 13514332896294099061657121)
              ·
                refine ⟨10135749672220574296242841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13514332896294099061657121 10135749672220574296242841)
                ·
                  refine ⟨7601812254165430722182131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10135749672220574296242841 7601812254165430722182131)
                  ·
                    refine ⟨11402718381248146083273197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7601812254165430722182131 11402718381248146083273197)
                    ·
                      refine ⟨4276019392968054781227449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11402718381248146083273197 4276019392968054781227449)
                      ·
                        rfl

theorem cell23_8327518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_8327518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8327518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8327518 prefixEnd_8327518 := by exact prefixLift 8327518
  have htrace : WordTrace (prefixWord ++ tailWord_8327518) baseStart_8327518 baseEnd_8327518 := by
    simpa [prefixWord, tailWord_8327518, baseEnd_8327518] using wordTrace_append hprefix tailTrace_8327518
  have hstable : (prefixWord ++ tailWord_8327518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8327518).length < 2 ^ (prefixWord ++ tailWord_8327518).sum := by decide
  have hdescent : baseEnd_8327518 < baseStart_8327518 := by decide
  rcases family_descends (prefixWord ++ tailWord_8327518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8327529 : List Nat := [1, 2, 1, 1, 1, 3, 4, 1, 4, 1, 4]
def baseStart_8327529 : Nat := 118140960795 + 8327529 * 2 ^ 59
def prefixEnd_8327529 : Nat := 4983230072969 + 3 ^ 40 * 8327529 * 2
def baseEnd_8327529 : Nat := 4276025041255254238189897

theorem tailTrace_8327529 : CollatzResearch.WordTrace tailWord_8327529 prefixEnd_8327529 4276025041255254238189897 := by
  unfold tailWord_8327529
  simp only [CollatzResearch.WordTrace]
  refine ⟨303729935047792136568897641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202486623365194757712598427 303729935047792136568897641)
  ·
    refine ⟨227797451285844102426673231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303729935047792136568897641 227797451285844102426673231)
    ·
      refine ⟨341696176928766153640009847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227797451285844102426673231 341696176928766153640009847)
      ·
        refine ⟨512544265393149230460014771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341696176928766153640009847 512544265393149230460014771)
        ·
          refine ⟨768816398089723845690022157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 512544265393149230460014771 768816398089723845690022157)
          ·
            refine ⟨288306149283646442133758309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 768816398089723845690022157 288306149283646442133758309)
            ·
              refine ⟨54057402990683707900079683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 288306149283646442133758309 54057402990683707900079683)
              ·
                refine ⟨81086104486025561850119525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54057402990683707900079683 81086104486025561850119525)
                ·
                  refine ⟨15203644591129792846897411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81086104486025561850119525 15203644591129792846897411)
                  ·
                    refine ⟨22805466886694689270346117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15203644591129792846897411 22805466886694689270346117)
                    ·
                      refine ⟨4276025041255254238189897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22805466886694689270346117 4276025041255254238189897)
                      ·
                        rfl

theorem cell23_8327529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 1, 4, 1, 4].length) (baseStart_8327529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8327529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8327529 prefixEnd_8327529 := by exact prefixLift 8327529
  have htrace : WordTrace (prefixWord ++ tailWord_8327529) baseStart_8327529 baseEnd_8327529 := by
    simpa [prefixWord, tailWord_8327529, baseEnd_8327529] using wordTrace_append hprefix tailTrace_8327529
  have hstable : (prefixWord ++ tailWord_8327529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8327529).length < 2 ^ (prefixWord ++ tailWord_8327529).sum := by decide
  have hdescent : baseEnd_8327529 < baseStart_8327529 := by decide
  rcases family_descends (prefixWord ++ tailWord_8327529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8327539 : List Nat := [1, 1, 1, 2, 2, 1, 2, 2, 7, 4]
def baseStart_8327539 : Nat := 118140960795 + 8327539 * 2 ^ 59
def prefixEnd_8327539 : Nat := 4983230072969 + 3 ^ 40 * 8327539 * 2
def baseEnd_8327539 : Nat := 1425343392020599733021617

theorem tailTrace_8327539 : CollatzResearch.WordTrace tailWord_8327539 prefixEnd_8327539 1425343392020599733021617 := by
  unfold tailWord_8327539
  simp only [CollatzResearch.WordTrace]
  refine ⟨303730299777755908276761671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202486866518503938851174447 303730299777755908276761671)
  ·
    refine ⟨455595449666633862415142507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303730299777755908276761671 455595449666633862415142507)
    ·
      refine ⟨683393174499950793622713761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 455595449666633862415142507 683393174499950793622713761)
      ·
        refine ⟨512544880874963095217035321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 683393174499950793622713761 512544880874963095217035321)
        ·
          refine ⟨384408660656222321412776491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 512544880874963095217035321 384408660656222321412776491)
          ·
            refine ⟨576612990984333482119164737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 384408660656222321412776491 576612990984333482119164737)
            ·
              refine ⟨432459743238250111589373553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 576612990984333482119164737 432459743238250111589373553)
              ·
                refine ⟨324344807428687583692030165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 432459743238250111589373553 324344807428687583692030165)
                ·
                  refine ⟨7601831424109865242781957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 324344807428687583692030165 7601831424109865242781957)
                  ·
                    refine ⟨1425343392020599733021617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7601831424109865242781957 1425343392020599733021617)
                    ·
                      rfl

theorem cell23_8327539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 7, 4].length) (baseStart_8327539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8327539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8327539 prefixEnd_8327539 := by exact prefixLift 8327539
  have htrace : WordTrace (prefixWord ++ tailWord_8327539) baseStart_8327539 baseEnd_8327539 := by
    simpa [prefixWord, tailWord_8327539, baseEnd_8327539] using wordTrace_append hprefix tailTrace_8327539
  have hstable : (prefixWord ++ tailWord_8327539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8327539).length < 2 ^ (prefixWord ++ tailWord_8327539).sum := by decide
  have hdescent : baseEnd_8327539 < baseStart_8327539 := by decide
  rcases family_descends (prefixWord ++ tailWord_8327539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8327556 : List Nat := [2, 3, 2, 1, 1, 2, 1, 4, 3, 4]
def baseStart_8327556 : Nat := 118140960795 + 8327556 * 2 ^ 59
def prefixEnd_8327556 : Nat := 4983230072969 + 3 ^ 40 * 8327556 * 2
def baseEnd_8327556 : Nat := 1425346301744308544184091

theorem tailTrace_8327556 : CollatzResearch.WordTrace tailWord_8327556 prefixEnd_8327556 1425346301744308544184091 := by
  unfold tailWord_8327556
  simp only [CollatzResearch.WordTrace]
  refine ⟨151865459909347160090065261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202487279879129546786753681 151865459909347160090065261)
  ·
    refine ⟨56949547466005185033774473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151865459909347160090065261 56949547466005185033774473)
    ·
      refine ⟨42712160599503888775330855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56949547466005185033774473 42712160599503888775330855)
      ·
        refine ⟨64068240899255833162996283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42712160599503888775330855 64068240899255833162996283)
        ·
          refine ⟨96102361348883749744494425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64068240899255833162996283 96102361348883749744494425)
          ·
            refine ⟨72076771011662812308370819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96102361348883749744494425 72076771011662812308370819)
            ·
              refine ⟨108115156517494218462556229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72076771011662812308370819 108115156517494218462556229)
              ·
                refine ⟨20271591847030165961729293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 108115156517494218462556229 20271591847030165961729293)
                ·
                  refine ⟨7601846942636312235648485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20271591847030165961729293 7601846942636312235648485)
                  ·
                    refine ⟨1425346301744308544184091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7601846942636312235648485 1425346301744308544184091)
                    ·
                      rfl

theorem cell23_8327556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 4, 3, 4].length) (baseStart_8327556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8327556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8327556 prefixEnd_8327556 := by exact prefixLift 8327556
  have htrace : WordTrace (prefixWord ++ tailWord_8327556) baseStart_8327556 baseEnd_8327556 := by
    simpa [prefixWord, tailWord_8327556, baseEnd_8327556] using wordTrace_append hprefix tailTrace_8327556
  have hstable : (prefixWord ++ tailWord_8327556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8327556).length < 2 ^ (prefixWord ++ tailWord_8327556).sum := by decide
  have hdescent : baseEnd_8327556 < baseStart_8327556 := by decide
  rcases family_descends (prefixWord ++ tailWord_8327556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8327559 : List Nat := [1, 1, 4, 2, 2, 1, 1, 1, 2, 4, 4]
def baseStart_8327559 : Nat := 118140960795 + 8327559 * 2 ^ 59
def prefixEnd_8327559 : Nat := 4983230072969 + 3 ^ 40 * 8327559 * 2
def baseEnd_8327559 : Nat := 4276040445674889120814759

theorem tailTrace_8327559 : CollatzResearch.WordTrace tailWord_8327559 prefixEnd_8327559 4276040445674889120814759 := by
  unfold tailWord_8327559
  simp only [CollatzResearch.WordTrace]
  refine ⟨303731029237683451692489731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202487352825122301128326487 303731029237683451692489731)
  ·
    refine ⟨455596543856525177538734597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303731029237683451692489731 455596543856525177538734597)
    ·
      refine ⟨85424351973098470788512737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 455596543856525177538734597 85424351973098470788512737)
      ·
        refine ⟨64068263979823853091384553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85424351973098470788512737 64068263979823853091384553)
        ·
          refine ⟨48051197984867889818538415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64068263979823853091384553 48051197984867889818538415)
          ·
            refine ⟨72076796977301834727807623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48051197984867889818538415 72076796977301834727807623)
            ·
              refine ⟨108115195465952752091711435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72076796977301834727807623 108115195465952752091711435)
              ·
                refine ⟨162172793198929128137567153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108115195465952752091711435 162172793198929128137567153)
                ·
                  refine ⟨121629594899196846103175365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 162172793198929128137567153 121629594899196846103175365)
                  ·
                    refine ⟨22805549043599408644345381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 121629594899196846103175365 22805549043599408644345381)
                    ·
                      refine ⟨4276040445674889120814759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22805549043599408644345381 4276040445674889120814759)
                      ·
                        rfl

theorem cell23_8327559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 2, 4, 4].length) (baseStart_8327559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8327559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8327559 prefixEnd_8327559 := by exact prefixLift 8327559
  have htrace : WordTrace (prefixWord ++ tailWord_8327559) baseStart_8327559 baseEnd_8327559 := by
    simpa [prefixWord, tailWord_8327559, baseEnd_8327559] using wordTrace_append hprefix tailTrace_8327559
  have hstable : (prefixWord ++ tailWord_8327559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8327559).length < 2 ^ (prefixWord ++ tailWord_8327559).sum := by decide
  have hdescent : baseEnd_8327559 < baseStart_8327559 := by decide
  rcases family_descends (prefixWord ++ tailWord_8327559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8327586 : List Nat := [3, 3, 1, 2, 1, 1, 2, 4, 6]
def baseStart_8327586 : Nat := 118140960795 + 8327586 * 2 ^ 59
def prefixEnd_8327586 : Nat := 4983230072969 + 3 ^ 40 * 8327586 * 2
def baseEnd_8327586 : Nat := 475117145516951168353015

theorem tailTrace_8327586 : CollatzResearch.WordTrace tailWord_8327586 prefixEnd_8327586 475117145516951168353015 := by
  unfold tailWord_8327586
  simp only [CollatzResearch.WordTrace]
  refine ⟨75933003502146408825930653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202488009339057090202481741 75933003502146408825930653)
  ·
    refine ⟨28474876313304903309723995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75933003502146408825930653 28474876313304903309723995)
    ·
      refine ⟨42712314469957354964585993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28474876313304903309723995 42712314469957354964585993)
      ·
        refine ⟨32034235852468016223439495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42712314469957354964585993 32034235852468016223439495)
        ·
          refine ⟨48051353778702024335159243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32034235852468016223439495 48051353778702024335159243)
          ·
            refine ⟨72077030668053036502738865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48051353778702024335159243 72077030668053036502738865)
            ·
              refine ⟨54057773001039777377054149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72077030668053036502738865 54057773001039777377054149)
              ·
                refine ⟨10135832437694958258197653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54057773001039777377054149 10135832437694958258197653)
                ·
                  refine ⟨475117145516951168353015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10135832437694958258197653 475117145516951168353015)
                  ·
                    rfl

theorem cell23_8327586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 4, 6].length) (baseStart_8327586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8327586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8327586 prefixEnd_8327586 := by exact prefixLift 8327586
  have htrace : WordTrace (prefixWord ++ tailWord_8327586) baseStart_8327586 baseEnd_8327586 := by
    simpa [prefixWord, tailWord_8327586, baseEnd_8327586] using wordTrace_append hprefix tailTrace_8327586
  have hstable : (prefixWord ++ tailWord_8327586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8327586).length < 2 ^ (prefixWord ++ tailWord_8327586).sum := by decide
  have hdescent : baseEnd_8327586 < baseStart_8327586 := by decide
  rcases family_descends (prefixWord ++ tailWord_8327586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8327623 : List Nat := [1, 1, 4, 1, 1, 4, 1, 3, 2, 3, 2]
def baseStart_8327623 : Nat := 118140960795 + 8327623 * 2 ^ 59
def prefixEnd_8327623 : Nat := 4983230072969 + 3 ^ 40 * 8327623 * 2
def baseEnd_8327623 : Nat := 4276073308436776870414465

theorem tailTrace_8327623 : CollatzResearch.WordTrace tailWord_8327623 prefixEnd_8327623 4276073308436776870414465 := by
  unfold tailWord_8327623
  simp only [CollatzResearch.WordTrace]
  refine ⟨303733363509451590622819523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202488909006301060415213015 303733363509451590622819523)
  ·
    refine ⟨455600045264177385934229285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303733363509451590622819523 455600045264177385934229285)
    ·
      refine ⟨85425008487033259862667991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 455600045264177385934229285 85425008487033259862667991)
      ·
        refine ⟨128137512730549889794001987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85425008487033259862667991 128137512730549889794001987)
        ·
          refine ⟨192206269095824834691002981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128137512730549889794001987 192206269095824834691002981)
          ·
            refine ⟨36038675455467156504563059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 192206269095824834691002981 36038675455467156504563059)
            ·
              refine ⟨54058013183200734756844589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36038675455467156504563059 54058013183200734756844589)
              ·
                refine ⟨20271754943700275533816721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54058013183200734756844589 20271754943700275533816721)
                ·
                  refine ⟨15203816207775206650362541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20271754943700275533816721 15203816207775206650362541)
                  ·
                    refine ⟨5701431077915702493885953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15203816207775206650362541 5701431077915702493885953)
                    ·
                      refine ⟨4276073308436776870414465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5701431077915702493885953 4276073308436776870414465)
                      ·
                        rfl

theorem cell23_8327623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 3, 2, 3, 2].length) (baseStart_8327623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8327623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8327623 prefixEnd_8327623 := by exact prefixLift 8327623
  have htrace : WordTrace (prefixWord ++ tailWord_8327623) baseStart_8327623 baseEnd_8327623 := by
    simpa [prefixWord, tailWord_8327623, baseEnd_8327623] using wordTrace_append hprefix tailTrace_8327623
  have hstable : (prefixWord ++ tailWord_8327623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8327623).length < 2 ^ (prefixWord ++ tailWord_8327623).sum := by decide
  have hdescent : baseEnd_8327623 < baseStart_8327623 := by decide
  rcases family_descends (prefixWord ++ tailWord_8327623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8327630 : List Nat := [4, 1, 1, 1, 2, 1, 1, 7, 1, 1, 3]
def baseStart_8327630 : Nat := 118140960795 + 8327630 * 2 ^ 59
def prefixEnd_8327630 : Nat := 4983230072969 + 3 ^ 40 * 8327630 * 2
def baseEnd_8327630 : Nat := 4276076902801358343026933

theorem tailTrace_8327630 : CollatzResearch.WordTrace tailWord_8327630 prefixEnd_8327630 4276076902801358343026933 := by
  unfold tailWord_8327630
  simp only [CollatzResearch.WordTrace]
  refine ⟨37966702352553278852290543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202489079213617487212216229 37966702352553278852290543)
  ·
    refine ⟨56950053528829918278435815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37966702352553278852290543 56950053528829918278435815)
    ·
      refine ⟨85425080293244877417653723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56950053528829918278435815 85425080293244877417653723)
      ·
        refine ⟨128137620439867316126480585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85425080293244877417653723 128137620439867316126480585)
        ·
          refine ⟨96103215329900487094860439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128137620439867316126480585 96103215329900487094860439)
          ·
            refine ⟨144154822994850730642290659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96103215329900487094860439 144154822994850730642290659)
            ·
              refine ⟨216232234492276095963435989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144154822994850730642290659 216232234492276095963435989)
              ·
                refine ⟨5067942995912720999143031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 216232234492276095963435989 5067942995912720999143031)
                ·
                  refine ⟨7601914493869081498714547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5067942995912720999143031 7601914493869081498714547)
                  ·
                    refine ⟨11402871740803622248071821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7601914493869081498714547 11402871740803622248071821)
                    ·
                      refine ⟨4276076902801358343026933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11402871740803622248071821 4276076902801358343026933)
                      ·
                        rfl

theorem cell23_8327630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 7, 1, 1, 3].length) (baseStart_8327630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8327630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8327630 prefixEnd_8327630 := by exact prefixLift 8327630
  have htrace : WordTrace (prefixWord ++ tailWord_8327630) baseStart_8327630 baseEnd_8327630 := by
    simpa [prefixWord, tailWord_8327630, baseEnd_8327630] using wordTrace_append hprefix tailTrace_8327630
  have hstable : (prefixWord ++ tailWord_8327630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8327630).length < 2 ^ (prefixWord ++ tailWord_8327630).sum := by decide
  have hdescent : baseEnd_8327630 < baseStart_8327630 := by decide
  rcases family_descends (prefixWord ++ tailWord_8327630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8327647 : List Nat := [1, 1, 2, 3, 3, 2, 4, 2, 1, 1, 3]
def baseStart_8327647 : Nat := 118140960795 + 8327647 * 2 ^ 59
def prefixEnd_8327647 : Nat := 4983230072969 + 3 ^ 40 * 8327647 * 2
def baseEnd_8327647 : Nat := 4276085631972484776514355

theorem tailTrace_8327647 : CollatzResearch.WordTrace tailWord_8327647 prefixEnd_8327647 4276085631972484776514355 := by
  unfold tailWord_8327647
  simp only [CollatzResearch.WordTrace]
  refine ⟨303734238861364642721693195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202489492574243095147795463 303734238861364642721693195)
  ·
    refine ⟨455601358292046964082539793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303734238861364642721693195 455601358292046964082539793)
    ·
      refine ⟨341701018719035223061904845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 455601358292046964082539793 341701018719035223061904845)
      ·
        refine ⟨128137882019638208648214317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 341701018719035223061904845 128137882019638208648214317)
        ·
          refine ⟨48051705757364328243080369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128137882019638208648214317 48051705757364328243080369)
          ·
            refine ⟨36038779318023246182310277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48051705757364328243080369 36038779318023246182310277)
            ·
              refine ⟨6757271122129358659183177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36038779318023246182310277 6757271122129358659183177)
              ·
                refine ⟨5067953341597018994387383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6757271122129358659183177 5067953341597018994387383)
                ·
                  refine ⟨7601930012395528491581075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5067953341597018994387383 7601930012395528491581075)
                  ·
                    refine ⟨11402895018593292737371613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7601930012395528491581075 11402895018593292737371613)
                    ·
                      refine ⟨4276085631972484776514355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11402895018593292737371613 4276085631972484776514355)
                      ·
                        rfl

theorem cell23_8327647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 4, 2, 1, 1, 3].length) (baseStart_8327647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8327647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8327647 prefixEnd_8327647 := by exact prefixLift 8327647
  have htrace : WordTrace (prefixWord ++ tailWord_8327647) baseStart_8327647 baseEnd_8327647 := by
    simpa [prefixWord, tailWord_8327647, baseEnd_8327647] using wordTrace_append hprefix tailTrace_8327647
  have hstable : (prefixWord ++ tailWord_8327647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8327647).length < 2 ^ (prefixWord ++ tailWord_8327647).sum := by decide
  have hdescent : baseEnd_8327647 < baseStart_8327647 := by decide
  rcases family_descends (prefixWord ++ tailWord_8327647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8327687 : List Nat := [1, 1, 4, 3, 3, 2, 2, 1, 1, 1, 4]
def baseStart_8327687 : Nat := 118140960795 + 8327687 * 2 ^ 59
def prefixEnd_8327687 : Nat := 4983230072969 + 3 ^ 40 * 8327687 * 2
def baseEnd_8327687 : Nat := 4276106171198664620014171

theorem tailTrace_8327687 : CollatzResearch.WordTrace tailWord_8327687 prefixEnd_8327687 4276106171198664620014171 := by
  unfold tailWord_8327687
  simp only [CollatzResearch.WordTrace]
  refine ⟨303735697781219729553149315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202490465187479819702099543 303735697781219729553149315)
  ·
    refine ⟨455603546671829594329723973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303735697781219729553149315 455603546671829594329723973)
    ·
      refine ⟨85425665000968048936823245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 455603546671829594329723973 85425665000968048936823245)
      ·
        refine ⟨32034624375363018351308717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85425665000968048936823245 32034624375363018351308717)
        ·
          refine ⟨12012984140761131881740769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32034624375363018351308717 12012984140761131881740769)
          ·
            refine ⟨9009738105570848911305577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12012984140761131881740769 9009738105570848911305577)
            ·
              refine ⟨6757303579178136683479183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9009738105570848911305577 6757303579178136683479183)
              ·
                refine ⟨10135955368767205025218775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6757303579178136683479183 10135955368767205025218775)
                ·
                  refine ⟨15203933053150807537828163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10135955368767205025218775 15203933053150807537828163)
                  ·
                    refine ⟨22805899579726211306742245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15203933053150807537828163 22805899579726211306742245)
                    ·
                      refine ⟨4276106171198664620014171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22805899579726211306742245 4276106171198664620014171)
                      ·
                        rfl

theorem cell23_8327687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 2, 1, 1, 1, 4].length) (baseStart_8327687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8327687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8327687 prefixEnd_8327687 := by exact prefixLift 8327687
  have htrace : WordTrace (prefixWord ++ tailWord_8327687) baseStart_8327687 baseEnd_8327687 := by
    simpa [prefixWord, tailWord_8327687, baseEnd_8327687] using wordTrace_append hprefix tailTrace_8327687
  have hstable : (prefixWord ++ tailWord_8327687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8327687).length < 2 ^ (prefixWord ++ tailWord_8327687).sum := by decide
  have hdescent : baseEnd_8327687 < baseStart_8327687 := by decide
  rcases family_descends (prefixWord ++ tailWord_8327687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8327689 : List Nat := [1, 2, 1, 1, 3, 1, 2, 2, 1, 9]
def baseStart_8327689 : Nat := 118140960795 + 8327689 * 2 ^ 59
def prefixEnd_8327689 : Nat := 4983230072969 + 3 ^ 40 * 8327689 * 2
def baseEnd_8327689 : Nat := 1425369066053324537396387

theorem tailTrace_8327689 : CollatzResearch.WordTrace tailWord_8327689 prefixEnd_8327689 1425369066053324537396387 := by
  unfold tailWord_8327689
  simp only [CollatzResearch.WordTrace]
  refine ⟨303735770727212483894722121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202490513818141655929814747 303735770727212483894722121)
  ·
    refine ⟨227801828045409362921041591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303735770727212483894722121 227801828045409362921041591)
    ·
      refine ⟨341702742068114044381562387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227801828045409362921041591 341702742068114044381562387)
      ·
        refine ⟨512554113102171066572343581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341702742068114044381562387 512554113102171066572343581)
        ·
          refine ⟨192207792413314149964628843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 512554113102171066572343581 192207792413314149964628843)
          ·
            refine ⟨288311688619971224946943265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192207792413314149964628843 288311688619971224946943265)
            ·
              refine ⟨216233766464978418710207449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 288311688619971224946943265 216233766464978418710207449)
              ·
                refine ⟨162175324848733814032655587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 216233766464978418710207449 162175324848733814032655587)
                ·
                  refine ⟨243262987273100721048983381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 162175324848733814032655587 243262987273100721048983381)
                  ·
                    refine ⟨1425369066053324537396387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 243262987273100721048983381 1425369066053324537396387)
                    ·
                      rfl

theorem cell23_8327689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 9].length) (baseStart_8327689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8327689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8327689 prefixEnd_8327689 := by exact prefixLift 8327689
  have htrace : WordTrace (prefixWord ++ tailWord_8327689) baseStart_8327689 baseEnd_8327689 := by
    simpa [prefixWord, tailWord_8327689, baseEnd_8327689] using wordTrace_append hprefix tailTrace_8327689
  have hstable : (prefixWord ++ tailWord_8327689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8327689).length < 2 ^ (prefixWord ++ tailWord_8327689).sum := by decide
  have hdescent : baseEnd_8327689 < baseStart_8327689 := by decide
  rcases family_descends (prefixWord ++ tailWord_8327689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8327720 : List Nat := [2, 1, 5, 2, 1, 1, 3, 1, 1, 3, 3]
def baseStart_8327720 : Nat := 118140960795 + 8327720 * 2 ^ 59
def prefixEnd_8327720 : Nat := 4983230072969 + 3 ^ 40 * 8327720 * 2
def baseEnd_8327720 : Nat := 4276123116060262990901519

theorem tailTrace_8327720 : CollatzResearch.WordTrace tailWord_8327720 prefixEnd_8327720 4276123116060262990901519 := by
  unfold tailWord_8327720
  simp only [CollatzResearch.WordTrace]
  refine ⟨151868450695050088094550307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202491267593400117459400409 151868450695050088094550307)
  ·
    refine ⟨227802676042575132141825461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151868450695050088094550307 227802676042575132141825461)
    ·
      refine ⟨21356500878991418638296137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 227802676042575132141825461 21356500878991418638296137)
      ·
        refine ⟨16017375659243563978722103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21356500878991418638296137 16017375659243563978722103)
        ·
          refine ⟨24026063488865345968083155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16017375659243563978722103 24026063488865345968083155)
          ·
            refine ⟨36039095233298018952124733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24026063488865345968083155 36039095233298018952124733)
            ·
              refine ⟨13514660712486757107046775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36039095233298018952124733 13514660712486757107046775)
              ·
                refine ⟨20271991068730135660570163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13514660712486757107046775 20271991068730135660570163)
                ·
                  refine ⟨30407986603095203490855245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20271991068730135660570163 30407986603095203490855245)
                  ·
                    refine ⟨11402994976160701309070717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30407986603095203490855245 11402994976160701309070717)
                    ·
                      refine ⟨4276123116060262990901519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11402994976160701309070717 4276123116060262990901519)
                      ·
                        rfl

theorem cell23_8327720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_8327720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8327720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8327720 prefixEnd_8327720 := by exact prefixLift 8327720
  have htrace : WordTrace (prefixWord ++ tailWord_8327720) baseStart_8327720 baseEnd_8327720 := by
    simpa [prefixWord, tailWord_8327720, baseEnd_8327720] using wordTrace_append hprefix tailTrace_8327720
  have hstable : (prefixWord ++ tailWord_8327720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8327720).length < 2 ^ (prefixWord ++ tailWord_8327720).sum := by decide
  have hdescent : baseEnd_8327720 < baseStart_8327720 := by decide
  rcases family_descends (prefixWord ++ tailWord_8327720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8327730 : List Nat := [3, 2, 1, 1, 2, 1, 3, 4, 1, 3, 2]
def baseStart_8327730 : Nat := 118140960795 + 8327730 * 2 ^ 59
def prefixEnd_8327730 : Nat := 4983230072969 + 3 ^ 40 * 8327730 * 2
def baseEnd_8327730 : Nat := 4276128250866807951776473

theorem tailTrace_8327730 : CollatzResearch.WordTrace tailWord_8327730 prefixEnd_8327730 4276128250866807951776473 := by
  unfold tailWord_8327730
  simp only [CollatzResearch.WordTrace]
  refine ⟨75934316530015986974241161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202491510746709298597976429 75934316530015986974241161)
  ·
    refine ⟨56950737397511990230680871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75934316530015986974241161 56950737397511990230680871)
    ·
      refine ⟨85426106096267985346021307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56950737397511990230680871 85426106096267985346021307)
      ·
        refine ⟨128139159144401978019031961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85426106096267985346021307 128139159144401978019031961)
        ·
          refine ⟨96104369358301483514273971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128139159144401978019031961 96104369358301483514273971)
          ·
            refine ⟨144156554037452225271410957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96104369358301483514273971 144156554037452225271410957)
            ·
              refine ⟨54058707764044584476779109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144156554037452225271410957 54058707764044584476779109)
              ·
                refine ⟨10136007705758359589396083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54058707764044584476779109 10136007705758359589396083)
                ·
                  refine ⟨15204011558637539384094125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10136007705758359589396083 15204011558637539384094125)
                  ·
                    refine ⟨5701504334489077269035297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15204011558637539384094125 5701504334489077269035297)
                    ·
                      refine ⟨4276128250866807951776473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5701504334489077269035297 4276128250866807951776473)
                      ·
                        rfl

theorem cell23_8327730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 4, 1, 3, 2].length) (baseStart_8327730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8327730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8327730 prefixEnd_8327730 := by exact prefixLift 8327730
  have htrace : WordTrace (prefixWord ++ tailWord_8327730) baseStart_8327730 baseEnd_8327730 := by
    simpa [prefixWord, tailWord_8327730, baseEnd_8327730] using wordTrace_append hprefix tailTrace_8327730
  have hstable : (prefixWord ++ tailWord_8327730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8327730).length < 2 ^ (prefixWord ++ tailWord_8327730).sum := by decide
  have hdescent : baseEnd_8327730 < baseStart_8327730 := by decide
  rcases family_descends (prefixWord ++ tailWord_8327730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8327743 : List Nat := [1, 1, 2, 2, 3, 2, 2, 1, 3, 4, 2]
def baseStart_8327743 : Nat := 118140960795 + 8327743 * 2 ^ 59
def prefixEnd_8327743 : Nat := 4983230072969 + 3 ^ 40 * 8327743 * 2
def baseEnd_8327743 : Nat := 4276134926115316400913913

theorem tailTrace_8327743 : CollatzResearch.WordTrace tailWord_8327743 prefixEnd_8327743 4276134926115316400913913 := by
  unfold tailWord_8327743
  simp only [CollatzResearch.WordTrace]
  refine ⟨303737740269016851117187883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202491826846011234078125255 303737740269016851117187883)
  ·
    refine ⟨455606610403525276675781825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303737740269016851117187883 455606610403525276675781825)
    ·
      refine ⟨341704957802643957506836369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 455606610403525276675781825 341704957802643957506836369)
      ·
        refine ⟨256278718351982968130127277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 341704957802643957506836369 256278718351982968130127277)
        ·
          refine ⟨96104519381993613048797729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 256278718351982968130127277 96104519381993613048797729)
          ·
            refine ⟨72078389536495209786598297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96104519381993613048797729 72078389536495209786598297)
            ·
              refine ⟨54058792152371407339948723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72078389536495209786598297 54058792152371407339948723)
              ·
                refine ⟨81088188228557111009923085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54058792152371407339948723 81088188228557111009923085)
                ·
                  refine ⟨30408070585708916628721157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81088188228557111009923085 30408070585708916628721157)
                  ·
                    refine ⟨5701513234820421867885217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30408070585708916628721157 5701513234820421867885217)
                    ·
                      refine ⟨4276134926115316400913913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5701513234820421867885217 4276134926115316400913913)
                      ·
                        rfl

theorem cell23_8327743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 1, 3, 4, 2].length) (baseStart_8327743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8327743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8327743 prefixEnd_8327743 := by exact prefixLift 8327743
  have htrace : WordTrace (prefixWord ++ tailWord_8327743) baseStart_8327743 baseEnd_8327743 := by
    simpa [prefixWord, tailWord_8327743, baseEnd_8327743] using wordTrace_append hprefix tailTrace_8327743
  have hstable : (prefixWord ++ tailWord_8327743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8327743).length < 2 ^ (prefixWord ++ tailWord_8327743).sum := by decide
  have hdescent : baseEnd_8327743 < baseStart_8327743 := by decide
  rcases family_descends (prefixWord ++ tailWord_8327743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8327777 : List Nat := [1, 2, 3, 1, 1, 5, 1, 3, 2, 2, 2]
def baseStart_8327777 : Nat := 118140960795 + 8327777 * 2 ^ 59
def prefixEnd_8327777 : Nat := 4983230072969 + 3 ^ 40 * 8327777 * 2
def baseEnd_8327777 : Nat := 4276152384457569267888757

theorem tailTrace_8327777 : CollatzResearch.WordTrace tailWord_8327777 prefixEnd_8327777 4276152384457569267888757 := by
  unfold tailWord_8327777
  simp only [CollatzResearch.WordTrace]
  refine ⟨303738980350893674923925585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202492653567262449949283723 303738980350893674923925585)
  ·
    refine ⟨227804235263170256192944189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303738980350893674923925585 227804235263170256192944189)
    ·
      refine ⟨85426588223688846072354071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227804235263170256192944189 85426588223688846072354071)
      ·
        refine ⟨128139882335533269108531107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85426588223688846072354071 128139882335533269108531107)
        ·
          refine ⟨192209823503299903662796661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128139882335533269108531107 192209823503299903662796661)
          ·
            refine ⟨18019670953434365968387187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 192209823503299903662796661 18019670953434365968387187)
            ·
              refine ⟨27029506430151548952580781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18019670953434365968387187 27029506430151548952580781)
              ·
                refine ⟨10136064911306830857217793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27029506430151548952580781 10136064911306830857217793)
                ·
                  refine ⟨7602048683480123142913345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10136064911306830857217793 7602048683480123142913345)
                  ·
                    refine ⟨5701536512610092357185009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7602048683480123142913345 5701536512610092357185009)
                    ·
                      refine ⟨4276152384457569267888757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5701536512610092357185009 4276152384457569267888757)
                      ·
                        rfl

theorem cell23_8327777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 3, 2, 2, 2].length) (baseStart_8327777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8327777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8327777 prefixEnd_8327777 := by exact prefixLift 8327777
  have htrace : WordTrace (prefixWord ++ tailWord_8327777) baseStart_8327777 baseEnd_8327777 := by
    simpa [prefixWord, tailWord_8327777, baseEnd_8327777] using wordTrace_append hprefix tailTrace_8327777
  have hstable : (prefixWord ++ tailWord_8327777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8327777).length < 2 ^ (prefixWord ++ tailWord_8327777).sum := by decide
  have hdescent : baseEnd_8327777 < baseStart_8327777 := by decide
  rcases family_descends (prefixWord ++ tailWord_8327777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8327813 : List Nat := [1, 3, 1, 1, 4, 2, 2, 2, 2, 5]
def baseStart_8327813 : Nat := 118140960795 + 8327813 * 2 ^ 59
def prefixEnd_8327813 : Nat := 4983230072969 + 3 ^ 40 * 8327813 * 2
def baseEnd_8327813 : Nat := 1425390289920377042346197

theorem tailTrace_8327813 : CollatzResearch.WordTrace tailWord_8327813 prefixEnd_8327813 1425390289920377042346197 := by
  unfold tailWord_8327813
  simp only [CollatzResearch.WordTrace]
  refine ⟨303740293378763253072236093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202493528919175502048157395 303740293378763253072236093)
  ·
    refine ⟨113902610017036219902088535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 303740293378763253072236093 113902610017036219902088535)
    ·
      refine ⟨170853915025554329853132803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113902610017036219902088535 170853915025554329853132803)
      ·
        refine ⟨256280872538331494779699205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170853915025554329853132803 256280872538331494779699205)
        ·
          refine ⟨48052663600937155271193601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 256280872538331494779699205 48052663600937155271193601)
          ·
            refine ⟨36039497700702866453395201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48052663600937155271193601 36039497700702866453395201)
            ·
              refine ⟨27029623275527149840046401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36039497700702866453395201 27029623275527149840046401)
              ·
                refine ⟨20272217456645362380034801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27029623275527149840046401 20272217456645362380034801)
                ·
                  refine ⟨15204163092484021785026101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20272217456645362380034801 15204163092484021785026101)
                  ·
                    refine ⟨1425390289920377042346197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15204163092484021785026101 1425390289920377042346197)
                    ·
                      rfl

theorem cell23_8327813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 2, 2, 5].length) (baseStart_8327813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8327813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8327813 prefixEnd_8327813 := by exact prefixLift 8327813
  have htrace : WordTrace (prefixWord ++ tailWord_8327813) baseStart_8327813 baseEnd_8327813 := by
    simpa [prefixWord, tailWord_8327813, baseEnd_8327813] using wordTrace_append hprefix tailTrace_8327813
  have hstable : (prefixWord ++ tailWord_8327813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8327813).length < 2 ^ (prefixWord ++ tailWord_8327813).sum := by decide
  have hdescent : baseEnd_8327813 < baseStart_8327813 := by decide
  rcases family_descends (prefixWord ++ tailWord_8327813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8327856 : List Nat := [2, 1, 1, 1, 2, 1, 3, 4, 8]
def baseStart_8327856 : Nat := 118140960795 + 8327856 * 2 ^ 59
def prefixEnd_8327856 : Nat := 4983230072969 + 3 ^ 40 * 8327856 * 2
def baseEnd_8327856 : Nat := 475132549936586050977877

theorem tailTrace_8327856 : CollatzResearch.WordTrace tailWord_8327856 prefixEnd_8327856 475132549936586050977877 := by
  unfold tailWord_8327856
  simp only [CollatzResearch.WordTrace]
  refine ⟨151870930858803735708025711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202494574478404980944034281 151870930858803735708025711)
  ·
    refine ⟨227806396288205603562038567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151870930858803735708025711 227806396288205603562038567)
    ·
      refine ⟨341709594432308405343057851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227806396288205603562038567 341709594432308405343057851)
      ·
        refine ⟨512564391648462608014586777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341709594432308405343057851 512564391648462608014586777)
        ·
          refine ⟨384423293736346956010940083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 512564391648462608014586777 384423293736346956010940083)
          ·
            refine ⟨576634940604520434016410125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 384423293736346956010940083 576634940604520434016410125)
            ·
              refine ⟨216238102726695162756153797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 576634940604520434016410125 216238102726695162756153797)
              ·
                refine ⟨40544644261255343016778837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 216238102726695162756153797 40544644261255343016778837)
                ·
                  refine ⟨475132549936586050977877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40544644261255343016778837 475132549936586050977877)
                  ·
                    rfl

theorem cell23_8327856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 4, 8].length) (baseStart_8327856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8327856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8327856 prefixEnd_8327856 := by exact prefixLift 8327856
  have htrace : WordTrace (prefixWord ++ tailWord_8327856) baseStart_8327856 baseEnd_8327856 := by
    simpa [prefixWord, tailWord_8327856, baseEnd_8327856] using wordTrace_append hprefix tailTrace_8327856
  have hstable : (prefixWord ++ tailWord_8327856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8327856).length < 2 ^ (prefixWord ++ tailWord_8327856).sum := by decide
  have hdescent : baseEnd_8327856 < baseStart_8327856 := by decide
  rcases family_descends (prefixWord ++ tailWord_8327856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8327870 : List Nat := [4, 2, 1, 1, 2, 1, 2, 1, 4, 2, 3]
def baseStart_8327870 : Nat := 118140960795 + 8327870 * 2 ^ 59
def prefixEnd_8327870 : Nat := 4983230072969 + 3 ^ 40 * 8327870 * 2
def baseEnd_8327870 : Nat := 4276200138158437404025829

theorem tailTrace_8327870 : CollatzResearch.WordTrace tailWord_8327870 prefixEnd_8327870 4276200138158437404025829 := by
  unfold tailWord_8327870
  simp only [CollatzResearch.WordTrace]
  refine ⟨37967796542444593975882633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202494914893037834538040709 37967796542444593975882633)
  ·
    refine ⟨28475847406833445481911975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37967796542444593975882633 28475847406833445481911975)
    ·
      refine ⟨42713771110250168222867963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28475847406833445481911975 42713771110250168222867963)
      ·
        refine ⟨64070656665375252334301945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42713771110250168222867963 64070656665375252334301945)
        ·
          refine ⟨48052992499031439250726459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64070656665375252334301945 48052992499031439250726459)
          ·
            refine ⟨72079488748547158876089689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48052992499031439250726459 72079488748547158876089689)
            ·
              refine ⟨54059616561410369157067267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72079488748547158876089689 54059616561410369157067267)
              ·
                refine ⟨81089424842115553735600901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54059616561410369157067267 81089424842115553735600901)
                ·
                  refine ⟨15204267157896666325425169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81089424842115553735600901 15204267157896666325425169)
                  ·
                    refine ⟨11403200368422499744068877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15204267157896666325425169 11403200368422499744068877)
                    ·
                      refine ⟨4276200138158437404025829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11403200368422499744068877 4276200138158437404025829)
                      ·
                        rfl

theorem cell23_8327870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 1, 4, 2, 3].length) (baseStart_8327870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8327870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8327870 prefixEnd_8327870 := by exact prefixLift 8327870
  have htrace : WordTrace (prefixWord ++ tailWord_8327870) baseStart_8327870 baseEnd_8327870 := by
    simpa [prefixWord, tailWord_8327870, baseEnd_8327870] using wordTrace_append hprefix tailTrace_8327870
  have hstable : (prefixWord ++ tailWord_8327870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8327870).length < 2 ^ (prefixWord ++ tailWord_8327870).sum := by decide
  have hdescent : baseEnd_8327870 < baseStart_8327870 := by decide
  rcases family_descends (prefixWord ++ tailWord_8327870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8327923 : List Nat := [1, 1, 1, 2, 2, 3, 1, 2, 5, 1, 4]
def baseStart_8327923 : Nat := 118140960795 + 8327923 * 2 ^ 59
def prefixEnd_8327923 : Nat := 4983230072969 + 3 ^ 40 * 8327923 * 2
def baseEnd_8327923 : Nat := 4276227352633125696663085

theorem tailTrace_8327923 : CollatzResearch.WordTrace tailWord_8327923 prefixEnd_8327923 4276227352633125696663085 := by
  unfold tailWord_8327923
  simp only [CollatzResearch.WordTrace]
  refine ⟨303744305408364741858740423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202496203605576494572493615 303744305408364741858740423)
  ·
    refine ⟨455616458112547112788110635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303744305408364741858740423 455616458112547112788110635)
    ·
      refine ⟨683424687168820669182165953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 455616458112547112788110635 683424687168820669182165953)
      ·
        refine ⟨512568515376615501886624465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 683424687168820669182165953 512568515376615501886624465)
        ·
          refine ⟨384426386532461626414968349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 512568515376615501886624465 384426386532461626414968349)
          ·
            refine ⟨144159894949673109905613131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 384426386532461626414968349 144159894949673109905613131)
            ·
              refine ⟨216239842424509664858419697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144159894949673109905613131 216239842424509664858419697)
              ·
                refine ⟨162179881818382248643814773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 216239842424509664858419697 162179881818382248643814773)
                ·
                  refine ⟨15204363920473335810357635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 162179881818382248643814773 15204363920473335810357635)
                  ·
                    refine ⟨22806545880710003715536453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15204363920473335810357635 22806545880710003715536453)
                    ·
                      refine ⟨4276227352633125696663085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22806545880710003715536453 4276227352633125696663085)
                      ·
                        rfl

theorem cell23_8327923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 5, 1, 4].length) (baseStart_8327923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8327923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8327923 prefixEnd_8327923 := by exact prefixLift 8327923
  have htrace : WordTrace (prefixWord ++ tailWord_8327923) baseStart_8327923 baseEnd_8327923 := by
    simpa [prefixWord, tailWord_8327923, baseEnd_8327923] using wordTrace_append hprefix tailTrace_8327923
  have hstable : (prefixWord ++ tailWord_8327923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8327923).length < 2 ^ (prefixWord ++ tailWord_8327923).sum := by decide
  have hdescent : baseEnd_8327923 < baseStart_8327923 := by decide
  rcases family_descends (prefixWord ++ tailWord_8327923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8327934 : List Nat := [4, 2, 2, 1, 2, 1, 3, 1, 3, 1, 3]
def baseStart_8327934 : Nat := 118140960795 + 8327934 * 2 ^ 59
def prefixEnd_8327934 : Nat := 4983230072969 + 3 ^ 40 * 8327934 * 2
def baseEnd_8327934 : Nat := 4276233000920325153625535

theorem tailTrace_8327934 : CollatzResearch.WordTrace tailWord_8327934 prefixEnd_8327934 4276233000920325153625535 := by
  unfold tailWord_8327934
  simp only [CollatzResearch.WordTrace]
  refine ⟨37968088326415611342173857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202496471074216593824927237 37968088326415611342173857)
  ·
    refine ⟨28476066244811708506630393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37968088326415611342173857 28476066244811708506630393)
    ·
      refine ⟨21357049683608781379972795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28476066244811708506630393 21357049683608781379972795)
      ·
        refine ⟨32035574525413172069959193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21357049683608781379972795 32035574525413172069959193)
        ·
          refine ⟨24026680894059879052469395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32035574525413172069959193 24026680894059879052469395)
          ·
            refine ⟨36040021341089818578704093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24026680894059879052469395 36040021341089818578704093)
            ·
              refine ⟨13515008002908681967014035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36040021341089818578704093 13515008002908681967014035)
              ·
                refine ⟨20272512004363022950521053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13515008002908681967014035 20272512004363022950521053)
                ·
                  refine ⟨7602192001636133606445395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20272512004363022950521053 7602192001636133606445395)
                  ·
                    refine ⟨11403288002454200409668093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7602192001636133606445395 11403288002454200409668093)
                    ·
                      refine ⟨4276233000920325153625535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11403288002454200409668093 4276233000920325153625535)
                      ·
                        rfl

theorem cell23_8327934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 3, 1, 3, 1, 3].length) (baseStart_8327934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8327934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8327934 prefixEnd_8327934 := by exact prefixLift 8327934
  have htrace : WordTrace (prefixWord ++ tailWord_8327934) baseStart_8327934 baseEnd_8327934 := by
    simpa [prefixWord, tailWord_8327934, baseEnd_8327934] using wordTrace_append hprefix tailTrace_8327934
  have hstable : (prefixWord ++ tailWord_8327934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8327934).length < 2 ^ (prefixWord ++ tailWord_8327934).sum := by decide
  have hdescent : baseEnd_8327934 < baseStart_8327934 := by decide
  rcases family_descends (prefixWord ++ tailWord_8327934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8327940 : List Nat := [2, 3, 2, 2, 1, 1, 2, 2, 3, 1, 4]
def baseStart_8327940 : Nat := 118140960795 + 8327940 * 2 ^ 59
def prefixEnd_8327940 : Nat := 4983230072969 + 3 ^ 40 * 8327940 * 2
def baseEnd_8327940 : Nat := 4276236081804252130150507

theorem tailTrace_8327940 : CollatzResearch.WordTrace tailWord_8327940 prefixEnd_8327940 4276236081804252130150507 := by
  unfold tailWord_8327940
  simp only [CollatzResearch.WordTrace]
  refine ⟨151872462724651576881054637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202496616966202102508072849 151872462724651576881054637)
  ·
    refine ⟨56952173521744341330395489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151872462724651576881054637 56952173521744341330395489)
    ·
      refine ⟨42714130141308255997796617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56952173521744341330395489 42714130141308255997796617)
      ·
        refine ⟨32035597605981191998347463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42714130141308255997796617 32035597605981191998347463)
        ·
          refine ⟨48053396408971787997521195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32035597605981191998347463 48053396408971787997521195)
          ·
            refine ⟨72080094613457681996281793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48053396408971787997521195 72080094613457681996281793)
            ·
              refine ⟨54060070960093261497211345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72080094613457681996281793 54060070960093261497211345)
              ·
                refine ⟨40545053220069946122908509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54060070960093261497211345 40545053220069946122908509)
                ·
                  refine ⟨15204394957526229796090691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40545053220069946122908509 15204394957526229796090691)
                  ·
                    refine ⟨22806592436289344694136037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15204394957526229796090691 22806592436289344694136037)
                    ·
                      refine ⟨4276236081804252130150507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22806592436289344694136037 4276236081804252130150507)
                      ·
                        rfl

theorem cell23_8327940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_8327940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8327940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8327940 prefixEnd_8327940 := by exact prefixLift 8327940
  have htrace : WordTrace (prefixWord ++ tailWord_8327940) baseStart_8327940 baseEnd_8327940 := by
    simpa [prefixWord, tailWord_8327940, baseEnd_8327940] using wordTrace_append hprefix tailTrace_8327940
  have hstable : (prefixWord ++ tailWord_8327940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8327940).length < 2 ^ (prefixWord ++ tailWord_8327940).sum := by decide
  have hdescent : baseEnd_8327940 < baseStart_8327940 := by decide
  rcases family_descends (prefixWord ++ tailWord_8327940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8327953 : List Nat := [1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 6]
def baseStart_8327953 : Nat := 118140960795 + 8327953 * 2 ^ 59
def prefixEnd_8327953 : Nat := 4983230072969 + 3 ^ 40 * 8327953 * 2
def baseEnd_8327953 : Nat := 4276242757052760579287947

theorem tailTrace_8327953 : CollatzResearch.WordTrace tailWord_8327953 prefixEnd_8327953 4276242757052760579287947 := by
  unfold tailWord_8327953
  simp only [CollatzResearch.WordTrace]
  refine ⟨303745399598256056982332513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202496933065504037988221675 303745399598256056982332513)
  ·
    refine ⟨227809049698692042736749385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303745399598256056982332513 227809049698692042736749385)
    ·
      refine ⟨170856787274019032052562039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227809049698692042736749385 170856787274019032052562039)
      ·
        refine ⟨256285180911028548078843059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170856787274019032052562039 256285180911028548078843059)
        ·
          refine ⟨384427771366542822118264589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256285180911028548078843059 384427771366542822118264589)
          ·
            refine ⟨144160414262453558294349221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 384427771366542822118264589 144160414262453558294349221)
            ·
              refine ⟨27030077674210042180190479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 144160414262453558294349221 27030077674210042180190479)
              ·
                refine ⟨40545116511315063270285719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27030077674210042180190479 40545116511315063270285719)
                ·
                  refine ⟨60817674766972594905428579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40545116511315063270285719 60817674766972594905428579)
                  ·
                    refine ⟨91226512150458892358142869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60817674766972594905428579 91226512150458892358142869)
                    ·
                      refine ⟨4276242757052760579287947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91226512150458892358142869 4276242757052760579287947)
                      ·
                        rfl

theorem cell23_8327953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 6].length) (baseStart_8327953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8327953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8327953 prefixEnd_8327953 := by exact prefixLift 8327953
  have htrace : WordTrace (prefixWord ++ tailWord_8327953) baseStart_8327953 baseEnd_8327953 := by
    simpa [prefixWord, tailWord_8327953, baseEnd_8327953] using wordTrace_append hprefix tailTrace_8327953
  have hstable : (prefixWord ++ tailWord_8327953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8327953).length < 2 ^ (prefixWord ++ tailWord_8327953).sum := by decide
  have hdescent : baseEnd_8327953 < baseStart_8327953 := by decide
  rcases family_descends (prefixWord ++ tailWord_8327953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8327957 : List Nat := [1, 3, 2, 1, 2, 2, 2, 1, 5, 2, 2]
def baseStart_8327957 : Nat := 118140960795 + 8327957 * 2 ^ 59
def prefixEnd_8327957 : Nat := 4983230072969 + 3 ^ 40 * 8327957 * 2
def baseEnd_8327957 : Nat := 4276244810975378563637929

theorem tailTrace_8327957 : CollatzResearch.WordTrace tailWord_8327957 prefixEnd_8327957 4276244810975378563637929 := by
  unfold tailWord_8327957
  simp only [CollatzResearch.WordTrace]
  refine ⟨303745545490241565665478125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202497030326827710443652083 303745545490241565665478125)
  ·
    refine ⟨113904579558840587124554297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 303745545490241565665478125 113904579558840587124554297)
    ·
      refine ⟨85428434669130440343415723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113904579558840587124554297 85428434669130440343415723)
      ·
        refine ⟨128142652003695660515123585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85428434669130440343415723 128142652003695660515123585)
        ·
          refine ⟨96106989002771745386342689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128142652003695660515123585 96106989002771745386342689)
          ·
            refine ⟨72080241752078809039757017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96106989002771745386342689 72080241752078809039757017)
            ·
              refine ⟨54060181314059106779817763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72080241752078809039757017 54060181314059106779817763)
              ·
                refine ⟨81090271971088660169726645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54060181314059106779817763 81090271971088660169726645)
                ·
                  refine ⟨7602212997289561890911873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 81090271971088660169726645 7602212997289561890911873)
                  ·
                    refine ⟨5701659747967171418183905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7602212997289561890911873 5701659747967171418183905)
                    ·
                      refine ⟨4276244810975378563637929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5701659747967171418183905 4276244810975378563637929)
                      ·
                        rfl

theorem cell23_8327957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 1, 5, 2, 2].length) (baseStart_8327957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8327957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8327957 prefixEnd_8327957 := by exact prefixLift 8327957
  have htrace : WordTrace (prefixWord ++ tailWord_8327957) baseStart_8327957 baseEnd_8327957 := by
    simpa [prefixWord, tailWord_8327957, baseEnd_8327957] using wordTrace_append hprefix tailTrace_8327957
  have hstable : (prefixWord ++ tailWord_8327957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8327957).length < 2 ^ (prefixWord ++ tailWord_8327957).sum := by decide
  have hdescent : baseEnd_8327957 < baseStart_8327957 := by decide
  rcases family_descends (prefixWord ++ tailWord_8327957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8327970 : List Nat := [3, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4]
def baseStart_8327970 : Nat := 118140960795 + 8327970 * 2 ^ 59
def prefixEnd_8327970 : Nat := 4983230072969 + 3 ^ 40 * 8327970 * 2
def baseEnd_8327970 : Nat := 4276251486223887012775369

theorem tailTrace_8327970 : CollatzResearch.WordTrace tailWord_8327970 prefixEnd_8327970 4276251486223887012775369 := by
  unfold tailWord_8327970
  simp only [CollatzResearch.WordTrace]
  refine ⟨75936504909798617221425341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202497346426129645923800909 75936504909798617221425341)
  ·
    refine ⟨28476189341174481458034503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75936504909798617221425341 28476189341174481458034503)
    ·
      refine ⟨42714284011761722187051755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28476189341174481458034503 42714284011761722187051755)
      ·
        refine ⟨64071426017642583280577633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42714284011761722187051755 64071426017642583280577633)
        ·
          refine ⟨48053569513231937460433225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64071426017642583280577633 48053569513231937460433225)
          ·
            refine ⟨36040177134923953095324919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48053569513231937460433225 36040177134923953095324919)
            ·
              refine ⟨54060265702385929642987379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36040177134923953095324919 54060265702385929642987379)
              ·
                refine ⟨81090398553578894464481069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54060265702385929642987379 81090398553578894464481069)
                ·
                  refine ⟨30408899457592085424180401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81090398553578894464481069 30408899457592085424180401)
                  ·
                    refine ⟨22806674593194064068135301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30408899457592085424180401 22806674593194064068135301)
                    ·
                      refine ⟨4276251486223887012775369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22806674593194064068135301 4276251486223887012775369)
                      ·
                        rfl

theorem cell23_8327970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4].length) (baseStart_8327970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8327970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8327970 prefixEnd_8327970 := by exact prefixLift 8327970
  have htrace : WordTrace (prefixWord ++ tailWord_8327970) baseStart_8327970 baseEnd_8327970 := by
    simpa [prefixWord, tailWord_8327970, baseEnd_8327970] using wordTrace_append hprefix tailTrace_8327970
  have hstable : (prefixWord ++ tailWord_8327970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8327970).length < 2 ^ (prefixWord ++ tailWord_8327970).sum := by decide
  have hdescent : baseEnd_8327970 < baseStart_8327970 := by decide
  rcases family_descends (prefixWord ++ tailWord_8327970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8327997 : List Nat := [1, 4, 1, 4, 2, 2, 1, 8]
def baseStart_8327997 : Nat := 118140960795 + 8327997 * 2 ^ 59
def prefixEnd_8327997 : Nat := 4983230072969 + 3 ^ 40 * 8327997 * 2
def baseEnd_8327997 : Nat := 158380198155613274338435

theorem tailTrace_8327997 : CollatzResearch.WordTrace tailWord_8327997 prefixEnd_8327997 158380198155613274338435 := by
  unfold tailWord_8327997
  simp only [CollatzResearch.WordTrace]
  refine ⟨303747004410096652496934245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202498002940064434997956163 303747004410096652496934245)
  ·
    refine ⟨56952563326893122343175171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 303747004410096652496934245 56952563326893122343175171)
    ·
      refine ⟨85428844990339683514762757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56952563326893122343175171 85428844990339683514762757)
      ·
        refine ⟨16017908435688690659018017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85428844990339683514762757 16017908435688690659018017)
        ·
          refine ⟨12013431326766517994263513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16017908435688690659018017 12013431326766517994263513)
          ·
            refine ⟨9010073495074888495697635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12013431326766517994263513 9010073495074888495697635)
            ·
              refine ⟨13515110242612332743546453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9010073495074888495697635 13515110242612332743546453)
              ·
                refine ⟨158380198155613274338435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13515110242612332743546453 158380198155613274338435)
                ·
                  rfl

theorem cell23_8327997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 1, 8].length) (baseStart_8327997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8327997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8327997 prefixEnd_8327997 := by exact prefixLift 8327997
  have htrace : WordTrace (prefixWord ++ tailWord_8327997) baseStart_8327997 baseEnd_8327997 := by
    simpa [prefixWord, tailWord_8327997, baseEnd_8327997] using wordTrace_append hprefix tailTrace_8327997
  have hstable : (prefixWord ++ tailWord_8327997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8327997).length < 2 ^ (prefixWord ++ tailWord_8327997).sum := by decide
  have hdescent : baseEnd_8327997 < baseStart_8327997 := by decide
  rcases family_descends (prefixWord ++ tailWord_8327997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8328040 : List Nat := [2, 1, 4, 2, 1, 2, 1, 2, 2, 6]
def baseStart_8328040 : Nat := 118140960795 + 8328040 * 2 ^ 59
def prefixEnd_8328040 : Nat := 4983230072969 + 3 ^ 40 * 8328040 * 2
def baseEnd_8328040 : Nat := 1425429143289900579633349

theorem tailTrace_8328040 : CollatzResearch.WordTrace tailWord_8328040 prefixEnd_8328040 1425429143289900579633349 := by
  unfold tailWord_8328040
  simp only [CollatzResearch.WordTrace]
  refine ⟨151874286374470435420374787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202499048499293913893833049 151874286374470435420374787)
  ·
    refine ⟨227811429561705653130562181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151874286374470435420374787 227811429561705653130562181)
    ·
      refine ⟨42714643042819809961980409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 227811429561705653130562181 42714643042819809961980409)
      ·
        refine ⟨32035982282114857471485307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42714643042819809961980409 32035982282114857471485307)
        ·
          refine ⟨48053973423172286207227961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32035982282114857471485307 48053973423172286207227961)
          ·
            refine ⟨36040480067379214655420971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48053973423172286207227961 36040480067379214655420971)
            ·
              refine ⟨54060720101068821983131457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36040480067379214655420971 54060720101068821983131457)
              ·
                refine ⟨40545540075801616487348593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54060720101068821983131457 40545540075801616487348593)
                ·
                  refine ⟨30409155056851212365511445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40545540075801616487348593 30409155056851212365511445)
                  ·
                    refine ⟨1425429143289900579633349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30409155056851212365511445 1425429143289900579633349)
                    ·
                      rfl

theorem cell23_8328040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 2, 2, 6].length) (baseStart_8328040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8328040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8328040 prefixEnd_8328040 := by exact prefixLift 8328040
  have htrace : WordTrace (prefixWord ++ tailWord_8328040) baseStart_8328040 baseEnd_8328040 := by
    simpa [prefixWord, tailWord_8328040, baseEnd_8328040] using wordTrace_append hprefix tailTrace_8328040
  have hstable : (prefixWord ++ tailWord_8328040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8328040).length < 2 ^ (prefixWord ++ tailWord_8328040).sum := by decide
  have hdescent : baseEnd_8328040 < baseStart_8328040 := by decide
  rcases family_descends (prefixWord ++ tailWord_8328040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8328050 : List Nat := [3, 2, 1, 2, 1, 1, 2, 1, 1, 6, 3]
def baseStart_8328050 : Nat := 118140960795 + 8328050 * 2 ^ 59
def prefixEnd_8328050 : Nat := 4983230072969 + 3 ^ 40 * 8328050 * 2
def baseEnd_8328050 : Nat := 4276292564676246699775001

theorem tailTrace_8328050 : CollatzResearch.WordTrace tailWord_8328050 prefixEnd_8328050 4276292564676246699775001 := by
  unfold tailWord_8328050
  simp only [CollatzResearch.WordTrace]
  refine ⟨75937234369726160637153401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202499291652603095032409069 75937234369726160637153401)
  ·
    refine ⟨56952925777294620477865051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75937234369726160637153401 56952925777294620477865051)
    ·
      refine ⟨85429388665941930716797577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56952925777294620477865051 85429388665941930716797577)
      ·
        refine ⟨64072041499456448037598183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85429388665941930716797577 64072041499456448037598183)
        ·
          refine ⟨96108062249184672056397275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64072041499456448037598183 96108062249184672056397275)
          ·
            refine ⟨144162093373777008084595913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96108062249184672056397275 144162093373777008084595913)
            ·
              refine ⟨108121570030332756063446935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144162093373777008084595913 108121570030332756063446935)
              ·
                refine ⟨162182355045499134095170403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108121570030332756063446935 162182355045499134095170403)
                ·
                  refine ⟨243273532568248701142755605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 162182355045499134095170403 243273532568248701142755605)
                  ·
                    refine ⟨11403446839136657866066669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 243273532568248701142755605 11403446839136657866066669)
                    ·
                      refine ⟨4276292564676246699775001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11403446839136657866066669 4276292564676246699775001)
                      ·
                        rfl

theorem cell23_8328050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 1, 6, 3].length) (baseStart_8328050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8328050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8328050 prefixEnd_8328050 := by exact prefixLift 8328050
  have htrace : WordTrace (prefixWord ++ tailWord_8328050) baseStart_8328050 baseEnd_8328050 := by
    simpa [prefixWord, tailWord_8328050, baseEnd_8328050] using wordTrace_append hprefix tailTrace_8328050
  have hstable : (prefixWord ++ tailWord_8328050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8328050).length < 2 ^ (prefixWord ++ tailWord_8328050).sum := by decide
  have hdescent : baseEnd_8328050 < baseStart_8328050 := by decide
  rcases family_descends (prefixWord ++ tailWord_8328050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8328177 : List Nat := [1, 2, 2, 2, 4, 1, 2, 3, 6]
def baseStart_8328177 : Nat := 118140960795 + 8328177 * 2 ^ 59
def prefixEnd_8328177 : Nat := 4983230072969 + 3 ^ 40 * 8328177 * 2
def baseEnd_8328177 : Nat := 475150864079929744765213

theorem tailTrace_8328177 : CollatzResearch.WordTrace tailWord_8328177 prefixEnd_8328177 475150864079929744765213 := by
  unfold tailWord_8328177
  simp only [CollatzResearch.WordTrace]
  refine ⟨303753569549444543238486785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202502379699629695492324523 303753569549444543238486785)
  ·
    refine ⟨227815177162083407428865089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303753569549444543238486785 227815177162083407428865089)
    ·
      refine ⟨170861382871562555571648817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227815177162083407428865089 170861382871562555571648817)
      ·
        refine ⟨128146037153671916678736613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170861382871562555571648817 128146037153671916678736613)
        ·
          refine ⟨24027381966313484377263115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128146037153671916678736613 24027381966313484377263115)
          ·
            refine ⟨36041072949470226565894673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24027381966313484377263115 36041072949470226565894673)
            ·
              refine ⟨27030804712102669924421005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36041072949470226565894673 27030804712102669924421005)
              ·
                refine ⟨10136551767038501221657877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27030804712102669924421005 10136551767038501221657877)
                ·
                  refine ⟨475150864079929744765213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10136551767038501221657877 475150864079929744765213)
                  ·
                    rfl

theorem cell23_8328177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 3, 6].length) (baseStart_8328177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8328177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8328177 prefixEnd_8328177 := by exact prefixLift 8328177
  have htrace : WordTrace (prefixWord ++ tailWord_8328177) baseStart_8328177 baseEnd_8328177 := by
    simpa [prefixWord, tailWord_8328177, baseEnd_8328177] using wordTrace_append hprefix tailTrace_8328177
  have hstable : (prefixWord ++ tailWord_8328177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8328177).length < 2 ^ (prefixWord ++ tailWord_8328177).sum := by decide
  have hdescent : baseEnd_8328177 < baseStart_8328177 := by decide
  rcases family_descends (prefixWord ++ tailWord_8328177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8328231 : List Nat := [1, 1, 7, 1, 1, 1, 1, 2, 1, 5, 2]
def baseStart_8328231 : Nat := 118140960795 + 8328231 * 2 ^ 59
def prefixEnd_8328231 : Nat := 4983230072969 + 3 ^ 40 * 8328231 * 2
def baseEnd_8328231 : Nat := 4276385504674710491611669

theorem tailTrace_8328231 : CollatzResearch.WordTrace tailWord_8328231 prefixEnd_8328231 4276385504674710491611669 := by
  unfold tailWord_8328231
  simp only [CollatzResearch.WordTrace]
  refine ⟨303755539091248910460952547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202503692727499273640635031 303755539091248910460952547)
  ·
    refine ⟨455633308636873365691428821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303755539091248910460952547 455633308636873365691428821)
    ·
      refine ⟨10678905671176719508392863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 455633308636873365691428821 10678905671176719508392863)
      ·
        refine ⟨16018358506765079262589295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10678905671176719508392863 16018358506765079262589295)
        ·
          refine ⟨24027537760147618893883943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16018358506765079262589295 24027537760147618893883943)
          ·
            refine ⟨36041306640221428340825915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24027537760147618893883943 36041306640221428340825915)
            ·
              refine ⟨54061959960332142511238873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36041306640221428340825915 54061959960332142511238873)
              ·
                refine ⟨40546469970249106883429155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54061959960332142511238873 40546469970249106883429155)
                ·
                  refine ⟨60819704955373660325143733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40546469970249106883429155 60819704955373660325143733)
                  ·
                    refine ⟨5701847339566280655482225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60819704955373660325143733 5701847339566280655482225)
                    ·
                      refine ⟨4276385504674710491611669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5701847339566280655482225 4276385504674710491611669)
                      ·
                        rfl

theorem cell23_8328231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 2, 1, 5, 2].length) (baseStart_8328231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8328231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8328231 prefixEnd_8328231 := by exact prefixLift 8328231
  have htrace : WordTrace (prefixWord ++ tailWord_8328231) baseStart_8328231 baseEnd_8328231 := by
    simpa [prefixWord, tailWord_8328231, baseEnd_8328231] using wordTrace_append hprefix tailTrace_8328231
  have hstable : (prefixWord ++ tailWord_8328231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8328231).length < 2 ^ (prefixWord ++ tailWord_8328231).sum := by decide
  have hdescent : baseEnd_8328231 < baseStart_8328231 := by decide
  rcases family_descends (prefixWord ++ tailWord_8328231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8328264 : List Nat := [2, 1, 3, 1, 1, 1, 3, 5, 1, 2, 3]
def baseStart_8328264 : Nat := 118140960795 + 8328264 * 2 ^ 59
def prefixEnd_8328264 : Nat := 4983230072969 + 3 ^ 40 * 8328264 * 2
def baseEnd_8328264 : Nat := 4276402449536308862499017

theorem tailTrace_8328264 : CollatzResearch.WordTrace tailWord_8328264 prefixEnd_8328264 4276402449536308862499017 := by
  unfold tailWord_8328264
  simp only [CollatzResearch.WordTrace]
  refine ⟨151878371350064678548451923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202504495133419571397935897 151878371350064678548451923)
  ·
    refine ⟨227817557025097017822677885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151878371350064678548451923 227817557025097017822677885)
    ·
      refine ⟨85431583884411381683504207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227817557025097017822677885 85431583884411381683504207)
      ·
        refine ⟨128147375826617072525256311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85431583884411381683504207 128147375826617072525256311)
        ·
          refine ⟨192221063739925608787884467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128147375826617072525256311 192221063739925608787884467)
          ·
            refine ⟨288331595609888413181826701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192221063739925608787884467 288331595609888413181826701)
            ·
              refine ⟨108124348353708154943185013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 288331595609888413181826701 108124348353708154943185013)
              ·
                refine ⟨10136657658160139525923595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 108124348353708154943185013 10136657658160139525923595)
                ·
                  refine ⟨15204986487240209288885393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10136657658160139525923595 15204986487240209288885393)
                  ·
                    refine ⟨11403739865430156966664045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15204986487240209288885393 11403739865430156966664045)
                    ·
                      refine ⟨4276402449536308862499017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11403739865430156966664045 4276402449536308862499017)
                      ·
                        rfl

theorem cell23_8328264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 5, 1, 2, 3].length) (baseStart_8328264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8328264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8328264 prefixEnd_8328264 := by exact prefixLift 8328264
  have htrace : WordTrace (prefixWord ++ tailWord_8328264) baseStart_8328264 baseEnd_8328264 := by
    simpa [prefixWord, tailWord_8328264, baseEnd_8328264] using wordTrace_append hprefix tailTrace_8328264
  have hstable : (prefixWord ++ tailWord_8328264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8328264).length < 2 ^ (prefixWord ++ tailWord_8328264).sum := by decide
  have hdescent : baseEnd_8328264 < baseStart_8328264 := by decide
  rcases family_descends (prefixWord ++ tailWord_8328264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8328298 : List Nat := [3, 1, 3, 2, 2, 3, 1, 2, 1, 2, 3]
def baseStart_8328298 : Nat := 118140960795 + 8328298 * 2 ^ 59
def prefixEnd_8328298 : Nat := 4983230072969 + 3 ^ 40 * 8328298 * 2
def baseEnd_8328298 : Nat := 4276419907878561729473861

theorem tailTrace_8328298 : CollatzResearch.WordTrace tailWord_8328298 prefixEnd_8328298 4276419907878561729473861 := by
  unfold tailWord_8328298
  simp only [CollatzResearch.WordTrace]
  refine ⟨75939495695501545225910387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202505321854670787269094365 75939495695501545225910387)
  ·
    refine ⟨113909243543252317838865581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75939495695501545225910387 113909243543252317838865581)
    ·
      refine ⟨42715966328719619189574593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113909243543252317838865581 42715966328719619189574593)
      ·
        refine ⟨32036974746539714392180945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42715966328719619189574593 32036974746539714392180945)
        ·
          refine ⟨24027731059904785794135709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32036974746539714392180945 24027731059904785794135709)
          ·
            refine ⟨9010399147464294672800891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24027731059904785794135709 9010399147464294672800891)
            ·
              refine ⟨13515598721196442009201337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9010399147464294672800891 13515598721196442009201337)
              ·
                refine ⟨10136699040897331506901003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13515598721196442009201337 10136699040897331506901003)
                ·
                  refine ⟨15205048561345997260351505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10136699040897331506901003 15205048561345997260351505)
                  ·
                    refine ⟨11403786421009497945263629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15205048561345997260351505 11403786421009497945263629)
                    ·
                      refine ⟨4276419907878561729473861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11403786421009497945263629 4276419907878561729473861)
                      ·
                        rfl

theorem cell23_8328298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 1, 2, 1, 2, 3].length) (baseStart_8328298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8328298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8328298 prefixEnd_8328298 := by exact prefixLift 8328298
  have htrace : WordTrace (prefixWord ++ tailWord_8328298) baseStart_8328298 baseEnd_8328298 := by
    simpa [prefixWord, tailWord_8328298, baseEnd_8328298] using wordTrace_append hprefix tailTrace_8328298
  have hstable : (prefixWord ++ tailWord_8328298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8328298).length < 2 ^ (prefixWord ++ tailWord_8328298).sum := by decide
  have hdescent : baseEnd_8328298 < baseStart_8328298 := by decide
  rcases family_descends (prefixWord ++ tailWord_8328298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8328318 : List Nat := [4, 2, 4, 1, 2, 10]
def baseStart_8328318 : Nat := 118140960795 + 8328318 * 2 ^ 59
def prefixEnd_8328318 : Nat := 4983230072969 + 3 ^ 40 * 8328318 * 2
def baseEnd_8328318 : Nat := 17598478096673463585283

theorem tailTrace_8328318 : CollatzResearch.WordTrace tailWord_8328318 prefixEnd_8328318 17598478096673463585283 := by
  unfold tailWord_8328318
  simp only [CollatzResearch.WordTrace]
  refine ⟨37969839030241715539921201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202505808161289149546246405 37969839030241715539921201)
  ·
    refine ⟨28477379272681286654940901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37969839030241715539921201 28477379272681286654940901)
    ·
      refine ⟨5339508613627741247801419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28477379272681286654940901 5339508613627741247801419)
      ·
        refine ⟨8009262920441611871702129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5339508613627741247801419 8009262920441611871702129)
        ·
          refine ⟨6006947190331208903776597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8009262920441611871702129 6006947190331208903776597)
          ·
            refine ⟨17598478096673463585283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 6006947190331208903776597 17598478096673463585283)
            ·
              rfl

theorem cell23_8328318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 10].length) (baseStart_8328318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8328318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8328318 prefixEnd_8328318 := by exact prefixLift 8328318
  have htrace : WordTrace (prefixWord ++ tailWord_8328318) baseStart_8328318 baseEnd_8328318 := by
    simpa [prefixWord, tailWord_8328318, baseEnd_8328318] using wordTrace_append hprefix tailTrace_8328318
  have hstable : (prefixWord ++ tailWord_8328318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8328318).length < 2 ^ (prefixWord ++ tailWord_8328318).sum := by decide
  have hdescent : baseEnd_8328318 < baseStart_8328318 := by decide
  rcases family_descends (prefixWord ++ tailWord_8328318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8328327 : List Nat := [1, 1, 4, 2, 1, 1, 1, 4, 2, 6]
def baseStart_8328327 : Nat := 118140960795 + 8328327 * 2 ^ 59
def prefixEnd_8328327 : Nat := 4983230072969 + 3 ^ 40 * 8328327 * 2
def baseEnd_8328327 : Nat := 1425478266272514038670409

theorem tailTrace_8328327 : CollatzResearch.WordTrace tailWord_8328327 prefixEnd_8328327 1425478266272514038670409 := by
  unfold tailWord_8328327
  simp only [CollatzResearch.WordTrace]
  refine ⟨303759040498901118856447235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202506026999267412570964823 303759040498901118856447235)
  ·
    refine ⟨455638560748351678284670853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303759040498901118856447235 455638560748351678284670853)
    ·
      refine ⟨85432230140315939678375785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 455638560748351678284670853 85432230140315939678375785)
      ·
        refine ⟨64074172605236954758781839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85432230140315939678375785 64074172605236954758781839)
        ·
          refine ⟨96111258907855432138172759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64074172605236954758781839 96111258907855432138172759)
          ·
            refine ⟨144166888361783148207259139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96111258907855432138172759 144166888361783148207259139)
            ·
              refine ⟨216250332542674722310888709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144166888361783148207259139 216250332542674722310888709)
              ·
                refine ⟨40546937351751510433291633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 216250332542674722310888709 40546937351751510433291633)
                ·
                  refine ⟨30410203013813632824968725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40546937351751510433291633 30410203013813632824968725)
                  ·
                    refine ⟨1425478266272514038670409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30410203013813632824968725 1425478266272514038670409)
                    ·
                      rfl

theorem cell23_8328327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 4, 2, 6].length) (baseStart_8328327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8328327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8328327 prefixEnd_8328327 := by exact prefixLift 8328327
  have htrace : WordTrace (prefixWord ++ tailWord_8328327) baseStart_8328327 baseEnd_8328327 := by
    simpa [prefixWord, tailWord_8328327, baseEnd_8328327] using wordTrace_append hprefix tailTrace_8328327
  have hstable : (prefixWord ++ tailWord_8328327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8328327).length < 2 ^ (prefixWord ++ tailWord_8328327).sum := by decide
  have hdescent : baseEnd_8328327 < baseStart_8328327 := by decide
  rcases family_descends (prefixWord ++ tailWord_8328327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8328334 : List Nat := [4, 1, 1, 3, 2, 1, 1, 1, 2, 3, 4]
def baseStart_8328334 : Nat := 118140960795 + 8328334 * 2 ^ 59
def prefixEnd_8328334 : Nat := 4983230072969 + 3 ^ 40 * 8328334 * 2
def baseEnd_8328334 : Nat := 4276438393182123588623695

theorem tailTrace_8328334 : CollatzResearch.WordTrace tailWord_8328334 prefixEnd_8328334 4276438393182123588623695 := by
  unfold tailWord_8328334
  simp only [CollatzResearch.WordTrace]
  refine ⟨37969911976234469881494007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202506197206583839367968037 37969911976234469881494007)
  ·
    refine ⟨56954867964351704822241011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37969911976234469881494007 56954867964351704822241011)
    ·
      refine ⟨85432301946527557233361517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56954867964351704822241011 85432301946527557233361517)
      ·
        refine ⟨32037113229947833962510569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85432301946527557233361517 32037113229947833962510569)
        ·
          refine ⟨24027834922460875471882927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32037113229947833962510569 24027834922460875471882927)
          ·
            refine ⟨36041752383691313207824391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24027834922460875471882927 36041752383691313207824391)
            ·
              refine ⟨54062628575536969811736587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36041752383691313207824391 54062628575536969811736587)
              ·
                refine ⟨81093942863305454717604881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54062628575536969811736587 81093942863305454717604881)
                ·
                  refine ⟨60820457147479091038203661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81093942863305454717604881 60820457147479091038203661)
                  ·
                    refine ⟨22807671430304659139326373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60820457147479091038203661 22807671430304659139326373)
                    ·
                      refine ⟨4276438393182123588623695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22807671430304659139326373 4276438393182123588623695)
                      ·
                        rfl

theorem cell23_8328334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_8328334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8328334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8328334 prefixEnd_8328334 := by exact prefixLift 8328334
  have htrace : WordTrace (prefixWord ++ tailWord_8328334) baseStart_8328334 baseEnd_8328334 := by
    simpa [prefixWord, tailWord_8328334, baseEnd_8328334] using wordTrace_append hprefix tailTrace_8328334
  have hstable : (prefixWord ++ tailWord_8328334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8328334).length < 2 ^ (prefixWord ++ tailWord_8328334).sum := by decide
  have hdescent : baseEnd_8328334 < baseStart_8328334 := by decide
  rcases family_descends (prefixWord ++ tailWord_8328334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8328344 : List Nat := [2, 1, 2, 4, 2, 2, 1, 1, 2, 6]
def baseStart_8328344 : Nat := 118140960795 + 8328344 * 2 ^ 59
def prefixEnd_8328344 : Nat := 4983230072969 + 3 ^ 40 * 8328344 * 2
def baseEnd_8328344 : Nat := 1425481175996222849832883

theorem tailTrace_8328344 : CollatzResearch.WordTrace tailWord_8328344 prefixEnd_8328344 1425481175996222849832883 := by
  unfold tailWord_8328344
  simp only [CollatzResearch.WordTrace]
  refine ⟨151879830269919765379908043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202506440359893020506544057 151879830269919765379908043)
  ·
    refine ⟨227819745404879648069862065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151879830269919765379908043 227819745404879648069862065)
    ·
      refine ⟨170864809053659736052396549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227819745404879648069862065 170864809053659736052396549)
      ·
        refine ⟨32037151697561200509824353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 170864809053659736052396549 32037151697561200509824353)
        ·
          refine ⟨24027863773170900382368265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32037151697561200509824353 24027863773170900382368265)
          ·
            refine ⟨18020897829878175286776199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24027863773170900382368265 18020897829878175286776199)
            ·
              refine ⟨27031346744817262930164299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18020897829878175286776199 27031346744817262930164299)
              ·
                refine ⟨40547020117225894395246449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27031346744817262930164299 40547020117225894395246449)
                ·
                  refine ⟨30410265087919420796434837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40547020117225894395246449 30410265087919420796434837)
                  ·
                    refine ⟨1425481175996222849832883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30410265087919420796434837 1425481175996222849832883)
                    ·
                      rfl

theorem cell23_8328344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 1, 2, 6].length) (baseStart_8328344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8328344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8328344 prefixEnd_8328344 := by exact prefixLift 8328344
  have htrace : WordTrace (prefixWord ++ tailWord_8328344) baseStart_8328344 baseEnd_8328344 := by
    simpa [prefixWord, tailWord_8328344, baseEnd_8328344] using wordTrace_append hprefix tailTrace_8328344
  have hstable : (prefixWord ++ tailWord_8328344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8328344).length < 2 ^ (prefixWord ++ tailWord_8328344).sum := by decide
  have hdescent : baseEnd_8328344 < baseStart_8328344 := by decide
  rcases family_descends (prefixWord ++ tailWord_8328344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8328357 : List Nat := [1, 3, 1, 2, 1, 4, 1, 1, 9]
def baseStart_8328357 : Nat := 118140960795 + 8328357 * 2 ^ 59
def prefixEnd_8328357 : Nat := 4983230072969 + 3 ^ 40 * 8328357 * 2
def baseEnd_8328357 : Nat := 475161133693019666515121

theorem tailTrace_8328357 : CollatzResearch.WordTrace tailWord_8328357 prefixEnd_8328357 475161133693019666515121 := by
  unfold tailWord_8328357
  simp only [CollatzResearch.WordTrace]
  refine ⟨303760134688792433980039325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202506756459194955986692883 303760134688792433980039325)
  ·
    refine ⟨113910050508297162742514747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 303760134688792433980039325 113910050508297162742514747)
    ·
      refine ⟨170865075762445744113772121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113910050508297162742514747 170865075762445744113772121)
      ·
        refine ⟨128148806821834308085329091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170865075762445744113772121 128148806821834308085329091)
        ·
          refine ⟨192223210232751462127993637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128148806821834308085329091 192223210232751462127993637)
          ·
            refine ⟨36041851918640899148998807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 192223210232751462127993637 36041851918640899148998807)
            ·
              refine ⟨54062777877961348723498211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36041851918640899148998807 54062777877961348723498211)
              ·
                refine ⟨81094166816942023085247317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54062777877961348723498211 81094166816942023085247317)
                ·
                  refine ⟨475161133693019666515121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 81094166816942023085247317 475161133693019666515121)
                  ·
                    rfl

theorem cell23_8328357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 1, 9].length) (baseStart_8328357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8328357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8328357 prefixEnd_8328357 := by exact prefixLift 8328357
  have htrace : WordTrace (prefixWord ++ tailWord_8328357) baseStart_8328357 baseEnd_8328357 := by
    simpa [prefixWord, tailWord_8328357, baseEnd_8328357] using wordTrace_append hprefix tailTrace_8328357
  have hstable : (prefixWord ++ tailWord_8328357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8328357).length < 2 ^ (prefixWord ++ tailWord_8328357).sum := by decide
  have hdescent : baseEnd_8328357 < baseStart_8328357 := by decide
  rcases family_descends (prefixWord ++ tailWord_8328357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8328385 : List Nat := [1, 2, 6, 1, 1, 2, 1, 1, 4, 2, 2]
def baseStart_8328385 : Nat := 118140960795 + 8328385 * 2 ^ 59
def prefixEnd_8328385 : Nat := 4983230072969 + 3 ^ 40 * 8328385 * 2
def baseEnd_8328385 : Nat := 4276464580695502889085961

theorem tailTrace_8328385 : CollatzResearch.WordTrace tailWord_8328385 prefixEnd_8328385 4276464580695502889085961 := by
  unfold tailWord_8328385
  simp only [CollatzResearch.WordTrace]
  refine ⟨303761155932690994762058609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202507437288460663174705739 303761155932690994762058609)
  ·
    refine ⟨227820866949518246071543957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303761155932690994762058609 227820866949518246071543957)
    ·
      refine ⟨10679103138258667784603623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 227820866949518246071543957 10679103138258667784603623)
      ·
        refine ⟨16018654707388001676905435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10679103138258667784603623 16018654707388001676905435)
        ·
          refine ⟨24027982061082002515358153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16018654707388001676905435 24027982061082002515358153)
          ·
            refine ⟨18020986545811501886518615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24027982061082002515358153 18020986545811501886518615)
            ·
              refine ⟨27031479818717252829777923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18020986545811501886518615 27031479818717252829777923)
              ·
                refine ⟨40547219728075879244666885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27031479818717252829777923 40547219728075879244666885)
                ·
                  refine ⟨7602603699014227358375041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40547219728075879244666885 7602603699014227358375041)
                  ·
                    refine ⟨5701952774260670518781281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7602603699014227358375041 5701952774260670518781281)
                    ·
                      refine ⟨4276464580695502889085961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5701952774260670518781281 4276464580695502889085961)
                      ·
                        rfl

theorem cell23_8328385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 1, 4, 2, 2].length) (baseStart_8328385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8328385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8328385 prefixEnd_8328385 := by exact prefixLift 8328385
  have htrace : WordTrace (prefixWord ++ tailWord_8328385) baseStart_8328385 baseEnd_8328385 := by
    simpa [prefixWord, tailWord_8328385, baseEnd_8328385] using wordTrace_append hprefix tailTrace_8328385
  have hstable : (prefixWord ++ tailWord_8328385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8328385).length < 2 ^ (prefixWord ++ tailWord_8328385).sum := by decide
  have hdescent : baseEnd_8328385 < baseStart_8328385 := by decide
  rcases family_descends (prefixWord ++ tailWord_8328385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
