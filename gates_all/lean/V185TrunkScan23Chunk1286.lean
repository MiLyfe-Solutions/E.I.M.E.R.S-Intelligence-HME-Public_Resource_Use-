import V185TrunkScan23Chunk1285

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7617217 : List Nat := [1, 2, 6, 2, 1, 1, 1, 1, 4, 4]
def baseStart_7617217 : Nat := 118140960795 + 7617217 * 2 ^ 59
def prefixEnd_7617217 : Nat := 4983230072969 + 3 ^ 40 * 7617217 * 2
def baseEnd_7617217 : Nat := 1303764523532943112385521

theorem tailTrace_7617217 : CollatzResearch.WordTrace tailWord_7617217 prefixEnd_7617217 1303764523532943112385521 := by
  unfold tailWord_7617217
  simp only [CollatzResearch.WordTrace]
  refine ⟨277822728045131200937409905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185215152030087467291606603 277822728045131200937409905)
  ·
    refine ⟨208367046033848400703057429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277822728045131200937409905 208367046033848400703057429)
    ·
      refine ⟨9767205282836643782955817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 208367046033848400703057429 9767205282836643782955817)
      ·
        refine ⟨7325403962127482837216863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9767205282836643782955817 7325403962127482837216863)
        ·
          refine ⟨10988105943191224255825295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7325403962127482837216863 10988105943191224255825295)
          ·
            refine ⟨16482158914786836383737943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10988105943191224255825295 16482158914786836383737943)
            ·
              refine ⟨24723238372180254575606915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16482158914786836383737943 24723238372180254575606915)
              ·
                refine ⟨37084857558270381863410373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24723238372180254575606915 37084857558270381863410373)
                ·
                  refine ⟨6953410792175696599389445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37084857558270381863410373 6953410792175696599389445)
                  ·
                    refine ⟨1303764523532943112385521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6953410792175696599389445 1303764523532943112385521)
                    ·
                      rfl

theorem cell23_7617217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_7617217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7617217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7617217 prefixEnd_7617217 := by exact prefixLift 7617217
  have htrace : WordTrace (prefixWord ++ tailWord_7617217) baseStart_7617217 baseEnd_7617217 := by
    simpa [prefixWord, tailWord_7617217, baseEnd_7617217] using wordTrace_append hprefix tailTrace_7617217
  have hstable : (prefixWord ++ tailWord_7617217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7617217).length < 2 ^ (prefixWord ++ tailWord_7617217).sum := by decide
  have hdescent : baseEnd_7617217 < baseStart_7617217 := by decide
  rcases family_descends (prefixWord ++ tailWord_7617217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7617237 : List Nat := [1, 3, 2, 5, 1, 2, 1, 1, 1, 2, 4]
def baseStart_7617237 : Nat := 118140960795 + 7617237 * 2 ^ 59
def prefixEnd_7617237 : Nat := 4983230072969 + 3 ^ 40 * 7617237 * 2
def baseEnd_7617237 : Nat := 3911303840211919258906471

theorem tailTrace_7617237 : CollatzResearch.WordTrace tailWord_7617237 prefixEnd_7617237 3911303840211919258906471 := by
  unfold tailWord_7617237
  simp only [CollatzResearch.WordTrace]
  refine ⟨277823457505058744353137965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185215638336705829568758643 277823457505058744353137965)
  ·
    refine ⟨104183796564397029132426737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 277823457505058744353137965 104183796564397029132426737)
    ·
      refine ⟨78137847423297771849320053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104183796564397029132426737 78137847423297771849320053)
      ·
        refine ⟨7325423195934166110873755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 78137847423297771849320053 7325423195934166110873755)
        ·
          refine ⟨10988134793901249166310633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7325423195934166110873755 10988134793901249166310633)
          ·
            refine ⟨8241101095425936874732975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10988134793901249166310633 8241101095425936874732975)
            ·
              refine ⟨12361651643138905312099463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8241101095425936874732975 12361651643138905312099463)
              ·
                refine ⟨18542477464708357968149195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12361651643138905312099463 18542477464708357968149195)
                ·
                  refine ⟨27813716197062536952223793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18542477464708357968149195 27813716197062536952223793)
                  ·
                    refine ⟨20860287147796902714167845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27813716197062536952223793 20860287147796902714167845)
                    ·
                      refine ⟨3911303840211919258906471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20860287147796902714167845 3911303840211919258906471)
                      ·
                        rfl

theorem cell23_7617237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_7617237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7617237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7617237 prefixEnd_7617237 := by exact prefixLift 7617237
  have htrace : WordTrace (prefixWord ++ tailWord_7617237) baseStart_7617237 baseEnd_7617237 := by
    simpa [prefixWord, tailWord_7617237, baseEnd_7617237] using wordTrace_append hprefix tailTrace_7617237
  have hstable : (prefixWord ++ tailWord_7617237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7617237).length < 2 ^ (prefixWord ++ tailWord_7617237).sum := by decide
  have hdescent : baseEnd_7617237 < baseStart_7617237 := by decide
  rcases family_descends (prefixWord ++ tailWord_7617237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7617240 : List Nat := [2, 1, 2, 2, 3, 4, 1, 1, 1, 3, 3]
def baseStart_7617240 : Nat := 118140960795 + 7617240 * 2 ^ 59
def prefixEnd_7617240 : Nat := 4983230072969 + 3 ^ 40 * 7617240 * 2
def baseEnd_7617240 : Nat := 3911305380653882747168957

theorem tailTrace_7617240 : CollatzResearch.WordTrace tailWord_7617240 prefixEnd_7617240 3911305380653882747168957 := by
  unfold tailWord_7617240
  simp only [CollatzResearch.WordTrace]
  refine ⟨138911783462023937932748587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185215711282698583910331449 138911783462023937932748587)
  ·
    refine ⟨208367675193035906899122881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138911783462023937932748587 208367675193035906899122881)
    ·
      refine ⟨156275756394776930174342161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208367675193035906899122881 156275756394776930174342161)
      ·
        refine ⟨117206817296082697630756621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156275756394776930174342161 117206817296082697630756621)
        ·
          refine ⟨43952556486031011611533733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117206817296082697630756621 43952556486031011611533733)
          ·
            refine ⟨8241104341130814677162575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43952556486031011611533733 8241104341130814677162575)
            ·
              refine ⟨12361656511696222015743863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8241104341130814677162575 12361656511696222015743863)
              ·
                refine ⟨18542484767544333023615795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12361656511696222015743863 18542484767544333023615795)
                ·
                  refine ⟨27813727151316499535423693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18542484767544333023615795 27813727151316499535423693)
                  ·
                    refine ⟨10430147681743687325783885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27813727151316499535423693 10430147681743687325783885)
                    ·
                      refine ⟨3911305380653882747168957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10430147681743687325783885 3911305380653882747168957)
                      ·
                        rfl

theorem cell23_7617240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 1, 1, 1, 3, 3].length) (baseStart_7617240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7617240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7617240 prefixEnd_7617240 := by exact prefixLift 7617240
  have htrace : WordTrace (prefixWord ++ tailWord_7617240) baseStart_7617240 baseEnd_7617240 := by
    simpa [prefixWord, tailWord_7617240, baseEnd_7617240] using wordTrace_append hprefix tailTrace_7617240
  have hstable : (prefixWord ++ tailWord_7617240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7617240).length < 2 ^ (prefixWord ++ tailWord_7617240).sum := by decide
  have hdescent : baseEnd_7617240 < baseStart_7617240 := by decide
  rcases family_descends (prefixWord ++ tailWord_7617240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7617320 : List Nat := [2, 1, 5, 1, 1, 1, 2, 5, 5]
def baseStart_7617320 : Nat := 118140960795 + 7617320 * 2 ^ 59
def prefixEnd_7617320 : Nat := 4983230072969 + 3 ^ 40 * 7617320 * 2
def baseEnd_7617320 : Nat := 434594051011804714907621

theorem tailTrace_7617320 : CollatzResearch.WordTrace tailWord_7617320 prefixEnd_7617320 434594051011804714907621 := by
  unfold tailWord_7617320
  simp only [CollatzResearch.WordTrace]
  refine ⟨138913242381879024764204707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185217656509172033018939609 138913242381879024764204707)
  ·
    refine ⟨208369863572818537146307061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138913242381879024764204707 208369863572818537146307061)
    ·
      refine ⟨19534674709951737857466287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 208369863572818537146307061 19534674709951737857466287)
      ·
        refine ⟨29302012064927606786199431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19534674709951737857466287 29302012064927606786199431)
        ·
          refine ⟨43953018097391410179299147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29302012064927606786199431 43953018097391410179299147)
          ·
            refine ⟨65929527146087115268948721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43953018097391410179299147 65929527146087115268948721)
            ·
              refine ⟨49447145359565336451711541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65929527146087115268948721 49447145359565336451711541)
              ·
                refine ⟨4635669877459250292347957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49447145359565336451711541 4635669877459250292347957)
                ·
                  refine ⟨434594051011804714907621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4635669877459250292347957 434594051011804714907621)
                  ·
                    rfl

theorem cell23_7617320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 5, 5].length) (baseStart_7617320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7617320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7617320 prefixEnd_7617320 := by exact prefixLift 7617320
  have htrace : WordTrace (prefixWord ++ tailWord_7617320) baseStart_7617320 baseEnd_7617320 := by
    simpa [prefixWord, tailWord_7617320, baseEnd_7617320] using wordTrace_append hprefix tailTrace_7617320
  have hstable : (prefixWord ++ tailWord_7617320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7617320).length < 2 ^ (prefixWord ++ tailWord_7617320).sum := by decide
  have hdescent : baseEnd_7617320 < baseStart_7617320 := by decide
  rcases family_descends (prefixWord ++ tailWord_7617320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7617323 : List Nat := [1, 1, 1, 1, 2, 1, 2, 4, 1, 7, 2]
def baseStart_7617323 : Nat := 118140960795 + 7617323 * 2 ^ 59
def prefixEnd_7617323 : Nat := 4983230072969 + 3 ^ 40 * 7617323 * 2
def baseEnd_7617323 : Nat := 3911347999548205922431075

theorem tailTrace_7617323 : CollatzResearch.WordTrace tailWord_7617323 prefixEnd_7617323 3911347999548205922431075 := by
  unfold tailWord_7617323
  simp only [CollatzResearch.WordTrace]
  refine ⟨277826594182747181040768623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185217729455164787360512415 277826594182747181040768623)
  ·
    refine ⟨416739891274120771561152935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277826594182747181040768623 416739891274120771561152935)
    ·
      refine ⟨625109836911181157341729403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 416739891274120771561152935 625109836911181157341729403)
      ·
        refine ⟨937664755366771736012594105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 625109836911181157341729403 937664755366771736012594105)
        ·
          refine ⟨703248566525078802009445579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 937664755366771736012594105 703248566525078802009445579)
          ·
            refine ⟨1054872849787618203014168369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 703248566525078802009445579 1054872849787618203014168369)
            ·
              refine ⟨791154637340713652260626277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1054872849787618203014168369 791154637340713652260626277)
              ·
                refine ⟨148341494501383809798867427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 791154637340713652260626277 148341494501383809798867427)
                ·
                  refine ⟨222512241752075714698301141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 148341494501383809798867427 222512241752075714698301141)
                  ·
                    refine ⟨5215130666064274563241433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 222512241752075714698301141 5215130666064274563241433)
                    ·
                      refine ⟨3911347999548205922431075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5215130666064274563241433 3911347999548205922431075)
                      ·
                        rfl

theorem cell23_7617323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 7, 2].length) (baseStart_7617323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7617323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7617323 prefixEnd_7617323 := by exact prefixLift 7617323
  have htrace : WordTrace (prefixWord ++ tailWord_7617323) baseStart_7617323 baseEnd_7617323 := by
    simpa [prefixWord, tailWord_7617323, baseEnd_7617323] using wordTrace_append hprefix tailTrace_7617323
  have hstable : (prefixWord ++ tailWord_7617323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7617323).length < 2 ^ (prefixWord ++ tailWord_7617323).sum := by decide
  have hdescent : baseEnd_7617323 < baseStart_7617323 := by decide
  rcases family_descends (prefixWord ++ tailWord_7617323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7617343 : List Nat := [1, 1, 2, 2, 5, 1, 2, 1, 1, 2, 5]
def baseStart_7617343 : Nat := 118140960795 + 7617343 * 2 ^ 59
def prefixEnd_7617343 : Nat := 4983230072969 + 3 ^ 40 * 7617343 * 2
def baseEnd_7617343 : Nat := 3911358269161295844180983

theorem tailTrace_7617343 : CollatzResearch.WordTrace tailWord_7617343 prefixEnd_7617343 3911358269161295844180983 := by
  unfold tailWord_7617343
  simp only [CollatzResearch.WordTrace]
  refine ⟨277827323642674724456496683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185218215761783149637664455 277827323642674724456496683)
  ·
    refine ⟨416740985464012086684745025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277827323642674724456496683 416740985464012086684745025)
    ·
      refine ⟨312555739098009065013558769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 416740985464012086684745025 312555739098009065013558769)
      ·
        refine ⟨234416804323506798760169077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 312555739098009065013558769 234416804323506798760169077)
        ·
          refine ⟨21976575405328762383765851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 234416804323506798760169077 21976575405328762383765851)
          ·
            refine ⟨32964863107993143575648777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21976575405328762383765851 32964863107993143575648777)
            ·
              refine ⟨24723647330994857681736583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32964863107993143575648777 24723647330994857681736583)
              ·
                refine ⟨37085470996492286522604875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24723647330994857681736583 37085470996492286522604875)
                ·
                  refine ⟨55628206494738429783907313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37085470996492286522604875 55628206494738429783907313)
                  ·
                    refine ⟨41721154871053822337930485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55628206494738429783907313 41721154871053822337930485)
                    ·
                      refine ⟨3911358269161295844180983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41721154871053822337930485 3911358269161295844180983)
                      ·
                        rfl

theorem cell23_7617343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 1, 1, 2, 5].length) (baseStart_7617343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7617343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7617343 prefixEnd_7617343 := by exact prefixLift 7617343
  have htrace : WordTrace (prefixWord ++ tailWord_7617343) baseStart_7617343 baseEnd_7617343 := by
    simpa [prefixWord, tailWord_7617343, baseEnd_7617343] using wordTrace_append hprefix tailTrace_7617343
  have hstable : (prefixWord ++ tailWord_7617343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7617343).length < 2 ^ (prefixWord ++ tailWord_7617343).sum := by decide
  have hdescent : baseEnd_7617343 < baseStart_7617343 := by decide
  rcases family_descends (prefixWord ++ tailWord_7617343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7617370 : List Nat := [3, 1, 1, 2, 1, 4, 3, 1, 2, 1, 4]
def baseStart_7617370 : Nat := 118140960795 + 7617370 * 2 ^ 59
def prefixEnd_7617370 : Nat := 4983230072969 + 3 ^ 40 * 7617370 * 2
def baseEnd_7617370 : Nat := 3911372133138967238543359

theorem tailTrace_7617370 : CollatzResearch.WordTrace tailWord_7617370 prefixEnd_7617370 3911372133138967238543359 := by
  unfold tailWord_7617370
  simp only [CollatzResearch.WordTrace]
  refine ⟨69457077103394227016932391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185218872275717938711819709 69457077103394227016932391)
  ·
    refine ⟨104185615655091340525398587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69457077103394227016932391 104185615655091340525398587)
    ·
      refine ⟨156278423482637010788097881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104185615655091340525398587 156278423482637010788097881)
      ·
        refine ⟨117208817611977758091073411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156278423482637010788097881 117208817611977758091073411)
        ·
          refine ⟨175813226417966637136610117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117208817611977758091073411 175813226417966637136610117)
          ·
            refine ⟨32964979953368744463114397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 175813226417966637136610117 32964979953368744463114397)
            ·
              refine ⟨12361867482513279173667899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32964979953368744463114397 12361867482513279173667899)
              ·
                refine ⟨18542801223769918760501849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12361867482513279173667899 18542801223769918760501849)
                ·
                  refine ⟨13907100917827439070376387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18542801223769918760501849 13907100917827439070376387)
                  ·
                    refine ⟨20860651376741158605564581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13907100917827439070376387 20860651376741158605564581)
                    ·
                      refine ⟨3911372133138967238543359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20860651376741158605564581 3911372133138967238543359)
                      ·
                        rfl

theorem cell23_7617370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 3, 1, 2, 1, 4].length) (baseStart_7617370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7617370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7617370 prefixEnd_7617370 := by exact prefixLift 7617370
  have htrace : WordTrace (prefixWord ++ tailWord_7617370) baseStart_7617370 baseEnd_7617370 := by
    simpa [prefixWord, tailWord_7617370, baseEnd_7617370] using wordTrace_append hprefix tailTrace_7617370
  have hstable : (prefixWord ++ tailWord_7617370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7617370).length < 2 ^ (prefixWord ++ tailWord_7617370).sum := by decide
  have hdescent : baseEnd_7617370 < baseStart_7617370 := by decide
  rcases family_descends (prefixWord ++ tailWord_7617370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7617383 : List Nat := [1, 1, 5, 1, 2, 2, 1, 1, 2, 1, 6]
def baseStart_7617383 : Nat := 118140960795 + 7617383 * 2 ^ 59
def prefixEnd_7617383 : Nat := 4983230072969 + 3 ^ 40 * 7617383 * 2
def baseEnd_7617383 : Nat := 3911378808387475687680799

theorem tailTrace_7617383 : CollatzResearch.WordTrace tailWord_7617383 prefixEnd_7617383 3911378808387475687680799 := by
  unfold tailWord_7617383
  simp only [CollatzResearch.WordTrace]
  refine ⟨277828782562529811287952803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185219188375019874191968535 277828782562529811287952803)
  ·
    refine ⟨416743173843794716931929205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277828782562529811287952803 416743173843794716931929205)
    ·
      refine ⟨39069672547855754712368363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 416743173843794716931929205 39069672547855754712368363)
      ·
        refine ⟨58604508821783632068552545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39069672547855754712368363 58604508821783632068552545)
        ·
          refine ⟨43953381616337724051414409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58604508821783632068552545 43953381616337724051414409)
          ·
            refine ⟨32965036212253293038560807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43953381616337724051414409 32965036212253293038560807)
            ·
              refine ⟨49447554318379939557841211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32965036212253293038560807 49447554318379939557841211)
              ·
                refine ⟨74171331477569909336761817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49447554318379939557841211 74171331477569909336761817)
                ·
                  refine ⟨55628498608177432002571363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74171331477569909336761817 55628498608177432002571363)
                  ·
                    refine ⟨83442747912266148003857045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55628498608177432002571363 83442747912266148003857045)
                    ·
                      refine ⟨3911378808387475687680799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83442747912266148003857045 3911378808387475687680799)
                      ·
                        rfl

theorem cell23_7617383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 1, 2, 1, 6].length) (baseStart_7617383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7617383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7617383 prefixEnd_7617383 := by exact prefixLift 7617383
  have htrace : WordTrace (prefixWord ++ tailWord_7617383) baseStart_7617383 baseEnd_7617383 := by
    simpa [prefixWord, tailWord_7617383, baseEnd_7617383] using wordTrace_append hprefix tailTrace_7617383
  have hstable : (prefixWord ++ tailWord_7617383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7617383).length < 2 ^ (prefixWord ++ tailWord_7617383).sum := by decide
  have hdescent : baseEnd_7617383 < baseStart_7617383 := by decide
  rcases family_descends (prefixWord ++ tailWord_7617383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7617393 : List Nat := [1, 2, 2, 2, 1, 5, 1, 1, 8]
def baseStart_7617393 : Nat := 118140960795 + 7617393 * 2 ^ 59
def prefixEnd_7617393 : Nat := 4983230072969 + 3 ^ 40 * 7617393 * 2
def baseEnd_7617393 : Nat := 434598215910446738728417

theorem tailTrace_7617393 : CollatzResearch.WordTrace tailWord_7617393 prefixEnd_7617393 434598215910446738728417 := by
  unfold tailWord_7617393
  simp only [CollatzResearch.WordTrace]
  refine ⟨277829147292493582995816833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185219431528329055330544555 277829147292493582995816833)
  ·
    refine ⟨208371860469370187246862625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277829147292493582995816833 208371860469370187246862625)
    ·
      refine ⟨156278895352027640435146969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208371860469370187246862625 156278895352027640435146969)
      ·
        refine ⟨117209171514020730326360227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156278895352027640435146969 117209171514020730326360227)
        ·
          refine ⟨175813757271031095489540341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117209171514020730326360227 175813757271031095489540341)
          ·
            refine ⟨16482539744159165202144407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 175813757271031095489540341 16482539744159165202144407)
            ·
              refine ⟨24723809616238747803216611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16482539744159165202144407 24723809616238747803216611)
              ·
                refine ⟨37085714424358121704824917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24723809616238747803216611 37085714424358121704824917)
                ·
                  refine ⟨434598215910446738728417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37085714424358121704824917 434598215910446738728417)
                  ·
                    rfl

theorem cell23_7617393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 1, 8].length) (baseStart_7617393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7617393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7617393 prefixEnd_7617393 := by exact prefixLift 7617393
  have htrace : WordTrace (prefixWord ++ tailWord_7617393) baseStart_7617393 baseEnd_7617393 := by
    simpa [prefixWord, tailWord_7617393, baseEnd_7617393] using wordTrace_append hprefix tailTrace_7617393
  have hstable : (prefixWord ++ tailWord_7617393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7617393).length < 2 ^ (prefixWord ++ tailWord_7617393).sum := by decide
  have hdescent : baseEnd_7617393 < baseStart_7617393 := by decide
  rcases family_descends (prefixWord ++ tailWord_7617393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7617397 : List Nat := [1, 3, 4, 1, 1, 3, 2, 1, 3, 4]
def baseStart_7617397 : Nat := 118140960795 + 7617397 * 2 ^ 59
def prefixEnd_7617397 : Nat := 4983230072969 + 3 ^ 40 * 7617397 * 2
def baseEnd_7617397 : Nat := 1303795332372212877635245

theorem tailTrace_7617397 : CollatzResearch.WordTrace tailWord_7617397 prefixEnd_7617397 1303795332372212877635245 := by
  unfold tailWord_7617397
  simp only [CollatzResearch.WordTrace]
  refine ⟨277829293184479091678962445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185219528789652727785974963 277829293184479091678962445)
  ·
    refine ⟨104185984944179659379610917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 277829293184479091678962445 104185984944179659379610917)
    ·
      refine ⟨19534872177033686133677047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104185984944179659379610917 19534872177033686133677047)
      ·
        refine ⟨29302308265550529200515571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19534872177033686133677047 29302308265550529200515571)
        ·
          refine ⟨43953462398325793800773357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29302308265550529200515571 43953462398325793800773357)
          ·
            refine ⟨16482548399372172675290009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43953462398325793800773357 16482548399372172675290009)
            ·
              refine ⟨12361911299529129506467507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16482548399372172675290009 12361911299529129506467507)
              ·
                refine ⟨18542866949293694259701261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12361911299529129506467507 18542866949293694259701261)
                ·
                  refine ⟨6953575105985135347387973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18542866949293694259701261 6953575105985135347387973)
                  ·
                    refine ⟨1303795332372212877635245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6953575105985135347387973 1303795332372212877635245)
                    ·
                      rfl

theorem cell23_7617397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 2, 1, 3, 4].length) (baseStart_7617397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7617397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7617397 prefixEnd_7617397 := by exact prefixLift 7617397
  have htrace : WordTrace (prefixWord ++ tailWord_7617397) baseStart_7617397 baseEnd_7617397 := by
    simpa [prefixWord, tailWord_7617397, baseEnd_7617397] using wordTrace_append hprefix tailTrace_7617397
  have hstable : (prefixWord ++ tailWord_7617397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7617397).length < 2 ^ (prefixWord ++ tailWord_7617397).sum := by decide
  have hdescent : baseEnd_7617397 < baseStart_7617397 := by decide
  rcases family_descends (prefixWord ++ tailWord_7617397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7617440 : List Nat := [2, 1, 1, 4, 1, 1, 4, 3, 1, 5]
def baseStart_7617440 : Nat := 118140960795 + 7617440 * 2 ^ 59
def prefixEnd_7617440 : Nat := 4983230072969 + 3 ^ 40 * 7617440 * 2
def baseEnd_7617440 : Nat := 1303802692261593988222679

theorem tailTrace_7617440 : CollatzResearch.WordTrace tailWord_7617440 prefixEnd_7617440 1303802692261593988222679 := by
  unfold tailWord_7617440
  simp only [CollatzResearch.WordTrace]
  refine ⟨138915430761661655011388887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185220574348882206681851849 138915430761661655011388887)
  ·
    refine ⟨208373146142492482517083331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138915430761661655011388887 208373146142492482517083331)
    ·
      refine ⟨312559719213738723775624997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208373146142492482517083331 312559719213738723775624997)
      ·
        refine ⟨58604947352576010707929687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 312559719213738723775624997 58604947352576010707929687)
        ·
          refine ⟨87907421028864016061894531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58604947352576010707929687 87907421028864016061894531)
          ·
            refine ⟨131861131543296024092841797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87907421028864016061894531 131861131543296024092841797)
            ·
              refine ⟨24723962164368004517407837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 131861131543296024092841797 24723962164368004517407837)
              ·
                refine ⟨9271485811638001694027939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24723962164368004517407837 9271485811638001694027939)
                ·
                  refine ⟨13907228717457002541041909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9271485811638001694027939 13907228717457002541041909)
                  ·
                    refine ⟨1303802692261593988222679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13907228717457002541041909 1303802692261593988222679)
                    ·
                      rfl

theorem cell23_7617440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 3, 1, 5].length) (baseStart_7617440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7617440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7617440 prefixEnd_7617440 := by exact prefixLift 7617440
  have htrace : WordTrace (prefixWord ++ tailWord_7617440) baseStart_7617440 baseEnd_7617440 := by
    simpa [prefixWord, tailWord_7617440, baseEnd_7617440] using wordTrace_append hprefix tailTrace_7617440
  have hstable : (prefixWord ++ tailWord_7617440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7617440).length < 2 ^ (prefixWord ++ tailWord_7617440).sum := by decide
  have hdescent : baseEnd_7617440 < baseStart_7617440 := by decide
  rcases family_descends (prefixWord ++ tailWord_7617440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7617470 : List Nat := [4, 2, 1, 1, 1, 2, 2, 3, 1, 6]
def baseStart_7617470 : Nat := 118140960795 + 7617470 * 2 ^ 59
def prefixEnd_7617470 : Nat := 4983230072969 + 3 ^ 40 * 7617470 * 2
def baseEnd_7617470 : Nat := 1303807827068138949097633

theorem tailTrace_7617470 : CollatzResearch.WordTrace tailWord_7617470 prefixEnd_7617470 1303807827068138949097633 := by
  unfold tailWord_7617470
  simp only [CollatzResearch.WordTrace]
  refine ⟨34728994464151828143296233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185221303808809750097579909 34728994464151828143296233)
  ·
    refine ⟨26046745848113871107472175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34728994464151828143296233 26046745848113871107472175)
    ·
      refine ⟨39070118772170806661208263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26046745848113871107472175 39070118772170806661208263)
      ·
        refine ⟨58605178158256209991812395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39070118772170806661208263 58605178158256209991812395)
        ·
          refine ⟨87907767237384314987718593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58605178158256209991812395 87907767237384314987718593)
          ·
            refine ⟨65930825428038236240788945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87907767237384314987718593 65930825428038236240788945)
            ·
              refine ⟨49448119071028677180591709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65930825428038236240788945 49448119071028677180591709)
              ·
                refine ⟨18543044651635753942721891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49448119071028677180591709 18543044651635753942721891)
                ·
                  refine ⟨27814566977453630914082837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18543044651635753942721891 27814566977453630914082837)
                  ·
                    refine ⟨1303807827068138949097633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27814566977453630914082837 1303807827068138949097633)
                    ·
                      rfl

theorem cell23_7617470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 3, 1, 6].length) (baseStart_7617470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7617470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7617470 prefixEnd_7617470 := by exact prefixLift 7617470
  have htrace : WordTrace (prefixWord ++ tailWord_7617470) baseStart_7617470 baseEnd_7617470 := by
    simpa [prefixWord, tailWord_7617470, baseEnd_7617470] using wordTrace_append hprefix tailTrace_7617470
  have hstable : (prefixWord ++ tailWord_7617470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7617470).length < 2 ^ (prefixWord ++ tailWord_7617470).sum := by decide
  have hdescent : baseEnd_7617470 < baseStart_7617470 := by decide
  rcases family_descends (prefixWord ++ tailWord_7617470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7617483 : List Nat := [1, 1, 1, 1, 3, 5, 2, 9]
def baseStart_7617483 : Nat := 118140960795 + 7617483 * 2 ^ 59
def prefixEnd_7617483 : Nat := 4983230072969 + 3 ^ 40 * 7617483 * 2
def baseEnd_7617483 : Nat := 144867783572330566534457

theorem tailTrace_7617483 : CollatzResearch.WordTrace tailWord_7617483 prefixEnd_7617483 144867783572330566534457 := by
  unfold tailWord_7617483
  simp only [CollatzResearch.WordTrace]
  refine ⟨277832429862167528366593103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185221619908111685577728735 277832429862167528366593103)
  ·
    refine ⟨416748644793251292549889655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277832429862167528366593103 416748644793251292549889655)
    ·
      refine ⟨625122967189876938824834483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 416748644793251292549889655 625122967189876938824834483)
      ·
        refine ⟨937684450784815408237251725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 625122967189876938824834483 937684450784815408237251725)
        ·
          refine ⟨351631669044305778088969397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 937684450784815408237251725 351631669044305778088969397)
          ·
            refine ⟨32965468972903666695840881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 351631669044305778088969397 32965468972903666695840881)
            ·
              refine ⟨24724101729677750021880661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32965468972903666695840881 24724101729677750021880661)
              ·
                refine ⟨144867783572330566534457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24724101729677750021880661 144867783572330566534457)
                ·
                  rfl

theorem cell23_7617483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 9].length) (baseStart_7617483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7617483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7617483 prefixEnd_7617483 := by exact prefixLift 7617483
  have htrace : WordTrace (prefixWord ++ tailWord_7617483) baseStart_7617483 baseEnd_7617483 := by
    simpa [prefixWord, tailWord_7617483, baseEnd_7617483] using wordTrace_append hprefix tailTrace_7617483
  have hstable : (prefixWord ++ tailWord_7617483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7617483).length < 2 ^ (prefixWord ++ tailWord_7617483).sum := by decide
  have hdescent : baseEnd_7617483 < baseStart_7617483 := by decide
  rcases family_descends (prefixWord ++ tailWord_7617483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7617497 : List Nat := [1, 2, 1, 2, 5, 3, 1, 1, 1, 1, 5]
def baseStart_7617497 : Nat := 118140960795 + 7617497 * 2 ^ 59
def prefixEnd_7617497 : Nat := 4983230072969 + 3 ^ 40 * 7617497 * 2
def baseEnd_7617497 : Nat := 3911437345182088241655275

theorem tailTrace_7617497 : CollatzResearch.WordTrace tailWord_7617497 prefixEnd_7617497 3911437345182088241655275 := by
  unfold tailWord_7617497
  simp only [CollatzResearch.WordTrace]
  refine ⟨277832940484116808757602745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185221960322744539171735163 277832940484116808757602745)
  ·
    refine ⟨208374705363087606568202059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277832940484116808757602745 208374705363087606568202059)
    ·
      refine ⟨312562058044631409852303089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208374705363087606568202059 312562058044631409852303089)
      ·
        refine ⟨234421543533473557389227317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 312562058044631409852303089 234421543533473557389227317)
        ·
          refine ⟨21977019706263146005240061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 234421543533473557389227317 21977019706263146005240061)
          ·
            refine ⟨8241382389848679751965023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21977019706263146005240061 8241382389848679751965023)
            ·
              refine ⟨12362073584773019627947535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8241382389848679751965023 12362073584773019627947535)
              ·
                refine ⟨18543110377159529441921303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12362073584773019627947535 18543110377159529441921303)
                ·
                  refine ⟨27814665565739294162881955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18543110377159529441921303 27814665565739294162881955)
                  ·
                    refine ⟨41721998348608941244322933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27814665565739294162881955 41721998348608941244322933)
                    ·
                      refine ⟨3911437345182088241655275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41721998348608941244322933 3911437345182088241655275)
                      ·
                        rfl

theorem cell23_7617497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 1, 1, 1, 1, 5].length) (baseStart_7617497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7617497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7617497 prefixEnd_7617497 := by exact prefixLift 7617497
  have htrace : WordTrace (prefixWord ++ tailWord_7617497) baseStart_7617497 baseEnd_7617497 := by
    simpa [prefixWord, tailWord_7617497, baseEnd_7617497] using wordTrace_append hprefix tailTrace_7617497
  have hstable : (prefixWord ++ tailWord_7617497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7617497).length < 2 ^ (prefixWord ++ tailWord_7617497).sum := by decide
  have hdescent : baseEnd_7617497 < baseStart_7617497 := by decide
  rcases family_descends (prefixWord ++ tailWord_7617497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7617500 : List Nat := [2, 2, 6, 13]
def baseStart_7617500 : Nat := 118140960795 + 7617500 * 2 ^ 59
def prefixEnd_7617500 : Nat := 4983230072969 + 3 ^ 40 * 7617500 * 2
def baseEnd_7617500 : Nat := 1788495146604504677603

theorem tailTrace_7617500 : CollatzResearch.WordTrace tailWord_7617500 prefixEnd_7617500 1788495146604504677603 := by
  unfold tailWord_7617500
  simp only [CollatzResearch.WordTrace]
  refine ⟨138916524951552970134980977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185222033268737293513307969 138916524951552970134980977)
  ·
    refine ⟨104187393713664727601235733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138916524951552970134980977 104187393713664727601235733)
    ·
      refine ⟨4883784080328034106307925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 104187393713664727601235733 4883784080328034106307925)
      ·
        refine ⟨1788495146604504677603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 13 4883784080328034106307925 1788495146604504677603)
        ·
          rfl

theorem cell23_7617500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 13].length) (baseStart_7617500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7617500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7617500 prefixEnd_7617500 := by exact prefixLift 7617500
  have htrace : WordTrace (prefixWord ++ tailWord_7617500) baseStart_7617500 baseEnd_7617500 := by
    simpa [prefixWord, tailWord_7617500, baseEnd_7617500] using wordTrace_append hprefix tailTrace_7617500
  have hstable : (prefixWord ++ tailWord_7617500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7617500).length < 2 ^ (prefixWord ++ tailWord_7617500).sum := by decide
  have hdescent : baseEnd_7617500 < baseStart_7617500 := by decide
  rcases family_descends (prefixWord ++ tailWord_7617500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7617523 : List Nat := [1, 1, 1, 2, 2, 2, 1, 1, 3, 4, 5]
def baseStart_7617523 : Nat := 118140960795 + 7617523 * 2 ^ 59
def prefixEnd_7617523 : Nat := 4983230072969 + 3 ^ 40 * 7617523 * 2
def baseEnd_7617523 : Nat := 3911450695679105139930155

theorem tailTrace_7617523 : CollatzResearch.WordTrace tailWord_7617523 prefixEnd_7617523 3911450695679105139930155 := by
  unfold tailWord_7617523
  simp only [CollatzResearch.WordTrace]
  refine ⟨277833888782022615198049223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185222592521348410132032815 277833888782022615198049223)
  ·
    refine ⟨416750833173033922797073835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277833888782022615198049223 416750833173033922797073835)
    ·
      refine ⟨625126249759550884195610753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 416750833173033922797073835 625126249759550884195610753)
      ·
        refine ⟨468844687319663163146708065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 625126249759550884195610753 468844687319663163146708065)
        ·
          refine ⟨351633515489747372360031049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 468844687319663163146708065 351633515489747372360031049)
          ·
            refine ⟨263725136617310529270023287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 351633515489747372360031049 263725136617310529270023287)
            ·
              refine ⟨395587704925965793905034931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 263725136617310529270023287 395587704925965793905034931)
              ·
                refine ⟨593381557388948690857552397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 395587704925965793905034931 593381557388948690857552397)
                ·
                  refine ⟨222518084020855759071582149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 593381557388948690857552397 222518084020855759071582149)
                  ·
                    refine ⟨41722140753910454825921653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 222518084020855759071582149 41722140753910454825921653)
                    ·
                      refine ⟨3911450695679105139930155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41722140753910454825921653 3911450695679105139930155)
                      ·
                        rfl

theorem cell23_7617523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 4, 5].length) (baseStart_7617523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7617523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7617523 prefixEnd_7617523 := by exact prefixLift 7617523
  have htrace : WordTrace (prefixWord ++ tailWord_7617523) baseStart_7617523 baseEnd_7617523 := by
    simpa [prefixWord, tailWord_7617523, baseEnd_7617523] using wordTrace_append hprefix tailTrace_7617523
  have hstable : (prefixWord ++ tailWord_7617523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7617523).length < 2 ^ (prefixWord ++ tailWord_7617523).sum := by decide
  have hdescent : baseEnd_7617523 < baseStart_7617523 := by decide
  rcases family_descends (prefixWord ++ tailWord_7617523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7617534 : List Nat := [4, 2, 2, 2, 2, 1, 3, 7]
def baseStart_7617534 : Nat := 118140960795 + 7617534 * 2 ^ 59
def prefixEnd_7617534 : Nat := 4983230072969 + 3 ^ 40 * 7617534 * 2
def baseEnd_7617534 : Nat := 144868753480233503588615

theorem tailTrace_7617534 : CollatzResearch.WordTrace tailWord_7617534 prefixEnd_7617534 144868753480233503588615 := by
  unfold tailWord_7617534
  simp only [CollatzResearch.WordTrace]
  refine ⟨34729286248122845509587457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185222859989988509384466437 34729286248122845509587457)
  ·
    refine ⟨26046964686092134132190593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34729286248122845509587457 26046964686092134132190593)
    ·
      refine ⟨19535223514569100599142945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26046964686092134132190593 19535223514569100599142945)
      ·
        refine ⟨14651417635926825449357209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19535223514569100599142945 14651417635926825449357209)
        ·
          refine ⟨10988563226945119087017907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14651417635926825449357209 10988563226945119087017907)
          ·
            refine ⟨16482844840417678630526861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10988563226945119087017907 16482844840417678630526861)
            ·
              refine ⟨6181066815156629486447573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16482844840417678630526861 6181066815156629486447573)
              ·
                refine ⟨144868753480233503588615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6181066815156629486447573 144868753480233503588615)
                ·
                  rfl

theorem cell23_7617534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 3, 7].length) (baseStart_7617534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7617534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7617534 prefixEnd_7617534 := by exact prefixLift 7617534
  have htrace : WordTrace (prefixWord ++ tailWord_7617534) baseStart_7617534 baseEnd_7617534 := by
    simpa [prefixWord, tailWord_7617534, baseEnd_7617534] using wordTrace_append hprefix tailTrace_7617534
  have hstable : (prefixWord ++ tailWord_7617534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7617534).length < 2 ^ (prefixWord ++ tailWord_7617534).sum := by decide
  have hdescent : baseEnd_7617534 < baseStart_7617534 := by decide
  rcases family_descends (prefixWord ++ tailWord_7617534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7617560 : List Nat := [2, 1, 2, 3, 2, 2, 1, 2, 2, 6]
def baseStart_7617560 : Nat := 118140960795 + 7617560 * 2 ^ 59
def prefixEnd_7617560 : Nat := 4983230072969 + 3 ^ 40 * 7617560 * 2
def baseEnd_7617560 : Nat := 1303823231487773831722495

theorem tailTrace_7617560 : CollatzResearch.WordTrace tailWord_7617560 prefixEnd_7617560 1303823231487773831722495 := by
  unfold tailWord_7617560
  simp only [CollatzResearch.WordTrace]
  refine ⟨138917619141444285258573067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185223492188592380344764089 138917619141444285258573067)
  ·
    refine ⟨208376428712166427887859601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138917619141444285258573067 208376428712166427887859601)
    ·
      refine ⟨156282321534124820915894701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208376428712166427887859601 156282321534124820915894701)
      ·
        refine ⟨58605870575296807843460513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156282321534124820915894701 58605870575296807843460513)
        ·
          refine ⟨43954402931472605882595385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58605870575296807843460513 43954402931472605882595385)
          ·
            refine ⟨32965802198604454411946539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43954402931472605882595385 32965802198604454411946539)
            ·
              refine ⟨49448703297906681617919809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32965802198604454411946539 49448703297906681617919809)
              ·
                refine ⟨37086527473430011213439857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49448703297906681617919809 37086527473430011213439857)
                ·
                  refine ⟨27814895605072508410079893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37086527473430011213439857 27814895605072508410079893)
                  ·
                    refine ⟨1303823231487773831722495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27814895605072508410079893 1303823231487773831722495)
                    ·
                      rfl

theorem cell23_7617560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 2, 2, 6].length) (baseStart_7617560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7617560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7617560 prefixEnd_7617560 := by exact prefixLift 7617560
  have htrace : WordTrace (prefixWord ++ tailWord_7617560) baseStart_7617560 baseEnd_7617560 := by
    simpa [prefixWord, tailWord_7617560, baseEnd_7617560] using wordTrace_append hprefix tailTrace_7617560
  have hstable : (prefixWord ++ tailWord_7617560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7617560).length < 2 ^ (prefixWord ++ tailWord_7617560).sum := by decide
  have hdescent : baseEnd_7617560 < baseStart_7617560 := by decide
  rcases family_descends (prefixWord ++ tailWord_7617560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7617578 : List Nat := [3, 1, 4, 1, 3, 1, 3, 1, 2, 1, 3]
def baseStart_7617578 : Nat := 118140960795 + 7617578 * 2 ^ 59
def prefixEnd_7617578 : Nat := 4983230072969 + 3 ^ 40 * 7617578 * 2
def baseEnd_7617578 : Nat := 3911478937115102424742403

theorem tailTrace_7617578 : CollatzResearch.WordTrace tailWord_7617578 prefixEnd_7617578 3911478937115102424742403 := by
  unfold tailWord_7617578
  simp only [CollatzResearch.WordTrace]
  refine ⟨69458973699205839897825347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185223929864548906394200925 69458973699205839897825347)
  ·
    refine ⟨104188460548808759846738021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69458973699205839897825347 104188460548808759846738021)
    ·
      refine ⟨19535336352901642471263379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104188460548808759846738021 19535336352901642471263379)
      ·
        refine ⟨29303004529352463706895069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19535336352901642471263379 29303004529352463706895069)
        ·
          refine ⟨10988626698507173890085651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29303004529352463706895069 10988626698507173890085651)
          ·
            refine ⟨16482940047760760835128477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10988626698507173890085651 16482940047760760835128477)
            ·
              refine ⟨6181102517910285313173179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16482940047760760835128477 6181102517910285313173179)
              ·
                refine ⟨9271653776865427969759769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6181102517910285313173179 9271653776865427969759769)
                ·
                  refine ⟨6953740332649070977319827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9271653776865427969759769 6953740332649070977319827)
                  ·
                    refine ⟨10430610498973606465979741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6953740332649070977319827 10430610498973606465979741)
                    ·
                      refine ⟨3911478937115102424742403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10430610498973606465979741 3911478937115102424742403)
                      ·
                        rfl

theorem cell23_7617578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 3, 1, 2, 1, 3].length) (baseStart_7617578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7617578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7617578 prefixEnd_7617578 := by exact prefixLift 7617578
  have htrace : WordTrace (prefixWord ++ tailWord_7617578) baseStart_7617578 baseEnd_7617578 := by
    simpa [prefixWord, tailWord_7617578, baseEnd_7617578] using wordTrace_append hprefix tailTrace_7617578
  have hstable : (prefixWord ++ tailWord_7617578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7617578).length < 2 ^ (prefixWord ++ tailWord_7617578).sum := by decide
  have hdescent : baseEnd_7617578 < baseStart_7617578 := by decide
  rcases family_descends (prefixWord ++ tailWord_7617578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7617580 : List Nat := [2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 4]
def baseStart_7617580 : Nat := 118140960795 + 7617580 * 2 ^ 59
def prefixEnd_7617580 : Nat := 4983230072969 + 3 ^ 40 * 7617580 * 2
def baseEnd_7617580 : Nat := 3911479964076411416917393

theorem tailTrace_7617580 : CollatzResearch.WordTrace tailWord_7617580 prefixEnd_7617580 3911479964076411416917393 := by
  unfold tailWord_7617580
  simp only [CollatzResearch.WordTrace]
  refine ⟨138917983871408056966437097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185223978495210742621916129 138917983871408056966437097)
  ·
    refine ⟨104188487903556042724827823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138917983871408056966437097 104188487903556042724827823)
    ·
      refine ⟨156282731855334064087241735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104188487903556042724827823 156282731855334064087241735)
      ·
        refine ⟨234424097783001096130862603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156282731855334064087241735 234424097783001096130862603)
        ·
          refine ⟨351636146674501644196293905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234424097783001096130862603 351636146674501644196293905)
          ·
            refine ⟨263727110005876233147220429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 351636146674501644196293905 263727110005876233147220429)
            ·
              refine ⟨98897666252203587430207661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 263727110005876233147220429 98897666252203587430207661)
              ·
                refine ⟨37086624844576345286327873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98897666252203587430207661 37086624844576345286327873)
                ·
                  refine ⟨27814968633432258964745905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37086624844576345286327873 27814968633432258964745905)
                  ·
                    refine ⟨20861226475074194223559429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27814968633432258964745905 20861226475074194223559429)
                    ·
                      refine ⟨3911479964076411416917393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20861226475074194223559429 3911479964076411416917393)
                      ·
                        rfl

theorem cell23_7617580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 4].length) (baseStart_7617580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7617580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7617580 prefixEnd_7617580 := by exact prefixLift 7617580
  have htrace : WordTrace (prefixWord ++ tailWord_7617580) baseStart_7617580 baseEnd_7617580 := by
    simpa [prefixWord, tailWord_7617580, baseEnd_7617580] using wordTrace_append hprefix tailTrace_7617580
  have hstable : (prefixWord ++ tailWord_7617580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7617580).length < 2 ^ (prefixWord ++ tailWord_7617580).sum := by decide
  have hdescent : baseEnd_7617580 < baseStart_7617580 := by decide
  rcases family_descends (prefixWord ++ tailWord_7617580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7617588 : List Nat := [2, 5, 1, 2, 1, 2, 2, 2, 1, 3, 2]
def baseStart_7617588 : Nat := 118140960795 + 7617588 * 2 ^ 59
def prefixEnd_7617588 : Nat := 4983230072969 + 3 ^ 40 * 7617588 * 2
def baseEnd_7617588 : Nat := 3911484071921647385617357

theorem tailTrace_7617588 : CollatzResearch.WordTrace tailWord_7617588 prefixEnd_7617588 3911484071921647385617357 := by
  unfold tailWord_7617588
  simp only [CollatzResearch.WordTrace]
  refine ⟨138918129763393565649582709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185224173017858087532776945 138918129763393565649582709)
  ·
    refine ⟨13023574665318146779648379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 138918129763393565649582709 13023574665318146779648379)
    ·
      refine ⟨19535361997977220169472569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13023574665318146779648379 19535361997977220169472569)
      ·
        refine ⟨14651521498482915127104427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19535361997977220169472569 14651521498482915127104427)
        ·
          refine ⟨21977282247724372690656641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14651521498482915127104427 21977282247724372690656641)
          ·
            refine ⟨16482961685793279517992481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21977282247724372690656641 16482961685793279517992481)
            ·
              refine ⟨12362221264344959638494361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16482961685793279517992481 12362221264344959638494361)
              ·
                refine ⟨9271665948258719728870771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12362221264344959638494361 9271665948258719728870771)
                ·
                  refine ⟨13907498922388079593306157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9271665948258719728870771 13907498922388079593306157)
                  ·
                    refine ⟨5215312095895529847489809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13907498922388079593306157 5215312095895529847489809)
                    ·
                      refine ⟨3911484071921647385617357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5215312095895529847489809 3911484071921647385617357)
                      ·
                        rfl

theorem cell23_7617588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 2, 2, 1, 3, 2].length) (baseStart_7617588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7617588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7617588 prefixEnd_7617588 := by exact prefixLift 7617588
  have htrace : WordTrace (prefixWord ++ tailWord_7617588) baseStart_7617588 baseEnd_7617588 := by
    simpa [prefixWord, tailWord_7617588, baseEnd_7617588] using wordTrace_append hprefix tailTrace_7617588
  have hstable : (prefixWord ++ tailWord_7617588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7617588).length < 2 ^ (prefixWord ++ tailWord_7617588).sum := by decide
  have hdescent : baseEnd_7617588 < baseStart_7617588 := by decide
  rcases family_descends (prefixWord ++ tailWord_7617588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7617624 : List Nat := [2, 1, 2, 2, 1, 3, 5, 2, 5]
def baseStart_7617624 : Nat := 118140960795 + 7617624 * 2 ^ 59
def prefixEnd_7617624 : Nat := 4983230072969 + 3 ^ 40 * 7617624 * 2
def baseEnd_7617624 : Nat := 434611395247245471640799

theorem tailTrace_7617624 : CollatzResearch.WordTrace tailWord_7617624 prefixEnd_7617624 434611395247245471640799 := by
  unfold tailWord_7617624
  simp only [CollatzResearch.WordTrace]
  refine ⟨138918786277328354723737963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185225048369771139631650617 138918786277328354723737963)
  ·
    refine ⟨208378179415992532085606945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138918786277328354723737963 208378179415992532085606945)
    ·
      refine ⟨156283634561994399064205209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208378179415992532085606945 156283634561994399064205209)
      ·
        refine ⟨117212725921495799298153907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156283634561994399064205209 117212725921495799298153907)
        ·
          refine ⟨175819088882243698947230861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117212725921495799298153907 175819088882243698947230861)
          ·
            refine ⟨65932158330841387105211573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 175819088882243698947230861 65932158330841387105211573)
            ·
              refine ⟨6181139843516380041113585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65932158330841387105211573 6181139843516380041113585)
              ·
                refine ⟨4635854882637285030835189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6181139843516380041113585 4635854882637285030835189)
                ·
                  refine ⟨434611395247245471640799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4635854882637285030835189 434611395247245471640799)
                  ·
                    rfl

theorem cell23_7617624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 5, 2, 5].length) (baseStart_7617624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7617624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7617624 prefixEnd_7617624 := by exact prefixLift 7617624
  have htrace : WordTrace (prefixWord ++ tailWord_7617624) baseStart_7617624 baseEnd_7617624 := by
    simpa [prefixWord, tailWord_7617624, baseEnd_7617624] using wordTrace_append hprefix tailTrace_7617624
  have hstable : (prefixWord ++ tailWord_7617624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7617624).length < 2 ^ (prefixWord ++ tailWord_7617624).sum := by decide
  have hdescent : baseEnd_7617624 < baseStart_7617624 := by decide
  rcases family_descends (prefixWord ++ tailWord_7617624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7617654 : List Nat := [5, 1, 1, 2, 1, 1, 4, 1, 2, 5]
def baseStart_7617654 : Nat := 118140960795 + 7617654 * 2 ^ 59
def prefixEnd_7617654 : Nat := 4983230072969 + 3 ^ 40 * 7617654 * 2
def baseEnd_7617654 : Nat := 1303839320548281375797351

theorem tailTrace_7617654 : CollatzResearch.WordTrace tailWord_7617654 prefixEnd_7617654 1303839320548281375797351 := by
  unfold tailWord_7617654
  simp only [CollatzResearch.WordTrace]
  refine ⟨17364916671534251535691751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 185225777829698683047378677 17364916671534251535691751)
  ·
    refine ⟨26047375007301377303537627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17364916671534251535691751 26047375007301377303537627)
    ·
      refine ⟨39071062510952065955306441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26047375007301377303537627 39071062510952065955306441)
      ·
        refine ⟨29303296883214049466479831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39071062510952065955306441 29303296883214049466479831)
        ·
          refine ⟨43954945324821074199719747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29303296883214049466479831 43954945324821074199719747)
          ·
            refine ⟨65932417987231611299579621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43954945324821074199719747 65932417987231611299579621)
            ·
              refine ⟨12362328372605927118671179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65932417987231611299579621 12362328372605927118671179)
              ·
                refine ⟨18543492558908890678006769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12362328372605927118671179 18543492558908890678006769)
                ·
                  refine ⟨13907619419181668008505077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18543492558908890678006769 13907619419181668008505077)
                  ·
                    refine ⟨1303839320548281375797351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13907619419181668008505077 1303839320548281375797351)
                    ·
                      rfl

theorem cell23_7617654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 4, 1, 2, 5].length) (baseStart_7617654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7617654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7617654 prefixEnd_7617654 := by exact prefixLift 7617654
  have htrace : WordTrace (prefixWord ++ tailWord_7617654) baseStart_7617654 baseEnd_7617654 := by
    simpa [prefixWord, tailWord_7617654, baseEnd_7617654] using wordTrace_append hprefix tailTrace_7617654
  have hstable : (prefixWord ++ tailWord_7617654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7617654).length < 2 ^ (prefixWord ++ tailWord_7617654).sum := by decide
  have hdescent : baseEnd_7617654 < baseStart_7617654 := by decide
  rcases family_descends (prefixWord ++ tailWord_7617654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7617674 : List Nat := [3, 1, 2, 3, 1, 1, 2, 2, 2, 4, 2]
def baseStart_7617674 : Nat := 118140960795 + 7617674 * 2 ^ 59
def prefixEnd_7617674 : Nat := 4983230072969 + 3 ^ 40 * 7617674 * 2
def baseEnd_7617674 : Nat := 3911528231257934049141961

theorem tailTrace_7617674 : CollatzResearch.WordTrace tailWord_7617674 prefixEnd_7617674 3911528231257934049141961 := by
  unfold tailWord_7617674
  simp only [CollatzResearch.WordTrace]
  refine ⟨69459849051118891996699019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185226264136317045324530717 69459849051118891996699019)
  ·
    refine ⟨104189773576678337995048529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69459849051118891996699019 104189773576678337995048529)
    ·
      refine ⟨78142330182508753496286397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104189773576678337995048529 78142330182508753496286397)
      ·
        refine ⟨29303373818440782561107399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78142330182508753496286397 29303373818440782561107399)
        ·
          refine ⟨43955060727661173841661099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29303373818440782561107399 43955060727661173841661099)
          ·
            refine ⟨65932591091491760762491649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43955060727661173841661099 65932591091491760762491649)
            ·
              refine ⟨49449443318618820571868737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65932591091491760762491649 49449443318618820571868737)
              ·
                refine ⟨37087082488964115428901553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49449443318618820571868737 37087082488964115428901553)
                ·
                  refine ⟨27815311866723086571676165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37087082488964115428901553 27815311866723086571676165)
                  ·
                    refine ⟨5215370975010578732189281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27815311866723086571676165 5215370975010578732189281)
                    ·
                      refine ⟨3911528231257934049141961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5215370975010578732189281 3911528231257934049141961)
                      ·
                        rfl

theorem cell23_7617674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 2, 2, 4, 2].length) (baseStart_7617674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7617674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7617674 prefixEnd_7617674 := by exact prefixLift 7617674
  have htrace : WordTrace (prefixWord ++ tailWord_7617674) baseStart_7617674 baseEnd_7617674 := by
    simpa [prefixWord, tailWord_7617674, baseEnd_7617674] using wordTrace_append hprefix tailTrace_7617674
  have hstable : (prefixWord ++ tailWord_7617674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7617674).length < 2 ^ (prefixWord ++ tailWord_7617674).sum := by decide
  have hdescent : baseEnd_7617674 < baseStart_7617674 := by decide
  rcases family_descends (prefixWord ++ tailWord_7617674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7617697 : List Nat := [1, 2, 3, 3, 1, 1, 1, 5, 6]
def baseStart_7617697 : Nat := 118140960795 + 7617697 * 2 ^ 59
def prefixEnd_7617697 : Nat := 4983230072969 + 3 ^ 40 * 7617697 * 2
def baseEnd_7617697 : Nat := 434615560145887495461595

theorem tailTrace_7617697 : CollatzResearch.WordTrace tailWord_7617697 prefixEnd_7617697 434615560145887495461595 := by
  unfold tailWord_7617697
  simp only [CollatzResearch.WordTrace]
  refine ⟨277840235083392242914883345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185226823388928161943255563 277840235083392242914883345)
  ·
    refine ⟨208380176312544182186162509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277840235083392242914883345 208380176312544182186162509)
    ·
      refine ⟨78142566117204068319810941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208380176312544182186162509 78142566117204068319810941)
      ·
        refine ⟨29303462293951525619929103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78142566117204068319810941 29303462293951525619929103)
        ·
          refine ⟨43955193440927288429893655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29303462293951525619929103 43955193440927288429893655)
          ·
            refine ⟨65932790161390932644840483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43955193440927288429893655 65932790161390932644840483)
            ·
              refine ⟨98899185242086398967260725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65932790161390932644840483 98899185242086398967260725)
              ·
                refine ⟨9271798616445599903180693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 98899185242086398967260725 9271798616445599903180693)
                ·
                  refine ⟨434615560145887495461595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9271798616445599903180693 434615560145887495461595)
                  ·
                    rfl

theorem cell23_7617697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 5, 6].length) (baseStart_7617697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7617697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7617697 prefixEnd_7617697 := by exact prefixLift 7617697
  have htrace : WordTrace (prefixWord ++ tailWord_7617697) baseStart_7617697 baseEnd_7617697 := by
    simpa [prefixWord, tailWord_7617697, baseEnd_7617697] using wordTrace_append hprefix tailTrace_7617697
  have hstable : (prefixWord ++ tailWord_7617697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7617697).length < 2 ^ (prefixWord ++ tailWord_7617697).sum := by decide
  have hdescent : baseEnd_7617697 < baseStart_7617697 := by decide
  rcases family_descends (prefixWord ++ tailWord_7617697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7617748 : List Nat := [2, 4, 1, 4, 1, 1, 3, 1, 6]
def baseStart_7617748 : Nat := 118140960795 + 7617748 * 2 ^ 59
def prefixEnd_7617748 : Nat := 4983230072969 + 3 ^ 40 * 7617748 * 2
def baseEnd_7617748 : Nat := 434618469869596306624069

theorem tailTrace_7617748 : CollatzResearch.WordTrace tailWord_7617748 prefixEnd_7617748 434618469869596306624069 := by
  unfold tailWord_7617748
  simp only [CollatzResearch.WordTrace]
  refine ⟨138921047603103739312494949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185228063470804985749993265 138921047603103739312494949)
  ·
    refine ⟨26047696425581951121092803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138921047603103739312494949 26047696425581951121092803)
    ·
      refine ⟨39071544638372926681639205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26047696425581951121092803 39071544638372926681639205)
      ·
        refine ⟨7325914619694923752807351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39071544638372926681639205 7325914619694923752807351)
        ·
          refine ⟨10988871929542385629211027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7325914619694923752807351 10988871929542385629211027)
          ·
            refine ⟨16483307894313578443816541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10988871929542385629211027 16483307894313578443816541)
            ·
              refine ⟨6181240460367591916431203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16483307894313578443816541 6181240460367591916431203)
              ·
                refine ⟨9271860690551387874646805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6181240460367591916431203 9271860690551387874646805)
                ·
                  refine ⟨434618469869596306624069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9271860690551387874646805 434618469869596306624069)
                  ·
                    rfl

theorem cell23_7617748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 3, 1, 6].length) (baseStart_7617748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7617748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7617748 prefixEnd_7617748 := by exact prefixLift 7617748
  have htrace : WordTrace (prefixWord ++ tailWord_7617748) baseStart_7617748 baseEnd_7617748 := by
    simpa [prefixWord, tailWord_7617748, baseEnd_7617748] using wordTrace_append hprefix tailTrace_7617748
  have hstable : (prefixWord ++ tailWord_7617748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7617748).length < 2 ^ (prefixWord ++ tailWord_7617748).sum := by decide
  have hdescent : baseEnd_7617748 < baseStart_7617748 := by decide
  rcases family_descends (prefixWord ++ tailWord_7617748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7617764 : List Nat := [2, 3, 1, 1, 1, 2, 3, 4, 1, 1, 4]
def baseStart_7617764 : Nat := 118140960795 + 7617764 * 2 ^ 59
def prefixEnd_7617764 : Nat := 4983230072969 + 3 ^ 40 * 7617764 * 2
def baseEnd_7617764 : Nat := 3911574444516838697016547

theorem tailTrace_7617764 : CollatzResearch.WordTrace tailWord_7617764 prefixEnd_7617764 3911574444516838697016547 := by
  unfold tailWord_7617764
  simp only [CollatzResearch.WordTrace]
  refine ⟨138921339387074756678786173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185228452516099675571714897 138921339387074756678786173)
  ·
    refine ⟨52095502270153033754544815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138921339387074756678786173 52095502270153033754544815)
    ·
      refine ⟨78143253405229550631817223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52095502270153033754544815 78143253405229550631817223)
      ·
        refine ⟨117214880107844325947725835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78143253405229550631817223 117214880107844325947725835)
        ·
          refine ⟨175822320161766488921588753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117214880107844325947725835 175822320161766488921588753)
          ·
            refine ⟨131866740121324866691191565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175822320161766488921588753 131866740121324866691191565)
            ·
              refine ⟨49450027545496825009196837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131866740121324866691191565 49450027545496825009196837)
              ·
                refine ⟨9271880164780654689224407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49450027545496825009196837 9271880164780654689224407)
                ·
                  refine ⟨13907820247170982033836611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9271880164780654689224407 13907820247170982033836611)
                  ·
                    refine ⟨20861730370756473050754917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13907820247170982033836611 20861730370756473050754917)
                    ·
                      refine ⟨3911574444516838697016547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20861730370756473050754917 3911574444516838697016547)
                      ·
                        rfl

theorem cell23_7617764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 4, 1, 1, 4].length) (baseStart_7617764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7617764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7617764 prefixEnd_7617764 := by exact prefixLift 7617764
  have htrace : WordTrace (prefixWord ++ tailWord_7617764) baseStart_7617764 baseEnd_7617764 := by
    simpa [prefixWord, tailWord_7617764, baseEnd_7617764] using wordTrace_append hprefix tailTrace_7617764
  have hstable : (prefixWord ++ tailWord_7617764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7617764).length < 2 ^ (prefixWord ++ tailWord_7617764).sum := by decide
  have hdescent : baseEnd_7617764 < baseStart_7617764 := by decide
  rcases family_descends (prefixWord ++ tailWord_7617764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7617774 : List Nat := [4, 1, 2, 1, 1, 1, 3, 2, 4, 4]
def baseStart_7617774 : Nat := 118140960795 + 7617774 * 2 ^ 59
def prefixEnd_7617774 : Nat := 4983230072969 + 3 ^ 40 * 7617774 * 2
def baseEnd_7617774 : Nat := 1303859859774461219297167

theorem tailTrace_7617774 : CollatzResearch.WordTrace tailWord_7617774 prefixEnd_7617774 1303859859774461219297167 := by
  unfold tailWord_7617774
  simp only [CollatzResearch.WordTrace]
  refine ⟨34730380438014160633179547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185228695669408856710290917 34730380438014160633179547)
  ·
    refine ⟨52095570657021240949769321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34730380438014160633179547 52095570657021240949769321)
    ·
      refine ⟨39071677992765930712326991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52095570657021240949769321 39071677992765930712326991)
      ·
        refine ⟨58607516989148896068490487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39071677992765930712326991 58607516989148896068490487)
        ·
          refine ⟨87911275483723344102735731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58607516989148896068490487 87911275483723344102735731)
          ·
            refine ⟨131866913225585016154103597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87911275483723344102735731 131866913225585016154103597)
            ·
              refine ⟨49450092459594381057788849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131866913225585016154103597 49450092459594381057788849)
              ·
                refine ⟨37087569344695785793341637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49450092459594381057788849 37087569344695785793341637)
                ·
                  refine ⟨6953919252130459836251557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37087569344695785793341637 6953919252130459836251557)
                  ·
                    refine ⟨1303859859774461219297167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6953919252130459836251557 1303859859774461219297167)
                    ·
                      rfl

theorem cell23_7617774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 2, 4, 4].length) (baseStart_7617774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7617774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7617774 prefixEnd_7617774 := by exact prefixLift 7617774
  have htrace : WordTrace (prefixWord ++ tailWord_7617774) baseStart_7617774 baseEnd_7617774 := by
    simpa [prefixWord, tailWord_7617774, baseEnd_7617774] using wordTrace_append hprefix tailTrace_7617774
  have hstable : (prefixWord ++ tailWord_7617774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7617774).length < 2 ^ (prefixWord ++ tailWord_7617774).sum := by decide
  have hdescent : baseEnd_7617774 < baseStart_7617774 := by decide
  rcases family_descends (prefixWord ++ tailWord_7617774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7617775 : List Nat := [1, 1, 2, 1, 7, 2, 1, 3, 1, 1, 3]
def baseStart_7617775 : Nat := 118140960795 + 7617775 * 2 ^ 59
def prefixEnd_7617775 : Nat := 4983230072969 + 3 ^ 40 * 7617775 * 2
def baseEnd_7617775 : Nat := 3911580092804038153978997

theorem tailTrace_7617775 : CollatzResearch.WordTrace tailWord_7617775 prefixEnd_7617775 3911580092804038153978997 := by
  unfold tailWord_7617775
  simp only [CollatzResearch.WordTrace]
  refine ⟨277843079977109662236222779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185228719984739774824148519 277843079977109662236222779)
  ·
    refine ⟨416764619965664493354334169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277843079977109662236222779 416764619965664493354334169)
    ·
      refine ⟨312573464974248370015750627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 416764619965664493354334169 312573464974248370015750627)
      ·
        refine ⟨468860197461372555023625941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312573464974248370015750627 468860197461372555023625941)
        ·
          refine ⟨10988910878000919258366233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 468860197461372555023625941 10988910878000919258366233)
          ·
            refine ⟨8241683158500689443774675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10988910878000919258366233 8241683158500689443774675)
            ·
              refine ⟨12362524737751034165662013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8241683158500689443774675 12362524737751034165662013)
              ·
                refine ⟨4635946776656637812123255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12362524737751034165662013 4635946776656637812123255)
                ·
                  refine ⟨6953920164984956718184883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4635946776656637812123255 6953920164984956718184883)
                  ·
                    refine ⟨10430880247477435077277325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6953920164984956718184883 10430880247477435077277325)
                    ·
                      refine ⟨3911580092804038153978997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10430880247477435077277325 3911580092804038153978997)
                      ·
                        rfl

theorem cell23_7617775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 1, 3, 1, 1, 3].length) (baseStart_7617775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7617775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7617775 prefixEnd_7617775 := by exact prefixLift 7617775
  have htrace : WordTrace (prefixWord ++ tailWord_7617775) baseStart_7617775 baseEnd_7617775 := by
    simpa [prefixWord, tailWord_7617775, baseEnd_7617775] using wordTrace_append hprefix tailTrace_7617775
  have hstable : (prefixWord ++ tailWord_7617775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7617775).length < 2 ^ (prefixWord ++ tailWord_7617775).sum := by decide
  have hdescent : baseEnd_7617775 < baseStart_7617775 := by decide
  rcases family_descends (prefixWord ++ tailWord_7617775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7617777 : List Nat := [1, 2, 2, 2, 2, 1, 1, 3, 3, 2, 4]
def baseStart_7617777 : Nat := 118140960795 + 7617777 * 2 ^ 59
def prefixEnd_7617777 : Nat := 4983230072969 + 3 ^ 40 * 7617777 * 2
def baseEnd_7617777 : Nat := 3911581119765347146153987

theorem tailTrace_7617777 : CollatzResearch.WordTrace tailWord_7617777 prefixEnd_7617777 3911581119765347146153987 := by
  unfold tailWord_7617777
  simp only [CollatzResearch.WordTrace]
  refine ⟨277843152923102416577795585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185228768615401611051863723 277843152923102416577795585)
  ·
    refine ⟨208382364692326812433346689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277843152923102416577795585 208382364692326812433346689)
    ·
      refine ⟨156286773519245109325010017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208382364692326812433346689 156286773519245109325010017)
      ·
        refine ⟨117215080139433831993757513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156286773519245109325010017 117215080139433831993757513)
        ·
          refine ⟨87911310104575373995318135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117215080139433831993757513 87911310104575373995318135)
          ·
            refine ⟨131866965156863060992977203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87911310104575373995318135 131866965156863060992977203)
            ·
              refine ⟨197800447735294591489465805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131866965156863060992977203 197800447735294591489465805)
              ·
                refine ⟨74175167900735471808549677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 197800447735294591489465805 74175167900735471808549677)
                ·
                  refine ⟨27815687962775801928206129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74175167900735471808549677 27815687962775801928206129)
                  ·
                    refine ⟨20861765972081851446154597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27815687962775801928206129 20861765972081851446154597)
                    ·
                      refine ⟨3911581119765347146153987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20861765972081851446154597 3911581119765347146153987)
                      ·
                        rfl

theorem cell23_7617777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 3, 3, 2, 4].length) (baseStart_7617777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7617777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7617777 prefixEnd_7617777 := by exact prefixLift 7617777
  have htrace : WordTrace (prefixWord ++ tailWord_7617777) baseStart_7617777 baseEnd_7617777 := by
    simpa [prefixWord, tailWord_7617777, baseEnd_7617777] using wordTrace_append hprefix tailTrace_7617777
  have hstable : (prefixWord ++ tailWord_7617777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7617777).length < 2 ^ (prefixWord ++ tailWord_7617777).sum := by decide
  have hdescent : baseEnd_7617777 < baseStart_7617777 := by decide
  rcases family_descends (prefixWord ++ tailWord_7617777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7617818 : List Nat := [3, 1, 1, 3, 3, 3, 1, 2, 1, 2, 3]
def baseStart_7617818 : Nat := 118140960795 + 7617818 * 2 ^ 59
def prefixEnd_7617818 : Nat := 4983230072969 + 3 ^ 40 * 7617818 * 2
def baseEnd_7617818 : Nat := 3911602172472181485741299

theorem tailTrace_7617818 : CollatzResearch.WordTrace tailWord_7617818 prefixEnd_7617818 3911602172472181485741299 := by
  unfold tailWord_7617818
  simp only [CollatzResearch.WordTrace]
  refine ⟨69461162078988470145009527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185229765543969253720025405 69461162078988470145009527)
  ·
    refine ⟨104191743118482705217514291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69461162078988470145009527 104191743118482705217514291)
    ·
      refine ⟨156287614677724057826271437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104191743118482705217514291 156287614677724057826271437)
      ·
        refine ⟨58607855504146521684851789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156287614677724057826271437 58607855504146521684851789)
        ·
          refine ⟨21977945814054945631819421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58607855504146521684851789 21977945814054945631819421)
          ·
            refine ⟨8241729680270604611932283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21977945814054945631819421 8241729680270604611932283)
            ·
              refine ⟨12362594520405906917898425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8241729680270604611932283 12362594520405906917898425)
              ·
                refine ⟨9271945890304430188423819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12362594520405906917898425 9271945890304430188423819)
                ·
                  refine ⟨13907918835456645282635729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9271945890304430188423819 13907918835456645282635729)
                  ·
                    refine ⟨10430939126592483961976797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13907918835456645282635729 10430939126592483961976797)
                    ·
                      refine ⟨3911602172472181485741299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10430939126592483961976797 3911602172472181485741299)
                      ·
                        rfl

theorem cell23_7617818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 1, 2, 1, 2, 3].length) (baseStart_7617818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7617818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7617818 prefixEnd_7617818 := by exact prefixLift 7617818
  have htrace : WordTrace (prefixWord ++ tailWord_7617818) baseStart_7617818 baseEnd_7617818 := by
    simpa [prefixWord, tailWord_7617818, baseEnd_7617818] using wordTrace_append hprefix tailTrace_7617818
  have hstable : (prefixWord ++ tailWord_7617818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7617818).length < 2 ^ (prefixWord ++ tailWord_7617818).sum := by decide
  have hdescent : baseEnd_7617818 < baseStart_7617818 := by decide
  rcases family_descends (prefixWord ++ tailWord_7617818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7617849 : List Nat := [1, 2, 1, 6, 2, 2, 2, 2, 1, 2, 2]
def baseStart_7617849 : Nat := 118140960795 + 7617849 * 2 ^ 59
def prefixEnd_7617849 : Nat := 4983230072969 + 3 ^ 40 * 7617849 * 2
def baseEnd_7617849 : Nat := 3911618090372470864453657

theorem tailTrace_7617849 : CollatzResearch.WordTrace tailWord_7617849 prefixEnd_7617849 3911618090372470864453657 := by
  unfold tailWord_7617849
  simp only [CollatzResearch.WordTrace]
  refine ⟨277845778978841572874416601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185230519319227715249611067 277845778978841572874416601)
  ·
    refine ⟨208384334234131179655812451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277845778978841572874416601 208384334234131179655812451)
    ·
      refine ⟨312576501351196769483718677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208384334234131179655812451 312576501351196769483718677)
      ·
        refine ⟨14652023500837348569549313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 312576501351196769483718677 14652023500837348569549313)
        ·
          refine ⟨10989017625628011427161985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14652023500837348569549313 10989017625628011427161985)
          ·
            refine ⟨8241763219221008570371489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10989017625628011427161985 8241763219221008570371489)
            ·
              refine ⟨6181322414415756427778617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8241763219221008570371489 6181322414415756427778617)
              ·
                refine ⟨4635991810811817320833963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6181322414415756427778617 4635991810811817320833963)
                ·
                  refine ⟨6953987716217725981250945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4635991810811817320833963 6953987716217725981250945)
                  ·
                    refine ⟨5215490787163294485938209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6953987716217725981250945 5215490787163294485938209)
                    ·
                      refine ⟨3911618090372470864453657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5215490787163294485938209 3911618090372470864453657)
                      ·
                        rfl

theorem cell23_7617849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 2, 2, 1, 2, 2].length) (baseStart_7617849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7617849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7617849 prefixEnd_7617849 := by exact prefixLift 7617849
  have htrace : WordTrace (prefixWord ++ tailWord_7617849) baseStart_7617849 baseEnd_7617849 := by
    simpa [prefixWord, tailWord_7617849, baseEnd_7617849] using wordTrace_append hprefix tailTrace_7617849
  have hstable : (prefixWord ++ tailWord_7617849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7617849).length < 2 ^ (prefixWord ++ tailWord_7617849).sum := by decide
  have hdescent : baseEnd_7617849 < baseStart_7617849 := by decide
  rcases family_descends (prefixWord ++ tailWord_7617849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7617854 : List Nat := [4, 2, 1, 2, 1, 1, 1, 1, 1, 5, 4]
def baseStart_7617854 : Nat := 118140960795 + 7617854 * 2 ^ 59
def prefixEnd_7617854 : Nat := 4983230072969 + 3 ^ 40 * 7617854 * 2
def baseEnd_7617854 : Nat := 3911620657775743344891133

theorem tailTrace_7617854 : CollatzResearch.WordTrace tailWord_7617854 prefixEnd_7617854 3911620657775743344891133 := by
  unfold tailWord_7617854
  simp only [CollatzResearch.WordTrace]
  refine ⟨34730745167977932341043577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185230640895882305818899077 34730745167977932341043577)
  ·
    refine ⟨26048058875983449255782683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34730745167977932341043577 26048058875983449255782683)
    ·
      refine ⟨39072088313975173883674025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26048058875983449255782683 39072088313975173883674025)
      ·
        refine ⟨29304066235481380412755519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39072088313975173883674025 29304066235481380412755519)
        ·
          refine ⟨43956099353222070619133279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29304066235481380412755519 43956099353222070619133279)
          ·
            refine ⟨65934149029833105928699919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43956099353222070619133279 65934149029833105928699919)
            ·
              refine ⟨98901223544749658893049879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65934149029833105928699919 98901223544749658893049879)
              ·
                refine ⟨148351835317124488339574819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98901223544749658893049879 148351835317124488339574819)
                ·
                  refine ⟨222527752975686732509362229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 148351835317124488339574819 222527752975686732509362229)
                  ·
                    refine ⟨20861976841470631172752709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 222527752975686732509362229 20861976841470631172752709)
                    ·
                      refine ⟨3911620657775743344891133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20861976841470631172752709 3911620657775743344891133)
                      ·
                        rfl

theorem cell23_7617854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_7617854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7617854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7617854 prefixEnd_7617854 := by exact prefixLift 7617854
  have htrace : WordTrace (prefixWord ++ tailWord_7617854) baseStart_7617854 baseEnd_7617854 := by
    simpa [prefixWord, tailWord_7617854, baseEnd_7617854] using wordTrace_append hprefix tailTrace_7617854
  have hstable : (prefixWord ++ tailWord_7617854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7617854).length < 2 ^ (prefixWord ++ tailWord_7617854).sum := by decide
  have hdescent : baseEnd_7617854 < baseStart_7617854 := by decide
  rcases family_descends (prefixWord ++ tailWord_7617854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7617874 : List Nat := [3, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3]
def baseStart_7617874 : Nat := 118140960795 + 7617874 * 2 ^ 59
def prefixEnd_7617874 : Nat := 4983230072969 + 3 ^ 40 * 7617874 * 2
def baseEnd_7617874 : Nat := 3911630927388833266641041

theorem tailTrace_7617874 : CollatzResearch.WordTrace tailWord_7617874 prefixEnd_7617874 3911630927388833266641041 := by
  unfold tailWord_7617874
  simp only [CollatzResearch.WordTrace]
  refine ⟨69461672700937750536019169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185231127202500668096051117 69461672700937750536019169)
  ·
    refine ⟨52096254525703312902014377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69461672700937750536019169 52096254525703312902014377)
    ·
      refine ⟨39072190894277484676510783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52096254525703312902014377 39072190894277484676510783)
      ·
        refine ⟨58608286341416227014766175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39072190894277484676510783 58608286341416227014766175)
        ·
          refine ⟨87912429512124340522149263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58608286341416227014766175 87912429512124340522149263)
          ·
            refine ⟨131868644268186510783223895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87912429512124340522149263 131868644268186510783223895)
            ·
              refine ⟨197802966402279766174835843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131868644268186510783223895 197802966402279766174835843)
              ·
                refine ⟨296704449603419649262253765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 197802966402279766174835843 296704449603419649262253765)
                ·
                  refine ⟨55632084300641184236672581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 296704449603419649262253765 55632084300641184236672581)
                  ·
                    refine ⟨10431015806370222044376109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55632084300641184236672581 10431015806370222044376109)
                    ·
                      refine ⟨3911630927388833266641041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10431015806370222044376109 3911630927388833266641041)
                      ·
                        rfl

theorem cell23_7617874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3].length) (baseStart_7617874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7617874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7617874 prefixEnd_7617874 := by exact prefixLift 7617874
  have htrace : WordTrace (prefixWord ++ tailWord_7617874) baseStart_7617874 baseEnd_7617874 := by
    simpa [prefixWord, tailWord_7617874, baseEnd_7617874] using wordTrace_append hprefix tailTrace_7617874
  have hstable : (prefixWord ++ tailWord_7617874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7617874).length < 2 ^ (prefixWord ++ tailWord_7617874).sum := by decide
  have hdescent : baseEnd_7617874 < baseStart_7617874 := by decide
  rcases family_descends (prefixWord ++ tailWord_7617874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7617887 : List Nat := [1, 1, 2, 3, 1, 2, 1, 2, 1, 2, 7]
def baseStart_7617887 : Nat := 118140960795 + 7617887 * 2 ^ 59
def prefixEnd_7617887 : Nat := 4983230072969 + 3 ^ 40 * 7617887 * 2
def baseEnd_7617887 : Nat := 3911637602637341715778481

theorem tailTrace_7617887 : CollatzResearch.WordTrace tailWord_7617887 prefixEnd_7617887 3911637602637341715778481 := by
  unfold tailWord_7617887
  simp only [CollatzResearch.WordTrace]
  refine ⟨277847164952703905364299915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185231443301802603576199943 277847164952703905364299915)
  ·
    refine ⟨416770747429055858046449873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277847164952703905364299915 416770747429055858046449873)
    ·
      refine ⟨312578060571791893534837405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 416770747429055858046449873 312578060571791893534837405)
      ·
        refine ⟨117216772714421960075564027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 312578060571791893534837405 117216772714421960075564027)
        ·
          refine ⟨175825159071632940113346041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117216772714421960075564027 175825159071632940113346041)
          ·
            refine ⟨131868869303724705085009531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175825159071632940113346041 131868869303724705085009531)
            ·
              refine ⟨197803303955587057627514297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131868869303724705085009531 197803303955587057627514297)
              ·
                refine ⟨148352477966690293220635723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 197803303955587057627514297 148352477966690293220635723)
                ·
                  refine ⟨222528716950035439830953585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 148352477966690293220635723 222528716950035439830953585)
                  ·
                    refine ⟨166896537712526579873215189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 222528716950035439830953585 166896537712526579873215189)
                    ·
                      refine ⟨3911637602637341715778481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 166896537712526579873215189 3911637602637341715778481)
                      ·
                        rfl

theorem cell23_7617887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 2, 7].length) (baseStart_7617887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7617887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7617887 prefixEnd_7617887 := by exact prefixLift 7617887
  have htrace : WordTrace (prefixWord ++ tailWord_7617887) baseStart_7617887 baseEnd_7617887 := by
    simpa [prefixWord, tailWord_7617887, baseEnd_7617887] using wordTrace_append hprefix tailTrace_7617887
  have hstable : (prefixWord ++ tailWord_7617887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7617887).length < 2 ^ (prefixWord ++ tailWord_7617887).sum := by decide
  have hdescent : baseEnd_7617887 < baseStart_7617887 := by decide
  rcases family_descends (prefixWord ++ tailWord_7617887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7617904 : List Nat := [2, 1, 1, 1, 4, 2, 1, 1, 4, 3, 3]
def baseStart_7617904 : Nat := 118140960795 + 7617904 * 2 ^ 59
def prefixEnd_7617904 : Nat := 4983230072969 + 3 ^ 40 * 7617904 * 2
def baseEnd_7617904 : Nat := 3911646331808468149265903

theorem tailTrace_7617904 : CollatzResearch.WordTrace tailWord_7617904 prefixEnd_7617904 3911646331808468149265903 := by
  unfold tailWord_7617904
  simp only [CollatzResearch.WordTrace]
  refine ⟨138923892496821158633834383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185231856662428211511779177 138923892496821158633834383)
  ·
    refine ⟨208385838745231737950751575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138923892496821158633834383 208385838745231737950751575)
    ·
      refine ⟨312578758117847606926127363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208385838745231737950751575 312578758117847606926127363)
      ·
        refine ⟨468868137176771410389191045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312578758117847606926127363 468868137176771410389191045)
        ·
          refine ⟨87912775720644639447973321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 468868137176771410389191045 87912775720644639447973321)
          ·
            refine ⟨65934581790483479585979991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87912775720644639447973321 65934581790483479585979991)
            ·
              refine ⟨98901872685725219378969987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65934581790483479585979991 98901872685725219378969987)
              ·
                refine ⟨148352809028587829068454981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98901872685725219378969987 148352809028587829068454981)
                ·
                  refine ⟨27816151692860217950335309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 148352809028587829068454981 27816151692860217950335309)
                  ·
                    refine ⟨10431056884822581731375741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27816151692860217950335309 10431056884822581731375741)
                    ·
                      refine ⟨3911646331808468149265903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10431056884822581731375741 3911646331808468149265903)
                      ·
                        rfl

theorem cell23_7617904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 4, 3, 3].length) (baseStart_7617904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7617904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7617904 prefixEnd_7617904 := by exact prefixLift 7617904
  have htrace : WordTrace (prefixWord ++ tailWord_7617904) baseStart_7617904 baseEnd_7617904 := by
    simpa [prefixWord, tailWord_7617904, baseEnd_7617904] using wordTrace_append hprefix tailTrace_7617904
  have hstable : (prefixWord ++ tailWord_7617904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7617904).length < 2 ^ (prefixWord ++ tailWord_7617904).sum := by decide
  have hdescent : baseEnd_7617904 < baseStart_7617904 := by decide
  rcases family_descends (prefixWord ++ tailWord_7617904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7617907 : List Nat := [1, 1, 1, 2, 2, 1, 2, 1, 5, 7]
def baseStart_7617907 : Nat := 118140960795 + 7617907 * 2 ^ 59
def prefixEnd_7617907 : Nat := 4983230072969 + 3 ^ 40 * 7617907 * 2
def baseEnd_7617907 : Nat := 1303882624083477212509463

theorem tailTrace_7617907 : CollatzResearch.WordTrace tailWord_7617907 prefixEnd_7617907 1303882624083477212509463 := by
  unfold tailWord_7617907
  simp only [CollatzResearch.WordTrace]
  refine ⟨277847894412631448780027975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185231929608420965853351983 277847894412631448780027975)
  ·
    refine ⟨416771841618947173170041963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277847894412631448780027975 416771841618947173170041963)
    ·
      refine ⟨625157762428420759755062945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 416771841618947173170041963 625157762428420759755062945)
      ·
        refine ⟨468868321821315569816297209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 625157762428420759755062945 468868321821315569816297209)
        ·
          refine ⟨351651241365986677362222907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 468868321821315569816297209 351651241365986677362222907)
          ·
            refine ⟨527476862048980016043334361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 351651241365986677362222907 527476862048980016043334361)
            ·
              refine ⟨395607646536735012032500771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 527476862048980016043334361 395607646536735012032500771)
              ·
                refine ⟨593411469805102518048751157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 395607646536735012032500771 593411469805102518048751157)
                ·
                  refine ⟨55632325294228361067070421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 593411469805102518048751157 55632325294228361067070421)
                  ·
                    refine ⟨1303882624083477212509463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55632325294228361067070421 1303882624083477212509463)
                    ·
                      rfl

theorem cell23_7617907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 5, 7].length) (baseStart_7617907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7617907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7617907 prefixEnd_7617907 := by exact prefixLift 7617907
  have htrace : WordTrace (prefixWord ++ tailWord_7617907) baseStart_7617907 baseEnd_7617907 := by
    simpa [prefixWord, tailWord_7617907, baseEnd_7617907] using wordTrace_append hprefix tailTrace_7617907
  have hstable : (prefixWord ++ tailWord_7617907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7617907).length < 2 ^ (prefixWord ++ tailWord_7617907).sum := by decide
  have hdescent : baseEnd_7617907 < baseStart_7617907 := by decide
  rcases family_descends (prefixWord ++ tailWord_7617907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7617922 : List Nat := [3, 4, 2, 1, 1, 3, 1, 1, 1, 4, 2]
def baseStart_7617922 : Nat := 118140960795 + 7617922 * 2 ^ 59
def prefixEnd_7617922 : Nat := 4983230072969 + 3 ^ 40 * 7617922 * 2
def baseEnd_7617922 : Nat := 3911655574460249078840821

theorem tailTrace_7617922 : CollatzResearch.WordTrace tailWord_7617922 prefixEnd_7617922 3911655574460249078840821 := by
  unfold tailWord_7617922
  simp only [CollatzResearch.WordTrace]
  refine ⟨69462110376894276585456005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185232294338384737561216013 69462110376894276585456005)
  ·
    refine ⟨13024145695667676859773001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69462110376894276585456005 13024145695667676859773001)
    ·
      refine ⟨9768109271750757644829751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13024145695667676859773001 9768109271750757644829751)
      ·
        refine ⟨14652163907626136467244627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9768109271750757644829751 14652163907626136467244627)
        ·
          refine ⟨21978245861439204700866941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14652163907626136467244627 21978245861439204700866941)
          ·
            refine ⟨8241842198039701762825103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21978245861439204700866941 8241842198039701762825103)
            ·
              refine ⟨12362763297059552644237655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8241842198039701762825103 12362763297059552644237655)
              ·
                refine ⟨18544144945589328966356483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12362763297059552644237655 18544144945589328966356483)
                ·
                  refine ⟨27816217418383993449534725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18544144945589328966356483 27816217418383993449534725)
                  ·
                    refine ⟨5215540765946998771787761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27816217418383993449534725 5215540765946998771787761)
                    ·
                      refine ⟨3911655574460249078840821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5215540765946998771787761 3911655574460249078840821)
                      ·
                        rfl

theorem cell23_7617922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 1, 1, 1, 4, 2].length) (baseStart_7617922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7617922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7617922 prefixEnd_7617922 := by exact prefixLift 7617922
  have htrace : WordTrace (prefixWord ++ tailWord_7617922) baseStart_7617922 baseEnd_7617922 := by
    simpa [prefixWord, tailWord_7617922, baseEnd_7617922] using wordTrace_append hprefix tailTrace_7617922
  have hstable : (prefixWord ++ tailWord_7617922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7617922).length < 2 ^ (prefixWord ++ tailWord_7617922).sum := by decide
  have hdescent : baseEnd_7617922 < baseStart_7617922 := by decide
  rcases family_descends (prefixWord ++ tailWord_7617922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7617924 : List Nat := [2, 3, 2, 1, 1, 3, 1, 2, 1, 7]
def baseStart_7617924 : Nat := 118140960795 + 7617924 * 2 ^ 59
def prefixEnd_7617924 : Nat := 4983230072969 + 3 ^ 40 * 7617924 * 2
def baseEnd_7617924 : Nat := 1303885533807186023671937

theorem tailTrace_7617924 : CollatzResearch.WordTrace tailWord_7617924 prefixEnd_7617924 1303885533807186023671937 := by
  unfold tailWord_7617924
  simp only [CollatzResearch.WordTrace]
  refine ⟨138924257226784930341698413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185232342969046573788931217 138924257226784930341698413)
  ·
    refine ⟨52096596460044348878136905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138924257226784930341698413 52096596460044348878136905)
    ·
      refine ⟨39072447345033261658602679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52096596460044348878136905 39072447345033261658602679)
      ·
        refine ⟨58608671017549892487904019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39072447345033261658602679 58608671017549892487904019)
        ·
          refine ⟨87913006526324838731856029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58608671017549892487904019 87913006526324838731856029)
          ·
            refine ⟨32967377447371814524446011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87913006526324838731856029 32967377447371814524446011)
            ·
              refine ⟨49451066171057721786669017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32967377447371814524446011 49451066171057721786669017)
              ·
                refine ⟨37088299628293291340001763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49451066171057721786669017 37088299628293291340001763)
                ·
                  refine ⟨55632449442439937010002645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37088299628293291340001763 55632449442439937010002645)
                  ·
                    refine ⟨1303885533807186023671937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55632449442439937010002645 1303885533807186023671937)
                    ·
                      rfl

theorem cell23_7617924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 2, 1, 7].length) (baseStart_7617924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7617924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7617924 prefixEnd_7617924 := by exact prefixLift 7617924
  have htrace : WordTrace (prefixWord ++ tailWord_7617924) baseStart_7617924 baseEnd_7617924 := by
    simpa [prefixWord, tailWord_7617924, baseEnd_7617924] using wordTrace_append hprefix tailTrace_7617924
  have hstable : (prefixWord ++ tailWord_7617924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7617924).length < 2 ^ (prefixWord ++ tailWord_7617924).sum := by decide
  have hdescent : baseEnd_7617924 < baseStart_7617924 := by decide
  rcases family_descends (prefixWord ++ tailWord_7617924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7617981 : List Nat := [1, 4, 1, 2, 2, 1, 1, 2, 4, 2, 3]
def baseStart_7617981 : Nat := 118140960795 + 7617981 * 2 ^ 59
def prefixEnd_7617981 : Nat := 4983230072969 + 3 ^ 40 * 7617981 * 2
def baseEnd_7617981 : Nat := 3911685869818864348003049

theorem tailTrace_7617981 : CollatzResearch.WordTrace tailWord_7617981 prefixEnd_7617981 3911685869818864348003049 := by
  unfold tailWord_7617981
  simp only [CollatzResearch.WordTrace]
  refine ⟨277850593414363359418221797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185233728942908906278814531 277850593414363359418221797)
  ·
    refine ⟨52096986265193129890916587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 277850593414363359418221797 52096986265193129890916587)
    ·
      refine ⟨78145479397789694836374881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52096986265193129890916587 78145479397789694836374881)
      ·
        refine ⟨58609109548342271127281161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78145479397789694836374881 58609109548342271127281161)
        ·
          refine ⟨43956832161256703345460871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58609109548342271127281161 43956832161256703345460871)
          ·
            refine ⟨65935248241885055018191307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43956832161256703345460871 65935248241885055018191307)
            ·
              refine ⟨98902872362827582527286961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65935248241885055018191307 98902872362827582527286961)
              ·
                refine ⟨74177154272120686895465221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98902872362827582527286961 74177154272120686895465221)
                ·
                  refine ⟨13908216426022628792899729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74177154272120686895465221 13908216426022628792899729)
                  ·
                    refine ⟨10431162319516971594674797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13908216426022628792899729 10431162319516971594674797)
                    ·
                      refine ⟨3911685869818864348003049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10431162319516971594674797 3911685869818864348003049)
                      ·
                        rfl

theorem cell23_7617981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 2, 4, 2, 3].length) (baseStart_7617981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7617981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7617981 prefixEnd_7617981 := by exact prefixLift 7617981
  have htrace : WordTrace (prefixWord ++ tailWord_7617981) baseStart_7617981 baseEnd_7617981 := by
    simpa [prefixWord, tailWord_7617981, baseEnd_7617981] using wordTrace_append hprefix tailTrace_7617981
  have hstable : (prefixWord ++ tailWord_7617981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7617981).length < 2 ^ (prefixWord ++ tailWord_7617981).sum := by decide
  have hdescent : baseEnd_7617981 < baseStart_7617981 := by decide
  rcases family_descends (prefixWord ++ tailWord_7617981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7618051 : List Nat := [1, 1, 1, 3, 2, 1, 2, 1, 1, 8, 2]
def baseStart_7618051 : Nat := 118140960795 + 7618051 * 2 ^ 59
def prefixEnd_7618051 : Nat := 4983230072969 + 3 ^ 40 * 7618051 * 2
def baseEnd_7618051 : Nat := 3911721813464679074127727

theorem tailTrace_7618051 : CollatzResearch.WordTrace tailWord_7618051 prefixEnd_7618051 3911721813464679074127727 := by
  unfold tailWord_7618051
  simp only [CollatzResearch.WordTrace]
  refine ⟨277853146524109761373270007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185235431016073174248846671 277853146524109761373270007)
  ·
    refine ⟨416779719786164642059905011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277853146524109761373270007 416779719786164642059905011)
    ·
      refine ⟨625169579679246963089857517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 416779719786164642059905011 625169579679246963089857517)
      ·
        refine ⟨234438592379717611158696569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 625169579679246963089857517 234438592379717611158696569)
        ·
          refine ⟨175828944284788208369022427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234438592379717611158696569 175828944284788208369022427)
          ·
            refine ⟨263743416427182312553533641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175828944284788208369022427 263743416427182312553533641)
            ·
              refine ⟨197807562320386734415150231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 263743416427182312553533641 197807562320386734415150231)
              ·
                refine ⟨296711343480580101622725347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 197807562320386734415150231 296711343480580101622725347)
                ·
                  refine ⟨445067015220870152434088021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 296711343480580101622725347 445067015220870152434088021)
                  ·
                    refine ⟨5215629084619572098836969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 445067015220870152434088021 5215629084619572098836969)
                    ·
                      refine ⟨3911721813464679074127727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5215629084619572098836969 3911721813464679074127727)
                      ·
                        rfl

theorem cell23_7618051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 8, 2].length) (baseStart_7618051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7618051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7618051 prefixEnd_7618051 := by exact prefixLift 7618051
  have htrace : WordTrace (prefixWord ++ tailWord_7618051) baseStart_7618051 baseEnd_7618051 := by
    simpa [prefixWord, tailWord_7618051, baseEnd_7618051] using wordTrace_append hprefix tailTrace_7618051
  have hstable : (prefixWord ++ tailWord_7618051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7618051).length < 2 ^ (prefixWord ++ tailWord_7618051).sum := by decide
  have hdescent : baseEnd_7618051 < baseStart_7618051 := by decide
  rcases family_descends (prefixWord ++ tailWord_7618051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7618055 : List Nat := [1, 1, 4, 3, 2, 1, 3, 1, 2, 3, 2]
def baseStart_7618055 : Nat := 118140960795 + 7618055 * 2 ^ 59
def prefixEnd_7618055 : Nat := 4983230072969 + 3 ^ 40 * 7618055 * 2
def baseEnd_7618055 : Nat := 3911723867387297058477709

theorem tailTrace_7618055 : CollatzResearch.WordTrace tailWord_7618055 prefixEnd_7618055 3911723867387297058477709 := by
  unfold tailWord_7618055
  simp only [CollatzResearch.WordTrace]
  refine ⟨277853292416095270056415619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185235528277396846704277079 277853292416095270056415619)
  ·
    refine ⟨416779938624142905084623429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277853292416095270056415619 416779938624142905084623429)
    ·
      refine ⟨78146238492026794703366893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 416779938624142905084623429 78146238492026794703366893)
      ·
        refine ⟨29304839434510048013762585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78146238492026794703366893 29304839434510048013762585)
        ·
          refine ⟨21978629575882536010321939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29304839434510048013762585 21978629575882536010321939)
          ·
            refine ⟨32967944363823804015482909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21978629575882536010321939 32967944363823804015482909)
            ·
              refine ⟨12362979136433926505806091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32967944363823804015482909 12362979136433926505806091)
              ·
                refine ⟨18544468704650889758709137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12362979136433926505806091 18544468704650889758709137)
                ·
                  refine ⟨13908351528488167319031853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18544468704650889758709137 13908351528488167319031853)
                  ·
                    refine ⟨5215631823183062744636945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13908351528488167319031853 5215631823183062744636945)
                    ·
                      refine ⟨3911723867387297058477709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5215631823183062744636945 3911723867387297058477709)
                      ·
                        rfl

theorem cell23_7618055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 3, 1, 2, 3, 2].length) (baseStart_7618055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7618055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7618055 prefixEnd_7618055 := by exact prefixLift 7618055
  have htrace : WordTrace (prefixWord ++ tailWord_7618055) baseStart_7618055 baseEnd_7618055 := by
    simpa [prefixWord, tailWord_7618055, baseEnd_7618055] using wordTrace_append hprefix tailTrace_7618055
  have hstable : (prefixWord ++ tailWord_7618055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7618055).length < 2 ^ (prefixWord ++ tailWord_7618055).sum := by decide
  have hdescent : baseEnd_7618055 < baseStart_7618055 := by decide
  rcases family_descends (prefixWord ++ tailWord_7618055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7618102 : List Nat := [5, 1, 2, 1, 3, 1, 2, 2, 1, 1, 4]
def baseStart_7618102 : Nat := 118140960795 + 7618102 * 2 ^ 59
def prefixEnd_7618102 : Nat := 4983230072969 + 3 ^ 40 * 7618102 * 2
def baseEnd_7618102 : Nat := 3911748000978058374589993

theorem tailTrace_7618102 : CollatzResearch.WordTrace tailWord_7618102 prefixEnd_7618102 3911748000978058374589993 := by
  unfold tailWord_7618102
  simp only [CollatzResearch.WordTrace]
  refine ⟨17365937915432812317711035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 185236671097949998055584373 17365937915432812317711035)
  ·
    refine ⟨26048906873149218476566553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17365937915432812317711035 26048906873149218476566553)
    ·
      refine ⟨19536680154861913857424915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26048906873149218476566553 19536680154861913857424915)
      ·
        refine ⟨29305020232292870786137373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19536680154861913857424915 29305020232292870786137373)
        ·
          refine ⟨10989382587109826544801515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29305020232292870786137373 10989382587109826544801515)
          ·
            refine ⟨16484073880664739817202273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10989382587109826544801515 16484073880664739817202273)
            ·
              refine ⟨12363055410498554862901705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16484073880664739817202273 12363055410498554862901705)
              ·
                refine ⟨9272291557873916147176279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12363055410498554862901705 9272291557873916147176279)
                ·
                  refine ⟨13908437336810874220764419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9272291557873916147176279 13908437336810874220764419)
                  ·
                    refine ⟨20862656005216311331146629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13908437336810874220764419 20862656005216311331146629)
                    ·
                      refine ⟨3911748000978058374589993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20862656005216311331146629 3911748000978058374589993)
                      ·
                        rfl

theorem cell23_7618102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 2, 2, 1, 1, 4].length) (baseStart_7618102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7618102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7618102 prefixEnd_7618102 := by exact prefixLift 7618102
  have htrace : WordTrace (prefixWord ++ tailWord_7618102) baseStart_7618102 baseEnd_7618102 := by
    simpa [prefixWord, tailWord_7618102, baseEnd_7618102] using wordTrace_append hprefix tailTrace_7618102
  have hstable : (prefixWord ++ tailWord_7618102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7618102).length < 2 ^ (prefixWord ++ tailWord_7618102).sum := by decide
  have hdescent : baseEnd_7618102 < baseStart_7618102 := by decide
  rcases family_descends (prefixWord ++ tailWord_7618102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7618105 : List Nat := [1, 2, 1, 5, 1, 3, 2, 2, 1, 2, 3]
def baseStart_7618105 : Nat := 118140960795 + 7618105 * 2 ^ 59
def prefixEnd_7618105 : Nat := 4983230072969 + 3 ^ 40 * 7618105 * 2
def baseEnd_7618105 : Nat := 3911749541420021862852479

theorem tailTrace_7618105 : CollatzResearch.WordTrace tailWord_7618105 prefixEnd_7618105 3911749541420021862852479 := by
  unfold tailWord_7618105
  simp only [CollatzResearch.WordTrace]
  refine ⟨277855116065914128595735769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185236744043942752397157179 277855116065914128595735769)
  ·
    refine ⟨208391337049435596446801827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277855116065914128595735769 208391337049435596446801827)
    ·
      refine ⟨312587005574153394670202741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208391337049435596446801827 312587005574153394670202741)
      ·
        refine ⟨29305031772576880750331507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 312587005574153394670202741 29305031772576880750331507)
        ·
          refine ⟨43957547658865321125497261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29305031772576880750331507 43957547658865321125497261)
          ·
            refine ⟨16484080372074495422061473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43957547658865321125497261 16484080372074495422061473)
            ·
              refine ⟨12363060279055871566546105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16484080372074495422061473 12363060279055871566546105)
              ·
                refine ⟨9272295209291903674909579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12363060279055871566546105 9272295209291903674909579)
                ·
                  refine ⟨13908442813937855512364369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9272295209291903674909579 13908442813937855512364369)
                  ·
                    refine ⟨10431332110453391634273277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13908442813937855512364369 10431332110453391634273277)
                    ·
                      refine ⟨3911749541420021862852479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10431332110453391634273277 3911749541420021862852479)
                      ·
                        rfl

theorem cell23_7618105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 2, 2, 1, 2, 3].length) (baseStart_7618105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7618105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7618105 prefixEnd_7618105 := by exact prefixLift 7618105
  have htrace : WordTrace (prefixWord ++ tailWord_7618105) baseStart_7618105 baseEnd_7618105 := by
    simpa [prefixWord, tailWord_7618105, baseEnd_7618105] using wordTrace_append hprefix tailTrace_7618105
  have hstable : (prefixWord ++ tailWord_7618105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7618105).length < 2 ^ (prefixWord ++ tailWord_7618105).sum := by decide
  have hdescent : baseEnd_7618105 < baseStart_7618105 := by decide
  rcases family_descends (prefixWord ++ tailWord_7618105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7618125 : List Nat := [1, 6, 1, 1, 4, 1, 9]
def baseStart_7618125 : Nat := 118140960795 + 7618125 * 2 ^ 59
def prefixEnd_7618125 : Nat := 4983230072969 + 3 ^ 40 * 7618125 * 2
def baseEnd_7618125 : Nat := 48293331000408787464227

theorem tailTrace_7618125 : CollatzResearch.WordTrace tailWord_7618125 prefixEnd_7618125 48293331000408787464227 := by
  unfold tailWord_7618125
  simp only [CollatzResearch.WordTrace]
  refine ⟨277855845525841672011463829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185237230350561114674309219 277855845525841672011463829)
  ·
    refine ⟨13024492759023828375537367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 277855845525841672011463829 13024492759023828375537367)
    ·
      refine ⟨19536739138535742563306051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13024492759023828375537367 19536739138535742563306051)
      ·
        refine ⟨29305108707803613844959077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19536739138535742563306051 29305108707803613844959077)
        ·
          refine ⟨5494707882713177595929827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29305108707803613844959077 5494707882713177595929827)
          ·
            refine ⟨8242061824069766393894741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5494707882713177595929827 8242061824069766393894741)
            ·
              refine ⟨48293331000408787464227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8242061824069766393894741 48293331000408787464227)
              ·
                rfl

theorem cell23_7618125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 9].length) (baseStart_7618125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7618125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7618125 prefixEnd_7618125 := by exact prefixLift 7618125
  have htrace : WordTrace (prefixWord ++ tailWord_7618125) baseStart_7618125 baseEnd_7618125 := by
    simpa [prefixWord, tailWord_7618125, baseEnd_7618125] using wordTrace_append hprefix tailTrace_7618125
  have hstable : (prefixWord ++ tailWord_7618125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7618125).length < 2 ^ (prefixWord ++ tailWord_7618125).sum := by decide
  have hdescent : baseEnd_7618125 < baseStart_7618125 := by decide
  rcases family_descends (prefixWord ++ tailWord_7618125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7618151 : List Nat := [1, 1, 5, 1, 1, 1, 2, 3, 2, 6]
def baseStart_7618151 : Nat := 118140960795 + 7618151 * 2 ^ 59
def prefixEnd_7618151 : Nat := 4983230072969 + 3 ^ 40 * 7618151 * 2
def baseEnd_7618151 : Nat := 1303924387176709560959089

theorem tailTrace_7618151 : CollatzResearch.WordTrace tailWord_7618151 prefixEnd_7618151 1303924387176709560959089 := by
  unfold tailWord_7618151
  simp only [CollatzResearch.WordTrace]
  refine ⟨277856793823747478451910307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185237862549164985634606871 277856793823747478451910307)
  ·
    refine ⟨416785190735621217677865461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277856793823747478451910307 416785190735621217677865461)
    ·
      refine ⟨39073611631464489157299887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 416785190735621217677865461 39073611631464489157299887)
      ·
        refine ⟨58610417447196733735949831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39073611631464489157299887 58610417447196733735949831)
        ·
          refine ⟨87915626170795100603924747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58610417447196733735949831 87915626170795100603924747)
          ·
            refine ⟨131873439256192650905887121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87915626170795100603924747 131873439256192650905887121)
            ·
              refine ⟨98905079442144488179415341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131873439256192650905887121 98905079442144488179415341)
              ·
                refine ⟨37089404790804183067280753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98905079442144488179415341 37089404790804183067280753)
                ·
                  refine ⟨27817053593103137300460565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37089404790804183067280753 27817053593103137300460565)
                  ·
                    refine ⟨1303924387176709560959089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27817053593103137300460565 1303924387176709560959089)
                    ·
                      rfl

theorem cell23_7618151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 3, 2, 6].length) (baseStart_7618151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7618151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7618151 prefixEnd_7618151 := by exact prefixLift 7618151
  have htrace : WordTrace (prefixWord ++ tailWord_7618151) baseStart_7618151 baseEnd_7618151 := by
    simpa [prefixWord, tailWord_7618151, baseEnd_7618151] using wordTrace_append hprefix tailTrace_7618151
  have hstable : (prefixWord ++ tailWord_7618151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7618151).length < 2 ^ (prefixWord ++ tailWord_7618151).sum := by decide
  have hdescent : baseEnd_7618151 < baseStart_7618151 := by decide
  rcases family_descends (prefixWord ++ tailWord_7618151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7618152 : List Nat := [2, 1, 4, 3, 1, 2, 1, 3, 2, 1, 3]
def baseStart_7618152 : Nat := 118140960795 + 7618152 * 2 ^ 59
def prefixEnd_7618152 : Nat := 4983230072969 + 3 ^ 40 * 7618152 * 2
def baseEnd_7618152 : Nat := 3911773675010783178964763

theorem tailTrace_7618152 : CollatzResearch.WordTrace tailWord_7618152 prefixEnd_7618152 3911773675010783178964763 := by
  unfold tailWord_7618152
  simp only [CollatzResearch.WordTrace]
  refine ⟨138928415148371927811348355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185237886864495903748464473 138928415148371927811348355)
  ·
    refine ⟨208392622722557891717022533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138928415148371927811348355 208392622722557891717022533)
    ·
      refine ⟨39073616760479604696941725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 208392622722557891717022533 39073616760479604696941725)
      ·
        refine ⟨14652606285179851761353147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39073616760479604696941725 14652606285179851761353147)
        ·
          refine ⟨21978909427769777642029721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14652606285179851761353147 21978909427769777642029721)
          ·
            refine ⟨16484182070827333231522291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21978909427769777642029721 16484182070827333231522291)
            ·
              refine ⟨24726273106240999847283437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16484182070827333231522291 24726273106240999847283437)
              ·
                refine ⟨9272352414840374942731289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24726273106240999847283437 9272352414840374942731289)
                ·
                  refine ⟨6954264311130281207048467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9272352414840374942731289 6954264311130281207048467)
                  ·
                    refine ⟨10431396466695421810572701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6954264311130281207048467 10431396466695421810572701)
                    ·
                      refine ⟨3911773675010783178964763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10431396466695421810572701 3911773675010783178964763)
                      ·
                        rfl

theorem cell23_7618152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_7618152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7618152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7618152 prefixEnd_7618152 := by exact prefixLift 7618152
  have htrace : WordTrace (prefixWord ++ tailWord_7618152) baseStart_7618152 baseEnd_7618152 := by
    simpa [prefixWord, tailWord_7618152, baseEnd_7618152] using wordTrace_append hprefix tailTrace_7618152
  have hstable : (prefixWord ++ tailWord_7618152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7618152).length < 2 ^ (prefixWord ++ tailWord_7618152).sum := by decide
  have hdescent : baseEnd_7618152 < baseStart_7618152 := by decide
  rcases family_descends (prefixWord ++ tailWord_7618152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7618162 : List Nat := [3, 2, 1, 2, 3, 1, 3, 2, 1, 3, 2]
def baseStart_7618162 : Nat := 118140960795 + 7618162 * 2 ^ 59
def prefixEnd_7618162 : Nat := 4983230072969 + 3 ^ 40 * 7618162 * 2
def baseEnd_7618162 : Nat := 3911778809817328139839717

theorem tailTrace_7618162 : CollatzResearch.WordTrace tailWord_7618162 prefixEnd_7618162 3911778809817328139839717 := by
  unfold tailWord_7618162
  simp only [CollatzResearch.WordTrace]
  refine ⟨69464298756676906832640185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185238130017805084887040493 69464298756676906832640185)
  ·
    refine ⟨52098224067507680124480139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69464298756676906832640185 52098224067507680124480139)
    ·
      refine ⟨78147336101261520186720209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52098224067507680124480139 78147336101261520186720209)
      ·
        refine ⟨58610502075946140140040157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78147336101261520186720209 58610502075946140140040157)
        ·
          refine ⟨21978938278479802552515059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58610502075946140140040157 21978938278479802552515059)
          ·
            refine ⟨32968407417719703828772589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21978938278479802552515059 32968407417719703828772589)
            ·
              refine ⟨12363152781644888935789721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32968407417719703828772589 12363152781644888935789721)
              ·
                refine ⟨9272364586233666701842291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12363152781644888935789721 9272364586233666701842291)
                ·
                  refine ⟨13908546879350500052763437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9272364586233666701842291 13908546879350500052763437)
                  ·
                    refine ⟨5215705079756437519786289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13908546879350500052763437 5215705079756437519786289)
                    ·
                      refine ⟨3911778809817328139839717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5215705079756437519786289 3911778809817328139839717)
                      ·
                        rfl

theorem cell23_7618162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 3, 2, 1, 3, 2].length) (baseStart_7618162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7618162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7618162 prefixEnd_7618162 := by exact prefixLift 7618162
  have htrace : WordTrace (prefixWord ++ tailWord_7618162) baseStart_7618162 baseEnd_7618162 := by
    simpa [prefixWord, tailWord_7618162, baseEnd_7618162] using wordTrace_append hprefix tailTrace_7618162
  have hstable : (prefixWord ++ tailWord_7618162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7618162).length < 2 ^ (prefixWord ++ tailWord_7618162).sum := by decide
  have hdescent : baseEnd_7618162 < baseStart_7618162 := by decide
  rcases family_descends (prefixWord ++ tailWord_7618162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7618208 : List Nat := [2, 1, 1, 4, 3, 1, 1, 1, 1, 5, 3]
def baseStart_7618208 : Nat := 118140960795 + 7618208 * 2 ^ 59
def prefixEnd_7618208 : Nat := 4983230072969 + 3 ^ 40 * 7618208 * 2
def baseEnd_7618208 : Nat := 3911802429927434959864505

theorem tailTrace_7618208 : CollatzResearch.WordTrace tailWord_7618208 prefixEnd_7618208 3911802429927434959864505 := by
  unfold tailWord_7618208
  simp only [CollatzResearch.WordTrace]
  refine ⟨138929436392270488593367639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185239248523027318124490185 138929436392270488593367639)
  ·
    refine ⟨208394154588405732890051459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138929436392270488593367639 208394154588405732890051459)
    ·
      refine ⟨312591231882608599335077189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208394154588405732890051459 312591231882608599335077189)
      ·
        refine ⟨58610855977989112375326973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 312591231882608599335077189 58610855977989112375326973)
        ·
          refine ⟨21979070991745917140747615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58610855977989112375326973 21979070991745917140747615)
          ·
            refine ⟨32968606487618875711121423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21979070991745917140747615 32968606487618875711121423)
            ·
              refine ⟨49452909731428313566682135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32968606487618875711121423 49452909731428313566682135)
              ·
                refine ⟨74179364597142470350023203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49452909731428313566682135 74179364597142470350023203)
                ·
                  refine ⟨111269046895713705525034805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74179364597142470350023203 111269046895713705525034805)
                  ·
                    refine ⟨10431473146473159892972013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 111269046895713705525034805 10431473146473159892972013)
                    ·
                      refine ⟨3911802429927434959864505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10431473146473159892972013 3911802429927434959864505)
                      ·
                        rfl

theorem cell23_7618208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 1, 1, 5, 3].length) (baseStart_7618208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7618208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7618208 prefixEnd_7618208 := by exact prefixLift 7618208
  have htrace : WordTrace (prefixWord ++ tailWord_7618208) baseStart_7618208 baseEnd_7618208 := by
    simpa [prefixWord, tailWord_7618208, baseEnd_7618208] using wordTrace_append hprefix tailTrace_7618208
  have hstable : (prefixWord ++ tailWord_7618208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7618208).length < 2 ^ (prefixWord ++ tailWord_7618208).sum := by decide
  have hdescent : baseEnd_7618208 < baseStart_7618208 := by decide
  rcases family_descends (prefixWord ++ tailWord_7618208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7618211 : List Nat := [1, 1, 1, 4, 1, 1, 4, 2, 1, 7]
def baseStart_7618211 : Nat := 118140960795 + 7618211 * 2 ^ 59
def prefixEnd_7618211 : Nat := 4983230072969 + 3 ^ 40 * 7618211 * 2
def baseEnd_7618211 : Nat := 1303934656789799482708997

theorem tailTrace_7618211 : CollatzResearch.WordTrace tailWord_7618211 prefixEnd_7618211 1303934656789799482708997 := by
  unfold tailWord_7618211
  simp only [CollatzResearch.WordTrace]
  refine ⟨277858982203530108699094487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185239321469020072466062991 277858982203530108699094487)
  ·
    refine ⟨416788473305295163048641731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277858982203530108699094487 416788473305295163048641731)
    ·
      refine ⟨625182709957942744572962597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 416788473305295163048641731 625182709957942744572962597)
      ·
        refine ⟨117221758117114264607430487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 625182709957942744572962597 117221758117114264607430487)
        ·
          refine ⟨175832637175671396911145731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117221758117114264607430487 175832637175671396911145731)
          ·
            refine ⟨263748955763507095366718597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175832637175671396911145731 263748955763507095366718597)
            ·
              refine ⟨49452929205657580381259737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 263748955763507095366718597 49452929205657580381259737)
              ·
                refine ⟨37089696904243185285944803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49452929205657580381259737 37089696904243185285944803)
                ·
                  refine ⟨55634545356364777928917205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37089696904243185285944803 55634545356364777928917205)
                  ·
                    refine ⟨1303934656789799482708997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55634545356364777928917205 1303934656789799482708997)
                    ·
                      rfl

theorem cell23_7618211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 2, 1, 7].length) (baseStart_7618211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7618211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7618211 prefixEnd_7618211 := by exact prefixLift 7618211
  have htrace : WordTrace (prefixWord ++ tailWord_7618211) baseStart_7618211 baseEnd_7618211 := by
    simpa [prefixWord, tailWord_7618211, baseEnd_7618211] using wordTrace_append hprefix tailTrace_7618211
  have hstable : (prefixWord ++ tailWord_7618211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7618211).length < 2 ^ (prefixWord ++ tailWord_7618211).sum := by decide
  have hdescent : baseEnd_7618211 < baseStart_7618211 := by decide
  rcases family_descends (prefixWord ++ tailWord_7618211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7618248 : List Nat := [2, 1, 3, 1, 2, 2, 2, 1, 4, 1, 4]
def baseStart_7618248 : Nat := 118140960795 + 7618248 * 2 ^ 59
def prefixEnd_7618248 : Nat := 4983230072969 + 3 ^ 40 * 7618248 * 2
def baseEnd_7618248 : Nat := 3911822969153614803364321

theorem tailTrace_7618248 : CollatzResearch.WordTrace tailWord_7618248 prefixEnd_7618248 3911822969153614803364321 := by
  unfold tailWord_7618248
  simp only [CollatzResearch.WordTrace]
  refine ⟨138930165852198032009095699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185240221136264042678794265 138930165852198032009095699)
  ·
    refine ⟨208395248778297048013643549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138930165852198032009095699 208395248778297048013643549)
    ·
      refine ⟨78148218291861393005116331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208395248778297048013643549 78148218291861393005116331)
      ·
        refine ⟨117222327437792089507674497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78148218291861393005116331 117222327437792089507674497)
        ·
          refine ⟨87916745578344067130755873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117222327437792089507674497 87916745578344067130755873)
          ·
            refine ⟨65937559183758050348066905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87916745578344067130755873 65937559183758050348066905)
            ·
              refine ⟨49453169387818537761050179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65937559183758050348066905 49453169387818537761050179)
              ·
                refine ⟨74179754081727806641575269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49453169387818537761050179 74179754081727806641575269)
                ·
                  refine ⟨13908703890323963745295363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74179754081727806641575269 13908703890323963745295363)
                  ·
                    refine ⟨20863055835485945617943045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13908703890323963745295363 20863055835485945617943045)
                    ·
                      refine ⟨3911822969153614803364321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20863055835485945617943045 3911822969153614803364321)
                      ·
                        rfl

theorem cell23_7618248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 1, 4, 1, 4].length) (baseStart_7618248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7618248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7618248 prefixEnd_7618248 := by exact prefixLift 7618248
  have htrace : WordTrace (prefixWord ++ tailWord_7618248) baseStart_7618248 baseEnd_7618248 := by
    simpa [prefixWord, tailWord_7618248, baseEnd_7618248] using wordTrace_append hprefix tailTrace_7618248
  have hstable : (prefixWord ++ tailWord_7618248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7618248).length < 2 ^ (prefixWord ++ tailWord_7618248).sum := by decide
  have hdescent : baseEnd_7618248 < baseStart_7618248 := by decide
  rcases family_descends (prefixWord ++ tailWord_7618248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7618251 : List Nat := [1, 1, 1, 1, 3, 2, 1, 3, 2, 3, 5]
def baseStart_7618251 : Nat := 118140960795 + 7618251 * 2 ^ 59
def prefixEnd_7618251 : Nat := 4983230072969 + 3 ^ 40 * 7618251 * 2
def baseEnd_7618251 : Nat := 3911824509595578291626807

theorem tailTrace_7618251 : CollatzResearch.WordTrace tailWord_7618251 prefixEnd_7618251 3911824509595578291626807 := by
  unfold tailWord_7618251
  simp only [CollatzResearch.WordTrace]
  refine ⟨277860441123385195530550607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185240294082256797020367071 277860441123385195530550607)
  ·
    refine ⟨416790661685077793295825911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277860441123385195530550607 416790661685077793295825911)
    ·
      refine ⟨625185992527616689943738867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 416790661685077793295825911 625185992527616689943738867)
      ·
        refine ⟨937778988791425034915608301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 625185992527616689943738867 937778988791425034915608301)
        ·
          refine ⟨351667120796784388093353113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 937778988791425034915608301 351667120796784388093353113)
          ·
            refine ⟨263750340597588291070014835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 351667120796784388093353113 263750340597588291070014835)
            ·
              refine ⟨395625510896382436605022253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 263750340597588291070014835 395625510896382436605022253)
              ·
                refine ⟨148359566586143413726883345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 395625510896382436605022253 148359566586143413726883345)
                ·
                  refine ⟨111269674939607560295162509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 148359566586143413726883345 111269674939607560295162509)
                  ·
                    refine ⟨41726128102352835110685941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 111269674939607560295162509 41726128102352835110685941)
                    ·
                      refine ⟨3911824509595578291626807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41726128102352835110685941 3911824509595578291626807)
                      ·
                        rfl

theorem cell23_7618251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 2, 3, 5].length) (baseStart_7618251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7618251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7618251 prefixEnd_7618251 := by exact prefixLift 7618251
  have htrace : WordTrace (prefixWord ++ tailWord_7618251) baseStart_7618251 baseEnd_7618251 := by
    simpa [prefixWord, tailWord_7618251, baseEnd_7618251] using wordTrace_append hprefix tailTrace_7618251
  have hstable : (prefixWord ++ tailWord_7618251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7618251).length < 2 ^ (prefixWord ++ tailWord_7618251).sum := by decide
  have hdescent : baseEnd_7618251 < baseStart_7618251 := by decide
  rcases family_descends (prefixWord ++ tailWord_7618251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7618265 : List Nat := [1, 2, 1, 2, 3, 3, 2, 1, 2, 4, 2]
def baseStart_7618265 : Nat := 118140960795 + 7618265 * 2 ^ 59
def prefixEnd_7618265 : Nat := 4983230072969 + 3 ^ 40 * 7618265 * 2
def baseEnd_7618265 : Nat := 3911831698324741236851743

theorem tailTrace_7618265 : CollatzResearch.WordTrace tailWord_7618265 prefixEnd_7618265 3911831698324741236851743 := by
  unfold tailWord_7618265
  simp only [CollatzResearch.WordTrace]
  refine ⟨277860951745334475921560249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185240634496889650614373499 277860951745334475921560249)
  ·
    refine ⟨208395713809000856941170187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277860951745334475921560249 208395713809000856941170187)
    ·
      refine ⟨312593570713501285411755281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208395713809000856941170187 312593570713501285411755281)
      ·
        refine ⟨234445178035125964058816461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 312593570713501285411755281 234445178035125964058816461)
        ·
          refine ⟨87916941763172236522056173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 234445178035125964058816461 87916941763172236522056173)
          ·
            refine ⟨32968853161189588695771065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87916941763172236522056173 32968853161189588695771065)
            ·
              refine ⟨24726639870892191521828299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32968853161189588695771065 24726639870892191521828299)
              ·
                refine ⟨37089959806338287282742449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24726639870892191521828299 37089959806338287282742449)
                ·
                  refine ⟨27817469854753715462056837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37089959806338287282742449 27817469854753715462056837)
                  ·
                    refine ⟨5215775597766321649135657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27817469854753715462056837 5215775597766321649135657)
                    ·
                      refine ⟨3911831698324741236851743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5215775597766321649135657 3911831698324741236851743)
                      ·
                        rfl

theorem cell23_7618265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 1, 2, 4, 2].length) (baseStart_7618265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7618265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7618265 prefixEnd_7618265 := by exact prefixLift 7618265
  have htrace : WordTrace (prefixWord ++ tailWord_7618265) baseStart_7618265 baseEnd_7618265 := by
    simpa [prefixWord, tailWord_7618265, baseEnd_7618265] using wordTrace_append hprefix tailTrace_7618265
  have hstable : (prefixWord ++ tailWord_7618265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7618265).length < 2 ^ (prefixWord ++ tailWord_7618265).sum := by decide
  have hdescent : baseEnd_7618265 < baseStart_7618265 := by decide
  rcases family_descends (prefixWord ++ tailWord_7618265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7618285 : List Nat := [1, 5, 1, 2, 1, 2, 2, 1, 1, 4, 3]
def baseStart_7618285 : Nat := 118140960795 + 7618285 * 2 ^ 59
def prefixEnd_7618285 : Nat := 4983230072969 + 3 ^ 40 * 7618285 * 2
def baseEnd_7618285 : Nat := 3911841967937831158601651

theorem tailTrace_7618285 : CollatzResearch.WordTrace tailWord_7618285 prefixEnd_7618285 3911841967937831158601651 := by
  unfold tailWord_7618285
  simp only [CollatzResearch.WordTrace]
  refine ⟨277861681205262019337288309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185241120803508012891525539 277861681205262019337288309)
  ·
    refine ⟨26049532612993314312870779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 277861681205262019337288309 26049532612993314312870779)
    ·
      refine ⟨39074298919489971469306169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26049532612993314312870779 39074298919489971469306169)
      ·
        refine ⟨29305724189617478601979627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39074298919489971469306169 29305724189617478601979627)
        ·
          refine ⟨43958586284426217902969441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29305724189617478601979627 43958586284426217902969441)
          ·
            refine ⟨32968939713319663427227081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43958586284426217902969441 32968939713319663427227081)
            ·
              refine ⟨24726704784989747570420311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32968939713319663427227081 24726704784989747570420311)
              ·
                refine ⟨37090057177484621355630467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24726704784989747570420311 37090057177484621355630467)
                ·
                  refine ⟨55635085766226932033445701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37090057177484621355630467 55635085766226932033445701)
                  ·
                    refine ⟨10431578581167549756271069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55635085766226932033445701 10431578581167549756271069)
                    ·
                      refine ⟨3911841967937831158601651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10431578581167549756271069 3911841967937831158601651)
                      ·
                        rfl

theorem cell23_7618285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 1, 1, 4, 3].length) (baseStart_7618285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7618285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7618285 prefixEnd_7618285 := by exact prefixLift 7618285
  have htrace : WordTrace (prefixWord ++ tailWord_7618285) baseStart_7618285 baseEnd_7618285 := by
    simpa [prefixWord, tailWord_7618285, baseEnd_7618285] using wordTrace_append hprefix tailTrace_7618285
  have hstable : (prefixWord ++ tailWord_7618285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7618285).length < 2 ^ (prefixWord ++ tailWord_7618285).sum := by decide
  have hdescent : baseEnd_7618285 < baseStart_7618285 := by decide
  rcases family_descends (prefixWord ++ tailWord_7618285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7618322 : List Nat := [3, 2, 4, 1, 1, 2, 1, 3, 6]
def baseStart_7618322 : Nat := 118140960795 + 7618322 * 2 ^ 59
def prefixEnd_7618322 : Nat := 4983230072969 + 3 ^ 40 * 7618322 * 2
def baseEnd_7618322 : Nat := 434651218524671945982109

theorem tailTrace_7618322 : CollatzResearch.WordTrace tailWord_7618322 prefixEnd_7618322 434651218524671945982109 := by
  unfold tailWord_7618322
  simp only [CollatzResearch.WordTrace]
  refine ⟨69465757676531993664096305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185242020470751983104256813 69465757676531993664096305)
  ·
    refine ⟨52099318257398995248072229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69465757676531993664096305 52099318257398995248072229)
    ·
      refine ⟨9768622173262311609013543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52099318257398995248072229 9768622173262311609013543)
      ·
        refine ⟨14652933259893467413520315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9768622173262311609013543 14652933259893467413520315)
        ·
          refine ⟨21979399889840201120280473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14652933259893467413520315 21979399889840201120280473)
          ·
            refine ⟨16484549917380150840210355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21979399889840201120280473 16484549917380150840210355)
            ·
              refine ⟨24726824876070226260315533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16484549917380150840210355 24726824876070226260315533)
              ·
                refine ⟨9272559328526334847618325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24726824876070226260315533 9272559328526334847618325)
                ·
                  refine ⟨434651218524671945982109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9272559328526334847618325 434651218524671945982109)
                  ·
                    rfl

theorem cell23_7618322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 3, 6].length) (baseStart_7618322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7618322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7618322 prefixEnd_7618322 := by exact prefixLift 7618322
  have htrace : WordTrace (prefixWord ++ tailWord_7618322) baseStart_7618322 baseEnd_7618322 := by
    simpa [prefixWord, tailWord_7618322, baseEnd_7618322] using wordTrace_append hprefix tailTrace_7618322
  have hstable : (prefixWord ++ tailWord_7618322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7618322).length < 2 ^ (prefixWord ++ tailWord_7618322).sum := by decide
  have hdescent : baseEnd_7618322 < baseStart_7618322 := by decide
  rcases family_descends (prefixWord ++ tailWord_7618322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7618348 : List Nat := [2, 2, 1, 1, 1, 5, 1, 1, 3, 6]
def baseStart_7618348 : Nat := 118140960795 + 7618348 * 2 ^ 59
def prefixEnd_7618348 : Nat := 4983230072969 + 3 ^ 40 * 7618348 * 2
def baseEnd_7618348 : Nat := 1303958105739688137371287

theorem tailTrace_7618348 : CollatzResearch.WordTrace tailWord_7618348 prefixEnd_7618348 1303958105739688137371287 := by
  unfold tailWord_7618348
  simp only [CollatzResearch.WordTrace]
  refine ⟨138931989502016890548415849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185242652669355854064554465 138931989502016890548415849)
  ·
    refine ⟨104198992126512667911311887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138931989502016890548415849 104198992126512667911311887)
    ·
      refine ⟨156298488189769001866967831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104198992126512667911311887 156298488189769001866967831)
      ·
        refine ⟨234447732284653502800451747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156298488189769001866967831 234447732284653502800451747)
        ·
          refine ⟨351671598426980254200677621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234447732284653502800451747 351671598426980254200677621)
          ·
            refine ⟨32969212352529398831313527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 351671598426980254200677621 32969212352529398831313527)
            ·
              refine ⟨49453818528794098246970291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32969212352529398831313527 49453818528794098246970291)
              ·
                refine ⟨74180727793191147370455437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49453818528794098246970291 74180727793191147370455437)
                ·
                  refine ⟨27817772922446680263920789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74180727793191147370455437 27817772922446680263920789)
                  ·
                    refine ⟨1303958105739688137371287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27817772922446680263920789 1303958105739688137371287)
                    ·
                      rfl

theorem cell23_7618348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 6].length) (baseStart_7618348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7618348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7618348 prefixEnd_7618348 := by exact prefixLift 7618348
  have htrace : WordTrace (prefixWord ++ tailWord_7618348) baseStart_7618348 baseEnd_7618348 := by
    simpa [prefixWord, tailWord_7618348, baseEnd_7618348] using wordTrace_append hprefix tailTrace_7618348
  have hstable : (prefixWord ++ tailWord_7618348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7618348).length < 2 ^ (prefixWord ++ tailWord_7618348).sum := by decide
  have hdescent : baseEnd_7618348 < baseStart_7618348 := by decide
  rcases family_descends (prefixWord ++ tailWord_7618348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7618366 : List Nat := [4, 2, 1, 2, 2, 2, 1, 4, 1, 1, 3]
def baseStart_7618366 : Nat := 118140960795 + 7618366 * 2 ^ 59
def prefixEnd_7618366 : Nat := 4983230072969 + 3 ^ 40 * 7618366 * 2
def baseEnd_7618366 : Nat := 3911883559870845341688779

theorem tailTrace_7618366 : CollatzResearch.WordTrace tailWord_7618366 prefixEnd_7618366 3911883559870845341688779 := by
  unfold tailWord_7618366
  simp only [CollatzResearch.WordTrace]
  refine ⟨34733079439746071271373369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185243090345312380113991301 34733079439746071271373369)
  ·
    refine ⟨26049809579809553453530027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34733079439746071271373369 26049809579809553453530027)
    ·
      refine ⟨39074714369714330180295041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26049809579809553453530027 39074714369714330180295041)
      ·
        refine ⟨29306035777285747635221281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39074714369714330180295041 29306035777285747635221281)
        ·
          refine ⟨21979526832964310726415961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29306035777285747635221281 21979526832964310726415961)
          ·
            refine ⟨16484645124723233044811971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21979526832964310726415961 16484645124723233044811971)
            ·
              refine ⟨24726967687084849567217957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16484645124723233044811971 24726967687084849567217957)
              ·
                refine ⟨4636306441328409293853367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24726967687084849567217957 4636306441328409293853367)
                ·
                  refine ⟨6954459661992613940780051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4636306441328409293853367 6954459661992613940780051)
                  ·
                    refine ⟨10431689492988920911170077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6954459661992613940780051 10431689492988920911170077)
                    ·
                      refine ⟨3911883559870845341688779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10431689492988920911170077 3911883559870845341688779)
                      ·
                        rfl

theorem cell23_7618366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 4, 1, 1, 3].length) (baseStart_7618366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7618366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7618366 prefixEnd_7618366 := by exact prefixLift 7618366
  have htrace : WordTrace (prefixWord ++ tailWord_7618366) baseStart_7618366 baseEnd_7618366 := by
    simpa [prefixWord, tailWord_7618366, baseEnd_7618366] using wordTrace_append hprefix tailTrace_7618366
  have hstable : (prefixWord ++ tailWord_7618366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7618366).length < 2 ^ (prefixWord ++ tailWord_7618366).sum := by decide
  have hdescent : baseEnd_7618366 < baseStart_7618366 := by decide
  rcases family_descends (prefixWord ++ tailWord_7618366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7618375 : List Nat := [1, 1, 4, 1, 2, 1, 3, 2, 3, 2, 3]
def baseStart_7618375 : Nat := 118140960795 + 7618375 * 2 ^ 59
def prefixEnd_7618375 : Nat := 4983230072969 + 3 ^ 40 * 7618375 * 2
def baseEnd_7618375 : Nat := 3911888181196735806476237

theorem tailTrace_7618375 : CollatzResearch.WordTrace tailWord_7618375 prefixEnd_7618375 3911888181196735806476237 := by
  unfold tailWord_7618375
  simp only [CollatzResearch.WordTrace]
  refine ⟨277864963774935964708064579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185243309183290643138709719 277864963774935964708064579)
  ·
    refine ⟨416797445662403947062096869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277864963774935964708064579 416797445662403947062096869)
    ·
      refine ⟨78149521061700740074143163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 416797445662403947062096869 78149521061700740074143163)
      ·
        refine ⟨117224281592551110111214745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78149521061700740074143163 117224281592551110111214745)
        ·
          refine ⟨87918211194413332583411059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117224281592551110111214745 87918211194413332583411059)
          ·
            refine ⟨131877316791619998875116589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87918211194413332583411059 131877316791619998875116589)
            ·
              refine ⟨49453993796857499578168721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131877316791619998875116589 49453993796857499578168721)
              ·
                refine ⟨37090495347643124683626541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49453993796857499578168721 37090495347643124683626541)
                ·
                  refine ⟨13908935755366171756359953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37090495347643124683626541 13908935755366171756359953)
                  ·
                    refine ⟨10431701816524628817269965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13908935755366171756359953 10431701816524628817269965)
                    ·
                      refine ⟨3911888181196735806476237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10431701816524628817269965 3911888181196735806476237)
                      ·
                        rfl

theorem cell23_7618375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 2, 3, 2, 3].length) (baseStart_7618375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7618375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7618375 prefixEnd_7618375 := by exact prefixLift 7618375
  have htrace : WordTrace (prefixWord ++ tailWord_7618375) baseStart_7618375 baseEnd_7618375 := by
    simpa [prefixWord, tailWord_7618375, baseEnd_7618375] using wordTrace_append hprefix tailTrace_7618375
  have hstable : (prefixWord ++ tailWord_7618375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7618375).length < 2 ^ (prefixWord ++ tailWord_7618375).sum := by decide
  have hdescent : baseEnd_7618375 < baseStart_7618375 := by decide
  rcases family_descends (prefixWord ++ tailWord_7618375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7618385 : List Nat := [1, 2, 2, 1, 5, 1, 1, 3, 1, 2, 4]
def baseStart_7618385 : Nat := 118140960795 + 7618385 * 2 ^ 59
def prefixEnd_7618385 : Nat := 4983230072969 + 3 ^ 40 * 7618385 * 2
def baseEnd_7618385 : Nat := 3911893316003280767351191

theorem tailTrace_7618385 : CollatzResearch.WordTrace tailWord_7618385 prefixEnd_7618385 3911893316003280767351191 := by
  unfold tailWord_7618385
  simp only [CollatzResearch.WordTrace]
  refine ⟨277865328504899736415928609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185243552336599824277285739 277865328504899736415928609)
  ·
    refine ⟨208398996378674802311946457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277865328504899736415928609 208398996378674802311946457)
    ·
      refine ⟨156299247284006101733959843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208398996378674802311946457 156299247284006101733959843)
      ·
        refine ⟨234448870926009152600939765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156299247284006101733959843 234448870926009152600939765)
        ·
          refine ⟨21979581649313358056338103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 234448870926009152600939765 21979581649313358056338103)
          ·
            refine ⟨32969372473970037084507155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21979581649313358056338103 32969372473970037084507155)
            ·
              refine ⟨49454058710955055626760733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32969372473970037084507155 49454058710955055626760733)
              ·
                refine ⟨18545272016608145860035275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49454058710955055626760733 18545272016608145860035275)
                ·
                  refine ⟨27817908024912218790052913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18545272016608145860035275 27817908024912218790052913)
                  ·
                    refine ⟨20863431018684164092539685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27817908024912218790052913 20863431018684164092539685)
                    ·
                      refine ⟨3911893316003280767351191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20863431018684164092539685 3911893316003280767351191)
                      ·
                        rfl

theorem cell23_7618385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 3, 1, 2, 4].length) (baseStart_7618385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7618385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7618385 prefixEnd_7618385 := by exact prefixLift 7618385
  have htrace : WordTrace (prefixWord ++ tailWord_7618385) baseStart_7618385 baseEnd_7618385 := by
    simpa [prefixWord, tailWord_7618385, baseEnd_7618385] using wordTrace_append hprefix tailTrace_7618385
  have hstable : (prefixWord ++ tailWord_7618385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7618385).length < 2 ^ (prefixWord ++ tailWord_7618385).sum := by decide
  have hdescent : baseEnd_7618385 < baseStart_7618385 := by decide
  rcases family_descends (prefixWord ++ tailWord_7618385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7618389 : List Nat := [1, 3, 2, 2, 2, 3, 1, 2, 3, 2, 2]
def baseStart_7618389 : Nat := 118140960795 + 7618389 * 2 ^ 59
def prefixEnd_7618389 : Nat := 4983230072969 + 3 ^ 40 * 7618389 * 2
def baseEnd_7618389 : Nat := 3911895369925898751701173

theorem tailTrace_7618389 : CollatzResearch.WordTrace tailWord_7618389 prefixEnd_7618389 3911895369925898751701173 := by
  unfold tailWord_7618389
  simp only [CollatzResearch.WordTrace]
  refine ⟨277865474396885245099074221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185243649597923496732716147 277865474396885245099074221)
  ·
    refine ⟨104199552898831966912152833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 277865474396885245099074221 104199552898831966912152833)
    ·
      refine ⟨78149664674123975184114625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104199552898831966912152833 78149664674123975184114625)
      ·
        refine ⟨58612248505592981388085969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78149664674123975184114625 58612248505592981388085969)
        ·
          refine ⟨43959186379194736041064477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58612248505592981388085969 43959186379194736041064477)
          ·
            refine ⟨16484694892198026015399179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43959186379194736041064477 16484694892198026015399179)
            ·
              refine ⟨24727042338297039023098769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16484694892198026015399179 24727042338297039023098769)
              ·
                refine ⟨18545281753722779267324077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24727042338297039023098769 18545281753722779267324077)
                ·
                  refine ⟨6954480657646042225246529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18545281753722779267324077 6954480657646042225246529)
                  ·
                    refine ⟨5215860493234531668934897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6954480657646042225246529 5215860493234531668934897)
                    ·
                      refine ⟨3911895369925898751701173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5215860493234531668934897 3911895369925898751701173)
                      ·
                        rfl

theorem cell23_7618389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 2, 3, 2, 2].length) (baseStart_7618389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7618389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7618389 prefixEnd_7618389 := by exact prefixLift 7618389
  have htrace : WordTrace (prefixWord ++ tailWord_7618389) baseStart_7618389 baseEnd_7618389 := by
    simpa [prefixWord, tailWord_7618389, baseEnd_7618389] using wordTrace_append hprefix tailTrace_7618389
  have hstable : (prefixWord ++ tailWord_7618389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7618389).length < 2 ^ (prefixWord ++ tailWord_7618389).sum := by decide
  have hdescent : baseEnd_7618389 < baseStart_7618389 := by decide
  rcases family_descends (prefixWord ++ tailWord_7618389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7618402 : List Nat := [3, 3, 2, 1, 2, 1, 2, 2, 1, 2, 4]
def baseStart_7618402 : Nat := 118140960795 + 7618402 * 2 ^ 59
def prefixEnd_7618402 : Nat := 4983230072969 + 3 ^ 40 * 7618402 * 2
def baseEnd_7618402 : Nat := 3911902045174407200838613

theorem tailTrace_7618402 : CollatzResearch.WordTrace tailWord_7618402 prefixEnd_7618402 3911902045174407200838613 := by
  unfold tailWord_7618402
  simp only [CollatzResearch.WordTrace]
  refine ⟨69466487136459537079824365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185243965697225432212864973 69466487136459537079824365)
  ·
    refine ⟨26049932676172326404934137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69466487136459537079824365 26049932676172326404934137)
    ·
      refine ⟨19537449507129244803700603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26049932676172326404934137 19537449507129244803700603)
      ·
        refine ⟨29306174260693867205550905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19537449507129244803700603 29306174260693867205550905)
        ·
          refine ⟨21979630695520400404163179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29306174260693867205550905 21979630695520400404163179)
          ·
            refine ⟨32969446043280600606244769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21979630695520400404163179 32969446043280600606244769)
            ·
              refine ⟨24727084532460450454683577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32969446043280600606244769 24727084532460450454683577)
              ·
                refine ⟨18545313399345337841012683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24727084532460450454683577 18545313399345337841012683)
                ·
                  refine ⟨27817970099018006761519025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18545313399345337841012683 27817970099018006761519025)
                  ·
                    refine ⟨20863477574263505071139269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27817970099018006761519025 20863477574263505071139269)
                    ·
                      refine ⟨3911902045174407200838613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20863477574263505071139269 3911902045174407200838613)
                      ·
                        rfl

theorem cell23_7618402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_7618402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7618402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7618402 prefixEnd_7618402 := by exact prefixLift 7618402
  have htrace : WordTrace (prefixWord ++ tailWord_7618402) baseStart_7618402 baseEnd_7618402 := by
    simpa [prefixWord, tailWord_7618402, baseEnd_7618402] using wordTrace_append hprefix tailTrace_7618402
  have hstable : (prefixWord ++ tailWord_7618402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7618402).length < 2 ^ (prefixWord ++ tailWord_7618402).sum := by decide
  have hdescent : baseEnd_7618402 < baseStart_7618402 := by decide
  rcases family_descends (prefixWord ++ tailWord_7618402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7618439 : List Nat := [1, 1, 4, 2, 4, 2, 1, 1, 1, 3, 3]
def baseStart_7618439 : Nat := 118140960795 + 7618439 * 2 ^ 59
def prefixEnd_7618439 : Nat := 4983230072969 + 3 ^ 40 * 7618439 * 2
def baseEnd_7618439 : Nat := 3911921043958623556075943

theorem tailTrace_7618439 : CollatzResearch.WordTrace tailWord_7618439 prefixEnd_7618439 3911921043958623556075943 := by
  unfold tailWord_7618439
  simp only [CollatzResearch.WordTrace]
  refine ⟨277867298046704103638394371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185244865364469402425596247 277867298046704103638394371)
  ·
    refine ⟨416800947070056155457591557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277867298046704103638394371 416800947070056155457591557)
    ·
      refine ⟨78150177575635529148298417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 416800947070056155457591557 78150177575635529148298417)
      ·
        refine ⟨58612633181726646861223813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78150177575635529148298417 58612633181726646861223813)
        ·
          refine ⟨10989868721573746286479465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58612633181726646861223813 10989868721573746286479465)
          ·
            refine ⟨8242401541180309714859599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10989868721573746286479465 8242401541180309714859599)
            ·
              refine ⟨12363602311770464572289399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8242401541180309714859599 12363602311770464572289399)
              ·
                refine ⟨18545403467655696858434099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12363602311770464572289399 18545403467655696858434099)
                ·
                  refine ⟨27818105201483545287651149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18545403467655696858434099 27818105201483545287651149)
                  ·
                    refine ⟨10431789450556329482869181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27818105201483545287651149 10431789450556329482869181)
                    ·
                      refine ⟨3911921043958623556075943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10431789450556329482869181 3911921043958623556075943)
                      ·
                        rfl

theorem cell23_7618439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 1, 1, 1, 3, 3].length) (baseStart_7618439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7618439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7618439 prefixEnd_7618439 := by exact prefixLift 7618439
  have htrace : WordTrace (prefixWord ++ tailWord_7618439) baseStart_7618439 baseEnd_7618439 := by
    simpa [prefixWord, tailWord_7618439, baseEnd_7618439] using wordTrace_append hprefix tailTrace_7618439
  have hstable : (prefixWord ++ tailWord_7618439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7618439).length < 2 ^ (prefixWord ++ tailWord_7618439).sum := by decide
  have hdescent : baseEnd_7618439 < baseStart_7618439 := by decide
  rcases family_descends (prefixWord ++ tailWord_7618439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7618446 : List Nat := [4, 1, 1, 5, 2, 1, 2, 7]
def baseStart_7618446 : Nat := 118140960795 + 7618446 * 2 ^ 59
def prefixEnd_7618446 : Nat := 4983230072969 + 3 ^ 40 * 7618446 * 2
def baseEnd_7618446 : Nat := 144886097715674260321793

theorem tailTrace_7618446 : CollatzResearch.WordTrace tailWord_7618446 prefixEnd_7618446 144886097715674260321793 := by
  unfold tailWord_7618446
  simp only [CollatzResearch.WordTrace]
  refine ⟨34733444169709842979237399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185245035571785829222599461 34733444169709842979237399)
  ·
    refine ⟨52100166254564764468856099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34733444169709842979237399 52100166254564764468856099)
    ·
      refine ⟨78150249381847146703284149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52100166254564764468856099 78150249381847146703284149)
      ·
        refine ⟨7326585879548170003432889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 78150249381847146703284149 7326585879548170003432889)
        ·
          refine ⟨5494939409661127502574667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7326585879548170003432889 5494939409661127502574667)
          ·
            refine ⟨8242409114491691253862001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5494939409661127502574667 8242409114491691253862001)
            ·
              refine ⟨6181806835868768440396501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8242409114491691253862001 6181806835868768440396501)
              ·
                refine ⟨144886097715674260321793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6181806835868768440396501 144886097715674260321793)
                ·
                  rfl

theorem cell23_7618446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 2, 7].length) (baseStart_7618446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7618446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7618446 prefixEnd_7618446 := by exact prefixLift 7618446
  have htrace : WordTrace (prefixWord ++ tailWord_7618446) baseStart_7618446 baseEnd_7618446 := by
    simpa [prefixWord, tailWord_7618446, baseEnd_7618446] using wordTrace_append hprefix tailTrace_7618446
  have hstable : (prefixWord ++ tailWord_7618446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7618446).length < 2 ^ (prefixWord ++ tailWord_7618446).sum := by decide
  have hdescent : baseEnd_7618446 < baseStart_7618446 := by decide
  rcases family_descends (prefixWord ++ tailWord_7618446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7618479 : List Nat := [1, 1, 2, 1, 2, 2, 4, 4, 2, 2, 2]
def baseStart_7618479 : Nat := 118140960795 + 7618479 * 2 ^ 59
def prefixEnd_7618479 : Nat := 4983230072969 + 3 ^ 40 * 7618479 * 2
def baseEnd_7618479 : Nat := 3911941583184803399575759

theorem tailTrace_7618479 : CollatzResearch.WordTrace tailWord_7618479 prefixEnd_7618479 3911941583184803399575759 := by
  unfold tailWord_7618479
  simp only [CollatzResearch.WordTrace]
  refine ⟨277868756966559190469850491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185245837977706126979900327 277868756966559190469850491)
  ·
    refine ⟨416803135449838785704775737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277868756966559190469850491 416803135449838785704775737)
    ·
      refine ⟨312602351587379089278581803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 416803135449838785704775737 312602351587379089278581803)
      ·
        refine ⟨468903527381068633917872705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312602351587379089278581803 468903527381068633917872705)
        ·
          refine ⟨351677645535801475438404529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 468903527381068633917872705 351677645535801475438404529)
          ·
            refine ⟨263758234151851106578803397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 351677645535801475438404529 263758234151851106578803397)
            ·
              refine ⟨49454668903472082483525637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 263758234151851106578803397 49454668903472082483525637)
              ·
                refine ⟨9272750419401015465661057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49454668903472082483525637 9272750419401015465661057)
                ·
                  refine ⟨6954562814550761599245793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9272750419401015465661057 6954562814550761599245793)
                  ·
                    refine ⟨5215922110913071199434345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6954562814550761599245793 5215922110913071199434345)
                    ·
                      refine ⟨3911941583184803399575759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5215922110913071199434345 3911941583184803399575759)
                      ·
                        rfl

theorem cell23_7618479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 4, 2, 2, 2].length) (baseStart_7618479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7618479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7618479 prefixEnd_7618479 := by exact prefixLift 7618479
  have htrace : WordTrace (prefixWord ++ tailWord_7618479) baseStart_7618479 baseEnd_7618479 := by
    simpa [prefixWord, tailWord_7618479, baseEnd_7618479] using wordTrace_append hprefix tailTrace_7618479
  have hstable : (prefixWord ++ tailWord_7618479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7618479).length < 2 ^ (prefixWord ++ tailWord_7618479).sum := by decide
  have hdescent : baseEnd_7618479 < baseStart_7618479 := by decide
  rcases family_descends (prefixWord ++ tailWord_7618479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7618495 : List Nat := [1, 1, 2, 2, 2, 1, 4, 1, 1, 5, 3]
def baseStart_7618495 : Nat := 118140960795 + 7618495 * 2 ^ 59
def prefixEnd_7618495 : Nat := 4983230072969 + 3 ^ 40 * 7618495 * 2
def baseEnd_7618495 : Nat := 3911949798875275336975685

theorem tailTrace_7618495 : CollatzResearch.WordTrace tailWord_7618495 prefixEnd_7618495 3911949798875275336975685 := by
  unfold tailWord_7618495
  simp only [CollatzResearch.WordTrace]
  refine ⟨277869340534501225202432939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185246227023000816801621959 277869340534501225202432939)
  ·
    refine ⟨416804010801751837803649409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277869340534501225202432939 416804010801751837803649409)
    ·
      refine ⟨312603008101313878352737057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 416804010801751837803649409 312603008101313878352737057)
      ·
        refine ⟨234452256075985408764552793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 312603008101313878352737057 234452256075985408764552793)
        ·
          refine ⟨175839192056989056573414595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234452256075985408764552793 175839192056989056573414595)
          ·
            refine ⟨263758788085483584860121893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175839192056989056573414595 263758788085483584860121893)
            ·
              refine ⟨49454772766028172161272855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 263758788085483584860121893 49454772766028172161272855)
              ·
                refine ⟨74182159149042258241909283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49454772766028172161272855 74182159149042258241909283)
                ·
                  refine ⟨111273238723563387362863925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74182159149042258241909283 111273238723563387362863925)
                  ·
                    refine ⟨10431866130334067565268493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 111273238723563387362863925 10431866130334067565268493)
                    ·
                      refine ⟨3911949798875275336975685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10431866130334067565268493 3911949798875275336975685)
                      ·
                        rfl

theorem cell23_7618495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 1, 1, 5, 3].length) (baseStart_7618495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7618495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7618495 prefixEnd_7618495 := by exact prefixLift 7618495
  have htrace : WordTrace (prefixWord ++ tailWord_7618495) baseStart_7618495 baseEnd_7618495 := by
    simpa [prefixWord, tailWord_7618495, baseEnd_7618495] using wordTrace_append hprefix tailTrace_7618495
  have hstable : (prefixWord ++ tailWord_7618495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7618495).length < 2 ^ (prefixWord ++ tailWord_7618495).sum := by decide
  have hdescent : baseEnd_7618495 < baseStart_7618495 := by decide
  rcases family_descends (prefixWord ++ tailWord_7618495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7618530 : List Nat := [3, 3, 3, 1, 2, 1, 2, 2, 2, 2, 2]
def baseStart_7618530 : Nat := 118140960795 + 7618530 * 2 ^ 59
def prefixEnd_7618530 : Nat := 4983230072969 + 3 ^ 40 * 7618530 * 2
def baseEnd_7618530 : Nat := 3911967770698182700038025

theorem tailTrace_7618530 : CollatzResearch.WordTrace tailWord_7618530 prefixEnd_7618530 3911967770698182700038025 := by
  unfold tailWord_7618530
  simp only [CollatzResearch.WordTrace]
  refine ⟨69467654272343606544989261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185247078059582950786638029 69467654272343606544989261)
  ·
    refine ⟨26050370352128852454370973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69467654272343606544989261 26050370352128852454370973)
    ·
      refine ⟨9768888882048319670389115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26050370352128852454370973 9768888882048319670389115)
      ·
        refine ⟨14653333323072479505583673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9768888882048319670389115 14653333323072479505583673)
        ·
          refine ⟨10989999992304359629187755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14653333323072479505583673 10989999992304359629187755)
          ·
            refine ⟨16484999988456539443781633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10989999992304359629187755 16484999988456539443781633)
            ·
              refine ⟨12363749991342404582836225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16484999988456539443781633 12363749991342404582836225)
              ·
                refine ⟨9272812493506803437127169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12363749991342404582836225 9272812493506803437127169)
                ·
                  refine ⟨6954609370130102577845377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9272812493506803437127169 6954609370130102577845377)
                  ·
                    refine ⟨5215957027597576933384033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6954609370130102577845377 5215957027597576933384033)
                    ·
                      refine ⟨3911967770698182700038025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5215957027597576933384033 3911967770698182700038025)
                      ·
                        rfl

theorem cell23_7618530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 2, 2, 2, 2, 2].length) (baseStart_7618530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7618530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7618530 prefixEnd_7618530 := by exact prefixLift 7618530
  have htrace : WordTrace (prefixWord ++ tailWord_7618530) baseStart_7618530 baseEnd_7618530 := by
    simpa [prefixWord, tailWord_7618530, baseEnd_7618530] using wordTrace_append hprefix tailTrace_7618530
  have hstable : (prefixWord ++ tailWord_7618530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7618530).length < 2 ^ (prefixWord ++ tailWord_7618530).sum := by decide
  have hdescent : baseEnd_7618530 < baseStart_7618530 := by decide
  rcases family_descends (prefixWord ++ tailWord_7618530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7618542 : List Nat := [4, 1, 2, 1, 3, 1, 2, 1, 1, 2, 5]
def baseStart_7618542 : Nat := 118140960795 + 7618542 * 2 ^ 59
def prefixEnd_7618542 : Nat := 4983230072969 + 3 ^ 40 * 7618542 * 2
def baseEnd_7618542 : Nat := 3911973932466036653087969

theorem tailTrace_7618542 : CollatzResearch.WordTrace tailWord_7618542 prefixEnd_7618542 3911973932466036653087969 := by
  unfold tailWord_7618542
  simp only [CollatzResearch.WordTrace]
  refine ⟨34733881845666369028674235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185247369843553968152929253 34733881845666369028674235)
  ·
    refine ⟨52100822768499553543011353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34733881845666369028674235 52100822768499553543011353)
    ·
      refine ⟨39075617076374665157258515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52100822768499553543011353 39075617076374665157258515)
      ·
        refine ⟨58613425614561997735887773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39075617076374665157258515 58613425614561997735887773)
        ·
          refine ⟨21980034605460749150957915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58613425614561997735887773 21980034605460749150957915)
          ·
            refine ⟨32970051908191123726436873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21980034605460749150957915 32970051908191123726436873)
            ·
              refine ⟨24727538931143342794827655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32970051908191123726436873 24727538931143342794827655)
              ·
                refine ⟨37091308396715014192241483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24727538931143342794827655 37091308396715014192241483)
                ·
                  refine ⟨55636962595072521288362225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37091308396715014192241483 55636962595072521288362225)
                  ·
                    refine ⟨41727721946304390966271669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55636962595072521288362225 41727721946304390966271669)
                    ·
                      refine ⟨3911973932466036653087969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41727721946304390966271669 3911973932466036653087969)
                      ·
                        rfl

theorem cell23_7618542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 1, 1, 2, 5].length) (baseStart_7618542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7618542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7618542 prefixEnd_7618542 := by exact prefixLift 7618542
  have htrace : WordTrace (prefixWord ++ tailWord_7618542) baseStart_7618542 baseEnd_7618542 := by
    simpa [prefixWord, tailWord_7618542, baseEnd_7618542] using wordTrace_append hprefix tailTrace_7618542
  have hstable : (prefixWord ++ tailWord_7618542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7618542).length < 2 ^ (prefixWord ++ tailWord_7618542).sum := by decide
  have hdescent : baseEnd_7618542 < baseStart_7618542 := by decide
  rcases family_descends (prefixWord ++ tailWord_7618542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7618552 : List Nat := [2, 1, 2, 1, 1, 3, 3, 1, 1, 6, 2]
def baseStart_7618552 : Nat := 118140960795 + 7618552 * 2 ^ 59
def prefixEnd_7618552 : Nat := 4983230072969 + 3 ^ 40 * 7618552 * 2
def baseEnd_7618552 : Nat := 3911979067272581613962923

theorem tailTrace_7618552 : CollatzResearch.WordTrace tailWord_7618552 prefixEnd_7618552 3911979067272581613962923 := by
  unfold tailWord_7618552
  simp only [CollatzResearch.WordTrace]
  refine ⟨138935709747647361968628955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185247612996863149291505273 138935709747647361968628955)
  ·
    refine ⟨208403564621471042952943433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138935709747647361968628955 208403564621471042952943433)
    ·
      refine ⟨156302673466103282214707575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208403564621471042952943433 156302673466103282214707575)
      ·
        refine ⟨234454010199154923322061363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156302673466103282214707575 234454010199154923322061363)
        ·
          refine ⟨351681015298732384983092045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234454010199154923322061363 351681015298732384983092045)
          ·
            refine ⟨131880380737024644368659517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 351681015298732384983092045 131880380737024644368659517)
            ·
              refine ⟨49455142776384241638247319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131880380737024644368659517 49455142776384241638247319)
              ·
                refine ⟨74182714164576362457370979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49455142776384241638247319 74182714164576362457370979)
                ·
                  refine ⟨111274071246864543686056469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74182714164576362457370979 111274071246864543686056469)
                  ·
                    refine ⟨5215972089696775485283897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 111274071246864543686056469 5215972089696775485283897)
                    ·
                      refine ⟨3911979067272581613962923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5215972089696775485283897 3911979067272581613962923)
                      ·
                        rfl

theorem cell23_7618552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 1, 1, 6, 2].length) (baseStart_7618552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7618552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7618552 prefixEnd_7618552 := by exact prefixLift 7618552
  have htrace : WordTrace (prefixWord ++ tailWord_7618552) baseStart_7618552 baseEnd_7618552 := by
    simpa [prefixWord, tailWord_7618552, baseEnd_7618552] using wordTrace_append hprefix tailTrace_7618552
  have hstable : (prefixWord ++ tailWord_7618552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7618552).length < 2 ^ (prefixWord ++ tailWord_7618552).sum := by decide
  have hdescent : baseEnd_7618552 < baseStart_7618552 := by decide
  rcases family_descends (prefixWord ++ tailWord_7618552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7618572 : List Nat := [2, 2, 1, 2, 3, 1, 3, 1, 1, 4, 3]
def baseStart_7618572 : Nat := 118140960795 + 7618572 * 2 ^ 59
def prefixEnd_7618572 : Nat := 4983230072969 + 3 ^ 40 * 7618572 * 2
def baseEnd_7618572 : Nat := 3911989336885671535712831

theorem tailTrace_7618572 : CollatzResearch.WordTrace tailWord_7618572 prefixEnd_7618572 3911989336885671535712831 := by
  unfold tailWord_7618572
  simp only [CollatzResearch.WordTrace]
  refine ⟨138936074477611133676492985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185248099303481511568657313 138936074477611133676492985)
  ·
    refine ⟨104202055858208350257369739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138936074477611133676492985 104202055858208350257369739)
    ·
      refine ⟨156303083787312525386054609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104202055858208350257369739 156303083787312525386054609)
      ·
        refine ⟨117227312840484394039540957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156303083787312525386054609 117227312840484394039540957)
        ·
          refine ⟨43960242315181647764827859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117227312840484394039540957 43960242315181647764827859)
          ·
            refine ⟨65940363472772471647241789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43960242315181647764827859 65940363472772471647241789)
            ·
              refine ⟨24727636302289676867715671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65940363472772471647241789 24727636302289676867715671)
              ·
                refine ⟨37091454453434515301573507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24727636302289676867715671 37091454453434515301573507)
                ·
                  refine ⟨55637181680151772952360261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37091454453434515301573507 55637181680151772952360261)
                  ·
                    refine ⟨10431971565028457428567549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55637181680151772952360261 10431971565028457428567549)
                    ·
                      refine ⟨3911989336885671535712831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10431971565028457428567549 3911989336885671535712831)
                      ·
                        rfl

theorem cell23_7618572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 1, 1, 4, 3].length) (baseStart_7618572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7618572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7618572 prefixEnd_7618572 := by exact prefixLift 7618572
  have htrace : WordTrace (prefixWord ++ tailWord_7618572) baseStart_7618572 baseEnd_7618572 := by
    simpa [prefixWord, tailWord_7618572, baseEnd_7618572] using wordTrace_append hprefix tailTrace_7618572
  have hstable : (prefixWord ++ tailWord_7618572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7618572).length < 2 ^ (prefixWord ++ tailWord_7618572).sum := by decide
  have hdescent : baseEnd_7618572 < baseStart_7618572 := by decide
  rcases family_descends (prefixWord ++ tailWord_7618572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7618579 : List Nat := [1, 1, 1, 2, 1, 4, 3, 5, 1, 4]
def baseStart_7618579 : Nat := 118140960795 + 7618579 * 2 ^ 59
def prefixEnd_7618579 : Nat := 4983230072969 + 3 ^ 40 * 7618579 * 2
def baseEnd_7618579 : Nat := 1303997643750084336108433

theorem tailTrace_7618579 : CollatzResearch.WordTrace tailWord_7618579 prefixEnd_7618579 1303997643750084336108433 := by
  unfold tailWord_7618579
  simp only [CollatzResearch.WordTrace]
  refine ⟨277872404266196907548490791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185248269510797938365660527 277872404266196907548490791)
  ·
    refine ⟨416808606399295361322736187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277872404266196907548490791 416808606399295361322736187)
    ·
      refine ⟨625212909598943041984104281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 416808606399295361322736187 625212909598943041984104281)
      ·
        refine ⟨468909682199207281488078211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 625212909598943041984104281 468909682199207281488078211)
        ·
          refine ⟨703364523298810922232117317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 468909682199207281488078211 703364523298810922232117317)
          ·
            refine ⟨131880848118527047918521997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 703364523298810922232117317 131880848118527047918521997)
            ·
              refine ⟨49455318044447642969445749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131880848118527047918521997 49455318044447642969445749)
              ·
                refine ⟨4636436066666966528385539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49455318044447642969445749 4636436066666966528385539)
                ·
                  refine ⟨6954654100000449792578309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4636436066666966528385539 6954654100000449792578309)
                  ·
                    refine ⟨1303997643750084336108433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6954654100000449792578309 1303997643750084336108433)
                    ·
                      rfl

theorem cell23_7618579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 5, 1, 4].length) (baseStart_7618579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7618579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7618579 prefixEnd_7618579 := by exact prefixLift 7618579
  have htrace : WordTrace (prefixWord ++ tailWord_7618579) baseStart_7618579 baseEnd_7618579 := by
    simpa [prefixWord, tailWord_7618579, baseEnd_7618579] using wordTrace_append hprefix tailTrace_7618579
  have hstable : (prefixWord ++ tailWord_7618579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7618579).length < 2 ^ (prefixWord ++ tailWord_7618579).sum := by decide
  have hdescent : baseEnd_7618579 < baseStart_7618579 := by decide
  rcases family_descends (prefixWord ++ tailWord_7618579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7618595 : List Nat := [1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 8]
def baseStart_7618595 : Nat := 118140960795 + 7618595 * 2 ^ 59
def prefixEnd_7618595 : Nat := 4983230072969 + 3 ^ 40 * 7618595 * 2
def baseEnd_7618595 : Nat := 3912001146940724945725225

theorem tailTrace_7618595 : CollatzResearch.WordTrace tailWord_7618595 prefixEnd_7618595 3912001146940724945725225 := by
  unfold tailWord_7618595
  simp only [CollatzResearch.WordTrace]
  refine ⟨277872987834138942281073239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185248658556092628187382159 277872987834138942281073239)
  ·
    refine ⟨416809481751208413421609859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277872987834138942281073239 416809481751208413421609859)
    ·
      refine ⟨625214222626812620132414789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 416809481751208413421609859 625214222626812620132414789)
      ·
        refine ⟨117227666742527366274827773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 625214222626812620132414789 117227666742527366274827773)
        ·
          refine ⟨43960375028447762353060415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117227666742527366274827773 43960375028447762353060415)
          ·
            refine ⟨65940562542671643529590623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43960375028447762353060415 65940562542671643529590623)
            ·
              refine ⟨98910843814007465294385935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65940562542671643529590623 98910843814007465294385935)
              ·
                refine ⟨148366265721011197941578903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98910843814007465294385935 148366265721011197941578903)
                ·
                  refine ⟨222549398581516796912368355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 148366265721011197941578903 222549398581516796912368355)
                  ·
                    refine ⟨333824097872275195368552533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 222549398581516796912368355 333824097872275195368552533)
                    ·
                      refine ⟨3912001146940724945725225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 333824097872275195368552533 3912001146940724945725225)
                      ·
                        rfl

theorem cell23_7618595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 8].length) (baseStart_7618595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7618595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7618595 prefixEnd_7618595 := by exact prefixLift 7618595
  have htrace : WordTrace (prefixWord ++ tailWord_7618595) baseStart_7618595 baseEnd_7618595 := by
    simpa [prefixWord, tailWord_7618595, baseEnd_7618595] using wordTrace_append hprefix tailTrace_7618595
  have hstable : (prefixWord ++ tailWord_7618595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7618595).length < 2 ^ (prefixWord ++ tailWord_7618595).sum := by decide
  have hdescent : baseEnd_7618595 < baseStart_7618595 := by decide
  rcases family_descends (prefixWord ++ tailWord_7618595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7618596 : List Nat := [2, 3, 1, 4, 2, 1, 2, 1, 3, 4]
def baseStart_7618596 : Nat := 118140960795 + 7618596 * 2 ^ 59
def prefixEnd_7618596 : Nat := 4983230072969 + 3 ^ 40 * 7618596 * 2
def baseEnd_7618596 : Nat := 1304000553473793147270907

theorem tailTrace_7618596 : CollatzResearch.WordTrace tailWord_7618596 prefixEnd_7618596 1304000553473793147270907 := by
  unfold tailWord_7618596
  simp only [CollatzResearch.WordTrace]
  refine ⟨138936512153567659725929821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185248682871423546301239761 138936512153567659725929821)
  ·
    refine ⟨52101192057587872397223683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138936512153567659725929821 52101192057587872397223683)
    ·
      refine ⟨78151788086381808595835525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52101192057587872397223683 78151788086381808595835525)
      ·
        refine ⟨14653460266196589111719161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78151788086381808595835525 14653460266196589111719161)
        ·
          refine ⟨10990095199647441833789371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14653460266196589111719161 10990095199647441833789371)
          ·
            refine ⟨16485142799471162750684057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10990095199647441833789371 16485142799471162750684057)
            ·
              refine ⟨12363857099603372063013043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16485142799471162750684057 12363857099603372063013043)
              ·
                refine ⟨18545785649405058094519565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12363857099603372063013043 18545785649405058094519565)
                ·
                  refine ⟨6954669618526896785444837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18545785649405058094519565 6954669618526896785444837)
                  ·
                    refine ⟨1304000553473793147270907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6954669618526896785444837 1304000553473793147270907)
                    ·
                      rfl

theorem cell23_7618596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 2, 1, 3, 4].length) (baseStart_7618596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7618596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7618596 prefixEnd_7618596 := by exact prefixLift 7618596
  have htrace : WordTrace (prefixWord ++ tailWord_7618596) baseStart_7618596 baseEnd_7618596 := by
    simpa [prefixWord, tailWord_7618596, baseEnd_7618596] using wordTrace_append hprefix tailTrace_7618596
  have hstable : (prefixWord ++ tailWord_7618596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7618596).length < 2 ^ (prefixWord ++ tailWord_7618596).sum := by decide
  have hdescent : baseEnd_7618596 < baseStart_7618596 := by decide
  rcases family_descends (prefixWord ++ tailWord_7618596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7618609 : List Nat := [1, 2, 2, 3, 1, 4, 3, 1, 6]
def baseStart_7618609 : Nat := 118140960795 + 7618609 * 2 ^ 59
def prefixEnd_7618609 : Nat := 4983230072969 + 3 ^ 40 * 7618609 * 2
def baseEnd_7618609 : Nat := 434667592852209765661129

theorem tailTrace_7618609 : CollatzResearch.WordTrace tailWord_7618609 prefixEnd_7618609 434667592852209765661129 := by
  unfold tailWord_7618609
  simp only [CollatzResearch.WordTrace]
  refine ⟨277873498456088222672082881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185248998970725481781388587 277873498456088222672082881)
  ·
    refine ⟨208405123842066167004062161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277873498456088222672082881 208405123842066167004062161)
    ·
      refine ⟨156303842881549625253046621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208405123842066167004062161 156303842881549625253046621)
      ·
        refine ⟨58613941080581109469892483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156303842881549625253046621 58613941080581109469892483)
        ·
          refine ⟨87920911620871664204838725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58613941080581109469892483 87920911620871664204838725)
          ·
            refine ⟨16485170928913437038407261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87920911620871664204838725 16485170928913437038407261)
            ·
              refine ⟨6181939098342538889402723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16485170928913437038407261 6181939098342538889402723)
              ·
                refine ⟨9272908647513808334104085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6181939098342538889402723 9272908647513808334104085)
                ·
                  refine ⟨434667592852209765661129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9272908647513808334104085 434667592852209765661129)
                  ·
                    rfl

theorem cell23_7618609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 3, 1, 6].length) (baseStart_7618609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7618609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7618609 prefixEnd_7618609 := by exact prefixLift 7618609
  have htrace : WordTrace (prefixWord ++ tailWord_7618609) baseStart_7618609 baseEnd_7618609 := by
    simpa [prefixWord, tailWord_7618609, baseEnd_7618609] using wordTrace_append hprefix tailTrace_7618609
  have hstable : (prefixWord ++ tailWord_7618609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7618609).length < 2 ^ (prefixWord ++ tailWord_7618609).sum := by decide
  have hdescent : baseEnd_7618609 < baseStart_7618609 := by decide
  rcases family_descends (prefixWord ++ tailWord_7618609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7618615 : List Nat := [1, 1, 3, 1, 2, 2, 2, 1, 2, 1, 7]
def baseStart_7618615 : Nat := 118140960795 + 7618615 * 2 ^ 59
def prefixEnd_7618615 : Nat := 4983230072969 + 3 ^ 40 * 7618615 * 2
def baseEnd_7618615 : Nat := 3912011416553814867475133

theorem tailTrace_7618615 : CollatzResearch.WordTrace tailWord_7618615 prefixEnd_7618615 3912011416553814867475133 := by
  unfold tailWord_7618615
  simp only [CollatzResearch.WordTrace]
  refine ⟨277873717294066485696801299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185249144862710990464534199 277873717294066485696801299)
  ·
    refine ⟨416810575941099728545201949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277873717294066485696801299 416810575941099728545201949)
    ·
      refine ⟨156303965977912398204450731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 416810575941099728545201949 156303965977912398204450731)
      ·
        refine ⟨234455948966868597306676097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156303965977912398204450731 234455948966868597306676097)
        ·
          refine ⟨175841961725151447980007073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234455948966868597306676097 175841961725151447980007073)
          ·
            refine ⟨131881471293863585985005305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175841961725151447980007073 131881471293863585985005305)
            ·
              refine ⟨98911103470397689488753979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131881471293863585985005305 98911103470397689488753979)
              ·
                refine ⟨148366655205596534233130969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98911103470397689488753979 148366655205596534233130969)
                ·
                  refine ⟨111274991404197400674848227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 148366655205596534233130969 111274991404197400674848227)
                  ·
                    refine ⟨166912487106296101012272341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 111274991404197400674848227 166912487106296101012272341)
                    ·
                      refine ⟨3912011416553814867475133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 166912487106296101012272341 3912011416553814867475133)
                      ·
                        rfl

theorem cell23_7618615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 2, 1, 7].length) (baseStart_7618615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7618615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7618615 prefixEnd_7618615 := by exact prefixLift 7618615
  have htrace : WordTrace (prefixWord ++ tailWord_7618615) baseStart_7618615 baseEnd_7618615 := by
    simpa [prefixWord, tailWord_7618615, baseEnd_7618615] using wordTrace_append hprefix tailTrace_7618615
  have hstable : (prefixWord ++ tailWord_7618615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7618615).length < 2 ^ (prefixWord ++ tailWord_7618615).sum := by decide
  have hdescent : baseEnd_7618615 < baseStart_7618615 := by decide
  rcases family_descends (prefixWord ++ tailWord_7618615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7618629 : List Nat := [1, 3, 1, 1, 1, 3, 1, 5, 2, 3, 2]
def baseStart_7618629 : Nat := 118140960795 + 7618629 * 2 ^ 59
def prefixEnd_7618629 : Nat := 4983230072969 + 3 ^ 40 * 7618629 * 2
def baseEnd_7618629 : Nat := 3912018605282977812700069

theorem tailTrace_7618629 : CollatzResearch.WordTrace tailWord_7618629 prefixEnd_7618629 3912018605282977812700069 := by
  unfold tailWord_7618629
  simp only [CollatzResearch.WordTrace]
  refine ⟨277874227916015766087810941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185249485277343844058540627 277874227916015766087810941)
  ·
    refine ⟨104202835468505912282929103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 277874227916015766087810941 104202835468505912282929103)
    ·
      refine ⟨156304253202758868424393655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104202835468505912282929103 156304253202758868424393655)
      ·
        refine ⟨234456379804138302636590483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156304253202758868424393655 234456379804138302636590483)
        ·
          refine ⟨351684569706207453954885725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234456379804138302636590483 351684569706207453954885725)
          ·
            refine ⟨131881713639827795233082147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 351684569706207453954885725 131881713639827795233082147)
            ·
              refine ⟨197822570459741692849623221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131881713639827795233082147 197822570459741692849623221)
              ·
                refine ⟨18545865980600783704652177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 197822570459741692849623221 18545865980600783704652177)
                ·
                  refine ⟨13909399485450587778489133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18545865980600783704652177 13909399485450587778489133)
                  ·
                    refine ⟨5216024807043970416933425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13909399485450587778489133 5216024807043970416933425)
                    ·
                      refine ⟨3912018605282977812700069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5216024807043970416933425 3912018605282977812700069)
                      ·
                        rfl

theorem cell23_7618629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 5, 2, 3, 2].length) (baseStart_7618629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7618629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7618629 prefixEnd_7618629 := by exact prefixLift 7618629
  have htrace : WordTrace (prefixWord ++ tailWord_7618629) baseStart_7618629 baseEnd_7618629 := by
    simpa [prefixWord, tailWord_7618629, baseEnd_7618629] using wordTrace_append hprefix tailTrace_7618629
  have hstable : (prefixWord ++ tailWord_7618629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7618629).length < 2 ^ (prefixWord ++ tailWord_7618629).sum := by decide
  have hdescent : baseEnd_7618629 < baseStart_7618629 := by decide
  rcases family_descends (prefixWord ++ tailWord_7618629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7618653 : List Nat := [1, 4, 4, 1, 1, 1, 3, 1, 3, 1, 3]
def baseStart_7618653 : Nat := 118140960795 + 7618653 * 2 ^ 59
def prefixEnd_7618653 : Nat := 4983230072969 + 3 ^ 40 * 7618653 * 2
def baseEnd_7618653 : Nat := 3912030928818685718799959

theorem tailTrace_7618653 : CollatzResearch.WordTrace tailWord_7618653 prefixEnd_7618653 3912030928818685718799959 := by
  unfold tailWord_7618653
  simp only [CollatzResearch.WordTrace]
  refine ⟨277875103267928818186684613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185250068845285878791123075 277875103267928818186684613)
  ·
    refine ⟨52101581862736653410003365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 277875103267928818186684613 52101581862736653410003365)
    ·
      refine ⟨9769046599263122514375631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52101581862736653410003365 9769046599263122514375631)
      ·
        refine ⟨14653569898894683771563447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9769046599263122514375631 14653569898894683771563447)
        ·
          refine ⟨21980354848342025657345171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14653569898894683771563447 21980354848342025657345171)
          ·
            refine ⟨32970532272513038486017757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21980354848342025657345171 32970532272513038486017757)
            ·
              refine ⟨12363949602192389432256659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32970532272513038486017757 12363949602192389432256659)
              ·
                refine ⟨18545924403288584148384989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12363949602192389432256659 18545924403288584148384989)
                ·
                  refine ⟨6954721651233219055644371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18545924403288584148384989 6954721651233219055644371)
                  ·
                    refine ⟨10432082476849828583466557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6954721651233219055644371 10432082476849828583466557)
                    ·
                      refine ⟨3912030928818685718799959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10432082476849828583466557 3912030928818685718799959)
                      ·
                        rfl

theorem cell23_7618653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_7618653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7618653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7618653 prefixEnd_7618653 := by exact prefixLift 7618653
  have htrace : WordTrace (prefixWord ++ tailWord_7618653) baseStart_7618653 baseEnd_7618653 := by
    simpa [prefixWord, tailWord_7618653, baseEnd_7618653] using wordTrace_append hprefix tailTrace_7618653
  have hstable : (prefixWord ++ tailWord_7618653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7618653).length < 2 ^ (prefixWord ++ tailWord_7618653).sum := by decide
  have hdescent : baseEnd_7618653 < baseStart_7618653 := by decide
  rcases family_descends (prefixWord ++ tailWord_7618653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7618672 : List Nat := [2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 6]
def baseStart_7618672 : Nat := 118140960795 + 7618672 * 2 ^ 59
def prefixEnd_7618672 : Nat := 4983230072969 + 3 ^ 40 * 7618672 * 2
def baseEnd_7618672 : Nat := 3912040684951121144462371

theorem tailTrace_7618672 : CollatzResearch.WordTrace tailWord_7618672 prefixEnd_7618672 3912040684951121144462371 := by
  unfold tailWord_7618672
  simp only [CollatzResearch.WordTrace]
  refine ⟨138937898127429992215813135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185250530836573322954417513 138937898127429992215813135)
  ·
    refine ⟨208406847191144988323719703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138937898127429992215813135 208406847191144988323719703)
    ·
      refine ⟨312610270786717482485579555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208406847191144988323719703 312610270786717482485579555)
      ·
        refine ⟨468915406180076223728369333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312610270786717482485579555 468915406180076223728369333)
        ·
          refine ⟨43960819329382145974534625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 468915406180076223728369333 43960819329382145974534625)
          ·
            refine ⟨32970614497036609480900969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43960819329382145974534625 32970614497036609480900969)
            ·
              refine ⟨24727960872777457110675727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32970614497036609480900969 24727960872777457110675727)
              ·
                refine ⟨37091941309166185666013591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24727960872777457110675727 37091941309166185666013591)
                ·
                  refine ⟨55637911963749278499020387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37091941309166185666013591 55637911963749278499020387)
                  ·
                    refine ⟨83456867945623917748530581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55637911963749278499020387 83456867945623917748530581)
                    ·
                      refine ⟨3912040684951121144462371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83456867945623917748530581 3912040684951121144462371)
                      ·
                        rfl

theorem cell23_7618672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 6].length) (baseStart_7618672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7618672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7618672 prefixEnd_7618672 := by exact prefixLift 7618672
  have htrace : WordTrace (prefixWord ++ tailWord_7618672) baseStart_7618672 baseEnd_7618672 := by
    simpa [prefixWord, tailWord_7618672, baseEnd_7618672] using wordTrace_append hprefix tailTrace_7618672
  have hstable : (prefixWord ++ tailWord_7618672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7618672).length < 2 ^ (prefixWord ++ tailWord_7618672).sum := by decide
  have hdescent : baseEnd_7618672 < baseStart_7618672 := by decide
  rcases family_descends (prefixWord ++ tailWord_7618672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7618679 : List Nat := [1, 1, 3, 1, 1, 6, 1, 1, 3, 2, 3]
def baseStart_7618679 : Nat := 118140960795 + 7618679 * 2 ^ 59
def prefixEnd_7618679 : Nat := 4983230072969 + 3 ^ 40 * 7618679 * 2
def baseEnd_7618679 : Nat := 3912044279315702617074839

theorem tailTrace_7618679 : CollatzResearch.WordTrace tailWord_7618679 prefixEnd_7618679 3912044279315702617074839 := by
  unfold tailWord_7618679
  simp only [CollatzResearch.WordTrace]
  refine ⟨277876051565834624627131091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185250701043889749751420727 277876051565834624627131091)
  ·
    refine ⟨416814077348751936940696637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277876051565834624627131091 416814077348751936940696637)
    ·
      refine ⟨156305279005781976352761239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 416814077348751936940696637 156305279005781976352761239)
      ·
        refine ⟨234457918508672964529141859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156305279005781976352761239 234457918508672964529141859)
        ·
          refine ⟨351686877763009446793712789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234457918508672964529141859 351686877763009446793712789)
          ·
            refine ⟨16485322395141067818455287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 351686877763009446793712789 16485322395141067818455287)
            ·
              refine ⟨24727983592711601727682931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16485322395141067818455287 24727983592711601727682931)
              ·
                refine ⟨37091975389067402591524397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24727983592711601727682931 37091975389067402591524397)
                ·
                  refine ⟨13909490770900275971821649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37091975389067402591524397 13909490770900275971821649)
                  ·
                    refine ⟨10432118078175206978866237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13909490770900275971821649 10432118078175206978866237)
                    ·
                      refine ⟨3912044279315702617074839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10432118078175206978866237 3912044279315702617074839)
                      ·
                        rfl

theorem cell23_7618679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 1, 3, 2, 3].length) (baseStart_7618679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7618679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7618679 prefixEnd_7618679 := by exact prefixLift 7618679
  have htrace : WordTrace (prefixWord ++ tailWord_7618679) baseStart_7618679 baseEnd_7618679 := by
    simpa [prefixWord, tailWord_7618679, baseEnd_7618679] using wordTrace_append hprefix tailTrace_7618679
  have hstable : (prefixWord ++ tailWord_7618679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7618679).length < 2 ^ (prefixWord ++ tailWord_7618679).sum := by decide
  have hdescent : baseEnd_7618679 < baseStart_7618679 := by decide
  rcases family_descends (prefixWord ++ tailWord_7618679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7618696 : List Nat := [2, 1, 3, 4, 1, 3, 1, 1, 1, 1, 5]
def baseStart_7618696 : Nat := 118140960795 + 7618696 * 2 ^ 59
def prefixEnd_7618696 : Nat := 4983230072969 + 3 ^ 40 * 7618696 * 2
def baseEnd_7618696 : Nat := 3912053008486829050562261

theorem tailTrace_7618696 : CollatzResearch.WordTrace tailWord_7618696 prefixEnd_7618696 3912053008486829050562261 := by
  unfold tailWord_7618696
  simp only [CollatzResearch.WordTrace]
  refine ⟨138938335803386518265249971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185251114404515357686999961 138938335803386518265249971)
  ·
    refine ⟨208407503705079777397874957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138938335803386518265249971 208407503705079777397874957)
    ·
      refine ⟨78152813889404916524203109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208407503705079777397874957 78152813889404916524203109)
      ·
        refine ⟨14653652604263421848288083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78152813889404916524203109 14653652604263421848288083)
        ·
          refine ⟨21980478906395132772432125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14653652604263421848288083 21980478906395132772432125)
          ·
            refine ⟨8242679589898174789662047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21980478906395132772432125 8242679589898174789662047)
            ·
              refine ⟨12364019384847262184493071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8242679589898174789662047 12364019384847262184493071)
              ·
                refine ⟨18546029077270893276739607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12364019384847262184493071 18546029077270893276739607)
                ·
                  refine ⟨27819043615906339915109411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18546029077270893276739607 27819043615906339915109411)
                  ·
                    refine ⟨41728565423859509872664117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27819043615906339915109411 41728565423859509872664117)
                    ·
                      refine ⟨3912053008486829050562261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41728565423859509872664117 3912053008486829050562261)
                      ·
                        rfl

theorem cell23_7618696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_7618696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7618696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7618696 prefixEnd_7618696 := by exact prefixLift 7618696
  have htrace : WordTrace (prefixWord ++ tailWord_7618696) baseStart_7618696 baseEnd_7618696 := by
    simpa [prefixWord, tailWord_7618696, baseEnd_7618696] using wordTrace_append hprefix tailTrace_7618696
  have hstable : (prefixWord ++ tailWord_7618696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7618696).length < 2 ^ (prefixWord ++ tailWord_7618696).sum := by decide
  have hdescent : baseEnd_7618696 < baseStart_7618696 := by decide
  rcases family_descends (prefixWord ++ tailWord_7618696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7618789 : List Nat := [1, 3, 1, 4, 2, 1, 2, 2, 7]
def baseStart_7618789 : Nat := 118140960795 + 7618789 * 2 ^ 59
def prefixEnd_7618789 : Nat := 4983230072969 + 3 ^ 40 * 7618789 * 2
def baseEnd_7618789 : Nat := 434677862465299687411037

theorem tailTrace_7618789 : CollatzResearch.WordTrace tailWord_7618789 prefixEnd_7618789 434677862465299687411037 := by
  unfold tailWord_7618789
  simp only [CollatzResearch.WordTrace]
  refine ⟨277880063595436113413635421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185253375730290742275756947 277880063595436113413635421)
  ·
    refine ⟨104205023848288542530113283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 277880063595436113413635421 104205023848288542530113283)
    ·
      refine ⟨156307535772432813795169925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104205023848288542530113283 156307535772432813795169925)
      ·
        refine ⟨29307662957331152586594361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 156307535772432813795169925 29307662957331152586594361)
        ·
          refine ⟨21980747217998364439945771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29307662957331152586594361 21980747217998364439945771)
          ·
            refine ⟨32971120826997546659918657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21980747217998364439945771 32971120826997546659918657)
            ·
              refine ⟨24728340620248159994938993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32971120826997546659918657 24728340620248159994938993)
              ·
                refine ⟨18546255465186119996204245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24728340620248159994938993 18546255465186119996204245)
                ·
                  refine ⟨434677862465299687411037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18546255465186119996204245 434677862465299687411037)
                  ·
                    rfl

theorem cell23_7618789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 2, 7].length) (baseStart_7618789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7618789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7618789 prefixEnd_7618789 := by exact prefixLift 7618789
  have htrace : WordTrace (prefixWord ++ tailWord_7618789) baseStart_7618789 baseEnd_7618789 := by
    simpa [prefixWord, tailWord_7618789, baseEnd_7618789] using wordTrace_append hprefix tailTrace_7618789
  have hstable : (prefixWord ++ tailWord_7618789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7618789).length < 2 ^ (prefixWord ++ tailWord_7618789).sum := by decide
  have hdescent : baseEnd_7618789 < baseStart_7618789 := by decide
  rcases family_descends (prefixWord ++ tailWord_7618789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7618819 : List Nat := [1, 1, 1, 3, 2, 3, 3, 2, 2, 5]
def baseStart_7618819 : Nat := 118140960795 + 7618819 * 2 ^ 59
def prefixEnd_7618819 : Nat := 4983230072969 + 3 ^ 40 * 7618819 * 2
def baseEnd_7618819 : Nat := 1304038722202444023108065

theorem tailTrace_7618819 : CollatzResearch.WordTrace tailWord_7618819 prefixEnd_7618819 1304038722202444023108065 := by
  unfold tailWord_7618819
  simp only [CollatzResearch.WordTrace]
  refine ⟨277881157785327428537227511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185254105190218285691485007 277881157785327428537227511)
  ·
    refine ⟨416821736677991142805841267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277881157785327428537227511 416821736677991142805841267)
    ·
      refine ⟨625232605016986714208761901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 416821736677991142805841267 625232605016986714208761901)
      ·
        refine ⟨234462226881370017828285713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 625232605016986714208761901 234462226881370017828285713)
        ·
          refine ⟨175846670161027513371214285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234462226881370017828285713 175846670161027513371214285)
          ·
            refine ⟨65942501310385317514205357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 175846670161027513371214285 65942501310385317514205357)
            ·
              refine ⟨24728437991394494067827009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65942501310385317514205357 24728437991394494067827009)
              ·
                refine ⟨18546328493545870550870257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24728437991394494067827009 18546328493545870550870257)
                ·
                  refine ⟨13909746370159402913152693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18546328493545870550870257 13909746370159402913152693)
                  ·
                    refine ⟨1304038722202444023108065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13909746370159402913152693 1304038722202444023108065)
                    ·
                      rfl

theorem cell23_7618819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 2, 2, 5].length) (baseStart_7618819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7618819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7618819 prefixEnd_7618819 := by exact prefixLift 7618819
  have htrace : WordTrace (prefixWord ++ tailWord_7618819) baseStart_7618819 baseEnd_7618819 := by
    simpa [prefixWord, tailWord_7618819, baseEnd_7618819] using wordTrace_append hprefix tailTrace_7618819
  have hstable : (prefixWord ++ tailWord_7618819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7618819).length < 2 ^ (prefixWord ++ tailWord_7618819).sum := by decide
  have hdescent : baseEnd_7618819 < baseStart_7618819 := by decide
  rcases family_descends (prefixWord ++ tailWord_7618819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7618823 : List Nat := [1, 1, 4, 5, 1, 2, 1, 1, 7]
def baseStart_7618823 : Nat := 118140960795 + 7618823 * 2 ^ 59
def prefixEnd_7618823 : Nat := 4983230072969 + 3 ^ 40 * 7618823 * 2
def baseEnd_7618823 : Nat := 434679802281105561519353

theorem tailTrace_7618823 : CollatzResearch.WordTrace tailWord_7618823 prefixEnd_7618823 434679802281105561519353 := by
  unfold tailWord_7618823
  simp only [CollatzResearch.WordTrace]
  refine ⟨277881303677312937220373123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185254202451541958146915415 277881303677312937220373123)
  ·
    refine ⟨416821955515969405830559685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277881303677312937220373123 416821955515969405830559685)
    ·
      refine ⟨78154116659244263593229941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 416821955515969405830559685 78154116659244263593229941)
      ·
        refine ⟨7326948436804149711865307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 78154116659244263593229941 7326948436804149711865307)
        ·
          refine ⟨10990422655206224567797961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7326948436804149711865307 10990422655206224567797961)
          ·
            refine ⟨8242816991404668425848471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10990422655206224567797961 8242816991404668425848471)
            ·
              refine ⟨12364225487107002638772707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8242816991404668425848471 12364225487107002638772707)
              ·
                refine ⟨18546338230660503958159061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12364225487107002638772707 18546338230660503958159061)
                ·
                  refine ⟨434679802281105561519353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18546338230660503958159061 434679802281105561519353)
                  ·
                    rfl

theorem cell23_7618823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 1, 1, 7].length) (baseStart_7618823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7618823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7618823 prefixEnd_7618823 := by exact prefixLift 7618823
  have htrace : WordTrace (prefixWord ++ tailWord_7618823) baseStart_7618823 baseEnd_7618823 := by
    simpa [prefixWord, tailWord_7618823, baseEnd_7618823] using wordTrace_append hprefix tailTrace_7618823
  have hstable : (prefixWord ++ tailWord_7618823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7618823).length < 2 ^ (prefixWord ++ tailWord_7618823).sum := by decide
  have hdescent : baseEnd_7618823 < baseStart_7618823 := by decide
  rcases family_descends (prefixWord ++ tailWord_7618823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7618869 : List Nat := [1, 3, 3, 1, 2, 1, 2, 1, 2, 1, 6]
def baseStart_7618869 : Nat := 118140960795 + 7618869 * 2 ^ 59
def prefixEnd_7618869 : Nat := 4983230072969 + 3 ^ 40 * 7618869 * 2
def baseEnd_7618869 : Nat := 3912141840640056873698965

theorem tailTrace_7618869 : CollatzResearch.WordTrace tailWord_7618869 prefixEnd_7618869 3912141840640056873698965 := by
  unfold tailWord_7618869
  simp only [CollatzResearch.WordTrace]
  refine ⟨277882981435146287076547661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185255320956764191384365107 277882981435146287076547661)
  ·
    refine ⟨104206118038179857653705373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 277882981435146287076547661 104206118038179857653705373)
    ·
      refine ⟨39077294264317446620139515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104206118038179857653705373 39077294264317446620139515)
      ·
        refine ⟨58615941396476169930209273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39077294264317446620139515 58615941396476169930209273)
        ·
          refine ⟨43961956047357127447656955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58615941396476169930209273 43961956047357127447656955)
          ·
            refine ⟨65942934071035691171485433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43961956047357127447656955 65942934071035691171485433)
            ·
              refine ⟨49457200553276768378614075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65942934071035691171485433 49457200553276768378614075)
              ·
                refine ⟨74185800829915152567921113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49457200553276768378614075 74185800829915152567921113)
                ·
                  refine ⟨55639350622436364425940835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74185800829915152567921113 55639350622436364425940835)
                  ·
                    refine ⟨83459025933654546638911253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55639350622436364425940835 83459025933654546638911253)
                    ·
                      refine ⟨3912141840640056873698965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83459025933654546638911253 3912141840640056873698965)
                      ·
                        rfl

theorem cell23_7618869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 1, 2, 1, 6].length) (baseStart_7618869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7618869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7618869 prefixEnd_7618869 := by exact prefixLift 7618869
  have htrace : WordTrace (prefixWord ++ tailWord_7618869) baseStart_7618869 baseEnd_7618869 := by
    simpa [prefixWord, tailWord_7618869, baseEnd_7618869] using wordTrace_append hprefix tailTrace_7618869
  have hstable : (prefixWord ++ tailWord_7618869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7618869).length < 2 ^ (prefixWord ++ tailWord_7618869).sum := by decide
  have hdescent : baseEnd_7618869 < baseStart_7618869 := by decide
  rcases family_descends (prefixWord ++ tailWord_7618869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7618876 : List Nat := [2, 2, 2, 2, 1, 2, 1, 4, 2, 2, 3]
def baseStart_7618876 : Nat := 118140960795 + 7618876 * 2 ^ 59
def prefixEnd_7618876 : Nat := 4983230072969 + 3 ^ 40 * 7618876 * 2
def baseEnd_7618876 : Nat := 3912145435004638346311433

theorem tailTrace_7618876 : CollatzResearch.WordTrace tailWord_7618876 prefixEnd_7618876 3912145435004638346311433 := by
  unfold tailWord_7618876
  simp only [CollatzResearch.WordTrace]
  refine ⟨138941618373060463636026241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185255491164080618181368321 138941618373060463636026241)
  ·
    refine ⟨104206213779795347727019681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138941618373060463636026241 104206213779795347727019681)
    ·
      refine ⟨78154660334846510795264761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104206213779795347727019681 78154660334846510795264761)
      ·
        refine ⟨58615995251134883096448571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78154660334846510795264761 58615995251134883096448571)
        ·
          refine ⟨87923992876702324644672857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58615995251134883096448571 87923992876702324644672857)
          ·
            refine ⟨65942994657526743483504643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87923992876702324644672857 65942994657526743483504643)
            ·
              refine ⟨98914491986290115225256965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65942994657526743483504643 98914491986290115225256965)
              ·
                refine ⟨18546467247429396604735681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98914491986290115225256965 18546467247429396604735681)
                ·
                  refine ⟨13909850435572047453551761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18546467247429396604735681 13909850435572047453551761)
                  ·
                    refine ⟨10432387826679035590163821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13909850435572047453551761 10432387826679035590163821)
                    ·
                      refine ⟨3912145435004638346311433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10432387826679035590163821 3912145435004638346311433)
                      ·
                        rfl

theorem cell23_7618876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 4, 2, 2, 3].length) (baseStart_7618876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7618876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7618876 prefixEnd_7618876 := by exact prefixLift 7618876
  have htrace : WordTrace (prefixWord ++ tailWord_7618876) baseStart_7618876 baseEnd_7618876 := by
    simpa [prefixWord, tailWord_7618876, baseEnd_7618876] using wordTrace_append hprefix tailTrace_7618876
  have hstable : (prefixWord ++ tailWord_7618876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7618876).length < 2 ^ (prefixWord ++ tailWord_7618876).sum := by decide
  have hdescent : baseEnd_7618876 < baseStart_7618876 := by decide
  rcases family_descends (prefixWord ++ tailWord_7618876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7618889 : List Nat := [1, 2, 1, 1, 2, 3, 1, 2, 2, 5, 3]
def baseStart_7618889 : Nat := 118140960795 + 7618889 * 2 ^ 59
def prefixEnd_7618889 : Nat := 4983230072969 + 3 ^ 40 * 7618889 * 2
def baseEnd_7618889 : Nat := 3912152110253146795448873

theorem tailTrace_7618889 : CollatzResearch.WordTrace tailWord_7618889 prefixEnd_7618889 3912152110253146795448873 := by
  unfold tailWord_7618889
  simp only [CollatzResearch.WordTrace]
  refine ⟨277883710895073830492275721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185255807263382553661517147 277883710895073830492275721)
  ·
    refine ⟨208412783171305372869206791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277883710895073830492275721 208412783171305372869206791)
    ·
      refine ⟨312619174756958059303810187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208412783171305372869206791 312619174756958059303810187)
      ·
        refine ⟨468928762135437088955715281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312619174756958059303810187 468928762135437088955715281)
        ·
          refine ⟨351696571601577816716786461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 468928762135437088955715281 351696571601577816716786461)
          ·
            refine ⟨131886214350591681268794923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 351696571601577816716786461 131886214350591681268794923)
            ·
              refine ⟨197829321525887521903192385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131886214350591681268794923 197829321525887521903192385)
              ·
                refine ⟨148371991144415641427394289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 197829321525887521903192385 148371991144415641427394289)
                ·
                  refine ⟨111278993358311731070545717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 148371991144415641427394289 111278993358311731070545717)
                  ·
                    refine ⟨10432405627341724787863661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 111278993358311731070545717 10432405627341724787863661)
                    ·
                      refine ⟨3912152110253146795448873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10432405627341724787863661 3912152110253146795448873)
                      ·
                        rfl

theorem cell23_7618889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 2, 5, 3].length) (baseStart_7618889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7618889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7618889 prefixEnd_7618889 := by exact prefixLift 7618889
  have htrace : WordTrace (prefixWord ++ tailWord_7618889) baseStart_7618889 baseEnd_7618889 := by
    simpa [prefixWord, tailWord_7618889, baseEnd_7618889] using wordTrace_append hprefix tailTrace_7618889
  have hstable : (prefixWord ++ tailWord_7618889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7618889).length < 2 ^ (prefixWord ++ tailWord_7618889).sum := by decide
  have hdescent : baseEnd_7618889 < baseStart_7618889 := by decide
  rcases family_descends (prefixWord ++ tailWord_7618889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7618956 : List Nat := [2, 2, 1, 2, 1, 4, 3, 1, 1, 6]
def baseStart_7618956 : Nat := 118140960795 + 7618956 * 2 ^ 59
def prefixEnd_7618956 : Nat := 4983230072969 + 3 ^ 40 * 7618956 * 2
def baseEnd_7618956 : Nat := 1304062171152332677770355

theorem tailTrace_7618956 : CollatzResearch.WordTrace tailWord_7618956 prefixEnd_7618956 1304062171152332677770355 := by
  unfold tailWord_7618956
  simp only [CollatzResearch.WordTrace]
  refine ⟨138943077292915550467482361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185257436390554067289976481 138943077292915550467482361)
  ·
    refine ⟨104207307969686662850611771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138943077292915550467482361 104207307969686662850611771)
    ·
      refine ⟨156310961954529994275917657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104207307969686662850611771 156310961954529994275917657)
      ·
        refine ⟨117233221465897495706938243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156310961954529994275917657 117233221465897495706938243)
        ·
          refine ⟨175849832198846243560407365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117233221465897495706938243 175849832198846243560407365)
          ·
            refine ⟨32971843537283670667576381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 175849832198846243560407365 32971843537283670667576381)
            ·
              refine ⟨12364441326481376500341143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32971843537283670667576381 12364441326481376500341143)
              ·
                refine ⟨18546661989722064750511715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12364441326481376500341143 18546661989722064750511715)
                ·
                  refine ⟨27819992984583097125767573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18546661989722064750511715 27819992984583097125767573)
                  ·
                    refine ⟨1304062171152332677770355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27819992984583097125767573 1304062171152332677770355)
                    ·
                      rfl

theorem cell23_7618956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 3, 1, 1, 6].length) (baseStart_7618956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7618956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7618956 prefixEnd_7618956 := by exact prefixLift 7618956
  have htrace : WordTrace (prefixWord ++ tailWord_7618956) baseStart_7618956 baseEnd_7618956 := by
    simpa [prefixWord, tailWord_7618956, baseEnd_7618956] using wordTrace_append hprefix tailTrace_7618956
  have hstable : (prefixWord ++ tailWord_7618956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7618956).length < 2 ^ (prefixWord ++ tailWord_7618956).sum := by decide
  have hdescent : baseEnd_7618956 < baseStart_7618956 := by decide
  rcases family_descends (prefixWord ++ tailWord_7618956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7618969 : List Nat := [1, 2, 1, 2, 1, 4, 3, 9]
def baseStart_7618969 : Nat := 118140960795 + 7618969 * 2 ^ 59
def prefixEnd_7618969 : Nat := 4983230072969 + 3 ^ 40 * 7618969 * 2
def baseEnd_7618969 : Nat := 144896044026129869720315

theorem tailTrace_7618969 : CollatzResearch.WordTrace tailWord_7618969 prefixEnd_7618969 144896044026129869720315 := by
  unfold tailWord_7618969
  simp only [CollatzResearch.WordTrace]
  refine ⟨277886628734784004155187961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185257752489856002770125307 277886628734784004155187961)
  ·
    refine ⟨208414971551088003116390971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277886628734784004155187961 208414971551088003116390971)
    ·
      refine ⟨312622457326632004674586457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208414971551088003116390971 312622457326632004674586457)
      ·
        refine ⟨234466842994974003505939843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 312622457326632004674586457 234466842994974003505939843)
        ·
          refine ⟨351700264492461005258909765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234466842994974003505939843 351700264492461005258909765)
          ·
            refine ⟨65943799592336438486045581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 351700264492461005258909765 65943799592336438486045581)
            ·
              refine ⟨24728924847126164432267093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65943799592336438486045581 24728924847126164432267093)
              ·
                refine ⟨144896044026129869720315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24728924847126164432267093 144896044026129869720315)
                ·
                  rfl

theorem cell23_7618969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 9].length) (baseStart_7618969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7618969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7618969 prefixEnd_7618969 := by exact prefixLift 7618969
  have htrace : WordTrace (prefixWord ++ tailWord_7618969) baseStart_7618969 baseEnd_7618969 := by
    simpa [prefixWord, tailWord_7618969, baseEnd_7618969] using wordTrace_append hprefix tailTrace_7618969
  have hstable : (prefixWord ++ tailWord_7618969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7618969).length < 2 ^ (prefixWord ++ tailWord_7618969).sum := by decide
  have hdescent : baseEnd_7618969 < baseStart_7618969 := by decide
  rcases family_descends (prefixWord ++ tailWord_7618969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7618974 : List Nat := [4, 3, 1, 2, 1, 1, 3, 3, 1, 1, 3]
def baseStart_7618974 : Nat := 118140960795 + 7618974 * 2 ^ 59
def prefixEnd_7618974 : Nat := 4983230072969 + 3 ^ 40 * 7618974 * 2
def baseEnd_7618974 : Nat := 3912195756108778962885983

theorem tailTrace_7618974 : CollatzResearch.WordTrace tailWord_7618974 prefixEnd_7618974 3912195756108778962885983 := by
  unfold tailWord_7618974
  simp only [CollatzResearch.WordTrace]
  refine ⟨34735851387470736251139997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185257874066510593339413317 34735851387470736251139997)
  ·
    refine ⟨13025944270301526094177499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34735851387470736251139997 13025944270301526094177499)
    ·
      refine ⟨19538916405452289141266249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13025944270301526094177499 19538916405452289141266249)
      ·
        refine ⟨14654187304089216855949687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19538916405452289141266249 14654187304089216855949687)
        ·
          refine ⟨21981280956133825283924531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14654187304089216855949687 21981280956133825283924531)
          ·
            refine ⟨32971921434200737925886797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21981280956133825283924531 32971921434200737925886797)
            ·
              refine ⟨12364470537825276722207549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32971921434200737925886797 12364470537825276722207549)
              ·
                refine ⟨4636676451684478770827831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12364470537825276722207549 4636676451684478770827831)
                ·
                  refine ⟨6955014677526718156241747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4636676451684478770827831 6955014677526718156241747)
                  ·
                    refine ⟨10432522016290077234362621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6955014677526718156241747 10432522016290077234362621)
                    ·
                      refine ⟨3912195756108778962885983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10432522016290077234362621 3912195756108778962885983)
                      ·
                        rfl

theorem cell23_7618974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 3, 3, 1, 1, 3].length) (baseStart_7618974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7618974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7618974 prefixEnd_7618974 := by exact prefixLift 7618974
  have htrace : WordTrace (prefixWord ++ tailWord_7618974) baseStart_7618974 baseEnd_7618974 := by
    simpa [prefixWord, tailWord_7618974, baseEnd_7618974] using wordTrace_append hprefix tailTrace_7618974
  have hstable : (prefixWord ++ tailWord_7618974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7618974).length < 2 ^ (prefixWord ++ tailWord_7618974).sum := by decide
  have hdescent : baseEnd_7618974 < baseStart_7618974 := by decide
  rcases family_descends (prefixWord ++ tailWord_7618974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7618983 : List Nat := [1, 1, 6, 1, 1, 3, 2, 1, 1, 1, 5]
def baseStart_7618983 : Nat := 118140960795 + 7618983 * 2 ^ 59
def prefixEnd_7618983 : Nat := 4983230072969 + 3 ^ 40 * 7618983 * 2
def baseEnd_7618983 : Nat := 3912200377434669427673441

theorem tailTrace_7618983 : CollatzResearch.WordTrace tailWord_7618983 prefixEnd_7618983 3912200377434669427673441 := by
  unfold tailWord_7618983
  simp only [CollatzResearch.WordTrace]
  refine ⟨277887139356733284546197603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185258092904488856364131735 277887139356733284546197603)
  ·
    refine ⟨416830709035099926819296405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277887139356733284546197603 416830709035099926819296405)
    ·
      refine ⟨19538939486020309069654519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 416830709035099926819296405 19538939486020309069654519)
      ·
        refine ⟨29308409229030463604481779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19538939486020309069654519 29308409229030463604481779)
        ·
          refine ⟨43962613843545695406722669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29308409229030463604481779 43962613843545695406722669)
          ·
            refine ⟨16485980191329635777521001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43962613843545695406722669 16485980191329635777521001)
            ·
              refine ⟨12364485143497226833140751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16485980191329635777521001 12364485143497226833140751)
              ·
                refine ⟨18546727715245840249711127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12364485143497226833140751 18546727715245840249711127)
                ·
                  refine ⟨27820091572868760374566691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18546727715245840249711127 27820091572868760374566691)
                  ·
                    refine ⟨41730137359303140561850037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27820091572868760374566691 41730137359303140561850037)
                    ·
                      refine ⟨3912200377434669427673441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41730137359303140561850037 3912200377434669427673441)
                      ·
                        rfl

theorem cell23_7618983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 2, 1, 1, 1, 5].length) (baseStart_7618983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7618983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7618983 prefixEnd_7618983 := by exact prefixLift 7618983
  have htrace : WordTrace (prefixWord ++ tailWord_7618983) baseStart_7618983 baseEnd_7618983 := by
    simpa [prefixWord, tailWord_7618983, baseEnd_7618983] using wordTrace_append hprefix tailTrace_7618983
  have hstable : (prefixWord ++ tailWord_7618983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7618983).length < 2 ^ (prefixWord ++ tailWord_7618983).sum := by decide
  have hdescent : baseEnd_7618983 < baseStart_7618983 := by decide
  rcases family_descends (prefixWord ++ tailWord_7618983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7619019 : List Nat := [1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 8]
def baseStart_7619019 : Nat := 118140960795 + 7619019 * 2 ^ 59
def prefixEnd_7619019 : Nat := 4983230072969 + 3 ^ 40 * 7619019 * 2
def baseEnd_7619019 : Nat := 3912218862738231286823275

theorem tailTrace_7619019 : CollatzResearch.WordTrace tailWord_7619019 prefixEnd_7619019 3912218862738231286823275 := by
  unfold tailWord_7619019
  simp only [CollatzResearch.WordTrace]
  refine ⟨277888452384602862694508111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185258968256401908463005407 277888452384602862694508111)
  ·
    refine ⟨416832678576904294041762167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277888452384602862694508111 416832678576904294041762167)
    ·
      refine ⟨625249017865356441062643251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 416832678576904294041762167 625249017865356441062643251)
      ·
        refine ⟨937873526798034661593964877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 625249017865356441062643251 937873526798034661593964877)
        ·
          refine ⟨351702572549262998097736829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 937873526798034661593964877 351702572549262998097736829)
          ·
            refine ⟨131888464705973624286651311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 351702572549262998097736829 131888464705973624286651311)
            ·
              refine ⟨197832697058960436429976967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131888464705973624286651311 197832697058960436429976967)
              ·
                refine ⟨296749045588440654644965451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 197832697058960436429976967 296749045588440654644965451)
                ·
                  refine ⟨445123568382660981967448177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 296749045588440654644965451 445123568382660981967448177)
                  ·
                    refine ⟨333842676286995736475586133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 445123568382660981967448177 333842676286995736475586133)
                    ·
                      refine ⟨3912218862738231286823275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 333842676286995736475586133 3912218862738231286823275)
                      ·
                        rfl

theorem cell23_7619019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 8].length) (baseStart_7619019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7619019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7619019 prefixEnd_7619019 := by exact prefixLift 7619019
  have htrace : WordTrace (prefixWord ++ tailWord_7619019) baseStart_7619019 baseEnd_7619019 := by
    simpa [prefixWord, tailWord_7619019, baseEnd_7619019] using wordTrace_append hprefix tailTrace_7619019
  have hstable : (prefixWord ++ tailWord_7619019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7619019).length < 2 ^ (prefixWord ++ tailWord_7619019).sum := by decide
  have hdescent : baseEnd_7619019 < baseStart_7619019 := by decide
  rcases family_descends (prefixWord ++ tailWord_7619019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7619030 : List Nat := [5, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3]
def baseStart_7619030 : Nat := 118140960795 + 7619030 * 2 ^ 59
def prefixEnd_7619030 : Nat := 4983230072969 + 3 ^ 40 * 7619030 * 2
def baseEnd_7619030 : Nat := 3912224511025430743785725

theorem tailTrace_7619030 : CollatzResearch.WordTrace tailWord_7619030 prefixEnd_7619030 3912224511025430743785725 := by
  unfold tailWord_7619030
  simp only [CollatzResearch.WordTrace]
  refine ⟨17368053349222688223322409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 185259235725042007715439029 17368053349222688223322409)
  ·
    refine ⟨13026040011917016167491807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17368053349222688223322409 13026040011917016167491807)
    ·
      refine ⟨19539060017875524251237711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13026040011917016167491807 19539060017875524251237711)
      ·
        refine ⟨29308590026813286376856567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19539060017875524251237711 29308590026813286376856567)
        ·
          refine ⟨43962885040219929565284851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29308590026813286376856567 43962885040219929565284851)
          ·
            refine ⟨65944327560329894347927277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43962885040219929565284851 65944327560329894347927277)
            ·
              refine ⟨24729122835123710380472729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65944327560329894347927277 24729122835123710380472729)
              ·
                refine ⟨18546842126342782785354547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24729122835123710380472729 18546842126342782785354547)
                ·
                  refine ⟨27820263189514174178031821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18546842126342782785354547 27820263189514174178031821)
                  ·
                    refine ⟨10432598696067815316761933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27820263189514174178031821 10432598696067815316761933)
                    ·
                      refine ⟨3912224511025430743785725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10432598696067815316761933 3912224511025430743785725)
                      ·
                        rfl

theorem cell23_7619030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3].length) (baseStart_7619030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7619030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7619030 prefixEnd_7619030 := by exact prefixLift 7619030
  have htrace : WordTrace (prefixWord ++ tailWord_7619030) baseStart_7619030 baseEnd_7619030 := by
    simpa [prefixWord, tailWord_7619030, baseEnd_7619030] using wordTrace_append hprefix tailTrace_7619030
  have hstable : (prefixWord ++ tailWord_7619030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7619030).length < 2 ^ (prefixWord ++ tailWord_7619030).sum := by decide
  have hdescent : baseEnd_7619030 < baseStart_7619030 := by decide
  rcases family_descends (prefixWord ++ tailWord_7619030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7619053 : List Nat := [1, 5, 1, 3, 1, 1, 1, 1, 2, 3, 4]
def baseStart_7619053 : Nat := 118140960795 + 7619053 * 2 ^ 59
def prefixEnd_7619053 : Nat := 4983230072969 + 3 ^ 40 * 7619053 * 2
def baseEnd_7619053 : Nat := 3912236321080484153798119

theorem tailTrace_7619053 : CollatzResearch.WordTrace tailWord_7619053 prefixEnd_7619053 3912236321080484153798119 := by
  unfold tailWord_7619053
  simp only [CollatzResearch.WordTrace]
  refine ⟨277889692466479686501245813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185259794977653124334163875 277889692466479686501245813)
  ·
    refine ⟨26052158668732470609491795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 277889692466479686501245813 26052158668732470609491795)
    ·
      refine ⟨39078238003098705914237693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26052158668732470609491795 39078238003098705914237693)
      ·
        refine ⟨14654339251162014717839135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39078238003098705914237693 14654339251162014717839135)
        ·
          refine ⟨21981508876743022076758703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14654339251162014717839135 21981508876743022076758703)
          ·
            refine ⟨32972263315114533115138055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21981508876743022076758703 32972263315114533115138055)
            ·
              refine ⟨49458394972671799672707083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32972263315114533115138055 49458394972671799672707083)
              ·
                refine ⟨74187592459007699509060625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49458394972671799672707083 74187592459007699509060625)
                ·
                  refine ⟨55640694344255774631795469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74187592459007699509060625 55640694344255774631795469)
                  ·
                    refine ⟨20865260379095915486923301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55640694344255774631795469 20865260379095915486923301)
                    ·
                      refine ⟨3912236321080484153798119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20865260379095915486923301 3912236321080484153798119)
                      ·
                        rfl

theorem cell23_7619053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_7619053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7619053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7619053 prefixEnd_7619053 := by exact prefixLift 7619053
  have htrace : WordTrace (prefixWord ++ tailWord_7619053) baseStart_7619053 baseEnd_7619053 := by
    simpa [prefixWord, tailWord_7619053, baseEnd_7619053] using wordTrace_append hprefix tailTrace_7619053
  have hstable : (prefixWord ++ tailWord_7619053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7619053).length < 2 ^ (prefixWord ++ tailWord_7619053).sum := by decide
  have hdescent : baseEnd_7619053 < baseStart_7619053 := by decide
  rcases family_descends (prefixWord ++ tailWord_7619053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7619056 : List Nat := [2, 1, 1, 1, 3, 3, 1, 1, 1, 6, 3]
def baseStart_7619056 : Nat := 118140960795 + 7619056 * 2 ^ 59
def prefixEnd_7619056 : Nat := 4983230072969 + 3 ^ 40 * 7619056 * 2
def baseEnd_7619056 : Nat := 3912237861522447642060605

theorem tailTrace_7619056 : CollatzResearch.WordTrace tailWord_7619056 prefixEnd_7619056 3912237861522447642060605 := by
  unfold tailWord_7619056
  simp only [CollatzResearch.WordTrace]
  refine ⟨138944900942734409006802511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185259867923645878675736681 138944900942734409006802511)
  ·
    refine ⟨208417351414101613510203767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138944900942734409006802511 208417351414101613510203767)
    ·
      refine ⟨312626027121152420265305651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208417351414101613510203767 312626027121152420265305651)
      ·
        refine ⟨468939040681728630397958477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312626027121152420265305651 468939040681728630397958477)
        ·
          refine ⟨175852140255648236399234429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 468939040681728630397958477 175852140255648236399234429)
          ·
            refine ⟨65944552595868088649712911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 175852140255648236399234429 65944552595868088649712911)
            ·
              refine ⟨98916828893802132974569367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65944552595868088649712911 98916828893802132974569367)
              ·
                refine ⟨148375243340703199461854051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98916828893802132974569367 148375243340703199461854051)
                ·
                  refine ⟨222562865011054799192781077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 148375243340703199461854051 222562865011054799192781077)
                  ·
                    refine ⟨10432634297393193712161613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 222562865011054799192781077 10432634297393193712161613)
                    ·
                      refine ⟨3912237861522447642060605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10432634297393193712161613 3912237861522447642060605)
                      ·
                        rfl

theorem cell23_7619056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 1, 6, 3].length) (baseStart_7619056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7619056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7619056 prefixEnd_7619056 := by exact prefixLift 7619056
  have htrace : WordTrace (prefixWord ++ tailWord_7619056) baseStart_7619056 baseEnd_7619056 := by
    simpa [prefixWord, tailWord_7619056, baseEnd_7619056] using wordTrace_append hprefix tailTrace_7619056
  have hstable : (prefixWord ++ tailWord_7619056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7619056).length < 2 ^ (prefixWord ++ tailWord_7619056).sum := by decide
  have hdescent : baseEnd_7619056 < baseStart_7619056 := by decide
  rcases family_descends (prefixWord ++ tailWord_7619056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7619116 : List Nat := [2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 5]
def baseStart_7619116 : Nat := 118140960795 + 7619116 * 2 ^ 59
def prefixEnd_7619116 : Nat := 4983230072969 + 3 ^ 40 * 7619116 * 2
def baseEnd_7619116 : Nat := 3912268670361717407310329

theorem tailTrace_7619116 : CollatzResearch.WordTrace tailWord_7619116 prefixEnd_7619116 3912268670361717407310329 := by
  unfold tailWord_7619116
  simp only [CollatzResearch.WordTrace]
  refine ⟨138945995132625724130394601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185261326843500965507192801 138945995132625724130394601)
  ·
    refine ⟨104209496349469293097795951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138945995132625724130394601 104209496349469293097795951)
    ·
      refine ⟨156314244524203939646693927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104209496349469293097795951 156314244524203939646693927)
      ·
        refine ⟨234471366786305909470040891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156314244524203939646693927 234471366786305909470040891)
        ·
          refine ⟨351707050179458864205061337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234471366786305909470040891 351707050179458864205061337)
          ·
            refine ⟨263780287634594148153796003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 351707050179458864205061337 263780287634594148153796003)
            ·
              refine ⟨395670431451891222230694005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 263780287634594148153796003 395670431451891222230694005)
              ·
                refine ⟨37094102948614802084127563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 395670431451891222230694005 37094102948614802084127563)
                ·
                  refine ⟨55641154422922203126191345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37094102948614802084127563 55641154422922203126191345)
                  ·
                    refine ⟨41730865817191652344643509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55641154422922203126191345 41730865817191652344643509)
                    ·
                      refine ⟨3912268670361717407310329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41730865817191652344643509 3912268670361717407310329)
                      ·
                        rfl

theorem cell23_7619116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 5].length) (baseStart_7619116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7619116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7619116 prefixEnd_7619116 := by exact prefixLift 7619116
  have htrace : WordTrace (prefixWord ++ tailWord_7619116) baseStart_7619116 baseEnd_7619116 := by
    simpa [prefixWord, tailWord_7619116, baseEnd_7619116] using wordTrace_append hprefix tailTrace_7619116
  have hstable : (prefixWord ++ tailWord_7619116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7619116).length < 2 ^ (prefixWord ++ tailWord_7619116).sum := by decide
  have hdescent : baseEnd_7619116 < baseStart_7619116 := by decide
  rcases family_descends (prefixWord ++ tailWord_7619116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7619143 : List Nat := [1, 1, 4, 1, 4, 1, 2, 1, 1, 3, 4]
def baseStart_7619143 : Nat := 118140960795 + 7619143 * 2 ^ 59
def prefixEnd_7619143 : Nat := 4983230072969 + 3 ^ 40 * 7619143 * 2
def baseEnd_7619143 : Nat := 3912282534339388801672705

theorem tailTrace_7619143 : CollatzResearch.WordTrace tailWord_7619143 prefixEnd_7619143 3912282534339388801672705 := by
  unfold tailWord_7619143
  simp only [CollatzResearch.WordTrace]
  refine ⟨277892975036153631872022083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185261983357435754581348055 277892975036153631872022083)
  ·
    refine ⟨416839462554230447808033125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277892975036153631872022083 416839462554230447808033125)
    ·
      refine ⟨78157399228918208964006211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 416839462554230447808033125 78157399228918208964006211)
      ·
        refine ⟨117236098843377313446009317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78157399228918208964006211 117236098843377313446009317)
        ·
          refine ⟨21981768533133246271126747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 117236098843377313446009317 21981768533133246271126747)
          ·
            refine ⟨32972652799699869406690121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21981768533133246271126747 32972652799699869406690121)
            ·
              refine ⟨24729489599774902055017591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32972652799699869406690121 24729489599774902055017591)
              ·
                refine ⟨37094234399662353082526387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24729489599774902055017591 37094234399662353082526387)
                ·
                  refine ⟨55641351599493529623789581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37094234399662353082526387 55641351599493529623789581)
                  ·
                    refine ⟨20865506849810073608921093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55641351599493529623789581 20865506849810073608921093)
                    ·
                      refine ⟨3912282534339388801672705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20865506849810073608921093 3912282534339388801672705)
                      ·
                        rfl

theorem cell23_7619143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 1, 1, 3, 4].length) (baseStart_7619143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7619143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7619143 prefixEnd_7619143 := by exact prefixLift 7619143
  have htrace : WordTrace (prefixWord ++ tailWord_7619143) baseStart_7619143 baseEnd_7619143 := by
    simpa [prefixWord, tailWord_7619143, baseEnd_7619143] using wordTrace_append hprefix tailTrace_7619143
  have hstable : (prefixWord ++ tailWord_7619143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7619143).length < 2 ^ (prefixWord ++ tailWord_7619143).sum := by decide
  have hdescent : baseEnd_7619143 < baseStart_7619143 := by decide
  rcases family_descends (prefixWord ++ tailWord_7619143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7619197 : List Nat := [1, 4, 1, 1, 5, 1, 2, 1, 2, 2, 3]
def baseStart_7619197 : Nat := 118140960795 + 7619197 * 2 ^ 59
def prefixEnd_7619197 : Nat := 4983230072969 + 3 ^ 40 * 7619197 * 2
def baseEnd_7619197 : Nat := 3912310262294731590397457

theorem tailTrace_7619197 : CollatzResearch.WordTrace tailWord_7619197 prefixEnd_7619197 3912310262294731590397457 := by
  unfold tailWord_7619197
  simp only [CollatzResearch.WordTrace]
  refine ⟨277894944577957999094487845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185263296385305332729658563 277894944577957999094487845)
  ·
    refine ⟨52105302108367124830216471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 277894944577957999094487845 52105302108367124830216471)
    ·
      refine ⟨78157953162550687245324707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52105302108367124830216471 78157953162550687245324707)
      ·
        refine ⟨117236929743826030867987061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78157953162550687245324707 117236929743826030867987061)
        ·
          refine ⟨10990962163483690393873787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 117236929743826030867987061 10990962163483690393873787)
          ·
            refine ⟨16486443245225535590810681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10990962163483690393873787 16486443245225535590810681)
            ·
              refine ⟨12364832433919151693108011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16486443245225535590810681 12364832433919151693108011)
              ·
                refine ⟨18547248650878727539662017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12364832433919151693108011 18547248650878727539662017)
                ·
                  refine ⟨13910436488159045654746513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18547248650878727539662017 13910436488159045654746513)
                  ·
                    refine ⟨10432827366119284241059885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13910436488159045654746513 10432827366119284241059885)
                    ·
                      refine ⟨3912310262294731590397457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10432827366119284241059885 3912310262294731590397457)
                      ·
                        rfl

theorem cell23_7619197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 2, 1, 2, 2, 3].length) (baseStart_7619197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7619197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7619197 prefixEnd_7619197 := by exact prefixLift 7619197
  have htrace : WordTrace (prefixWord ++ tailWord_7619197) baseStart_7619197 baseEnd_7619197 := by
    simpa [prefixWord, tailWord_7619197, baseEnd_7619197] using wordTrace_append hprefix tailTrace_7619197
  have hstable : (prefixWord ++ tailWord_7619197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7619197).length < 2 ^ (prefixWord ++ tailWord_7619197).sum := by decide
  have hdescent : baseEnd_7619197 < baseStart_7619197 := by decide
  rcases family_descends (prefixWord ++ tailWord_7619197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7619230 : List Nat := [4, 3, 1, 1, 1, 1, 1, 1, 5, 5]
def baseStart_7619230 : Nat := 118140960795 + 7619230 * 2 ^ 59
def prefixEnd_7619230 : Nat := 4983230072969 + 3 ^ 40 * 7619230 * 2
def baseEnd_7619230 : Nat := 1304109069052109987094935

theorem tailTrace_7619230 : CollatzResearch.WordTrace tailWord_7619230 prefixEnd_7619230 1304109069052109987094935 := by
  unfold tailWord_7619230
  simp only [CollatzResearch.WordTrace]
  refine ⟨34737018523354805716304893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185264098791225630486959429 34737018523354805716304893)
  ·
    refine ⟨13026381946258052143614335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34737018523354805716304893 13026381946258052143614335)
    ·
      refine ⟨19539572919387078215421503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13026381946258052143614335 19539572919387078215421503)
      ·
        refine ⟨29309359379080617323132255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19539572919387078215421503 29309359379080617323132255)
        ·
          refine ⟨43964039068620925984698383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29309359379080617323132255 43964039068620925984698383)
          ·
            refine ⟨65946058602931388977047575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43964039068620925984698383 65946058602931388977047575)
            ·
              refine ⟨98919087904397083465571363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65946058602931388977047575 98919087904397083465571363)
              ·
                refine ⟨148378631856595625198357045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98919087904397083465571363 148378631856595625198357045)
                ·
                  refine ⟨13910496736555839862345973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 148378631856595625198357045 13910496736555839862345973)
                  ·
                    refine ⟨1304109069052109987094935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13910496736555839862345973 1304109069052109987094935)
                    ·
                      rfl

theorem cell23_7619230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 5, 5].length) (baseStart_7619230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7619230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7619230 prefixEnd_7619230 := by exact prefixLift 7619230
  have htrace : WordTrace (prefixWord ++ tailWord_7619230) baseStart_7619230 baseEnd_7619230 := by
    simpa [prefixWord, tailWord_7619230, baseEnd_7619230] using wordTrace_append hprefix tailTrace_7619230
  have hstable : (prefixWord ++ tailWord_7619230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7619230).length < 2 ^ (prefixWord ++ tailWord_7619230).sum := by decide
  have hdescent : baseEnd_7619230 < baseStart_7619230 := by decide
  rcases family_descends (prefixWord ++ tailWord_7619230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7619250 : List Nat := [3, 2, 1, 1, 1, 2, 1, 6, 1, 1, 4]
def baseStart_7619250 : Nat := 118140960795 + 7619250 * 2 ^ 59
def prefixEnd_7619250 : Nat := 4983230072969 + 3 ^ 40 * 7619250 * 2
def baseEnd_7619250 : Nat := 3912337476769419883034713

theorem tailTrace_7619250 : CollatzResearch.WordTrace tailWord_7619250 prefixEnd_7619250 3912337476769419883034713 := by
  unfold tailWord_7619250
  simp only [CollatzResearch.WordTrace]
  refine ⟨69474219411691497286541801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185264585097843992764111469 69474219411691497286541801)
  ·
    refine ⟨52105664558768622964906351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69474219411691497286541801 52105664558768622964906351)
    ·
      refine ⟨78158496838152934447359527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52105664558768622964906351 78158496838152934447359527)
      ·
        refine ⟨117237745257229401671039291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78158496838152934447359527 117237745257229401671039291)
        ·
          refine ⟨175856617885844102506558937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117237745257229401671039291 175856617885844102506558937)
          ·
            refine ⟨131892463414383076879919203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175856617885844102506558937 131892463414383076879919203)
            ·
              refine ⟨197838695121574615319878805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131892463414383076879919203 197838695121574615319878805)
              ·
                refine ⟨9273688833823810093119319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 197838695121574615319878805 9273688833823810093119319)
                ·
                  refine ⟨13910533250735715139678979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9273688833823810093119319 13910533250735715139678979)
                  ·
                    refine ⟨20865799876103572709518469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13910533250735715139678979 20865799876103572709518469)
                    ·
                      refine ⟨3912337476769419883034713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20865799876103572709518469 3912337476769419883034713)
                      ·
                        rfl

theorem cell23_7619250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 6, 1, 1, 4].length) (baseStart_7619250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7619250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7619250 prefixEnd_7619250 := by exact prefixLift 7619250
  have htrace : WordTrace (prefixWord ++ tailWord_7619250) baseStart_7619250 baseEnd_7619250 := by
    simpa [prefixWord, tailWord_7619250, baseEnd_7619250] using wordTrace_append hprefix tailTrace_7619250
  have hstable : (prefixWord ++ tailWord_7619250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7619250).length < 2 ^ (prefixWord ++ tailWord_7619250).sum := by decide
  have hdescent : baseEnd_7619250 < baseStart_7619250 := by decide
  rcases family_descends (prefixWord ++ tailWord_7619250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7619260 : List Nat := [2, 2, 2, 3, 1, 1, 2, 2, 4, 4]
def baseStart_7619260 : Nat := 118140960795 + 7619260 * 2 ^ 59
def prefixEnd_7619260 : Nat := 4983230072969 + 3 ^ 40 * 7619260 * 2
def baseEnd_7619260 : Nat := 1304114203858654947969889

theorem tailTrace_7619260 : CollatzResearch.WordTrace tailWord_7619260 prefixEnd_7619260 1304114203858654947969889 := by
  unfold tailWord_7619260
  simp only [CollatzResearch.WordTrace]
  refine ⟨138948621188364880427015617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185264828251153173902687489 138948621188364880427015617)
  ·
    refine ⟨104211465891273660320261713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138948621188364880427015617 104211465891273660320261713)
    ·
      refine ⟨78158599418455245240196285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104211465891273660320261713 78158599418455245240196285)
      ·
        refine ⟨29309474781920716965073607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78158599418455245240196285 29309474781920716965073607)
        ·
          refine ⟨43964212172881075447610411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29309474781920716965073607 43964212172881075447610411)
          ·
            refine ⟨65946318259321613171415617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43964212172881075447610411 65946318259321613171415617)
            ·
              refine ⟨49459738694491209878561713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65946318259321613171415617 49459738694491209878561713)
              ·
                refine ⟨37094804020868407408921285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49459738694491209878561713 37094804020868407408921285)
                ·
                  refine ⟨6955275753912826389172741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37094804020868407408921285 6955275753912826389172741)
                  ·
                    refine ⟨1304114203858654947969889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6955275753912826389172741 1304114203858654947969889)
                    ·
                      rfl

theorem cell23_7619260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 2, 4, 4].length) (baseStart_7619260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7619260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7619260 prefixEnd_7619260 := by exact prefixLift 7619260
  have htrace : WordTrace (prefixWord ++ tailWord_7619260) baseStart_7619260 baseEnd_7619260 := by
    simpa [prefixWord, tailWord_7619260, baseEnd_7619260] using wordTrace_append hprefix tailTrace_7619260
  have hstable : (prefixWord ++ tailWord_7619260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7619260).length < 2 ^ (prefixWord ++ tailWord_7619260).sum := by decide
  have hdescent : baseEnd_7619260 < baseStart_7619260 := by decide
  rcases family_descends (prefixWord ++ tailWord_7619260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7619297 : List Nat := [1, 2, 3, 1, 4, 3, 1, 1, 1, 2, 4]
def baseStart_7619297 : Nat := 118140960795 + 7619297 * 2 ^ 59
def prefixEnd_7619297 : Nat := 4983230072969 + 3 ^ 40 * 7619297 * 2
def baseEnd_7619297 : Nat := 3912361610360181199146997

theorem tailTrace_7619297 : CollatzResearch.WordTrace tailWord_7619297 prefixEnd_7619297 3912361610360181199146997 := by
  unfold tailWord_7619297
  simp only [CollatzResearch.WordTrace]
  refine ⟨277898591877595716173128145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185265727918397144115418763 277898591877595716173128145)
  ·
    refine ⟨208423943908196787129846109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277898591877595716173128145 208423943908196787129846109)
    ·
      refine ⟨78158978965573795173692291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208423943908196787129846109 78158978965573795173692291)
      ·
        refine ⟨117238468448360692760538437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78158978965573795173692291 117238468448360692760538437)
        ·
          refine ⟨21982212834067629892600957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 117238468448360692760538437 21982212834067629892600957)
          ·
            refine ⟨8243329812775361209725359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21982212834067629892600957 8243329812775361209725359)
            ·
              refine ⟨12364994719163041814588039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8243329812775361209725359 12364994719163041814588039)
              ·
                refine ⟨18547492078744562721882059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12364994719163041814588039 18547492078744562721882059)
                ·
                  refine ⟨27821238118116844082823089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18547492078744562721882059 27821238118116844082823089)
                  ·
                    refine ⟨20865928588587633062117317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27821238118116844082823089 20865928588587633062117317)
                    ·
                      refine ⟨3912361610360181199146997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20865928588587633062117317 3912361610360181199146997)
                      ·
                        rfl

theorem cell23_7619297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 1, 1, 1, 2, 4].length) (baseStart_7619297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7619297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7619297 prefixEnd_7619297 := by exact prefixLift 7619297
  have htrace : WordTrace (prefixWord ++ tailWord_7619297) baseStart_7619297 baseEnd_7619297 := by
    simpa [prefixWord, tailWord_7619297, baseEnd_7619297] using wordTrace_append hprefix tailTrace_7619297
  have hstable : (prefixWord ++ tailWord_7619297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7619297).length < 2 ^ (prefixWord ++ tailWord_7619297).sum := by decide
  have hdescent : baseEnd_7619297 < baseStart_7619297 := by decide
  rcases family_descends (prefixWord ++ tailWord_7619297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7619304 : List Nat := [2, 1, 4, 1, 4, 1, 2, 2, 1, 2, 3]
def baseStart_7619304 : Nat := 118140960795 + 7619304 * 2 ^ 59
def prefixEnd_7619304 : Nat := 4983230072969 + 3 ^ 40 * 7619304 * 2
def baseEnd_7619304 : Nat := 3912365204724762671759465

theorem tailTrace_7619304 : CollatzResearch.WordTrace tailWord_7619304 prefixEnd_7619304 3912365204724762671759465 := by
  unfold tailWord_7619304
  simp only [CollatzResearch.WordTrace]
  refine ⟨138949423594285178184316483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185265898125713570912421977 138949423594285178184316483)
  ·
    refine ⟨208424135391427767276474725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138949423594285178184316483 208424135391427767276474725)
    ·
      refine ⟨39079525385892706364339011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 208424135391427767276474725 39079525385892706364339011)
      ·
        refine ⟨58619288078839059546508517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39079525385892706364339011 58619288078839059546508517)
        ·
          refine ⟨10991116514782323664970347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58619288078839059546508517 10991116514782323664970347)
          ·
            refine ⟨16486674772173485497455521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10991116514782323664970347 16486674772173485497455521)
            ·
              refine ⟨12365006079130114123091641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16486674772173485497455521 12365006079130114123091641)
              ·
                refine ⟨9273754559347585592318731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12365006079130114123091641 9273754559347585592318731)
                ·
                  refine ⟨13910631839021378388478097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9273754559347585592318731 13910631839021378388478097)
                  ·
                    refine ⟨10432973879266033791358573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13910631839021378388478097 10432973879266033791358573)
                    ·
                      refine ⟨3912365204724762671759465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10432973879266033791358573 3912365204724762671759465)
                      ·
                        rfl

theorem cell23_7619304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 2, 2, 1, 2, 3].length) (baseStart_7619304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7619304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7619304 prefixEnd_7619304 := by exact prefixLift 7619304
  have htrace : WordTrace (prefixWord ++ tailWord_7619304) baseStart_7619304 baseEnd_7619304 := by
    simpa [prefixWord, tailWord_7619304, baseEnd_7619304] using wordTrace_append hprefix tailTrace_7619304
  have hstable : (prefixWord ++ tailWord_7619304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7619304).length < 2 ^ (prefixWord ++ tailWord_7619304).sum := by decide
  have hdescent : baseEnd_7619304 < baseStart_7619304 := by decide
  rcases family_descends (prefixWord ++ tailWord_7619304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7619313 : List Nat := [1, 2, 2, 2, 2, 2, 1, 1, 1, 4, 5]
def baseStart_7619313 : Nat := 118140960795 + 7619313 * 2 ^ 59
def prefixEnd_7619313 : Nat := 4983230072969 + 3 ^ 40 * 7619313 * 2
def baseEnd_7619313 : Nat := 3912369826050653136546923

theorem tailTrace_7619313 : CollatzResearch.WordTrace tailWord_7619313 prefixEnd_7619313 3912369826050653136546923 := by
  unfold tailWord_7619313
  simp only [CollatzResearch.WordTrace]
  refine ⟨277899175445537750905710593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185266116963691833937140395 277899175445537750905710593)
  ·
    refine ⟨208424381584153313179282945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277899175445537750905710593 208424381584153313179282945)
    ·
      refine ⟨156318286188114984884462209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208424381584153313179282945 156318286188114984884462209)
      ·
        refine ⟨117238714641086238663346657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156318286188114984884462209 117238714641086238663346657)
        ·
          refine ⟨87929035980814678997509993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117238714641086238663346657 87929035980814678997509993)
          ·
            refine ⟨65946776985611009248132495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87929035980814678997509993 65946776985611009248132495)
            ·
              refine ⟨98920165478416513872198743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65946776985611009248132495 98920165478416513872198743)
              ·
                refine ⟨148380248217624770808298115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98920165478416513872198743 148380248217624770808298115)
                ·
                  refine ⟨222570372326437156212447173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 148380248217624770808298115 222570372326437156212447173)
                  ·
                    refine ⟨41731944811206966789833845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 222570372326437156212447173 41731944811206966789833845)
                    ·
                      refine ⟨3912369826050653136546923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41731944811206966789833845 3912369826050653136546923)
                      ·
                        rfl

theorem cell23_7619313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 4, 5].length) (baseStart_7619313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7619313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7619313 prefixEnd_7619313 := by exact prefixLift 7619313
  have htrace : WordTrace (prefixWord ++ tailWord_7619313) baseStart_7619313 baseEnd_7619313 := by
    simpa [prefixWord, tailWord_7619313, baseEnd_7619313] using wordTrace_append hprefix tailTrace_7619313
  have hstable : (prefixWord ++ tailWord_7619313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7619313).length < 2 ^ (prefixWord ++ tailWord_7619313).sum := by decide
  have hdescent : baseEnd_7619313 < baseStart_7619313 := by decide
  rcases family_descends (prefixWord ++ tailWord_7619313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7619333 : List Nat := [1, 3, 1, 1, 2, 1, 1, 3, 4, 6]
def baseStart_7619333 : Nat := 118140960795 + 7619333 * 2 ^ 59
def prefixEnd_7619333 : Nat := 4983230072969 + 3 ^ 40 * 7619333 * 2
def baseEnd_7619333 : Nat := 1304126698554581019432277

theorem tailTrace_7619333 : CollatzResearch.WordTrace tailWord_7619333 prefixEnd_7619333 1304126698554581019432277 := by
  unfold tailWord_7619333
  simp only [CollatzResearch.WordTrace]
  refine ⟨277899904905465294321438653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185266603270310196214292435 277899904905465294321438653)
  ·
    refine ⟨104212464339549485370539495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 277899904905465294321438653 104212464339549485370539495)
    ·
      refine ⟨156318696509324228055809243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104212464339549485370539495 156318696509324228055809243)
      ·
        refine ⟨234478044763986342083713865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156318696509324228055809243 234478044763986342083713865)
        ·
          refine ⟨175858533572989756562785399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234478044763986342083713865 175858533572989756562785399)
          ·
            refine ⟨263787800359484634844178099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175858533572989756562785399 263787800359484634844178099)
            ·
              refine ⟨395681700539226952266267149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 263787800359484634844178099 395681700539226952266267149)
              ·
                refine ⟨148380637702210107099850181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 395681700539226952266267149 148380637702210107099850181)
                ·
                  refine ⟨27821369569164395081221909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 148380637702210107099850181 27821369569164395081221909)
                  ·
                    refine ⟨1304126698554581019432277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27821369569164395081221909 1304126698554581019432277)
                    ·
                      rfl

theorem cell23_7619333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 4, 6].length) (baseStart_7619333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7619333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7619333 prefixEnd_7619333 := by exact prefixLift 7619333
  have htrace : WordTrace (prefixWord ++ tailWord_7619333) baseStart_7619333 baseEnd_7619333 := by
    simpa [prefixWord, tailWord_7619333, baseEnd_7619333] using wordTrace_append hprefix tailTrace_7619333
  have hstable : (prefixWord ++ tailWord_7619333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7619333).length < 2 ^ (prefixWord ++ tailWord_7619333).sum := by decide
  have hdescent : baseEnd_7619333 < baseStart_7619333 := by decide
  rcases family_descends (prefixWord ++ tailWord_7619333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7619343 : List Nat := [1, 1, 2, 1, 1, 1, 5, 2, 1, 3, 5]
def baseStart_7619343 : Nat := 118140960795 + 7619343 * 2 ^ 59
def prefixEnd_7619343 : Nat := 4983230072969 + 3 ^ 40 * 7619343 * 2
def baseEnd_7619343 : Nat := 3912385230470288019171785

theorem tailTrace_7619343 : CollatzResearch.WordTrace tailWord_7619343 prefixEnd_7619343 3912385230470288019171785 := by
  unfold tailWord_7619343
  simp only [CollatzResearch.WordTrace]
  refine ⟨277900269635429066029302683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185266846423619377352868455 277900269635429066029302683)
  ·
    refine ⟨416850404453143599043954025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277900269635429066029302683 416850404453143599043954025)
    ·
      refine ⟨312637803339857699282965519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 416850404453143599043954025 312637803339857699282965519)
      ·
        refine ⟨468956705009786548924448279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312637803339857699282965519 468956705009786548924448279)
        ·
          refine ⟨703435057514679823386672419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 468956705009786548924448279 703435057514679823386672419)
          ·
            refine ⟨1055152586272019735080008629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 703435057514679823386672419 1055152586272019735080008629)
            ·
              refine ⟨98920554963001850163750809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1055152586272019735080008629 98920554963001850163750809)
              ·
                refine ⟨74190416222251387622813107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98920554963001850163750809 74190416222251387622813107)
                ·
                  refine ⟨111285624333377081434219661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74190416222251387622813107 111285624333377081434219661)
                  ·
                    refine ⟨41732109125016405537832373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 111285624333377081434219661 41732109125016405537832373)
                    ·
                      refine ⟨3912385230470288019171785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41732109125016405537832373 3912385230470288019171785)
                      ·
                        rfl

theorem cell23_7619343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 2, 1, 3, 5].length) (baseStart_7619343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7619343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7619343 prefixEnd_7619343 := by exact prefixLift 7619343
  have htrace : WordTrace (prefixWord ++ tailWord_7619343) baseStart_7619343 baseEnd_7619343 := by
    simpa [prefixWord, tailWord_7619343, baseEnd_7619343] using wordTrace_append hprefix tailTrace_7619343
  have hstable : (prefixWord ++ tailWord_7619343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7619343).length < 2 ^ (prefixWord ++ tailWord_7619343).sum := by decide
  have hdescent : baseEnd_7619343 < baseStart_7619343 := by decide
  rcases family_descends (prefixWord ++ tailWord_7619343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7619360 : List Nat := [2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 5]
def baseStart_7619360 : Nat := 118140960795 + 7619360 * 2 ^ 59
def prefixEnd_7619360 : Nat := 4983230072969 + 3 ^ 40 * 7619360 * 2
def baseEnd_7619360 : Nat := 3912393959641414452659207

theorem tailTrace_7619360 : CollatzResearch.WordTrace tailWord_7619360 prefixEnd_7619360 3912393959641414452659207 := by
  unfold tailWord_7619360
  simp only [CollatzResearch.WordTrace]
  refine ⟨138950444838183738966335767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185267259784244985288447689 138950444838183738966335767)
  ·
    refine ⟨208425667257275608449503651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138950444838183738966335767 208425667257275608449503651)
    ·
      refine ⟨312638500885913412674255477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208425667257275608449503651 312638500885913412674255477)
      ·
        refine ⟨29309859458054382438211451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 312638500885913412674255477 29309859458054382438211451)
        ·
          refine ⟨43964789187081573657317177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29309859458054382438211451 43964789187081573657317177)
          ·
            refine ⟨32973591890311180242987883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43964789187081573657317177 32973591890311180242987883)
            ·
              refine ⟨49460387835466770364481825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32973591890311180242987883 49460387835466770364481825)
              ·
                refine ⟨37095290876600077773361369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49460387835466770364481825 37095290876600077773361369)
                ·
                  refine ⟨27821468157450058330021027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37095290876600077773361369 27821468157450058330021027)
                  ·
                    refine ⟨41732202236175087495031541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27821468157450058330021027 41732202236175087495031541)
                    ·
                      refine ⟨3912393959641414452659207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41732202236175087495031541 3912393959641414452659207)
                      ·
                        rfl

theorem cell23_7619360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_7619360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7619360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7619360 prefixEnd_7619360 := by exact prefixLift 7619360
  have htrace : WordTrace (prefixWord ++ tailWord_7619360) baseStart_7619360 baseEnd_7619360 := by
    simpa [prefixWord, tailWord_7619360, baseEnd_7619360] using wordTrace_append hprefix tailTrace_7619360
  have hstable : (prefixWord ++ tailWord_7619360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7619360).length < 2 ^ (prefixWord ++ tailWord_7619360).sum := by decide
  have hdescent : baseEnd_7619360 < baseStart_7619360 := by decide
  rcases family_descends (prefixWord ++ tailWord_7619360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7619363 : List Nat := [1, 1, 1, 4, 2, 1, 1, 3, 9]
def baseStart_7619363 : Nat := 118140960795 + 7619363 * 2 ^ 59
def prefixEnd_7619363 : Nat := 4983230072969 + 3 ^ 40 * 7619363 * 2
def baseEnd_7619363 : Nat := 434710611120375326769077

theorem tailTrace_7619363 : CollatzResearch.WordTrace tailWord_7619363 prefixEnd_7619363 434710611120375326769077 := by
  unfold tailWord_7619363
  simp only [CollatzResearch.WordTrace]
  refine ⟨277900999095356609445030743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185267332730237739630020495 277900999095356609445030743)
  ·
    refine ⟨416851498643034914167546115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277900999095356609445030743 416851498643034914167546115)
    ·
      refine ⟨625277247964552371251319173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 416851498643034914167546115 625277247964552371251319173)
      ·
        refine ⟨117239483993353569609622345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 625277247964552371251319173 117239483993353569609622345)
        ·
          refine ⟨87929612995015177207216759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117239483993353569609622345 87929612995015177207216759)
          ·
            refine ⟨131894419492522765810825139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87929612995015177207216759 131894419492522765810825139)
            ·
              refine ⟨197841629238784148716237709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131894419492522765810825139 197841629238784148716237709)
              ·
                refine ⟨74190610964544055768589141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 197841629238784148716237709 74190610964544055768589141)
                ·
                  refine ⟨434710611120375326769077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 74190610964544055768589141 434710611120375326769077)
                  ·
                    rfl

theorem cell23_7619363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 3, 9].length) (baseStart_7619363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7619363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7619363 prefixEnd_7619363 := by exact prefixLift 7619363
  have htrace : WordTrace (prefixWord ++ tailWord_7619363) baseStart_7619363 baseEnd_7619363 := by
    simpa [prefixWord, tailWord_7619363, baseEnd_7619363] using wordTrace_append hprefix tailTrace_7619363
  have hstable : (prefixWord ++ tailWord_7619363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7619363).length < 2 ^ (prefixWord ++ tailWord_7619363).sum := by decide
  have hdescent : baseEnd_7619363 < baseStart_7619363 := by decide
  rcases family_descends (prefixWord ++ tailWord_7619363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7619374 : List Nat := [4, 1, 3, 2, 1, 1, 1, 1, 3, 4, 2]
def baseStart_7619374 : Nat := 118140960795 + 7619374 * 2 ^ 59
def prefixEnd_7619374 : Nat := 4983230072969 + 3 ^ 40 * 7619374 * 2
def baseEnd_7619374 : Nat := 3912401148370577397884143

theorem tailTrace_7619374 : CollatzResearch.WordTrace tailWord_7619374 prefixEnd_7619374 3912401148370577397884143 := by
  unfold tailWord_7619374
  simp only [CollatzResearch.WordTrace]
  refine ⟨34737675037289594790460147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185267600198877838882454117 34737675037289594790460147)
  ·
    refine ⟨52106512555934392185690221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34737675037289594790460147 52106512555934392185690221)
    ·
      refine ⟨19539942208475397069633833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52106512555934392185690221 19539942208475397069633833)
      ·
        refine ⟨14654956656356547802225375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19539942208475397069633833 14654956656356547802225375)
        ·
          refine ⟨21982434984534821703338063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14654956656356547802225375 21982434984534821703338063)
          ·
            refine ⟨32973652476802232555007095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21982434984534821703338063 32973652476802232555007095)
            ·
              refine ⟨49460478715203348832510643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32973652476802232555007095 49460478715203348832510643)
              ·
                refine ⟨74190718072805023248765965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49460478715203348832510643 74190718072805023248765965)
                ·
                  refine ⟨27821519277301883718287237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74190718072805023248765965 27821519277301883718287237)
                  ·
                    refine ⟨5216534864494103197178857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27821519277301883718287237 5216534864494103197178857)
                    ·
                      refine ⟨3912401148370577397884143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5216534864494103197178857 3912401148370577397884143)
                      ·
                        rfl

theorem cell23_7619374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 1, 3, 4, 2].length) (baseStart_7619374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7619374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7619374 prefixEnd_7619374 := by exact prefixLift 7619374
  have htrace : WordTrace (prefixWord ++ tailWord_7619374) baseStart_7619374 baseEnd_7619374 := by
    simpa [prefixWord, tailWord_7619374, baseEnd_7619374] using wordTrace_append hprefix tailTrace_7619374
  have hstable : (prefixWord ++ tailWord_7619374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7619374).length < 2 ^ (prefixWord ++ tailWord_7619374).sum := by decide
  have hdescent : baseEnd_7619374 < baseStart_7619374 := by decide
  rcases family_descends (prefixWord ++ tailWord_7619374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7619391 : List Nat := [1, 1, 2, 2, 5, 2, 2, 2, 2, 2, 2]
def baseStart_7619391 : Nat := 118140960795 + 7619391 * 2 ^ 59
def prefixEnd_7619391 : Nat := 4983230072969 + 3 ^ 40 * 7619391 * 2
def baseEnd_7619391 : Nat := 3912409877541703831371565

theorem tailTrace_7619391 : CollatzResearch.WordTrace tailWord_7619391 prefixEnd_7619391 3912409877541703831371565 := by
  unfold tailWord_7619391
  simp only [CollatzResearch.WordTrace]
  refine ⟨277902020339255170227050027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185268013559503446818033351 277902020339255170227050027)
  ·
    refine ⟨416853030508882755340575041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277902020339255170227050027 416853030508882755340575041)
    ·
      refine ⟨312639772881662066505431281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 416853030508882755340575041 312639772881662066505431281)
      ·
        refine ⟨234479829661246549879073461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 312639772881662066505431281 234479829661246549879073461)
        ·
          refine ⟨21982484030741864051163137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 234479829661246549879073461 21982484030741864051163137)
          ·
            refine ⟨16486863023056398038372353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21982484030741864051163137 16486863023056398038372353)
            ·
              refine ⟨12365147267292298528779265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16486863023056398038372353 12365147267292298528779265)
              ·
                refine ⟨9273860450469223896584449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12365147267292298528779265 9273860450469223896584449)
                ·
                  refine ⟨6955395337851917922438337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9273860450469223896584449 6955395337851917922438337)
                  ·
                    refine ⟨5216546503388938441828753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6955395337851917922438337 5216546503388938441828753)
                    ·
                      refine ⟨3912409877541703831371565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5216546503388938441828753 3912409877541703831371565)
                      ·
                        rfl

theorem cell23_7619391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 2, 2, 2, 2, 2].length) (baseStart_7619391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7619391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7619391 prefixEnd_7619391 := by exact prefixLift 7619391
  have htrace : WordTrace (prefixWord ++ tailWord_7619391) baseStart_7619391 baseEnd_7619391 := by
    simpa [prefixWord, tailWord_7619391, baseEnd_7619391] using wordTrace_append hprefix tailTrace_7619391
  have hstable : (prefixWord ++ tailWord_7619391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7619391).length < 2 ^ (prefixWord ++ tailWord_7619391).sum := by decide
  have hdescent : baseEnd_7619391 < baseStart_7619391 := by decide
  rcases family_descends (prefixWord ++ tailWord_7619391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7619410 : List Nat := [3, 2, 2, 1, 1, 2, 2, 2, 1, 7]
def baseStart_7619410 : Nat := 118140960795 + 7619410 * 2 ^ 59
def prefixEnd_7619410 : Nat := 4983230072969 + 3 ^ 40 * 7619410 * 2
def baseEnd_7619410 : Nat := 1304139877891379752344659

theorem tailTrace_7619410 : CollatzResearch.WordTrace tailWord_7619410 prefixEnd_7619410 1304139877891379752344659 := by
  unfold tailWord_7619410
  simp only [CollatzResearch.WordTrace]
  refine ⟨69475678331546584117997921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185268475550790890981327789 69475678331546584117997921)
  ·
    refine ⟨52106758748659938088498441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69475678331546584117997921 52106758748659938088498441)
    ·
      refine ⟨39080069061494953566373831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52106758748659938088498441 39080069061494953566373831)
      ·
        refine ⟨58620103592242430349560747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39080069061494953566373831 58620103592242430349560747)
        ·
          refine ⟨87930155388363645524341121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58620103592242430349560747 87930155388363645524341121)
          ·
            refine ⟨65947616541272734143255841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87930155388363645524341121 65947616541272734143255841)
            ·
              refine ⟨49460712405954550607441881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65947616541272734143255841 49460712405954550607441881)
              ·
                refine ⟨37095534304465912955581411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49460712405954550607441881 37095534304465912955581411)
                ·
                  refine ⟨55643301456698869433372117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37095534304465912955581411 55643301456698869433372117)
                  ·
                    refine ⟨1304139877891379752344659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55643301456698869433372117 1304139877891379752344659)
                    ·
                      rfl

theorem cell23_7619410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 2, 1, 7].length) (baseStart_7619410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7619410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7619410 prefixEnd_7619410 := by exact prefixLift 7619410
  have htrace : WordTrace (prefixWord ++ tailWord_7619410) baseStart_7619410 baseEnd_7619410 := by
    simpa [prefixWord, tailWord_7619410, baseEnd_7619410] using wordTrace_append hprefix tailTrace_7619410
  have hstable : (prefixWord ++ tailWord_7619410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7619410).length < 2 ^ (prefixWord ++ tailWord_7619410).sum := by decide
  have hdescent : baseEnd_7619410 < baseStart_7619410 := by decide
  rcases family_descends (prefixWord ++ tailWord_7619410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7619427 : List Nat := [1, 1, 1, 5, 3, 1, 3, 1, 2, 5]
def baseStart_7619427 : Nat := 118140960795 + 7619427 * 2 ^ 59
def prefixEnd_7619427 : Nat := 4983230072969 + 3 ^ 40 * 7619427 * 2
def baseEnd_7619427 : Nat := 1304142787615088563507133

theorem tailTrace_7619427 : CollatzResearch.WordTrace tailWord_7619427 prefixEnd_7619427 1304142787615088563507133 := by
  unfold tailWord_7619427
  simp only [CollatzResearch.WordTrace]
  refine ⟨277903333367124748375360535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185268888911416498916907023 277903333367124748375360535)
  ·
    refine ⟨416855000050687122563040803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277903333367124748375360535 416855000050687122563040803)
    ·
      refine ⟨625282500076030683844561205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 416855000050687122563040803 625282500076030683844561205)
      ·
        refine ⟨58620234382127876610427613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 625282500076030683844561205 58620234382127876610427613)
        ·
          refine ⟨21982587893297953728910355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58620234382127876610427613 21982587893297953728910355)
          ·
            refine ⟨32973881839946930593365533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21982587893297953728910355 32973881839946930593365533)
            ·
              refine ⟨12365205689980098972512075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32973881839946930593365533 12365205689980098972512075)
              ·
                refine ⟨18547808534970148458768113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12365205689980098972512075 18547808534970148458768113)
                ·
                  refine ⟨13910856401227611344076085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18547808534970148458768113 13910856401227611344076085)
                  ·
                    refine ⟨1304142787615088563507133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13910856401227611344076085 1304142787615088563507133)
                    ·
                      rfl

theorem cell23_7619427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 3, 1, 2, 5].length) (baseStart_7619427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7619427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7619427 prefixEnd_7619427 := by exact prefixLift 7619427
  have htrace : WordTrace (prefixWord ++ tailWord_7619427) baseStart_7619427 baseEnd_7619427 := by
    simpa [prefixWord, tailWord_7619427, baseEnd_7619427] using wordTrace_append hprefix tailTrace_7619427
  have hstable : (prefixWord ++ tailWord_7619427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7619427).length < 2 ^ (prefixWord ++ tailWord_7619427).sum := by decide
  have hdescent : baseEnd_7619427 < baseStart_7619427 := by decide
  rcases family_descends (prefixWord ++ tailWord_7619427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7619460 : List Nat := [2, 3, 2, 1, 1, 1, 1, 1, 4, 1, 6]
def baseStart_7619460 : Nat := 118140960795 + 7619460 * 2 ^ 59
def prefixEnd_7619460 : Nat := 4983230072969 + 3 ^ 40 * 7619460 * 2
def baseEnd_7619460 : Nat := 3912445307706864061408747

theorem tailTrace_7619460 : CollatzResearch.WordTrace tailWord_7619460 prefixEnd_7619460 3912445307706864061408747 := by
  unfold tailWord_7619460
  simp only [CollatzResearch.WordTrace]
  refine ⟨138952268488002597505655917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185269691317336796674207889 138952268488002597505655917)
  ·
    refine ⟨52107100683000974064620969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138952268488002597505655917 52107100683000974064620969)
    ·
      refine ⟨39080325512250730548465727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52107100683000974064620969 39080325512250730548465727)
      ·
        refine ⟨58620488268376095822698591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39080325512250730548465727 58620488268376095822698591)
        ·
          refine ⟨87930732402564143734047887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58620488268376095822698591 87930732402564143734047887)
          ·
            refine ⟨131896098603846215601071831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87930732402564143734047887 131896098603846215601071831)
            ·
              refine ⟨197844147905769323401607747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131896098603846215601071831 197844147905769323401607747)
              ·
                refine ⟨296766221858653985102411621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 197844147905769323401607747 296766221858653985102411621)
                ·
                  refine ⟨55643666598497622206702179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 296766221858653985102411621 55643666598497622206702179)
                  ·
                    refine ⟨83465499897746433310053269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55643666598497622206702179 83465499897746433310053269)
                    ·
                      refine ⟨3912445307706864061408747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83465499897746433310053269 3912445307706864061408747)
                      ·
                        rfl

theorem cell23_7619460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 4, 1, 6].length) (baseStart_7619460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7619460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7619460 prefixEnd_7619460 := by exact prefixLift 7619460
  have htrace : WordTrace (prefixWord ++ tailWord_7619460) baseStart_7619460 baseEnd_7619460 := by
    simpa [prefixWord, tailWord_7619460, baseEnd_7619460] using wordTrace_append hprefix tailTrace_7619460
  have hstable : (prefixWord ++ tailWord_7619460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7619460).length < 2 ^ (prefixWord ++ tailWord_7619460).sum := by decide
  have hdescent : baseEnd_7619460 < baseStart_7619460 := by decide
  rcases family_descends (prefixWord ++ tailWord_7619460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7619464 : List Nat := [2, 1, 3, 3, 2, 1, 2, 1, 2, 4, 2]
def baseStart_7619464 : Nat := 118140960795 + 7619464 * 2 ^ 59
def prefixEnd_7619464 : Nat := 4983230072969 + 3 ^ 40 * 7619464 * 2
def baseEnd_7619464 : Nat := 3912447361629482045758729

theorem tailTrace_7619464 : CollatzResearch.WordTrace tailWord_7619464 prefixEnd_7619464 3912447361629482045758729 := by
  unfold tailWord_7619464
  simp only [CollatzResearch.WordTrace]
  refine ⟨138952341433995351847228723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185269788578660469129638297 138952341433995351847228723)
  ·
    refine ⟨208428512150993027770843085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138952341433995351847228723 208428512150993027770843085)
    ·
      refine ⟨78160692056622385414066157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208428512150993027770843085 78160692056622385414066157)
      ·
        refine ⟨29310259521233394530274809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78160692056622385414066157 29310259521233394530274809)
        ·
          refine ⟨21982694640925045897706107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29310259521233394530274809 21982694640925045897706107)
          ·
            refine ⟨32974041961387568846559161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21982694640925045897706107 32974041961387568846559161)
            ·
              refine ⟨24730531471040676634919371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32974041961387568846559161 24730531471040676634919371)
              ·
                refine ⟨37095797206561014952379057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24730531471040676634919371 37095797206561014952379057)
                ·
                  refine ⟨27821847904920761214284293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37095797206561014952379057 27821847904920761214284293)
                  ·
                    refine ⟨5216596482172642727678305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27821847904920761214284293 5216596482172642727678305)
                    ·
                      refine ⟨3912447361629482045758729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5216596482172642727678305 3912447361629482045758729)
                      ·
                        rfl

theorem cell23_7619464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 1, 2, 4, 2].length) (baseStart_7619464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7619464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7619464 prefixEnd_7619464 := by exact prefixLift 7619464
  have htrace : WordTrace (prefixWord ++ tailWord_7619464) baseStart_7619464 baseEnd_7619464 := by
    simpa [prefixWord, tailWord_7619464, baseEnd_7619464] using wordTrace_append hprefix tailTrace_7619464
  have hstable : (prefixWord ++ tailWord_7619464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7619464).length < 2 ^ (prefixWord ++ tailWord_7619464).sum := by decide
  have hdescent : baseEnd_7619464 < baseStart_7619464 := by decide
  rcases family_descends (prefixWord ++ tailWord_7619464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7619507 : List Nat := [1, 1, 1, 2, 3, 1, 2, 2, 3, 5, 2]
def baseStart_7619507 : Nat := 118140960795 + 7619507 * 2 ^ 59
def prefixEnd_7619507 : Nat := 4983230072969 + 3 ^ 40 * 7619507 * 2
def baseEnd_7619507 : Nat := 3912469441297625377521031

theorem tailTrace_7619507 : CollatzResearch.WordTrace tailWord_7619507 prefixEnd_7619507 3912469441297625377521031 := by
  unfold tailWord_7619507
  simp only [CollatzResearch.WordTrace]
  refine ⟨277906251206834922038272775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185270834137889948025515183 277906251206834922038272775)
  ·
    refine ⟨416859376810252383057409163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277906251206834922038272775 416859376810252383057409163)
    ·
      refine ⟨625289065215378574586113745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 416859376810252383057409163 625289065215378574586113745)
      ·
        refine ⟨468966798911533930939585309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 625289065215378574586113745 468966798911533930939585309)
        ·
          refine ⟨175862549591825224102344491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 468966798911533930939585309 175862549591825224102344491)
          ·
            refine ⟨263793824387737836153516737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175862549591825224102344491 263793824387737836153516737)
            ·
              refine ⟨197845368290803377115137553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 263793824387737836153516737 197845368290803377115137553)
              ·
                refine ⟨148384026218102532836353165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 197845368290803377115137553 148384026218102532836353165)
                ·
                  refine ⟨55644009831788449813632437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 148384026218102532836353165 55644009831788449813632437)
                  ·
                    refine ⟨5216625921730167170028041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55644009831788449813632437 5216625921730167170028041)
                    ·
                      refine ⟨3912469441297625377521031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5216625921730167170028041 3912469441297625377521031)
                      ·
                        rfl

theorem cell23_7619507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 3, 5, 2].length) (baseStart_7619507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7619507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7619507 prefixEnd_7619507 := by exact prefixLift 7619507
  have htrace : WordTrace (prefixWord ++ tailWord_7619507) baseStart_7619507 baseEnd_7619507 := by
    simpa [prefixWord, tailWord_7619507, baseEnd_7619507] using wordTrace_append hprefix tailTrace_7619507
  have hstable : (prefixWord ++ tailWord_7619507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7619507).length < 2 ^ (prefixWord ++ tailWord_7619507).sum := by decide
  have hdescent : baseEnd_7619507 < baseStart_7619507 := by decide
  rcases family_descends (prefixWord ++ tailWord_7619507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7619508 : List Nat := [2, 5, 2, 1, 1, 3, 1, 1, 3, 4]
def baseStart_7619508 : Nat := 118140960795 + 7619508 * 2 ^ 59
def prefixEnd_7619508 : Nat := 4983230072969 + 3 ^ 40 * 7619508 * 2
def baseEnd_7619508 : Nat := 1304156651592759957869509

theorem tailTrace_7619508 : CollatzResearch.WordTrace tailWord_7619508 prefixEnd_7619508 1304156651592759957869509 := by
  unfold tailWord_7619508
  simp only [CollatzResearch.WordTrace]
  refine ⟨138953143839915649604529589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185270858453220866139372785 138953143839915649604529589)
  ·
    refine ⟨13026857234992092150424649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 138953143839915649604529589 13026857234992092150424649)
    ·
      refine ⟨9770142926244069112818487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13026857234992092150424649 9770142926244069112818487)
      ·
        refine ⟨14655214389366103669227731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9770142926244069112818487 14655214389366103669227731)
        ·
          refine ⟨21982821584049155503841597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14655214389366103669227731 21982821584049155503841597)
          ·
            refine ⟨8243558094018433313940599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21982821584049155503841597 8243558094018433313940599)
            ·
              refine ⟨12365337141027649970910899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8243558094018433313940599 12365337141027649970910899)
              ·
                refine ⟨18548005711541474956366349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12365337141027649970910899 18548005711541474956366349)
                ·
                  refine ⟨6955502141828053108637381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18548005711541474956366349 6955502141828053108637381)
                  ·
                    refine ⟨1304156651592759957869509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6955502141828053108637381 1304156651592759957869509)
                    ·
                      rfl

theorem cell23_7619508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_7619508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7619508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7619508 prefixEnd_7619508 := by exact prefixLift 7619508
  have htrace : WordTrace (prefixWord ++ tailWord_7619508) baseStart_7619508 baseEnd_7619508 := by
    simpa [prefixWord, tailWord_7619508, baseEnd_7619508] using wordTrace_append hprefix tailTrace_7619508
  have hstable : (prefixWord ++ tailWord_7619508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7619508).length < 2 ^ (prefixWord ++ tailWord_7619508).sum := by decide
  have hdescent : baseEnd_7619508 < baseStart_7619508 := by decide
  rcases family_descends (prefixWord ++ tailWord_7619508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7619534 : List Nat := [4, 1, 1, 1, 2, 3, 3, 2, 1, 5]
def baseStart_7619534 : Nat := 118140960795 + 7619534 * 2 ^ 59
def prefixEnd_7619534 : Nat := 4983230072969 + 3 ^ 40 * 7619534 * 2
def baseEnd_7619534 : Nat := 1304161101758432257294469

theorem tailTrace_7619534 : CollatzResearch.WordTrace tailWord_7619534 prefixEnd_7619534 1304161101758432257294469 := by
  unfold tailWord_7619534
  simp only [CollatzResearch.WordTrace]
  refine ⟨34738404497217138206188207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185271490651824737099670437 34738404497217138206188207)
  ·
    refine ⟨52107606745825707309282311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34738404497217138206188207 52107606745825707309282311)
    ·
      refine ⟨78161410118738560963923467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52107606745825707309282311 78161410118738560963923467)
      ·
        refine ⟨117242115178107841445885201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78161410118738560963923467 117242115178107841445885201)
        ·
          refine ⟨87931586383580881084413901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117242115178107841445885201 87931586383580881084413901)
          ·
            refine ⟨32974344893842830406655213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87931586383580881084413901 32974344893842830406655213)
            ·
              refine ⟨12365379335191061402495705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32974344893842830406655213 12365379335191061402495705)
              ·
                refine ⟨9274034501393296051871779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12365379335191061402495705 9274034501393296051871779)
                ·
                  refine ⟨13911051752089944077807669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9274034501393296051871779 13911051752089944077807669)
                  ·
                    refine ⟨1304161101758432257294469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13911051752089944077807669 1304161101758432257294469)
                    ·
                      rfl

theorem cell23_7619534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 3, 2, 1, 5].length) (baseStart_7619534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7619534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7619534 prefixEnd_7619534 := by exact prefixLift 7619534
  have htrace : WordTrace (prefixWord ++ tailWord_7619534) baseStart_7619534 baseEnd_7619534 := by
    simpa [prefixWord, tailWord_7619534, baseEnd_7619534] using wordTrace_append hprefix tailTrace_7619534
  have hstable : (prefixWord ++ tailWord_7619534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7619534).length < 2 ^ (prefixWord ++ tailWord_7619534).sum := by decide
  have hdescent : baseEnd_7619534 < baseStart_7619534 := by decide
  rcases family_descends (prefixWord ++ tailWord_7619534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7619537 : List Nat := [1, 2, 2, 1, 2, 1, 5, 1, 3, 1, 4]
def baseStart_7619537 : Nat := 118140960795 + 7619537 * 2 ^ 59
def prefixEnd_7619537 : Nat := 4983230072969 + 3 ^ 40 * 7619537 * 2
def baseEnd_7619537 : Nat := 3912484845717260260145893

theorem tailTrace_7619537 : CollatzResearch.WordTrace tailWord_7619537 prefixEnd_7619537 3912484845717260260145893 := by
  unfold tailWord_7619537
  simp only [CollatzResearch.WordTrace]
  refine ⟨277907345396726237161864865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185271563597817491441243243 277907345396726237161864865)
  ·
    refine ⟨208430509047544677871398649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277907345396726237161864865 208430509047544677871398649)
    ·
      refine ⟨156322881785658508403548987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208430509047544677871398649 156322881785658508403548987)
      ·
        refine ⟨234484322678487762605323481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156322881785658508403548987 234484322678487762605323481)
        ·
          refine ⟨175863242008865821953992611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234484322678487762605323481 175863242008865821953992611)
          ·
            refine ⟨263794863013298732930988917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175863242008865821953992611 263794863013298732930988917)
            ·
              refine ⟨24730768407496756212280211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 263794863013298732930988917 24730768407496756212280211)
              ·
                refine ⟨37096152611245134318420317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24730768407496756212280211 37096152611245134318420317)
                ·
                  refine ⟨13911057229216925369407619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37096152611245134318420317 13911057229216925369407619)
                  ·
                    refine ⟨20866585843825388054111429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13911057229216925369407619 20866585843825388054111429)
                    ·
                      refine ⟨3912484845717260260145893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20866585843825388054111429 3912484845717260260145893)
                      ·
                        rfl

theorem cell23_7619537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 1, 3, 1, 4].length) (baseStart_7619537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7619537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7619537 prefixEnd_7619537 := by exact prefixLift 7619537
  have htrace : WordTrace (prefixWord ++ tailWord_7619537) baseStart_7619537 baseEnd_7619537 := by
    simpa [prefixWord, tailWord_7619537, baseEnd_7619537] using wordTrace_append hprefix tailTrace_7619537
  have hstable : (prefixWord ++ tailWord_7619537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7619537).length < 2 ^ (prefixWord ++ tailWord_7619537).sum := by decide
  have hdescent : baseEnd_7619537 < baseStart_7619537 := by decide
  rcases family_descends (prefixWord ++ tailWord_7619537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7619551 : List Nat := [1, 1, 2, 3, 5, 1, 3, 1, 1, 5]
def baseStart_7619551 : Nat := 118140960795 + 7619551 * 2 ^ 59
def prefixEnd_7619551 : Nat := 4983230072969 + 3 ^ 40 * 7619551 * 2
def baseEnd_7619551 : Nat := 1304164011482141068456943

theorem tailTrace_7619551 : CollatzResearch.WordTrace tailWord_7619551 prefixEnd_7619551 1304164011482141068456943 := by
  unfold tailWord_7619551
  simp only [CollatzResearch.WordTrace]
  refine ⟨277907856018675517552874507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185271904012450345035249671 277907856018675517552874507)
  ·
    refine ⟨416861784028013276329311761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277907856018675517552874507 416861784028013276329311761)
    ·
      refine ⟨312646338021009957246983821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 416861784028013276329311761 312646338021009957246983821)
      ·
        refine ⟨117242376757878733967618933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 312646338021009957246983821 117242376757878733967618933)
        ·
          refine ⟨10991472821051131309464275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 117242376757878733967618933 10991472821051131309464275)
          ·
            refine ⟨16487209231576696964196413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10991472821051131309464275 16487209231576696964196413)
            ·
              refine ⟨6182703461841261361573655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16487209231576696964196413 6182703461841261361573655)
              ·
                refine ⟨9274055192761892042360483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6182703461841261361573655 9274055192761892042360483)
                ·
                  refine ⟨13911082789142838063540725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9274055192761892042360483 13911082789142838063540725)
                  ·
                    refine ⟨1304164011482141068456943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13911082789142838063540725 1304164011482141068456943)
                    ·
                      rfl

theorem cell23_7619551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 3, 1, 1, 5].length) (baseStart_7619551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7619551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7619551 prefixEnd_7619551 := by exact prefixLift 7619551
  have htrace : WordTrace (prefixWord ++ tailWord_7619551) baseStart_7619551 baseEnd_7619551 := by
    simpa [prefixWord, tailWord_7619551, baseEnd_7619551] using wordTrace_append hprefix tailTrace_7619551
  have hstable : (prefixWord ++ tailWord_7619551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7619551).length < 2 ^ (prefixWord ++ tailWord_7619551).sum := by decide
  have hdescent : baseEnd_7619551 < baseStart_7619551 := by decide
  rcases family_descends (prefixWord ++ tailWord_7619551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7619594 : List Nat := [3, 1, 2, 2, 3, 2, 3, 7]
def baseStart_7619594 : Nat := 118140960795 + 7619594 * 2 ^ 59
def prefixEnd_7619594 : Nat := 4983230072969 + 3 ^ 40 * 7619594 * 2
def baseEnd_7619594 : Nat := 144907930152391353227153

theorem tailTrace_7619594 : CollatzResearch.WordTrace tailWord_7619594 prefixEnd_7619594 144907930152391353227153 := by
  unfold tailWord_7619594
  simp only [CollatzResearch.WordTrace]
  refine ⟨69477356089379933974172459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185272949571679823931126557 69477356089379933974172459)
  ·
    refine ⟨104216034134069900961258689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69477356089379933974172459 104216034134069900961258689)
    ·
      refine ⟨78162025600552425720944017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104216034134069900961258689 78162025600552425720944017)
      ·
        refine ⟨58621519200414319290708013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78162025600552425720944017 58621519200414319290708013)
        ·
          refine ⟨21983069700155369734015505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58621519200414319290708013 21983069700155369734015505)
          ·
            refine ⟨16487302275116527300511629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21983069700155369734015505 16487302275116527300511629)
            ·
              refine ⟨6182738353168697737691861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16487302275116527300511629 6182738353168697737691861)
              ·
                refine ⟨144907930152391353227153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6182738353168697737691861 144907930152391353227153)
                ·
                  rfl

theorem cell23_7619594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 3, 7].length) (baseStart_7619594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7619594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7619594 prefixEnd_7619594 := by exact prefixLift 7619594
  have htrace : WordTrace (prefixWord ++ tailWord_7619594) baseStart_7619594 baseEnd_7619594 := by
    simpa [prefixWord, tailWord_7619594, baseEnd_7619594] using wordTrace_append hprefix tailTrace_7619594
  have hstable : (prefixWord ++ tailWord_7619594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7619594).length < 2 ^ (prefixWord ++ tailWord_7619594).sum := by decide
  have hdescent : baseEnd_7619594 < baseStart_7619594 := by decide
  rcases family_descends (prefixWord ++ tailWord_7619594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7619602 : List Nat := [3, 2, 5, 1, 1, 2, 2, 1, 1, 5]
def baseStart_7619602 : Nat := 118140960795 + 7619602 * 2 ^ 59
def prefixEnd_7619602 : Nat := 4983230072969 + 3 ^ 40 * 7619602 * 2
def baseEnd_7619602 : Nat := 1304172740653267501944365

theorem tailTrace_7619602 : CollatzResearch.WordTrace tailWord_7619602 prefixEnd_7619602 1304172740653267501944365 := by
  unfold tailWord_7619602
  simp only [CollatzResearch.WordTrace]
  refine ⟨69477429035372688315745265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185273144094327168841987373 69477429035372688315745265)
  ·
    refine ⟨52108071776529516236808949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69477429035372688315745265 52108071776529516236808949)
    ·
      refine ⟨4885131729049642147200839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 52108071776529516236808949 4885131729049642147200839)
      ·
        refine ⟨7327697593574463220801259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4885131729049642147200839 7327697593574463220801259)
        ·
          refine ⟨10991546390361694831201889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7327697593574463220801259 10991546390361694831201889)
          ·
            refine ⟨8243659792771271123401417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10991546390361694831201889 8243659792771271123401417)
            ·
              refine ⟨6182744844578453342551063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8243659792771271123401417 6182744844578453342551063)
              ·
                refine ⟨9274117266867680013826595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6182744844578453342551063 9274117266867680013826595)
                ·
                  refine ⟨13911175900301520020739893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9274117266867680013826595 13911175900301520020739893)
                  ·
                    refine ⟨1304172740653267501944365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13911175900301520020739893 1304172740653267501944365)
                    ·
                      rfl

theorem cell23_7619602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_7619602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7619602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7619602 prefixEnd_7619602 := by exact prefixLift 7619602
  have htrace : WordTrace (prefixWord ++ tailWord_7619602) baseStart_7619602 baseEnd_7619602 := by
    simpa [prefixWord, tailWord_7619602, baseEnd_7619602] using wordTrace_append hprefix tailTrace_7619602
  have hstable : (prefixWord ++ tailWord_7619602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7619602).length < 2 ^ (prefixWord ++ tailWord_7619602).sum := by decide
  have hdescent : baseEnd_7619602 < baseStart_7619602 := by decide
  rcases family_descends (prefixWord ++ tailWord_7619602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7619605 : List Nat := [1, 3, 2, 1, 4, 2, 2, 3, 1, 2, 2]
def baseStart_7619605 : Nat := 118140960795 + 7619605 * 2 ^ 59
def prefixEnd_7619605 : Nat := 4983230072969 + 3 ^ 40 * 7619605 * 2
def baseEnd_7619605 : Nat := 3912519762401765994095581

theorem tailTrace_7619605 : CollatzResearch.WordTrace tailWord_7619605 prefixEnd_7619605 3912519762401765994095581 := by
  unfold tailWord_7619605
  simp only [CollatzResearch.WordTrace]
  refine ⟨277909825560479884775340269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185273217040319923183560179 277909825560479884775340269)
  ·
    refine ⟨104216184585179956790752601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 277909825560479884775340269 104216184585179956790752601)
    ·
      refine ⟨78162138438884967593064451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104216184585179956790752601 78162138438884967593064451)
      ·
        refine ⟨117243207658327451389596677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78162138438884967593064451 117243207658327451389596677)
        ·
          refine ⟨21983101435936397135549377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 117243207658327451389596677 21983101435936397135549377)
          ·
            refine ⟨16487326076952297851662033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21983101435936397135549377 16487326076952297851662033)
            ·
              refine ⟨12365494557714223388746525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16487326076952297851662033 12365494557714223388746525)
              ·
                refine ⟨4637060459142833770779947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12365494557714223388746525 4637060459142833770779947)
                ·
                  refine ⟨6955590688714250656169921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4637060459142833770779947 6955590688714250656169921)
                  ·
                    refine ⟨5216693016535687992127441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6955590688714250656169921 5216693016535687992127441)
                    ·
                      refine ⟨3912519762401765994095581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5216693016535687992127441 3912519762401765994095581)
                      ·
                        rfl

theorem cell23_7619605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 2, 3, 1, 2, 2].length) (baseStart_7619605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7619605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7619605 prefixEnd_7619605 := by exact prefixLift 7619605
  have htrace : WordTrace (prefixWord ++ tailWord_7619605) baseStart_7619605 baseEnd_7619605 := by
    simpa [prefixWord, tailWord_7619605, baseEnd_7619605] using wordTrace_append hprefix tailTrace_7619605
  have hstable : (prefixWord ++ tailWord_7619605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7619605).length < 2 ^ (prefixWord ++ tailWord_7619605).sum := by decide
  have hdescent : baseEnd_7619605 < baseStart_7619605 := by decide
  rcases family_descends (prefixWord ++ tailWord_7619605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7619608 : List Nat := [2, 1, 2, 3, 2, 4, 2, 1, 1, 2, 3]
def baseStart_7619608 : Nat := 118140960795 + 7619608 * 2 ^ 59
def prefixEnd_7619608 : Nat := 4983230072969 + 3 ^ 40 * 7619608 * 2
def baseEnd_7619608 : Nat := 3912521302843729482358067

theorem tailTrace_7619608 : CollatzResearch.WordTrace tailWord_7619608 prefixEnd_7619608 3912521302843729482358067 := by
  unfold tailWord_7619608
  simp only [CollatzResearch.WordTrace]
  refine ⟨138954967489734508143849739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185273289986312677525132985 138954967489734508143849739)
  ·
    refine ⟨208432451234601762215774609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138954967489734508143849739 208432451234601762215774609)
    ·
      refine ⟨156324338425951321661830957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208432451234601762215774609 156324338425951321661830957)
      ·
        refine ⟨58621626909731745623186609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156324338425951321661830957 58621626909731745623186609)
        ·
          refine ⟨43966220182298809217389957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58621626909731745623186609 43966220182298809217389957)
          ·
            refine ⟨8243666284181026728260617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43966220182298809217389957 8243666284181026728260617)
            ·
              refine ⟨6182749713135770046195463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8243666284181026728260617 6182749713135770046195463)
              ·
                refine ⟨9274124569703655069293195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6182749713135770046195463 9274124569703655069293195)
                ·
                  refine ⟨13911186854555482603939793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9274124569703655069293195 13911186854555482603939793)
                  ·
                    refine ⟨10433390140916611952954845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13911186854555482603939793 10433390140916611952954845)
                    ·
                      refine ⟨3912521302843729482358067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10433390140916611952954845 3912521302843729482358067)
                      ·
                        rfl

theorem cell23_7619608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 2, 1, 1, 2, 3].length) (baseStart_7619608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7619608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7619608 prefixEnd_7619608 := by exact prefixLift 7619608
  have htrace : WordTrace (prefixWord ++ tailWord_7619608) baseStart_7619608 baseEnd_7619608 := by
    simpa [prefixWord, tailWord_7619608, baseEnd_7619608] using wordTrace_append hprefix tailTrace_7619608
  have hstable : (prefixWord ++ tailWord_7619608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7619608).length < 2 ^ (prefixWord ++ tailWord_7619608).sum := by decide
  have hdescent : baseEnd_7619608 < baseStart_7619608 := by decide
  rcases family_descends (prefixWord ++ tailWord_7619608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7619638 : List Nat := [5, 1, 2, 1, 1, 4, 1, 1, 1, 3, 3]
def baseStart_7619638 : Nat := 118140960795 + 7619638 * 2 ^ 59
def prefixEnd_7619638 : Nat := 4983230072969 + 3 ^ 40 * 7619638 * 2
def baseEnd_7619638 : Nat := 3912536707263364364982929

theorem tailTrace_7619638 : CollatzResearch.WordTrace tailWord_7619638 prefixEnd_7619638 3912536707263364364982929 := by
  unfold tailWord_7619638
  simp only [CollatzResearch.WordTrace]
  refine ⟨17369439323085020713205723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 185274019446240220940861045 17369439323085020713205723)
  ·
    refine ⟨26054158984627531069808585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17369439323085020713205723 26054158984627531069808585)
    ·
      refine ⟨19540619238470648302356439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26054158984627531069808585 19540619238470648302356439)
      ·
        refine ⟨29310928857705972453534659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19540619238470648302356439 29310928857705972453534659)
        ·
          refine ⟨43966393286558958680301989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29310928857705972453534659 43966393286558958680301989)
          ·
            refine ⟨8243698741229804752556623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43966393286558958680301989 8243698741229804752556623)
            ·
              refine ⟨12365548111844707128834935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8243698741229804752556623 12365548111844707128834935)
              ·
                refine ⟨18548322167767060693252403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12365548111844707128834935 18548322167767060693252403)
                ·
                  refine ⟨27822483251650591039878605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18548322167767060693252403 27822483251650591039878605)
                  ·
                    refine ⟨10433431219368971639954477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27822483251650591039878605 10433431219368971639954477)
                    ·
                      refine ⟨3912536707263364364982929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10433431219368971639954477 3912536707263364364982929)
                      ·
                        rfl

theorem cell23_7619638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 1, 1, 1, 3, 3].length) (baseStart_7619638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7619638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7619638 prefixEnd_7619638 := by exact prefixLift 7619638
  have htrace : WordTrace (prefixWord ++ tailWord_7619638) baseStart_7619638 baseEnd_7619638 := by
    simpa [prefixWord, tailWord_7619638, baseEnd_7619638] using wordTrace_append hprefix tailTrace_7619638
  have hstable : (prefixWord ++ tailWord_7619638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7619638).length < 2 ^ (prefixWord ++ tailWord_7619638).sum := by decide
  have hdescent : baseEnd_7619638 < baseStart_7619638 := by decide
  rcases family_descends (prefixWord ++ tailWord_7619638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7619647 : List Nat := [1, 1, 2, 2, 3, 1, 1, 4, 2, 1, 5]
def baseStart_7619647 : Nat := 118140960795 + 7619647 * 2 ^ 59
def prefixEnd_7619647 : Nat := 4983230072969 + 3 ^ 40 * 7619647 * 2
def baseEnd_7619647 : Nat := 3912541328589254829770387

theorem tailTrace_7619647 : CollatzResearch.WordTrace tailWord_7619647 prefixEnd_7619647 3912541328589254829770387 := by
  unfold tailWord_7619647
  simp only [CollatzResearch.WordTrace]
  refine ⟨277911357426327725948369195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185274238284218483965579463 277911357426327725948369195)
  ·
    refine ⟨416867036139491588922553793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277911357426327725948369195 416867036139491588922553793)
    ·
      refine ⟨312650277104618691691915345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 416867036139491588922553793 312650277104618691691915345)
      ·
        refine ⟨234487707828464018768936509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 312650277104618691691915345 234487707828464018768936509)
        ·
          refine ⟨87932890435674007038351191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 234487707828464018768936509 87932890435674007038351191)
          ·
            refine ⟨131899335653511010557526787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87932890435674007038351191 131899335653511010557526787)
            ·
              refine ⟨197849003480266515836290181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131899335653511010557526787 197849003480266515836290181)
              ·
                refine ⟨37096688152549971719304409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 197849003480266515836290181 37096688152549971719304409)
                ·
                  refine ⟨27822516114412478789478307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37096688152549971719304409 27822516114412478789478307)
                  ·
                    refine ⟨41733774171618718184217461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27822516114412478789478307 41733774171618718184217461)
                    ·
                      refine ⟨3912541328589254829770387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41733774171618718184217461 3912541328589254829770387)
                      ·
                        rfl

theorem cell23_7619647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 4, 2, 1, 5].length) (baseStart_7619647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7619647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7619647 prefixEnd_7619647 := by exact prefixLift 7619647
  have htrace : WordTrace (prefixWord ++ tailWord_7619647) baseStart_7619647 baseEnd_7619647 := by
    simpa [prefixWord, tailWord_7619647, baseEnd_7619647] using wordTrace_append hprefix tailTrace_7619647
  have hstable : (prefixWord ++ tailWord_7619647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7619647).length < 2 ^ (prefixWord ++ tailWord_7619647).sum := by decide
  have hdescent : baseEnd_7619647 < baseStart_7619647 := by decide
  rcases family_descends (prefixWord ++ tailWord_7619647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7619657 : List Nat := [1, 2, 1, 1, 2, 2, 2, 2, 4, 2, 4]
def baseStart_7619657 : Nat := 118140960795 + 7619657 * 2 ^ 59
def prefixEnd_7619657 : Nat := 4983230072969 + 3 ^ 40 * 7619657 * 2
def baseEnd_7619657 : Nat := 3912546463395799790645341

theorem tailTrace_7619657 : CollatzResearch.WordTrace tailWord_7619657 prefixEnd_7619657 3912546463395799790645341 := by
  unfold tailWord_7619657
  simp only [CollatzResearch.WordTrace]
  refine ⟨277911722156291497656233225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185274481437527665104155483 277911722156291497656233225)
  ·
    refine ⟨208433791617218623242174919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277911722156291497656233225 208433791617218623242174919)
    ·
      refine ⟨312650687425827934863262379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208433791617218623242174919 312650687425827934863262379)
      ·
        refine ⟨468976031138741902294893569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312650687425827934863262379 468976031138741902294893569)
        ·
          refine ⟨351732023354056426721170177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 468976031138741902294893569 351732023354056426721170177)
          ·
            refine ⟨263799017515542320040877633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 351732023354056426721170177 263799017515542320040877633)
            ·
              refine ⟨197849263136656740030658225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 263799017515542320040877633 197849263136656740030658225)
              ·
                refine ⟨148386947352492555022993669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 197849263136656740030658225 148386947352492555022993669)
                ·
                  refine ⟨27822552628592354066811313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 148386947352492555022993669 27822552628592354066811313)
                  ·
                    refine ⟨20866914471444265550108485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27822552628592354066811313 20866914471444265550108485)
                    ·
                      refine ⟨3912546463395799790645341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20866914471444265550108485 3912546463395799790645341)
                      ·
                        rfl

theorem cell23_7619657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 4, 2, 4].length) (baseStart_7619657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7619657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7619657 prefixEnd_7619657 := by exact prefixLift 7619657
  have htrace : WordTrace (prefixWord ++ tailWord_7619657) baseStart_7619657 baseEnd_7619657 := by
    simpa [prefixWord, tailWord_7619657, baseEnd_7619657] using wordTrace_append hprefix tailTrace_7619657
  have hstable : (prefixWord ++ tailWord_7619657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7619657).length < 2 ^ (prefixWord ++ tailWord_7619657).sum := by decide
  have hdescent : baseEnd_7619657 < baseStart_7619657 := by decide
  rcases family_descends (prefixWord ++ tailWord_7619657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7619697 : List Nat := [1, 2, 2, 2, 1, 1, 2, 4, 1, 7]
def baseStart_7619697 : Nat := 118140960795 + 7619697 * 2 ^ 59
def prefixEnd_7619697 : Nat := 4983230072969 + 3 ^ 40 * 7619697 * 2
def baseEnd_7619697 : Nat := 1304189000873993211381719

theorem tailTrace_7619697 : CollatzResearch.WordTrace tailWord_7619697 prefixEnd_7619697 1304189000873993211381719 := by
  unfold tailWord_7619697
  simp only [CollatzResearch.WordTrace]
  refine ⟨277913181076146584487689345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185275454050764389658459563 277913181076146584487689345)
  ·
    refine ⟨208434885807109938365767009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277913181076146584487689345 208434885807109938365767009)
    ·
      refine ⟨156326164355332453774325257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208434885807109938365767009 156326164355332453774325257)
      ·
        refine ⟨117244623266499340330743943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156326164355332453774325257 117244623266499340330743943)
        ·
          refine ⟨175866934899749010496115915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117244623266499340330743943 175866934899749010496115915)
          ·
            refine ⟨263800402349623515744173873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175866934899749010496115915 263800402349623515744173873)
            ·
              refine ⟨197850301762217636808130405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 263800402349623515744173873 197850301762217636808130405)
              ·
                refine ⟨37096931580415806901524451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 197850301762217636808130405 37096931580415806901524451)
                ·
                  refine ⟨55645397370623710352286677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37096931580415806901524451 55645397370623710352286677)
                  ·
                    refine ⟨1304189000873993211381719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55645397370623710352286677 1304189000873993211381719)
                    ·
                      rfl

theorem cell23_7619697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 4, 1, 7].length) (baseStart_7619697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7619697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7619697 prefixEnd_7619697 := by exact prefixLift 7619697
  have htrace : WordTrace (prefixWord ++ tailWord_7619697) baseStart_7619697 baseEnd_7619697 := by
    simpa [prefixWord, tailWord_7619697, baseEnd_7619697] using wordTrace_append hprefix tailTrace_7619697
  have hstable : (prefixWord ++ tailWord_7619697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7619697).length < 2 ^ (prefixWord ++ tailWord_7619697).sum := by decide
  have hdescent : baseEnd_7619697 < baseStart_7619697 := by decide
  rcases family_descends (prefixWord ++ tailWord_7619697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7619761 : List Nat := [1, 2, 2, 5, 1, 1, 1, 1, 5, 4]
def baseStart_7619761 : Nat := 118140960795 + 7619761 * 2 ^ 59
def prefixEnd_7619761 : Nat := 4983230072969 + 3 ^ 40 * 7619761 * 2
def baseEnd_7619761 : Nat := 1304199955127955794581621

theorem tailTrace_7619761 : CollatzResearch.WordTrace tailWord_7619761 prefixEnd_7619761 1304199955127955794581621 := by
  unfold tailWord_7619761
  simp only [CollatzResearch.WordTrace]
  refine ⟨277915515347914723418019137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185277010231943148945346091 277915515347914723418019137)
  ·
    refine ⟨208436636510936042563514353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277915515347914723418019137 208436636510936042563514353)
    ·
      refine ⟨156327477383202031922635765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208436636510936042563514353 156327477383202031922635765)
      ·
        refine ⟨14655701004675190492747103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 156327477383202031922635765 14655701004675190492747103)
        ·
          refine ⟨21983551507012785739120655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14655701004675190492747103 21983551507012785739120655)
          ·
            refine ⟨32975327260519178608680983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21983551507012785739120655 32975327260519178608680983)
            ·
              refine ⟨49462990890778767913021475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32975327260519178608680983 49462990890778767913021475)
              ·
                refine ⟨74194486336168151869532213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49462990890778767913021475 74194486336168151869532213)
                ·
                  refine ⟨6955733094015764237768645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74194486336168151869532213 6955733094015764237768645)
                  ·
                    refine ⟨1304199955127955794581621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6955733094015764237768645 1304199955127955794581621)
                    ·
                      rfl

theorem cell23_7619761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 1, 5, 4].length) (baseStart_7619761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7619761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7619761 prefixEnd_7619761 := by exact prefixLift 7619761
  have htrace : WordTrace (prefixWord ++ tailWord_7619761) baseStart_7619761 baseEnd_7619761 := by
    simpa [prefixWord, tailWord_7619761, baseEnd_7619761] using wordTrace_append hprefix tailTrace_7619761
  have hstable : (prefixWord ++ tailWord_7619761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7619761).length < 2 ^ (prefixWord ++ tailWord_7619761).sum := by decide
  have hdescent : baseEnd_7619761 < baseStart_7619761 := by decide
  rcases family_descends (prefixWord ++ tailWord_7619761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7619794 : List Nat := [3, 2, 2, 2, 1, 1, 1, 1, 1, 1, 8]
def baseStart_7619794 : Nat := 118140960795 + 7619794 * 2 ^ 59
def prefixEnd_7619794 : Nat := 4983230072969 + 3 ^ 40 * 7619794 * 2
def baseEnd_7619794 : Nat := 3912616810245465754632211

theorem tailTrace_7619794 : CollatzResearch.WordTrace tailWord_7619794 prefixEnd_7619794 3912616810245465754632211 := by
  unfold tailWord_7619794
  simp only [CollatzResearch.WordTrace]
  refine ⟨69479179739198792513492609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185277812637863446702646957 69479179739198792513492609)
  ·
    refine ⟨52109384804399094385119457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69479179739198792513492609 52109384804399094385119457)
    ·
      refine ⟨39082038603299320788839593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52109384804399094385119457 39082038603299320788839593)
      ·
        refine ⟨29311528952474490591629695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39082038603299320788839593 29311528952474490591629695)
        ·
          refine ⟨43967293428711735887444543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29311528952474490591629695 43967293428711735887444543)
          ·
            refine ⟨65950940143067603831166815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43967293428711735887444543 65950940143067603831166815)
            ·
              refine ⟨98926410214601405746750223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65950940143067603831166815 98926410214601405746750223)
              ·
                refine ⟨148389615321902108620125335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98926410214601405746750223 148389615321902108620125335)
                ·
                  refine ⟨222584422982853162930188003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 148389615321902108620125335 222584422982853162930188003)
                  ·
                    refine ⟨333876634474279744395282005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 222584422982853162930188003 333876634474279744395282005)
                    ·
                      refine ⟨3912616810245465754632211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 333876634474279744395282005 3912616810245465754632211)
                      ·
                        rfl

theorem cell23_7619794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_7619794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7619794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7619794 prefixEnd_7619794 := by exact prefixLift 7619794
  have htrace : WordTrace (prefixWord ++ tailWord_7619794) baseStart_7619794 baseEnd_7619794 := by
    simpa [prefixWord, tailWord_7619794, baseEnd_7619794] using wordTrace_append hprefix tailTrace_7619794
  have hstable : (prefixWord ++ tailWord_7619794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7619794).length < 2 ^ (prefixWord ++ tailWord_7619794).sum := by decide
  have hdescent : baseEnd_7619794 < baseStart_7619794 := by decide
  rcases family_descends (prefixWord ++ tailWord_7619794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7619818 : List Nat := [3, 1, 3, 1, 1, 3, 2, 2, 3, 1, 3]
def baseStart_7619818 : Nat := 118140960795 + 7619818 * 2 ^ 59
def prefixEnd_7619818 : Nat := 4983230072969 + 3 ^ 40 * 7619818 * 2
def baseEnd_7619818 : Nat := 3912629133781173660732101

theorem tailTrace_7619818 : CollatzResearch.WordTrace tailWord_7619818 prefixEnd_7619818 3912629133781173660732101 := by
  unfold tailWord_7619818
  simp only [CollatzResearch.WordTrace]
  refine ⟨69479398577177055538211027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185278396205805481435229405 69479398577177055538211027)
  ·
    refine ⟨104219097865765583307316541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69479398577177055538211027 104219097865765583307316541)
    ·
      refine ⟨39082161699662093740243703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104219097865765583307316541 39082161699662093740243703)
      ·
        refine ⟨58623242549493140610365555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39082161699662093740243703 58623242549493140610365555)
        ·
          refine ⟨87934863824239710915548333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58623242549493140610365555 87934863824239710915548333)
          ·
            refine ⟨32975573934089891593330625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87934863824239710915548333 32975573934089891593330625)
            ·
              refine ⟨24731680450567418694997969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32975573934089891593330625 24731680450567418694997969)
              ·
                refine ⟨18548760337925564021248477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24731680450567418694997969 18548760337925564021248477)
                ·
                  refine ⟨6955785126722086507968179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18548760337925564021248477 6955785126722086507968179)
                  ·
                    refine ⟨10433677690083129761952269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6955785126722086507968179 10433677690083129761952269)
                    ·
                      refine ⟨3912629133781173660732101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10433677690083129761952269 3912629133781173660732101)
                      ·
                        rfl

theorem cell23_7619818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 2, 3, 1, 3].length) (baseStart_7619818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7619818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7619818 prefixEnd_7619818 := by exact prefixLift 7619818
  have htrace : WordTrace (prefixWord ++ tailWord_7619818) baseStart_7619818 baseEnd_7619818 := by
    simpa [prefixWord, tailWord_7619818, baseEnd_7619818] using wordTrace_append hprefix tailTrace_7619818
  have hstable : (prefixWord ++ tailWord_7619818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7619818).length < 2 ^ (prefixWord ++ tailWord_7619818).sum := by decide
  have hdescent : baseEnd_7619818 < baseStart_7619818 := by decide
  rcases family_descends (prefixWord ++ tailWord_7619818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7619834 : List Nat := [3, 1, 1, 1, 1, 4, 2, 1, 3, 6]
def baseStart_7619834 : Nat := 118140960795 + 7619834 * 2 ^ 59
def prefixEnd_7619834 : Nat := 4983230072969 + 3 ^ 40 * 7619834 * 2
def baseEnd_7619834 : Nat := 1304212449823881866044009

theorem tailTrace_7619834 : CollatzResearch.WordTrace tailWord_7619834 prefixEnd_7619834 1304212449823881866044009 := by
  unfold tailWord_7619834
  simp only [CollatzResearch.WordTrace]
  refine ⟨69479544469162564221356639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185278785251100171256951037 69479544469162564221356639)
  ·
    refine ⟨104219316703743846332034959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69479544469162564221356639 104219316703743846332034959)
    ·
      refine ⟨156328975055615769498052439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104219316703743846332034959 156328975055615769498052439)
      ·
        refine ⟨234493462583423654247078659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156328975055615769498052439 234493462583423654247078659)
        ·
          refine ⟨351740193875135481370617989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234493462583423654247078659 351740193875135481370617989)
          ·
            refine ⟨65951286351587902756990873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 351740193875135481370617989 65951286351587902756990873)
            ·
              refine ⟨49463464763690927067743155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65951286351587902756990873 49463464763690927067743155)
              ·
                refine ⟨74195197145536390601614733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49463464763690927067743155 74195197145536390601614733)
                ·
                  refine ⟨27823198929576146475605525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74195197145536390601614733 27823198929576146475605525)
                  ·
                    refine ⟨1304212449823881866044009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27823198929576146475605525 1304212449823881866044009)
                    ·
                      rfl

theorem cell23_7619834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 1, 3, 6].length) (baseStart_7619834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7619834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7619834 prefixEnd_7619834 := by exact prefixLift 7619834
  have htrace : WordTrace (prefixWord ++ tailWord_7619834) baseStart_7619834 baseEnd_7619834 := by
    simpa [prefixWord, tailWord_7619834, baseEnd_7619834] using wordTrace_append hprefix tailTrace_7619834
  have hstable : (prefixWord ++ tailWord_7619834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7619834).length < 2 ^ (prefixWord ++ tailWord_7619834).sum := by decide
  have hdescent : baseEnd_7619834 < baseStart_7619834 := by decide
  rcases family_descends (prefixWord ++ tailWord_7619834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7619838 : List Nat := [4, 2, 2, 1, 1, 2, 2, 3, 1, 5]
def baseStart_7619838 : Nat := 118140960795 + 7619838 * 2 ^ 59
def prefixEnd_7619838 : Nat := 4983230072969 + 3 ^ 40 * 7619838 * 2
def baseEnd_7619838 : Nat := 1304213134464754527494003

theorem tailTrace_7619838 : CollatzResearch.WordTrace tailWord_7619838 prefixEnd_7619838 1304213134464754527494003 := by
  unfold tailWord_7619838
  simp only [CollatzResearch.WordTrace]
  refine ⟨34739790471079470696071521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185278882512423843712381445 34739790471079470696071521)
  ·
    refine ⟨26054842853309603022053641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34739790471079470696071521 26054842853309603022053641)
    ·
      refine ⟨19541132139982202266540231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26054842853309603022053641 19541132139982202266540231)
      ·
        refine ⟨29311698209973303399810347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19541132139982202266540231 29311698209973303399810347)
        ·
          refine ⟨43967547314959955099715521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29311698209973303399810347 43967547314959955099715521)
          ·
            refine ⟨32975660486219966324786641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43967547314959955099715521 32975660486219966324786641)
            ·
              refine ⟨24731745364664974743589981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32975660486219966324786641 24731745364664974743589981)
              ·
                refine ⟨9274404511749365528846243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24731745364664974743589981 9274404511749365528846243)
                ·
                  refine ⟨13911606767624048293269365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9274404511749365528846243 13911606767624048293269365)
                  ·
                    refine ⟨1304213134464754527494003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13911606767624048293269365 1304213134464754527494003)
                    ·
                      rfl

theorem cell23_7619838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 3, 1, 5].length) (baseStart_7619838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7619838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7619838 prefixEnd_7619838 := by exact prefixLift 7619838
  have htrace : WordTrace (prefixWord ++ tailWord_7619838) baseStart_7619838 baseEnd_7619838 := by
    simpa [prefixWord, tailWord_7619838, baseEnd_7619838] using wordTrace_append hprefix tailTrace_7619838
  have hstable : (prefixWord ++ tailWord_7619838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7619838).length < 2 ^ (prefixWord ++ tailWord_7619838).sum := by decide
  have hdescent : baseEnd_7619838 < baseStart_7619838 := by decide
  rcases family_descends (prefixWord ++ tailWord_7619838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7619851 : List Nat := [1, 1, 1, 1, 5, 3, 2, 1, 4, 4]
def baseStart_7619851 : Nat := 118140960795 + 7619851 * 2 ^ 59
def prefixEnd_7619851 : Nat := 4983230072969 + 3 ^ 40 * 7619851 * 2
def baseEnd_7619851 : Nat := 1304215359547590677206483

theorem tailTrace_7619851 : CollatzResearch.WordTrace tailWord_7619851 prefixEnd_7619851 1304215359547590677206483 := by
  unfold tailWord_7619851
  simp only [CollatzResearch.WordTrace]
  refine ⟨277918797917588668788795407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185279198611725779192530271 277918797917588668788795407)
  ·
    refine ⟨416878196876383003183193111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277918797917588668788795407 416878196876383003183193111)
    ·
      refine ⟨625317295314574504774789667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 416878196876383003183193111 625317295314574504774789667)
      ·
        refine ⟨937975942971861757162184501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 625317295314574504774789667 937975942971861757162184501)
        ·
          refine ⟨87935244653612039733954797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 937975942971861757162184501 87935244653612039733954797)
          ·
            refine ⟨32975716745104514900233049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87935244653612039733954797 32975716745104514900233049)
            ·
              refine ⟨24731787558828386175174787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32975716745104514900233049 24731787558828386175174787)
              ·
                refine ⟨37097681338242579262762181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24731787558828386175174787 37097681338242579262762181)
                ·
                  refine ⟨6955815250920483611767909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37097681338242579262762181 6955815250920483611767909)
                  ·
                    refine ⟨1304215359547590677206483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6955815250920483611767909 1304215359547590677206483)
                    ·
                      rfl

theorem cell23_7619851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 1, 4, 4].length) (baseStart_7619851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7619851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7619851 prefixEnd_7619851 := by exact prefixLift 7619851
  have htrace : WordTrace (prefixWord ++ tailWord_7619851) baseStart_7619851 baseEnd_7619851 := by
    simpa [prefixWord, tailWord_7619851, baseEnd_7619851] using wordTrace_append hprefix tailTrace_7619851
  have hstable : (prefixWord ++ tailWord_7619851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7619851).length < 2 ^ (prefixWord ++ tailWord_7619851).sum := by decide
  have hdescent : baseEnd_7619851 < baseStart_7619851 := by decide
  rcases family_descends (prefixWord ++ tailWord_7619851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7619852 : List Nat := [2, 2, 1, 2, 2, 4, 3, 2, 1, 1, 3]
def baseStart_7619852 : Nat := 118140960795 + 7619852 * 2 ^ 59
def prefixEnd_7619852 : Nat := 4983230072969 + 3 ^ 40 * 7619852 * 2
def baseEnd_7619852 : Nat := 3912646592123426527706945

theorem tailTrace_7619852 : CollatzResearch.WordTrace tailWord_7619852 prefixEnd_7619852 3912646592123426527706945 := by
  unfold tailWord_7619852
  simp only [CollatzResearch.WordTrace]
  refine ⟨138959417195292522979790905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185279222927056697306387873 138959417195292522979790905)
  ·
    refine ⟨104219562896469392234843179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138959417195292522979790905 104219562896469392234843179)
    ·
      refine ⟨156329344344704088352264769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104219562896469392234843179 156329344344704088352264769)
      ·
        refine ⟨117247008258528066264198577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156329344344704088352264769 117247008258528066264198577)
        ·
          refine ⟨87935256193896049698148933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117247008258528066264198577 87935256193896049698148933)
          ·
            refine ⟨16487860536355509318402925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87935256193896049698148933 16487860536355509318402925)
            ·
              refine ⟨6182947701133315994401097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16487860536355509318402925 6182947701133315994401097)
              ·
                refine ⟨4637210775849986995800823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6182947701133315994401097 4637210775849986995800823)
                ·
                  refine ⟨6955816163774980493701235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4637210775849986995800823 6955816163774980493701235)
                  ·
                    refine ⟨10433724245662470740551853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6955816163774980493701235 10433724245662470740551853)
                    ·
                      refine ⟨3912646592123426527706945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10433724245662470740551853 3912646592123426527706945)
                      ·
                        rfl

theorem cell23_7619852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 3, 2, 1, 1, 3].length) (baseStart_7619852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7619852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7619852 prefixEnd_7619852 := by exact prefixLift 7619852
  have htrace : WordTrace (prefixWord ++ tailWord_7619852) baseStart_7619852 baseEnd_7619852 := by
    simpa [prefixWord, tailWord_7619852, baseEnd_7619852] using wordTrace_append hprefix tailTrace_7619852
  have hstable : (prefixWord ++ tailWord_7619852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7619852).length < 2 ^ (prefixWord ++ tailWord_7619852).sum := by decide
  have hdescent : baseEnd_7619852 < baseStart_7619852 := by decide
  rcases family_descends (prefixWord ++ tailWord_7619852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7619861 : List Nat := [1, 3, 2, 1, 2, 1, 1, 4, 3, 2, 3]
def baseStart_7619861 : Nat := 118140960795 + 7619861 * 2 ^ 59
def prefixEnd_7619861 : Nat := 4983230072969 + 3 ^ 40 * 7619861 * 2
def baseEnd_7619861 : Nat := 3912651213449316992494403

theorem tailTrace_7619861 : CollatzResearch.WordTrace tailWord_7619861 prefixEnd_7619861 3912651213449316992494403 := by
  unfold tailWord_7619861
  simp only [CollatzResearch.WordTrace]
  refine ⟨277919162647552440496659437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185279441765034960331106291 277919162647552440496659437)
  ·
    refine ⟨104219685992832165186247289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 277919162647552440496659437 104219685992832165186247289)
    ·
      refine ⟨78164764494624123889685467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104219685992832165186247289 78164764494624123889685467)
      ·
        refine ⟨117247146741936185834528201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78164764494624123889685467 117247146741936185834528201)
        ·
          refine ⟨87935360056452139375896151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117247146741936185834528201 87935360056452139375896151)
          ·
            refine ⟨131903040084678209063844227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87935360056452139375896151 131903040084678209063844227)
            ·
              refine ⟨197854560127017313595766341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131903040084678209063844227 197854560127017313595766341)
              ·
                refine ⟨37097730023815746299206189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 197854560127017313595766341 37097730023815746299206189)
                ·
                  refine ⟨13911648758930904862202321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37097730023815746299206189 13911648758930904862202321)
                  ·
                    refine ⟨10433736569198178646651741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13911648758930904862202321 10433736569198178646651741)
                    ·
                      refine ⟨3912651213449316992494403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10433736569198178646651741 3912651213449316992494403)
                      ·
                        rfl

theorem cell23_7619861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 4, 3, 2, 3].length) (baseStart_7619861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7619861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7619861 prefixEnd_7619861 := by exact prefixLift 7619861
  have htrace : WordTrace (prefixWord ++ tailWord_7619861) baseStart_7619861 baseEnd_7619861 := by
    simpa [prefixWord, tailWord_7619861, baseEnd_7619861] using wordTrace_append hprefix tailTrace_7619861
  have hstable : (prefixWord ++ tailWord_7619861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7619861).length < 2 ^ (prefixWord ++ tailWord_7619861).sum := by decide
  have hdescent : baseEnd_7619861 < baseStart_7619861 := by decide
  rcases family_descends (prefixWord ++ tailWord_7619861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7619864 : List Nat := [2, 1, 2, 3, 1, 3, 1, 10]
def baseStart_7619864 : Nat := 118140960795 + 7619864 * 2 ^ 59
def prefixEnd_7619864 : Nat := 4983230072969 + 3 ^ 40 * 7619864 * 2
def baseEnd_7619864 : Nat := 144913064958936314102107

theorem tailTrace_7619864 : CollatzResearch.WordTrace tailWord_7619864 prefixEnd_7619864 144913064958936314102107 := by
  unfold tailWord_7619864
  simp only [CollatzResearch.WordTrace]
  refine ⟨138959636033270786004509323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185279514711027714672679097 138959636033270786004509323)
  ·
    refine ⟨208439454049906179006763985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138959636033270786004509323 208439454049906179006763985)
    ·
      refine ⟨156329590537429634255072989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208439454049906179006763985 156329590537429634255072989)
      ·
        refine ⟨58623596451536112845652371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156329590537429634255072989 58623596451536112845652371)
        ·
          refine ⟨87935394677304169268478557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58623596451536112845652371 87935394677304169268478557)
          ·
            refine ⟨32975773003989063475679459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87935394677304169268478557 32975773003989063475679459)
            ·
              refine ⟨49463659505983595213519189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32975773003989063475679459 49463659505983595213519189)
              ·
                refine ⟨144913064958936314102107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 49463659505983595213519189 144913064958936314102107)
                ·
                  rfl

theorem cell23_7619864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 10].length) (baseStart_7619864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7619864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7619864 prefixEnd_7619864 := by exact prefixLift 7619864
  have htrace : WordTrace (prefixWord ++ tailWord_7619864) baseStart_7619864 baseEnd_7619864 := by
    simpa [prefixWord, tailWord_7619864, baseEnd_7619864] using wordTrace_append hprefix tailTrace_7619864
  have hstable : (prefixWord ++ tailWord_7619864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7619864).length < 2 ^ (prefixWord ++ tailWord_7619864).sum := by decide
  have hdescent : baseEnd_7619864 < baseStart_7619864 := by decide
  rcases family_descends (prefixWord ++ tailWord_7619864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7619891 : List Nat := [1, 1, 1, 2, 5, 2, 1, 1, 3, 3, 3]
def baseStart_7619891 : Nat := 118140960795 + 7619891 * 2 ^ 59
def prefixEnd_7619891 : Nat := 4983230072969 + 3 ^ 40 * 7619891 * 2
def baseEnd_7619891 : Nat := 3912666617868951875119265

theorem tailTrace_7619891 : CollatzResearch.WordTrace tailWord_7619891 prefixEnd_7619891 3912666617868951875119265 := by
  unfold tailWord_7619891
  simp only [CollatzResearch.WordTrace]
  refine ⟨277920256837443755620251527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185280171224962503746834351 277920256837443755620251527)
  ·
    refine ⟨416880385256165633430377291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277920256837443755620251527 416880385256165633430377291)
    ·
      refine ⟨625320577884248450145565937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 416880385256165633430377291 625320577884248450145565937)
      ·
        refine ⟨468990433413186337609174453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 625320577884248450145565937 468990433413186337609174453)
        ·
          refine ⟨43967853132486219150860105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 468990433413186337609174453 43967853132486219150860105)
          ·
            refine ⟨32975889849364664363145079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43967853132486219150860105 32975889849364664363145079)
            ·
              refine ⟨49463834774046996544717619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32975889849364664363145079 49463834774046996544717619)
              ·
                refine ⟨74195752161070494817076429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49463834774046996544717619 74195752161070494817076429)
                ·
                  refine ⟨27823407060401435556403661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74195752161070494817076429 27823407060401435556403661)
                  ·
                    refine ⟨10433777647650538333651373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27823407060401435556403661 10433777647650538333651373)
                    ·
                      refine ⟨3912666617868951875119265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10433777647650538333651373 3912666617868951875119265)
                      ·
                        rfl

theorem cell23_7619891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 1, 3, 3, 3].length) (baseStart_7619891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7619891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7619891 prefixEnd_7619891 := by exact prefixLift 7619891
  have htrace : WordTrace (prefixWord ++ tailWord_7619891) baseStart_7619891 baseEnd_7619891 := by
    simpa [prefixWord, tailWord_7619891, baseEnd_7619891] using wordTrace_append hprefix tailTrace_7619891
  have hstable : (prefixWord ++ tailWord_7619891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7619891).length < 2 ^ (prefixWord ++ tailWord_7619891).sum := by decide
  have hdescent : baseEnd_7619891 < baseStart_7619891 := by decide
  rcases family_descends (prefixWord ++ tailWord_7619891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7619918 : List Nat := [4, 1, 1, 1, 1, 1, 3, 1, 5, 3, 2]
def baseStart_7619918 : Nat := 118140960795 + 7619918 * 2 ^ 59
def prefixEnd_7619918 : Nat := 4983230072969 + 3 ^ 40 * 7619918 * 2
def baseEnd_7619918 : Nat := 3912680481846623269481641

theorem tailTrace_7619918 : CollatzResearch.WordTrace tailWord_7619918 prefixEnd_7619918 3912680481846623269481641 := by
  unfold tailWord_7619918
  simp only [CollatzResearch.WordTrace]
  refine ⟨34740155201043242403935551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185280827738897292820989605 34740155201043242403935551)
  ·
    refine ⟨52110232801564863605903327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34740155201043242403935551 52110232801564863605903327)
    ·
      refine ⟨78165349202347295408854991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52110232801564863605903327 78165349202347295408854991)
      ·
        refine ⟨117248023803520943113282487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78165349202347295408854991 117248023803520943113282487)
        ·
          refine ⟨175872035705281414669923731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117248023803520943113282487 175872035705281414669923731)
          ·
            refine ⟨263808053557922122004885597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175872035705281414669923731 263808053557922122004885597)
            ·
              refine ⟨98928020084220795751832099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 263808053557922122004885597 98928020084220795751832099)
              ·
                refine ⟨148392030126331193627748149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98928020084220795751832099 148392030126331193627748149)
                ·
                  refine ⟨13911752824343549402601389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 148392030126331193627748149 13911752824343549402601389)
                  ·
                    refine ⟨5216907309128831025975521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13911752824343549402601389 5216907309128831025975521)
                    ·
                      refine ⟨3912680481846623269481641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5216907309128831025975521 3912680481846623269481641)
                      ·
                        rfl

theorem cell23_7619918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 5, 3, 2].length) (baseStart_7619918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7619918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7619918 prefixEnd_7619918 := by exact prefixLift 7619918
  have htrace : WordTrace (prefixWord ++ tailWord_7619918) baseStart_7619918 baseEnd_7619918 := by
    simpa [prefixWord, tailWord_7619918, baseEnd_7619918] using wordTrace_append hprefix tailTrace_7619918
  have hstable : (prefixWord ++ tailWord_7619918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7619918).length < 2 ^ (prefixWord ++ tailWord_7619918).sum := by decide
  have hdescent : baseEnd_7619918 < baseStart_7619918 := by decide
  rcases family_descends (prefixWord ++ tailWord_7619918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7619925 : List Nat := [1, 3, 2, 2, 3, 1, 2, 3, 2, 1, 3]
def baseStart_7619925 : Nat := 118140960795 + 7619925 * 2 ^ 59
def prefixEnd_7619925 : Nat := 4983230072969 + 3 ^ 40 * 7619925 * 2
def baseEnd_7619925 : Nat := 3912684076211204742094109

theorem tailTrace_7619925 : CollatzResearch.WordTrace tailWord_7619925 prefixEnd_7619925 3912684076211204742094109 := by
  unfold tailWord_7619925
  simp only [CollatzResearch.WordTrace]
  refine ⟨277921496919320579426989229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185280997946213719617992819 277921496919320579426989229)
  ·
    refine ⟨104220561344745217285120961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 277921496919320579426989229 104220561344745217285120961)
    ·
      refine ⟨78165421008558912963840721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104220561344745217285120961 78165421008558912963840721)
      ·
        refine ⟨58624065756419184722880541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78165421008558912963840721 58624065756419184722880541)
        ·
          refine ⟨21984024658657194271080203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58624065756419184722880541 21984024658657194271080203)
          ·
            refine ⟨32976036987985791406620305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21984024658657194271080203 32976036987985791406620305)
            ·
              refine ⟨24732027740989343554965229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32976036987985791406620305 24732027740989343554965229)
              ·
                refine ⟨9274510402871003833111961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24732027740989343554965229 9274510402871003833111961)
                ·
                  refine ⟨6955882802153252874833971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9274510402871003833111961 6955882802153252874833971)
                  ·
                    refine ⟨10433824203229879312250957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6955882802153252874833971 10433824203229879312250957)
                    ·
                      refine ⟨3912684076211204742094109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10433824203229879312250957 3912684076211204742094109)
                      ·
                        rfl

theorem cell23_7619925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 3, 2, 1, 3].length) (baseStart_7619925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7619925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7619925 prefixEnd_7619925 := by exact prefixLift 7619925
  have htrace : WordTrace (prefixWord ++ tailWord_7619925) baseStart_7619925 baseEnd_7619925 := by
    simpa [prefixWord, tailWord_7619925, baseEnd_7619925] using wordTrace_append hprefix tailTrace_7619925
  have hstable : (prefixWord ++ tailWord_7619925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7619925).length < 2 ^ (prefixWord ++ tailWord_7619925).sum := by decide
  have hdescent : baseEnd_7619925 < baseStart_7619925 := by decide
  rcases family_descends (prefixWord ++ tailWord_7619925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7619961 : List Nat := [1, 2, 1, 3, 2, 1, 3, 2, 2, 2, 4]
def baseStart_7619961 : Nat := 118140960795 + 7619961 * 2 ^ 59
def prefixEnd_7619961 : Nat := 4983230072969 + 3 ^ 40 * 7619961 * 2
def baseEnd_7619961 : Nat := 3912702561514766601243943

theorem tailTrace_7619961 : CollatzResearch.WordTrace tailWord_7619961 prefixEnd_7619961 3912702561514766601243943 := by
  unfold tailWord_7619961
  simp only [CollatzResearch.WordTrace]
  refine ⟨277922809947190157575299737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185281873298126771716866491 277922809947190157575299737)
  ·
    refine ⟨208442107460392618181474803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277922809947190157575299737 208442107460392618181474803)
    ·
      refine ⟨312663161190588927272212205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208442107460392618181474803 312663161190588927272212205)
      ·
        refine ⟨117248685446470847727079577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 312663161190588927272212205 117248685446470847727079577)
        ·
          refine ⟨87936514084853135795309683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117248685446470847727079577 87936514084853135795309683)
          ·
            refine ⟨131904771127279703692964525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87936514084853135795309683 131904771127279703692964525)
            ·
              refine ⟨49464289172729888884861697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131904771127279703692964525 49464289172729888884861697)
              ·
                refine ⟨37098216879547416663646273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49464289172729888884861697 37098216879547416663646273)
                ·
                  refine ⟨27823662659660562497734705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37098216879547416663646273 27823662659660562497734705)
                  ·
                    refine ⟨20867746994745421873301029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27823662659660562497734705 20867746994745421873301029)
                    ·
                      refine ⟨3912702561514766601243943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20867746994745421873301029 3912702561514766601243943)
                      ·
                        rfl

theorem cell23_7619961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 2, 2, 2, 4].length) (baseStart_7619961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7619961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7619961 prefixEnd_7619961 := by exact prefixLift 7619961
  have htrace : WordTrace (prefixWord ++ tailWord_7619961) baseStart_7619961 baseEnd_7619961 := by
    simpa [prefixWord, tailWord_7619961, baseEnd_7619961] using wordTrace_append hprefix tailTrace_7619961
  have hstable : (prefixWord ++ tailWord_7619961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7619961).length < 2 ^ (prefixWord ++ tailWord_7619961).sum := by decide
  have hdescent : baseEnd_7619961 < baseStart_7619961 := by decide
  rcases family_descends (prefixWord ++ tailWord_7619961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7619965 : List Nat := [1, 4, 1, 1, 2, 2, 3, 1, 4, 2, 2]
def baseStart_7619965 : Nat := 118140960795 + 7619965 * 2 ^ 59
def prefixEnd_7619965 : Nat := 4983230072969 + 3 ^ 40 * 7619965 * 2
def baseEnd_7619965 : Nat := 3912704615437384585593925

theorem tailTrace_7619965 : CollatzResearch.WordTrace tailWord_7619965 prefixEnd_7619965 3912704615437384585593925 := by
  unfold tailWord_7619965
  simp only [CollatzResearch.WordTrace]
  refine ⟨277922955839175666258445349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185281970559450444172296899 277922955839175666258445349)
  ·
    refine ⟨52110554219845437423458503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 277922955839175666258445349 52110554219845437423458503)
    ·
      refine ⟨78165831329768156135187755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52110554219845437423458503 78165831329768156135187755)
      ·
        refine ⟨117248746994652234202781633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78165831329768156135187755 117248746994652234202781633)
        ·
          refine ⟨87936560245989175652086225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117248746994652234202781633 87936560245989175652086225)
          ·
            refine ⟨65952420184491881739064669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87936560245989175652086225 65952420184491881739064669)
            ·
              refine ⟨24732157569184455652149251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65952420184491881739064669 24732157569184455652149251)
              ·
                refine ⟨37098236353776683478223877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24732157569184455652149251 37098236353776683478223877)
                ·
                  refine ⟨6955919316333128152166977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37098236353776683478223877 6955919316333128152166977)
                  ·
                    refine ⟨5216939487249846114125233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6955919316333128152166977 5216939487249846114125233)
                    ·
                      refine ⟨3912704615437384585593925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5216939487249846114125233 3912704615437384585593925)
                      ·
                        rfl

theorem cell23_7619965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 1, 4, 2, 2].length) (baseStart_7619965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7619965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7619965 prefixEnd_7619965 := by exact prefixLift 7619965
  have htrace : WordTrace (prefixWord ++ tailWord_7619965) baseStart_7619965 baseEnd_7619965 := by
    simpa [prefixWord, tailWord_7619965, baseEnd_7619965] using wordTrace_append hprefix tailTrace_7619965
  have hstable : (prefixWord ++ tailWord_7619965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7619965).length < 2 ^ (prefixWord ++ tailWord_7619965).sum := by decide
  have hdescent : baseEnd_7619965 < baseStart_7619965 := by decide
  rcases family_descends (prefixWord ++ tailWord_7619965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7619971 : List Nat := [1, 1, 1, 3, 5, 1, 1, 3, 7]
def baseStart_7619971 : Nat := 118140960795 + 7619971 * 2 ^ 59
def prefixEnd_7619971 : Nat := 4983230072969 + 3 ^ 40 * 7619971 * 2
def baseEnd_7619971 : Nat := 434745299591256840235433

theorem tailTrace_7619971 : CollatzResearch.WordTrace tailWord_7619971 prefixEnd_7619971 434745299591256840235433 := by
  unfold tailWord_7619971
  simp only [CollatzResearch.WordTrace]
  refine ⟨277923174677153929283163767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185282116451435952855442511 277923174677153929283163767)
  ·
    refine ⟨416884762015730893924745651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277923174677153929283163767 416884762015730893924745651)
    ·
      refine ⟨625327143023596340887118477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 416884762015730893924745651 625327143023596340887118477)
      ·
        refine ⟨234497678633848627832669429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 625327143023596340887118477 234497678633848627832669429)
        ·
          refine ⟨21984157371923308859312759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 234497678633848627832669429 21984157371923308859312759)
          ·
            refine ⟨32976236057884963288969139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21984157371923308859312759 32976236057884963288969139)
            ·
              refine ⟨49464354086827444933453709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32976236057884963288969139 49464354086827444933453709)
              ·
                refine ⟨18549132782560291850045141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49464354086827444933453709 18549132782560291850045141)
                ·
                  refine ⟨434745299591256840235433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18549132782560291850045141 434745299591256840235433)
                  ·
                    rfl

theorem cell23_7619971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 3, 7].length) (baseStart_7619971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7619971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7619971 prefixEnd_7619971 := by exact prefixLift 7619971
  have htrace : WordTrace (prefixWord ++ tailWord_7619971) baseStart_7619971 baseEnd_7619971 := by
    simpa [prefixWord, tailWord_7619971, baseEnd_7619971] using wordTrace_append hprefix tailTrace_7619971
  have hstable : (prefixWord ++ tailWord_7619971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7619971).length < 2 ^ (prefixWord ++ tailWord_7619971).sum := by decide
  have hdescent : baseEnd_7619971 < baseStart_7619971 := by decide
  rcases family_descends (prefixWord ++ tailWord_7619971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7619988 : List Nat := [2, 4, 2, 1, 2, 1, 2, 2, 7]
def baseStart_7619988 : Nat := 118140960795 + 7619988 * 2 ^ 59
def prefixEnd_7619988 : Nat := 4983230072969 + 3 ^ 40 * 7619988 * 2
def baseEnd_7619988 : Nat := 434746269499159777289591

theorem tailTrace_7619988 : CollatzResearch.WordTrace tailWord_7619988 prefixEnd_7619988 434746269499159777289591 := by
  unfold tailWord_7619988
  simp only [CollatzResearch.WordTrace]
  refine ⟨138961897359046170593266309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185282529812061560791021745 138961897359046170593266309)
  ·
    refine ⟨26055355754821156986237433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138961897359046170593266309 26055355754821156986237433)
    ·
      refine ⟨19541516816115867739678075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26055355754821156986237433 19541516816115867739678075)
      ·
        refine ⟨29312275224173801609517113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19541516816115867739678075 29312275224173801609517113)
        ·
          refine ⟨21984206418130351207137835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29312275224173801609517113 21984206418130351207137835)
          ·
            refine ⟨32976309627195526810706753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21984206418130351207137835 32976309627195526810706753)
            ·
              refine ⟨24732232220396645108030065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32976309627195526810706753 24732232220396645108030065)
              ·
                refine ⟨18549174165297483831022549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24732232220396645108030065 18549174165297483831022549)
                ·
                  refine ⟨434746269499159777289591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18549174165297483831022549 434746269499159777289591)
                  ·
                    rfl

theorem cell23_7619988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 2, 7].length) (baseStart_7619988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7619988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7619988 prefixEnd_7619988 := by exact prefixLift 7619988
  have htrace : WordTrace (prefixWord ++ tailWord_7619988) baseStart_7619988 baseEnd_7619988 := by
    simpa [prefixWord, tailWord_7619988, baseEnd_7619988] using wordTrace_append hprefix tailTrace_7619988
  have hstable : (prefixWord ++ tailWord_7619988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7619988).length < 2 ^ (prefixWord ++ tailWord_7619988).sum := by decide
  have hdescent : baseEnd_7619988 < baseStart_7619988 := by decide
  rcases family_descends (prefixWord ++ tailWord_7619988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7620101 : List Nat := [1, 3, 1, 1, 2, 2, 1, 1, 1, 3, 7]
def baseStart_7620101 : Nat := 118140960795 + 7620101 * 2 ^ 59
def prefixEnd_7620101 : Nat := 4983230072969 + 3 ^ 40 * 7620101 * 2
def baseEnd_7620101 : Nat := 3912774448806396053493299

theorem tailTrace_7620101 : CollatzResearch.WordTrace tailWord_7620101 prefixEnd_7620101 3912774448806396053493299 := by
  unfold tailWord_7620101
  simp only [CollatzResearch.WordTrace]
  refine ⟨277927916166682961485396157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185285277444455307656930771 277927916166682961485396157)
  ·
    refine ⟨104222968562506110557023559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 277927916166682961485396157 104222968562506110557023559)
    ·
      refine ⟨156334452843759165835535339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104222968562506110557023559 156334452843759165835535339)
      ·
        refine ⟨234501679265638748753303009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156334452843759165835535339 234501679265638748753303009)
        ·
          refine ⟨175876259449229061564977257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234501679265638748753303009 175876259449229061564977257)
          ·
            refine ⟨131907194586921796173732943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175876259449229061564977257 131907194586921796173732943)
            ·
              refine ⟨197860791880382694260599415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131907194586921796173732943 197860791880382694260599415)
              ·
                refine ⟨296791187820574041390899123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 197860791880382694260599415 296791187820574041390899123)
                ·
                  refine ⟨445186781730861062086348685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 296791187820574041390899123 445186781730861062086348685)
                  ·
                    refine ⟨166945043149072898282380757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 445186781730861062086348685 166945043149072898282380757)
                    ·
                      refine ⟨3912774448806396053493299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 166945043149072898282380757 3912774448806396053493299)
                      ·
                        rfl

theorem cell23_7620101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 3, 7].length) (baseStart_7620101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7620101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7620101 prefixEnd_7620101 := by exact prefixLift 7620101
  have htrace : WordTrace (prefixWord ++ tailWord_7620101) baseStart_7620101 baseEnd_7620101 := by
    simpa [prefixWord, tailWord_7620101, baseEnd_7620101] using wordTrace_append hprefix tailTrace_7620101
  have hstable : (prefixWord ++ tailWord_7620101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7620101).length < 2 ^ (prefixWord ++ tailWord_7620101).sum := by decide
  have hdescent : baseEnd_7620101 < baseStart_7620101 := by decide
  rcases family_descends (prefixWord ++ tailWord_7620101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7620105 : List Nat := [1, 2, 1, 1, 3, 1, 5, 2, 3, 1, 3]
def baseStart_7620105 : Nat := 118140960795 + 7620105 * 2 ^ 59
def prefixEnd_7620105 : Nat := 4983230072969 + 3 ^ 40 * 7620105 * 2
def baseEnd_7620105 : Nat := 3912776502729014037843281

theorem tailTrace_7620105 : CollatzResearch.WordTrace tailWord_7620105 prefixEnd_7620105 3912776502729014037843281 := by
  unfold tailWord_7620105
  simp only [CollatzResearch.WordTrace]
  refine ⟨277928062058668470168541769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185285374705778980112361179 277928062058668470168541769)
  ·
    refine ⟨208446046544001352626406327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277928062058668470168541769 208446046544001352626406327)
    ·
      refine ⟨312669069816002028939609491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208446046544001352626406327 312669069816002028939609491)
      ·
        refine ⟨469003604724003043409414237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312669069816002028939609491 469003604724003043409414237)
        ·
          refine ⟨175876351771501141278530339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 469003604724003043409414237 175876351771501141278530339)
          ·
            refine ⟨263814527657251711917795509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175876351771501141278530339 263814527657251711917795509)
            ·
              refine ⟨24732611967867347992293329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 263814527657251711917795509 24732611967867347992293329)
              ·
                refine ⟨18549458975900510994219997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24732611967867347992293329 18549458975900510994219997)
                ·
                  refine ⟨6956047115962691622832499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18549458975900510994219997 6956047115962691622832499)
                  ·
                    refine ⟨10434070673944037434248749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6956047115962691622832499 10434070673944037434248749)
                    ·
                      refine ⟨3912776502729014037843281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10434070673944037434248749 3912776502729014037843281)
                      ·
                        rfl

theorem cell23_7620105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 2, 3, 1, 3].length) (baseStart_7620105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7620105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7620105 prefixEnd_7620105 := by exact prefixLift 7620105
  have htrace : WordTrace (prefixWord ++ tailWord_7620105) baseStart_7620105 baseEnd_7620105 := by
    simpa [prefixWord, tailWord_7620105, baseEnd_7620105] using wordTrace_append hprefix tailTrace_7620105
  have hstable : (prefixWord ++ tailWord_7620105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7620105).length < 2 ^ (prefixWord ++ tailWord_7620105).sum := by decide
  have hdescent : baseEnd_7620105 < baseStart_7620105 := by decide
  rcases family_descends (prefixWord ++ tailWord_7620105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7620109 : List Nat := [1, 7, 1, 1, 2, 1, 1, 1, 1, 4, 3]
def baseStart_7620109 : Nat := 118140960795 + 7620109 * 2 ^ 59
def prefixEnd_7620109 : Nat := 4983230072969 + 3 ^ 40 * 7620109 * 2
def baseEnd_7620109 : Nat := 3912778556651632022193263

theorem tailTrace_7620109 : CollatzResearch.WordTrace tailWord_7620109 prefixEnd_7620109 3912778556651632022193263 := by
  unfold tailWord_7620109
  simp only [CollatzResearch.WordTrace]
  refine ⟨277928207950653978851687381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185285471967102652567791587 277928207950653978851687381)
  ·
    refine ⟨6513942373843452629336423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 277928207950653978851687381 6513942373843452629336423)
    ·
      refine ⟨9770913560765178944004635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6513942373843452629336423 9770913560765178944004635)
      ·
        refine ⟨14656370341147768416006953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9770913560765178944004635 14656370341147768416006953)
        ·
          refine ⟨10992277755860826312005215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14656370341147768416006953 10992277755860826312005215)
          ·
            refine ⟨16488416633791239468007823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10992277755860826312005215 16488416633791239468007823)
            ·
              refine ⟨24732624950686859202011735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16488416633791239468007823 24732624950686859202011735)
              ·
                refine ⟨37098937426030288803017603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24732624950686859202011735 37098937426030288803017603)
                ·
                  refine ⟨55648406139045433204526405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37098937426030288803017603 55648406139045433204526405)
                  ·
                    refine ⟨10434076151071018725848701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55648406139045433204526405 10434076151071018725848701)
                    ·
                      refine ⟨3912778556651632022193263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10434076151071018725848701 3912778556651632022193263)
                      ·
                        rfl

theorem cell23_7620109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_7620109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7620109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7620109 prefixEnd_7620109 := by exact prefixLift 7620109
  have htrace : WordTrace (prefixWord ++ tailWord_7620109) baseStart_7620109 baseEnd_7620109 := by
    simpa [prefixWord, tailWord_7620109, baseEnd_7620109] using wordTrace_append hprefix tailTrace_7620109
  have hstable : (prefixWord ++ tailWord_7620109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7620109).length < 2 ^ (prefixWord ++ tailWord_7620109).sum := by decide
  have hdescent : baseEnd_7620109 < baseStart_7620109 := by decide
  rcases family_descends (prefixWord ++ tailWord_7620109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7620115 : List Nat := [1, 1, 1, 2, 1, 7, 1, 1, 1, 5, 2]
def baseStart_7620115 : Nat := 118140960795 + 7620115 * 2 ^ 59
def prefixEnd_7620115 : Nat := 4983230072969 + 3 ^ 40 * 7620115 * 2
def baseEnd_7620115 : Nat := 3912781637535558998718235

theorem tailTrace_7620115 : CollatzResearch.WordTrace tailWord_7620115 prefixEnd_7620115 3912781637535558998718235 := by
  unfold tailWord_7620115
  simp only [CollatzResearch.WordTrace]
  refine ⟨277928426788632241876405799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185285617859088161250937199 277928426788632241876405799)
  ·
    refine ⟨416892640182948362814608699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277928426788632241876405799 416892640182948362814608699)
    ·
      refine ⟨625338960274422544221913049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 416892640182948362814608699 625338960274422544221913049)
      ·
        refine ⟨469004220205816908166434787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 625338960274422544221913049 469004220205816908166434787)
        ·
          refine ⟨703506330308725362249652181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 469004220205816908166434787 703506330308725362249652181)
          ·
            refine ⟨16488429616610750677726223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 703506330308725362249652181 16488429616610750677726223)
            ·
              refine ⟨24732644424916126016589335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16488429616610750677726223 24732644424916126016589335)
              ·
                refine ⟨37098966637374189024884003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24732644424916126016589335 37098966637374189024884003)
                ·
                  refine ⟨55648449956061283537326005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37098966637374189024884003 55648449956061283537326005)
                  ·
                    refine ⟨5217042183380745331624313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55648449956061283537326005 5217042183380745331624313)
                    ·
                      refine ⟨3912781637535558998718235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5217042183380745331624313 3912781637535558998718235)
                      ·
                        rfl

theorem cell23_7620115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 1, 1, 5, 2].length) (baseStart_7620115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7620115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7620115 prefixEnd_7620115 := by exact prefixLift 7620115
  have htrace : WordTrace (prefixWord ++ tailWord_7620115) baseStart_7620115 baseEnd_7620115 := by
    simpa [prefixWord, tailWord_7620115, baseEnd_7620115] using wordTrace_append hprefix tailTrace_7620115
  have hstable : (prefixWord ++ tailWord_7620115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7620115).length < 2 ^ (prefixWord ++ tailWord_7620115).sum := by decide
  have hdescent : baseEnd_7620115 < baseStart_7620115 := by decide
  rcases family_descends (prefixWord ++ tailWord_7620115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7620116 : List Nat := [2, 4, 3, 1, 2, 1, 2, 3, 1, 4]
def baseStart_7620116 : Nat := 118140960795 + 7620116 * 2 ^ 59
def prefixEnd_7620116 : Nat := 4983230072969 + 3 ^ 40 * 7620116 * 2
def baseEnd_7620116 : Nat := 1304260717005404498268577

theorem tailTrace_7620116 : CollatzResearch.WordTrace tailWord_7620116 prefixEnd_7620116 1304260717005404498268577 := by
  unfold tailWord_7620116
  simp only [CollatzResearch.WordTrace]
  refine ⟨138964231630814309523596101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185285642174419079364794801 138964231630814309523596101)
  ·
    refine ⟨26055793430777683035674269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138964231630814309523596101 26055793430777683035674269)
    ·
      refine ⟨9770922536541631138377851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26055793430777683035674269 9770922536541631138377851)
      ·
        refine ⟨14656383804812446707566777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9770922536541631138377851 14656383804812446707566777)
        ·
          refine ⟨10992287853609335030675083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14656383804812446707566777 10992287853609335030675083)
          ·
            refine ⟨16488431780414002546012625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10992287853609335030675083 16488431780414002546012625)
            ·
              refine ⟨12366323835310501909509469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16488431780414002546012625 12366323835310501909509469)
              ·
                refine ⟨4637371438241438216066051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12366323835310501909509469 4637371438241438216066051)
                ·
                  refine ⟨6956057157362157324099077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4637371438241438216066051 6956057157362157324099077)
                  ·
                    refine ⟨1304260717005404498268577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6956057157362157324099077 1304260717005404498268577)
                    ·
                      rfl

theorem cell23_7620116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_7620116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7620116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7620116 prefixEnd_7620116 := by exact prefixLift 7620116
  have htrace : WordTrace (prefixWord ++ tailWord_7620116) baseStart_7620116 baseEnd_7620116 := by
    simpa [prefixWord, tailWord_7620116, baseEnd_7620116] using wordTrace_append hprefix tailTrace_7620116
  have hstable : (prefixWord ++ tailWord_7620116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7620116).length < 2 ^ (prefixWord ++ tailWord_7620116).sum := by decide
  have hdescent : baseEnd_7620116 < baseStart_7620116 := by decide
  rcases family_descends (prefixWord ++ tailWord_7620116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7620125 : List Nat := [1, 4, 2, 2, 1, 1, 3, 3, 1, 5]
def baseStart_7620125 : Nat := 118140960795 + 7620125 * 2 ^ 59
def prefixEnd_7620125 : Nat := 4983230072969 + 3 ^ 40 * 7620125 * 2
def baseEnd_7620125 : Nat := 1304262257447367986531063

theorem tailTrace_7620125 : CollatzResearch.WordTrace tailWord_7620125 prefixEnd_7620125 1304262257447367986531063 := by
  unfold tailWord_7620125
  simp only [CollatzResearch.WordTrace]
  refine ⟨277928791518596013584269829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185285861012397342389513219 277928791518596013584269829)
  ·
    refine ⟨52111648409736752547050593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 277928791518596013584269829 52111648409736752547050593)
    ·
      refine ⟨39083736307302564410287945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52111648409736752547050593 39083736307302564410287945)
      ·
        refine ⟨29312802230476923307715959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39083736307302564410287945 29312802230476923307715959)
        ·
          refine ⟨43969203345715384961573939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29312802230476923307715959 43969203345715384961573939)
          ·
            refine ⟨65953805018573077442360909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43969203345715384961573939 65953805018573077442360909)
            ·
              refine ⟨24732676881964904040885341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65953805018573077442360909 24732676881964904040885341)
              ·
                refine ⟨9274753830736839015332003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24732676881964904040885341 9274753830736839015332003)
                ·
                  refine ⟨13912130746105258522998005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9274753830736839015332003 13912130746105258522998005)
                  ·
                    refine ⟨1304262257447367986531063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13912130746105258522998005 1304262257447367986531063)
                    ·
                      rfl

theorem cell23_7620125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 3, 1, 5].length) (baseStart_7620125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7620125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7620125 prefixEnd_7620125 := by exact prefixLift 7620125
  have htrace : WordTrace (prefixWord ++ tailWord_7620125) baseStart_7620125 baseEnd_7620125 := by
    simpa [prefixWord, tailWord_7620125, baseEnd_7620125] using wordTrace_append hprefix tailTrace_7620125
  have hstable : (prefixWord ++ tailWord_7620125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7620125).length < 2 ^ (prefixWord ++ tailWord_7620125).sum := by decide
  have hdescent : baseEnd_7620125 < baseStart_7620125 := by decide
  rcases family_descends (prefixWord ++ tailWord_7620125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7620173 : List Nat := [1, 6, 1, 1, 3, 2, 1, 3, 1, 1, 3]
def baseStart_7620173 : Nat := 118140960795 + 7620173 * 2 ^ 59
def prefixEnd_7620173 : Nat := 4983230072969 + 3 ^ 40 * 7620173 * 2
def baseEnd_7620173 : Nat := 3912811419413519771792969

theorem tailTrace_7620173 : CollatzResearch.WordTrace tailWord_7620173 prefixEnd_7620173 3912811419413519771792969 := by
  unfold tailWord_7620173
  simp only [CollatzResearch.WordTrace]
  refine ⟨277930542222422117782017173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185287028148281411854678115 277930542222422117782017173)
  ·
    refine ⟨13027994166676036771032055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 277930542222422117782017173 13027994166676036771032055)
    ·
      refine ⟨19541991250014055156548083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13027994166676036771032055 19541991250014055156548083)
      ·
        refine ⟨29312986875021082734822125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19541991250014055156548083 29312986875021082734822125)
        ·
          refine ⟨10992370078132906025558297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29312986875021082734822125 10992370078132906025558297)
          ·
            refine ⟨8244277558599679519168723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10992370078132906025558297 8244277558599679519168723)
            ·
              refine ⟨12366416337899519278753085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8244277558599679519168723 12366416337899519278753085)
              ·
                refine ⟨4637406126712319729532407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12366416337899519278753085 4637406126712319729532407)
                ·
                  refine ⟨6956109190068479594298611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4637406126712319729532407 6956109190068479594298611)
                  ·
                    refine ⟨10434163785102719391447917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6956109190068479594298611 10434163785102719391447917)
                    ·
                      refine ⟨3912811419413519771792969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10434163785102719391447917 3912811419413519771792969)
                      ·
                        rfl

theorem cell23_7620173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 1, 3, 1, 1, 3].length) (baseStart_7620173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7620173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7620173 prefixEnd_7620173 := by exact prefixLift 7620173
  have htrace : WordTrace (prefixWord ++ tailWord_7620173) baseStart_7620173 baseEnd_7620173 := by
    simpa [prefixWord, tailWord_7620173, baseEnd_7620173] using wordTrace_append hprefix tailTrace_7620173
  have hstable : (prefixWord ++ tailWord_7620173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7620173).length < 2 ^ (prefixWord ++ tailWord_7620173).sum := by decide
  have hdescent : baseEnd_7620173 < baseStart_7620173 := by decide
  rcases family_descends (prefixWord ++ tailWord_7620173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7620206 : List Nat := [4, 1, 2, 2, 3, 2, 2, 1, 2, 4]
def baseStart_7620206 : Nat := 118140960795 + 7620206 * 2 ^ 59
def prefixEnd_7620206 : Nat := 4983230072969 + 3 ^ 40 * 7620206 * 2
def baseEnd_7620206 : Nat := 1304276121425039380893439

theorem tailTrace_7620206 : CollatzResearch.WordTrace tailWord_7620206 prefixEnd_7620206 1304276121425039380893439 := by
  unfold tailWord_7620206
  simp only [CollatzResearch.WordTrace]
  refine ⟨34741468228912820552246059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185287830554201709611978981 34741468228912820552246059)
  ·
    refine ⟨52112202343369230828369089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34741468228912820552246059 52112202343369230828369089)
    ·
      refine ⟨39084151757526923121276817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52112202343369230828369089 39084151757526923121276817)
      ·
        refine ⟨29313113818145192340957613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39084151757526923121276817 29313113818145192340957613)
        ·
          refine ⟨10992417681804447127859105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29313113818145192340957613 10992417681804447127859105)
          ·
            refine ⟨8244313261353335345894329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10992417681804447127859105 8244313261353335345894329)
            ·
              refine ⟨6183234946015001509420747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8244313261353335345894329 6183234946015001509420747)
              ·
                refine ⟨9274852419022502264131121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6183234946015001509420747 9274852419022502264131121)
                ·
                  refine ⟨6956139314266876698098341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9274852419022502264131121 6956139314266876698098341)
                  ·
                    refine ⟨1304276121425039380893439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6956139314266876698098341 1304276121425039380893439)
                    ·
                      rfl

theorem cell23_7620206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 2, 1, 2, 4].length) (baseStart_7620206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7620206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7620206 prefixEnd_7620206 := by exact prefixLift 7620206
  have htrace : WordTrace (prefixWord ++ tailWord_7620206) baseStart_7620206 baseEnd_7620206 := by
    simpa [prefixWord, tailWord_7620206, baseEnd_7620206] using wordTrace_append hprefix tailTrace_7620206
  have hstable : (prefixWord ++ tailWord_7620206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7620206).length < 2 ^ (prefixWord ++ tailWord_7620206).sum := by decide
  have hdescent : baseEnd_7620206 < baseStart_7620206 := by decide
  rcases family_descends (prefixWord ++ tailWord_7620206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7620218 : List Nat := [3, 1, 1, 1, 1, 1, 1, 3, 4, 3, 4]
def baseStart_7620218 : Nat := 118140960795 + 7620218 * 2 ^ 59
def prefixEnd_7620218 : Nat := 4983230072969 + 3 ^ 40 * 7620218 * 2
def baseEnd_7620218 : Nat := 3912834526042972095730261

theorem tailTrace_7620218 : CollatzResearch.WordTrace tailWord_7620218 prefixEnd_7620218 3912834526042972095730261 := by
  unfold tailWord_7620218
  simp only [CollatzResearch.WordTrace]
  refine ⟨69483045876814772616851327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185288122338172726978270205 69483045876814772616851327)
  ·
    refine ⟨104224568815222158925276991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69483045876814772616851327 104224568815222158925276991)
    ·
      refine ⟨156336853222833238387915487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104224568815222158925276991 156336853222833238387915487)
      ·
        refine ⟨234505279834249857581873231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156336853222833238387915487 234505279834249857581873231)
        ·
          refine ⟨351757919751374786372809847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234505279834249857581873231 351757919751374786372809847)
          ·
            refine ⟨527636879627062179559214771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 351757919751374786372809847 527636879627062179559214771)
            ·
              refine ⟨791455319440593269338822157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 527636879627062179559214771 791455319440593269338822157)
              ·
                refine ⟨296795744790222476002058309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 791455319440593269338822157 296795744790222476002058309)
                ·
                  refine ⟨55649202148166714250385933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 296795744790222476002058309 55649202148166714250385933)
                  ·
                    refine ⟨20868450805562517843894725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55649202148166714250385933 20868450805562517843894725)
                    ·
                      refine ⟨3912834526042972095730261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20868450805562517843894725 3912834526042972095730261)
                      ·
                        rfl

theorem cell23_7620218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 4, 3, 4].length) (baseStart_7620218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7620218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7620218 prefixEnd_7620218 := by exact prefixLift 7620218
  have htrace : WordTrace (prefixWord ++ tailWord_7620218) baseStart_7620218 baseEnd_7620218 := by
    simpa [prefixWord, tailWord_7620218, baseEnd_7620218] using wordTrace_append hprefix tailTrace_7620218
  have hstable : (prefixWord ++ tailWord_7620218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7620218).length < 2 ^ (prefixWord ++ tailWord_7620218).sum := by decide
  have hdescent : baseEnd_7620218 < baseStart_7620218 := by decide
  rcases family_descends (prefixWord ++ tailWord_7620218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7620269 : List Nat := [1, 5, 2, 1, 1, 1, 4, 1, 1, 4, 2]
def baseStart_7620269 : Nat := 118140960795 + 7620269 * 2 ^ 59
def prefixEnd_7620269 : Nat := 4983230072969 + 3 ^ 40 * 7620269 * 2
def baseEnd_7620269 : Nat := 3912860713556351396192527

theorem tailTrace_7620269 : CollatzResearch.WordTrace tailWord_7620269 prefixEnd_7620269 3912860713556351396192527 := by
  unfold tailWord_7620269
  simp only [CollatzResearch.WordTrace]
  refine ⟨277934043630074326177511861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185289362420049550785007907 277934043630074326177511861)
  ·
    refine ⟨26056316590319468079141737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 277934043630074326177511861 26056316590319468079141737)
    ·
      refine ⟨19542237442739601059356303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26056316590319468079141737 19542237442739601059356303)
      ·
        refine ⟨29313356164109401589034455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19542237442739601059356303 29313356164109401589034455)
        ·
          refine ⟨43970034246164102383551683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29313356164109401589034455 43970034246164102383551683)
          ·
            refine ⟨65955051369246153575327525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43970034246164102383551683 65955051369246153575327525)
            ·
              refine ⟨12366572131733653795373911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65955051369246153575327525 12366572131733653795373911)
              ·
                refine ⟨18549858197600480693060867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12366572131733653795373911 18549858197600480693060867)
                ·
                  refine ⟨27824787296400721039591301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18549858197600480693060867 27824787296400721039591301)
                  ·
                    refine ⟨5217147618075135194923369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27824787296400721039591301 5217147618075135194923369)
                    ·
                      refine ⟨3912860713556351396192527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5217147618075135194923369 3912860713556351396192527)
                      ·
                        rfl

theorem cell23_7620269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 4, 1, 1, 4, 2].length) (baseStart_7620269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7620269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7620269 prefixEnd_7620269 := by exact prefixLift 7620269
  have htrace : WordTrace (prefixWord ++ tailWord_7620269) baseStart_7620269 baseEnd_7620269 := by
    simpa [prefixWord, tailWord_7620269, baseEnd_7620269] using wordTrace_append hprefix tailTrace_7620269
  have hstable : (prefixWord ++ tailWord_7620269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7620269).length < 2 ^ (prefixWord ++ tailWord_7620269).sum := by decide
  have hdescent : baseEnd_7620269 < baseStart_7620269 := by decide
  rcases family_descends (prefixWord ++ tailWord_7620269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7620285 : List Nat := [1, 4, 1, 2, 1, 2, 1, 2, 1, 5, 3]
def baseStart_7620285 : Nat := 118140960795 + 7620285 * 2 ^ 59
def prefixEnd_7620285 : Nat := 4983230072969 + 3 ^ 40 * 7620285 * 2
def baseEnd_7620285 : Nat := 3912868929246823333592453

theorem tailTrace_7620285 : CollatzResearch.WordTrace tailWord_7620285 prefixEnd_7620285 3912868929246823333592453 := by
  unfold tailWord_7620285
  simp only [CollatzResearch.WordTrace]
  refine ⟨277934627198016360910094309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185289751465344240606729539 277934627198016360910094309)
  ·
    refine ⟨52112742599628067670642683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 277934627198016360910094309 52112742599628067670642683)
    ·
      refine ⟨78169113899442101505964025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52112742599628067670642683 78169113899442101505964025)
      ·
        refine ⟨58626835424581576129473019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78169113899442101505964025 58626835424581576129473019)
        ·
          refine ⟨87940253136872364194209529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58626835424581576129473019 87940253136872364194209529)
          ·
            refine ⟨65955189852654273145657147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87940253136872364194209529 65955189852654273145657147)
            ·
              refine ⟨98932784778981409718485721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65955189852654273145657147 98932784778981409718485721)
              ·
                refine ⟨74199588584236057288864291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98932784778981409718485721 74199588584236057288864291)
                ·
                  refine ⟨111299382876354085933296437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74199588584236057288864291 111299382876354085933296437)
                  ·
                    refine ⟨10434317144658195556246541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 111299382876354085933296437 10434317144658195556246541)
                    ·
                      refine ⟨3912868929246823333592453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10434317144658195556246541 3912868929246823333592453)
                      ·
                        rfl

theorem cell23_7620285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 2, 1, 5, 3].length) (baseStart_7620285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7620285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7620285 prefixEnd_7620285 := by exact prefixLift 7620285
  have htrace : WordTrace (prefixWord ++ tailWord_7620285) baseStart_7620285 baseEnd_7620285 := by
    simpa [prefixWord, tailWord_7620285, baseEnd_7620285] using wordTrace_append hprefix tailTrace_7620285
  have hstable : (prefixWord ++ tailWord_7620285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7620285).length < 2 ^ (prefixWord ++ tailWord_7620285).sum := by decide
  have hdescent : baseEnd_7620285 < baseStart_7620285 := by decide
  rcases family_descends (prefixWord ++ tailWord_7620285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7620290 : List Nat := [3, 5, 1, 2, 1, 1, 1, 3, 1, 3, 2]
def baseStart_7620290 : Nat := 118140960795 + 7620290 * 2 ^ 59
def prefixEnd_7620290 : Nat := 4983230072969 + 3 ^ 40 * 7620290 * 2
def baseEnd_7620290 : Nat := 3912871496650095814029931

theorem tailTrace_7620290 : CollatzResearch.WordTrace tailWord_7620290 prefixEnd_7620290 3912871496650095814029931 := by
  unfold tailWord_7620290
  simp only [CollatzResearch.WordTrace]
  refine ⟨69483702390749561691006581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185289873041998831176017549 69483702390749561691006581)
  ·
    refine ⟨6514097099132771408531867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 69483702390749561691006581 6514097099132771408531867)
    ·
      refine ⟨9771145648699157112797801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6514097099132771408531867 9771145648699157112797801)
      ·
        refine ⟨7328359236524367834598351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9771145648699157112797801 7328359236524367834598351)
        ·
          refine ⟨10992538854786551751897527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7328359236524367834598351 10992538854786551751897527)
          ·
            refine ⟨16488808282179827627846291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10992538854786551751897527 16488808282179827627846291)
            ·
              refine ⟨24733212423269741441769437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16488808282179827627846291 24733212423269741441769437)
              ·
                refine ⟨9274954658726153040663539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24733212423269741441769437 9274954658726153040663539)
                ·
                  refine ⟨13912431988089229560995309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9274954658726153040663539 13912431988089229560995309)
                  ·
                    refine ⟨5217161995533461085373241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13912431988089229560995309 5217161995533461085373241)
                    ·
                      refine ⟨3912871496650095814029931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5217161995533461085373241 3912871496650095814029931)
                      ·
                        rfl

theorem cell23_7620290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_7620290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7620290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7620290 prefixEnd_7620290 := by exact prefixLift 7620290
  have htrace : WordTrace (prefixWord ++ tailWord_7620290) baseStart_7620290 baseEnd_7620290 := by
    simpa [prefixWord, tailWord_7620290, baseEnd_7620290] using wordTrace_append hprefix tailTrace_7620290
  have hstable : (prefixWord ++ tailWord_7620290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7620290).length < 2 ^ (prefixWord ++ tailWord_7620290).sum := by decide
  have hdescent : baseEnd_7620290 < baseStart_7620290 := by decide
  rcases family_descends (prefixWord ++ tailWord_7620290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7620325 : List Nat := [1, 3, 1, 4, 1, 1, 1, 1, 3, 3, 4]
def baseStart_7620325 : Nat := 118140960795 + 7620325 * 2 ^ 59
def prefixEnd_7620325 : Nat := 4983230072969 + 3 ^ 40 * 7620325 * 2
def baseEnd_7620325 : Nat := 3912889468473003177092269

theorem tailTrace_7620325 : CollatzResearch.WordTrace tailWord_7620325 prefixEnd_7620325 3912889468473003177092269 := by
  unfold tailWord_7620325
  simp only [CollatzResearch.WordTrace]
  refine ⟨277936086117871447741550429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185290724078580965161033619 277936086117871447741550429)
  ·
    refine ⟨104226032294201792903081411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 277936086117871447741550429 104226032294201792903081411)
    ·
      refine ⟨156339048441302689354622117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104226032294201792903081411 156339048441302689354622117)
      ·
        refine ⟨29313571582744254253991647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 156339048441302689354622117 29313571582744254253991647)
        ·
          refine ⟨43970357374116381380987471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29313571582744254253991647 43970357374116381380987471)
          ·
            refine ⟨65955536061174572071481207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43970357374116381380987471 65955536061174572071481207)
            ·
              refine ⟨98933304091761858107221811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65955536061174572071481207 98933304091761858107221811)
              ·
                refine ⟨148399956137642787160832717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98933304091761858107221811 148399956137642787160832717)
                ·
                  refine ⟨55649983551616045185312269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 148399956137642787160832717 55649983551616045185312269)
                  ·
                    refine ⟨20868743831856016944492101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55649983551616045185312269 20868743831856016944492101)
                    ·
                      refine ⟨3912889468473003177092269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20868743831856016944492101 3912889468473003177092269)
                      ·
                        rfl

theorem cell23_7620325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_7620325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7620325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7620325 prefixEnd_7620325 := by exact prefixLift 7620325
  have htrace : WordTrace (prefixWord ++ tailWord_7620325) baseStart_7620325 baseEnd_7620325 := by
    simpa [prefixWord, tailWord_7620325, baseEnd_7620325] using wordTrace_append hprefix tailTrace_7620325
  have hstable : (prefixWord ++ tailWord_7620325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7620325).length < 2 ^ (prefixWord ++ tailWord_7620325).sum := by decide
  have hdescent : baseEnd_7620325 < baseStart_7620325 := by decide
  rcases family_descends (prefixWord ++ tailWord_7620325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7620342 : List Nat := [5, 1, 1, 1, 1, 3, 2, 1, 1, 3, 4]
def baseStart_7620342 : Nat := 118140960795 + 7620342 * 2 ^ 59
def prefixEnd_7620342 : Nat := 4983230072969 + 3 ^ 40 * 7620342 * 2
def baseEnd_7620342 : Nat := 3912898197644129610579691

theorem tailTrace_7620342 : CollatzResearch.WordTrace tailWord_7620342 prefixEnd_7620342 3912898197644129610579691 := by
  unfold tailWord_7620342
  simp only [CollatzResearch.WordTrace]
  refine ⟨17371044134925616227807455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 185291137439206573096612853 17371044134925616227807455)
  ·
    refine ⟨26056566202388424341711183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17371044134925616227807455 26056566202388424341711183)
    ·
      refine ⟨39084849303582636512566775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26056566202388424341711183 39084849303582636512566775)
      ·
        refine ⟨58627273955373954768850163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39084849303582636512566775 58627273955373954768850163)
        ·
          refine ⟨87940910933060932153275245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58627273955373954768850163 87940910933060932153275245)
          ·
            refine ⟨32977841599897849557478217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87940910933060932153275245 32977841599897849557478217)
            ·
              refine ⟨24733381199923387168108663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32977841599897849557478217 24733381199923387168108663)
              ·
                refine ⟨37100071799885080752162995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24733381199923387168108663 37100071799885080752162995)
                ·
                  refine ⟨55650107699827621128244493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37100071799885080752162995 55650107699827621128244493)
                  ·
                    refine ⟨20868790387435357923091685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55650107699827621128244493 20868790387435357923091685)
                    ·
                      refine ⟨3912898197644129610579691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20868790387435357923091685 3912898197644129610579691)
                      ·
                        rfl

theorem cell23_7620342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 1, 1, 3, 4].length) (baseStart_7620342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7620342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7620342 prefixEnd_7620342 := by exact prefixLift 7620342
  have htrace : WordTrace (prefixWord ++ tailWord_7620342) baseStart_7620342 baseEnd_7620342 := by
    simpa [prefixWord, tailWord_7620342, baseEnd_7620342] using wordTrace_append hprefix tailTrace_7620342
  have hstable : (prefixWord ++ tailWord_7620342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7620342).length < 2 ^ (prefixWord ++ tailWord_7620342).sum := by decide
  have hdescent : baseEnd_7620342 < baseStart_7620342 := by decide
  rcases family_descends (prefixWord ++ tailWord_7620342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7620359 : List Nat := [1, 1, 4, 4, 2, 1, 1, 2, 2, 1, 4]
def baseStart_7620359 : Nat := 118140960795 + 7620359 * 2 ^ 59
def prefixEnd_7620359 : Nat := 4983230072969 + 3 ^ 40 * 7620359 * 2
def baseEnd_7620359 : Nat := 3912906926815256044067113

theorem tailTrace_7620359 : CollatzResearch.WordTrace tailWord_7620359 prefixEnd_7620359 3912906926815256044067113 := by
  unfold tailWord_7620359
  simp only [CollatzResearch.WordTrace]
  refine ⟨277937326199748271548288131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185291550799832181032192087 277937326199748271548288131)
  ·
    refine ⟨416905989299622407322432197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277937326199748271548288131 416905989299622407322432197)
    ·
      refine ⟨78169872993679201372956037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 416905989299622407322432197 78169872993679201372956037)
      ·
        refine ⟨14656851186314850257429257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78169872993679201372956037 14656851186314850257429257)
        ·
          refine ⟨10992638389736137693071943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14656851186314850257429257 10992638389736137693071943)
          ·
            refine ⟨16488957584604206539607915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10992638389736137693071943 16488957584604206539607915)
            ·
              refine ⟨24733436376906309809411873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16488957584604206539607915 24733436376906309809411873)
              ·
                refine ⟨18550077282679732357058905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24733436376906309809411873 18550077282679732357058905)
                ·
                  refine ⟨13912557962009799267794179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18550077282679732357058905 13912557962009799267794179)
                  ·
                    refine ⟨20868836943014698901691269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13912557962009799267794179 20868836943014698901691269)
                    ·
                      refine ⟨3912906926815256044067113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20868836943014698901691269 3912906926815256044067113)
                      ·
                        rfl

theorem cell23_7620359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_7620359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7620359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7620359 prefixEnd_7620359 := by exact prefixLift 7620359
  have htrace : WordTrace (prefixWord ++ tailWord_7620359) baseStart_7620359 baseEnd_7620359 := by
    simpa [prefixWord, tailWord_7620359, baseEnd_7620359] using wordTrace_append hprefix tailTrace_7620359
  have hstable : (prefixWord ++ tailWord_7620359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7620359).length < 2 ^ (prefixWord ++ tailWord_7620359).sum := by decide
  have hdescent : baseEnd_7620359 < baseStart_7620359 := by decide
  rcases family_descends (prefixWord ++ tailWord_7620359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7620362 : List Nat := [3, 1, 2, 2, 1, 3, 1, 1, 4, 2, 3]
def baseStart_7620362 : Nat := 118140960795 + 7620362 * 2 ^ 59
def prefixEnd_7620362 : Nat := 4983230072969 + 3 ^ 40 * 7620362 * 2
def baseEnd_7620362 : Nat := 3912908467257219532329599

theorem tailTrace_7620362 : CollatzResearch.WordTrace tailWord_7620362 prefixEnd_7620362 3912908467257219532329599 := by
  unfold tailWord_7620362
  simp only [CollatzResearch.WordTrace]
  refine ⟨69484358904684350765161835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185291623745824935373764893 69484358904684350765161835)
  ·
    refine ⟨104226538357026526147742753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69484358904684350765161835 104226538357026526147742753)
    ·
      refine ⟨78169903767769894610807065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104226538357026526147742753 78169903767769894610807065)
      ·
        refine ⟨58627427825827420958105299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78169903767769894610807065 58627427825827420958105299)
        ·
          refine ⟨87941141738741131437157949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58627427825827420958105299 87941141738741131437157949)
          ·
            refine ⟨32977928152027924288934231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87941141738741131437157949 32977928152027924288934231)
            ·
              refine ⟨49466892228041886433401347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32977928152027924288934231 49466892228041886433401347)
              ·
                refine ⟨74200338342062829650102021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49466892228041886433401347 74200338342062829650102021)
                ·
                  refine ⟨13912563439136780559394129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74200338342062829650102021 13912563439136780559394129)
                  ·
                    refine ⟨10434422579352585419545597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13912563439136780559394129 10434422579352585419545597)
                    ·
                      refine ⟨3912908467257219532329599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10434422579352585419545597 3912908467257219532329599)
                      ·
                        rfl

theorem cell23_7620362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 1, 4, 2, 3].length) (baseStart_7620362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7620362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7620362 prefixEnd_7620362 := by exact prefixLift 7620362
  have htrace : WordTrace (prefixWord ++ tailWord_7620362) baseStart_7620362 baseEnd_7620362 := by
    simpa [prefixWord, tailWord_7620362, baseEnd_7620362] using wordTrace_append hprefix tailTrace_7620362
  have hstable : (prefixWord ++ tailWord_7620362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7620362).length < 2 ^ (prefixWord ++ tailWord_7620362).sum := by decide
  have hdescent : baseEnd_7620362 < baseStart_7620362 := by decide
  rcases family_descends (prefixWord ++ tailWord_7620362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7620412 : List Nat := [2, 2, 2, 2, 1, 1, 2, 5, 1, 5]
def baseStart_7620412 : Nat := 118140960795 + 7620412 * 2 ^ 59
def prefixEnd_7620412 : Nat := 4983230072969 + 3 ^ 40 * 7620412 * 2
def baseEnd_7620412 : Nat := 1304311380429981445568123

theorem tailTrace_7620412 : CollatzResearch.WordTrace tailWord_7620412 prefixEnd_7620412 1304311380429981445568123 := by
  unfold tailWord_7620412
  simp only [CollatzResearch.WordTrace]
  refine ⟨138969629634278130799983745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185292839512370841066644993 138969629634278130799983745)
  ·
    refine ⟨104227222225708598099987809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138969629634278130799983745 104227222225708598099987809)
    ·
      refine ⟨78170416669281448574990857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104227222225708598099987809 78170416669281448574990857)
      ·
        refine ⟨58627812501961086431243143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78170416669281448574990857 58627812501961086431243143)
        ·
          refine ⟨87941718752941629646864715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58627812501961086431243143 87941718752941629646864715)
          ·
            refine ⟨131912578129412444470297073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87941718752941629646864715 131912578129412444470297073)
            ·
              refine ⟨98934433597059333352722805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131912578129412444470297073 98934433597059333352722805)
              ·
                refine ⟨9275103149724312501817763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 98934433597059333352722805 9275103149724312501817763)
                ·
                  refine ⟨13912654724586468752726645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9275103149724312501817763 13912654724586468752726645)
                  ·
                    refine ⟨1304311380429981445568123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13912654724586468752726645 1304311380429981445568123)
                    ·
                      rfl

theorem cell23_7620412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 5, 1, 5].length) (baseStart_7620412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7620412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7620412 prefixEnd_7620412 := by exact prefixLift 7620412
  have htrace : WordTrace (prefixWord ++ tailWord_7620412) baseStart_7620412 baseEnd_7620412 := by
    simpa [prefixWord, tailWord_7620412, baseEnd_7620412] using wordTrace_append hprefix tailTrace_7620412
  have hstable : (prefixWord ++ tailWord_7620412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7620412).length < 2 ^ (prefixWord ++ tailWord_7620412).sum := by decide
  have hdescent : baseEnd_7620412 < baseStart_7620412 := by decide
  rcases family_descends (prefixWord ++ tailWord_7620412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7620419 : List Nat := [1, 1, 1, 3, 1, 5, 2, 2, 2, 3, 2]
def baseStart_7620419 : Nat := 118140960795 + 7620419 * 2 ^ 59
def prefixEnd_7620419 : Nat := 4983230072969 + 3 ^ 40 * 7620419 * 2
def baseEnd_7620419 : Nat := 3912937735654525809316837

theorem tailTrace_7620419 : CollatzResearch.WordTrace tailWord_7620419 prefixEnd_7620419 3912937735654525809316837 := by
  unfold tailWord_7620419
  simp only [CollatzResearch.WordTrace]
  refine ⟨277939514579530901795472311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185293009719687267863648207 277939514579530901795472311)
  ·
    refine ⟨416909271869296352693208467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277939514579530901795472311 416909271869296352693208467)
    ·
      refine ⟨625363907803944529039812701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 416909271869296352693208467 625363907803944529039812701)
      ·
        refine ⟨234511465426479198389929763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 625363907803944529039812701 234511465426479198389929763)
        ·
          refine ⟨351767198139718797584894645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234511465426479198389929763 351767198139718797584894645)
          ·
            refine ⟨32978174825598637273583873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 351767198139718797584894645 32978174825598637273583873)
            ·
              refine ⟨24733631119198977955187905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32978174825598637273583873 24733631119198977955187905)
              ·
                refine ⟨18550223339399233466390929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24733631119198977955187905 18550223339399233466390929)
                ·
                  refine ⟨13912667504549425099793197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18550223339399233466390929 13912667504549425099793197)
                  ·
                    refine ⟨5217250314206034412422449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13912667504549425099793197 5217250314206034412422449)
                    ·
                      refine ⟨3912937735654525809316837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5217250314206034412422449 3912937735654525809316837)
                      ·
                        rfl

theorem cell23_7620419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 2, 2, 3, 2].length) (baseStart_7620419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7620419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7620419 prefixEnd_7620419 := by exact prefixLift 7620419
  have htrace : WordTrace (prefixWord ++ tailWord_7620419) baseStart_7620419 baseEnd_7620419 := by
    simpa [prefixWord, tailWord_7620419, baseEnd_7620419] using wordTrace_append hprefix tailTrace_7620419
  have hstable : (prefixWord ++ tailWord_7620419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7620419).length < 2 ^ (prefixWord ++ tailWord_7620419).sum := by decide
  have hdescent : baseEnd_7620419 < baseStart_7620419 := by decide
  rcases family_descends (prefixWord ++ tailWord_7620419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7620425 : List Nat := [1, 2, 1, 1, 2, 4, 1, 2, 3, 6]
def baseStart_7620425 : Nat := 118140960795 + 7620425 * 2 ^ 59
def prefixEnd_7620425 : Nat := 4983230072969 + 3 ^ 40 * 7620425 * 2
def baseEnd_7620425 : Nat := 1304313605512817595280603

theorem tailTrace_7620425 : CollatzResearch.WordTrace tailWord_7620425 prefixEnd_7620425 1304313605512817595280603 := by
  unfold tailWord_7620425
  simp only [CollatzResearch.WordTrace]
  refine ⟨277939733417509164820190729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185293155611672776546793819 277939733417509164820190729)
  ·
    refine ⟨208454800063131873615143047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277939733417509164820190729 208454800063131873615143047)
    ·
      refine ⟨312682200094697810422714571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208454800063131873615143047 312682200094697810422714571)
      ·
        refine ⟨469023300142046715634071857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312682200094697810422714571 469023300142046715634071857)
        ·
          refine ⟨351767475106535036725553893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 469023300142046715634071857 351767475106535036725553893)
          ·
            refine ⟨65956401582475319386041355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 351767475106535036725553893 65956401582475319386041355)
            ·
              refine ⟨98934602373712979079062033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65956401582475319386041355 98934602373712979079062033)
              ·
                refine ⟨74200951780284734309296525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98934602373712979079062033 74200951780284734309296525)
                ·
                  refine ⟨27825356917606775365986197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74200951780284734309296525 27825356917606775365986197)
                  ·
                    refine ⟨1304313605512817595280603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27825356917606775365986197 1304313605512817595280603)
                    ·
                      rfl

theorem cell23_7620425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 2, 3, 6].length) (baseStart_7620425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7620425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7620425 prefixEnd_7620425 := by exact prefixLift 7620425
  have htrace : WordTrace (prefixWord ++ tailWord_7620425) baseStart_7620425 baseEnd_7620425 := by
    simpa [prefixWord, tailWord_7620425, baseEnd_7620425] using wordTrace_append hprefix tailTrace_7620425
  have hstable : (prefixWord ++ tailWord_7620425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7620425).length < 2 ^ (prefixWord ++ tailWord_7620425).sum := by decide
  have hdescent : baseEnd_7620425 < baseStart_7620425 := by decide
  rcases family_descends (prefixWord ++ tailWord_7620425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7620426 : List Nat := [3, 1, 2, 1, 1, 1, 5, 4, 1, 1, 3]
def baseStart_7620426 : Nat := 118140960795 + 7620426 * 2 ^ 59
def prefixEnd_7620426 : Nat := 4983230072969 + 3 ^ 40 * 7620426 * 2
def baseEnd_7620426 : Nat := 3912941330019107281929305

theorem tailTrace_7620426 : CollatzResearch.WordTrace tailWord_7620426 prefixEnd_7620426 3912941330019107281929305 := by
  unfold tailWord_7620426
  simp only [CollatzResearch.WordTrace]
  refine ⟨69484942472626385497744283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185293179927003694660651421 69484942472626385497744283)
  ·
    refine ⟨104227413708939578246616425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69484942472626385497744283 104227413708939578246616425)
    ·
      refine ⟨78170560281704683684962319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104227413708939578246616425 78170560281704683684962319)
      ·
        refine ⟨117255840422557025527443479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78170560281704683684962319 117255840422557025527443479)
        ·
          refine ⟨175883760633835538291165219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117255840422557025527443479 175883760633835538291165219)
          ·
            refine ⟨263825640950753307436747829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175883760633835538291165219 263825640950753307436747829)
            ·
              refine ⟨24733653839133122572195109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 263825640950753307436747829 24733653839133122572195109)
              ·
                refine ⟨4637560094837460482286583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24733653839133122572195109 4637560094837460482286583)
                ·
                  refine ⟨6956340142256190723429875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4637560094837460482286583 6956340142256190723429875)
                  ·
                    refine ⟨10434510213384286085144813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6956340142256190723429875 10434510213384286085144813)
                    ·
                      refine ⟨3912941330019107281929305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10434510213384286085144813 3912941330019107281929305)
                      ·
                        rfl

theorem cell23_7620426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 4, 1, 1, 3].length) (baseStart_7620426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7620426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7620426 prefixEnd_7620426 := by exact prefixLift 7620426
  have htrace : WordTrace (prefixWord ++ tailWord_7620426) baseStart_7620426 baseEnd_7620426 := by
    simpa [prefixWord, tailWord_7620426, baseEnd_7620426] using wordTrace_append hprefix tailTrace_7620426
  have hstable : (prefixWord ++ tailWord_7620426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7620426).length < 2 ^ (prefixWord ++ tailWord_7620426).sum := by decide
  have hdescent : baseEnd_7620426 < baseStart_7620426 := by decide
  rcases family_descends (prefixWord ++ tailWord_7620426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7620429 : List Nat := [1, 6, 1, 2, 1, 1, 1, 2, 3, 5]
def baseStart_7620429 : Nat := 118140960795 + 7620429 * 2 ^ 59
def prefixEnd_7620429 : Nat := 4983230072969 + 3 ^ 40 * 7620429 * 2
def baseEnd_7620429 : Nat := 1304314290153690256730597

theorem tailTrace_7620429 : CollatzResearch.WordTrace tailWord_7620429 prefixEnd_7620429 1304314290153690256730597 := by
  unfold tailWord_7620429
  simp only [CollatzResearch.WordTrace]
  refine ⟨277939879309494673503336341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185293252872996449002224227 277939879309494673503336341)
  ·
    refine ⟨13028431842632562820468891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 277939879309494673503336341 13028431842632562820468891)
    ·
      refine ⟨19542647763948844230703337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13028431842632562820468891 19542647763948844230703337)
      ·
        refine ⟨14656985822961633173027503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19542647763948844230703337 14656985822961633173027503)
        ·
          refine ⟨21985478734442449759541255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14656985822961633173027503 21985478734442449759541255)
          ·
            refine ⟨32978218101663674639311883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21985478734442449759541255 32978218101663674639311883)
            ·
              refine ⟨49467327152495511958967825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32978218101663674639311883 49467327152495511958967825)
              ·
                refine ⟨37100495364371633969225869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49467327152495511958967825 37100495364371633969225869)
                ·
                  refine ⟨13912685761639362738459701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37100495364371633969225869 13912685761639362738459701)
                  ·
                    refine ⟨1304314290153690256730597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13912685761639362738459701 1304314290153690256730597)
                    ·
                      rfl

theorem cell23_7620429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 2, 3, 5].length) (baseStart_7620429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7620429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7620429 prefixEnd_7620429 := by exact prefixLift 7620429
  have htrace : WordTrace (prefixWord ++ tailWord_7620429) baseStart_7620429 baseEnd_7620429 := by
    simpa [prefixWord, tailWord_7620429, baseEnd_7620429] using wordTrace_append hprefix tailTrace_7620429
  have hstable : (prefixWord ++ tailWord_7620429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7620429).length < 2 ^ (prefixWord ++ tailWord_7620429).sum := by decide
  have hdescent : baseEnd_7620429 < baseStart_7620429 := by decide
  rcases family_descends (prefixWord ++ tailWord_7620429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7620432 : List Nat := [2, 1, 1, 1, 1, 4, 1, 2, 2, 6, 2]
def baseStart_7620432 : Nat := 118140960795 + 7620432 * 2 ^ 59
def prefixEnd_7620432 : Nat := 4983230072969 + 3 ^ 40 * 7620432 * 2
def baseEnd_7620432 : Nat := 3912944410903034258454277

theorem tailTrace_7620432 : CollatzResearch.WordTrace tailWord_7620432 prefixEnd_7620432 3912944410903034258454277 := by
  unfold tailWord_7620432
  simp only [CollatzResearch.WordTrace]
  refine ⟨138969994364241902507847775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185293325818989203343797033 138969994364241902507847775)
  ·
    refine ⟨208454991546362853761771663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138969994364241902507847775 208454991546362853761771663)
    ·
      refine ⟨312682487319544280642657495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208454991546362853761771663 312682487319544280642657495)
      ·
        refine ⟨469023730979316420963986243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312682487319544280642657495 469023730979316420963986243)
        ·
          refine ⟨703535596468974631445979365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 469023730979316420963986243 703535596468974631445979365)
          ·
            refine ⟨131912924337932743396121131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 703535596468974631445979365 131912924337932743396121131)
            ·
              refine ⟨197869386506899115094181697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131912924337932743396121131 197869386506899115094181697)
              ·
                refine ⟨148402039880174336320636273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 197869386506899115094181697 148402039880174336320636273)
                ·
                  refine ⟨111301529910130752240477205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 148402039880174336320636273 111301529910130752240477205)
                  ·
                    refine ⟨5217259214537379011272369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 111301529910130752240477205 5217259214537379011272369)
                    ·
                      refine ⟨3912944410903034258454277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5217259214537379011272369 3912944410903034258454277)
                      ·
                        rfl

theorem cell23_7620432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 2, 6, 2].length) (baseStart_7620432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7620432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7620432 prefixEnd_7620432 := by exact prefixLift 7620432
  have htrace : WordTrace (prefixWord ++ tailWord_7620432) baseStart_7620432 baseEnd_7620432 := by
    simpa [prefixWord, tailWord_7620432, baseEnd_7620432] using wordTrace_append hprefix tailTrace_7620432
  have hstable : (prefixWord ++ tailWord_7620432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7620432).length < 2 ^ (prefixWord ++ tailWord_7620432).sum := by decide
  have hdescent : baseEnd_7620432 < baseStart_7620432 := by decide
  rcases family_descends (prefixWord ++ tailWord_7620432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7620442 : List Nat := [3, 1, 1, 2, 1, 3, 4, 1, 1, 6]
def baseStart_7620442 : Nat := 118140960795 + 7620442 * 2 ^ 59
def prefixEnd_7620442 : Nat := 4983230072969 + 3 ^ 40 * 7620442 * 2
def baseEnd_7620442 : Nat := 1304316515236526406443077

theorem tailTrace_7620442 : CollatzResearch.WordTrace tailWord_7620442 prefixEnd_7620442 1304316515236526406443077 := by
  unfold tailWord_7620442
  simp only [CollatzResearch.WordTrace]
  refine ⟨69485088364611894180889895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185293568972298384482373053 69485088364611894180889895)
  ·
    refine ⟨104227632546917841271334843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69485088364611894180889895 104227632546917841271334843)
    ·
      refine ⟨156341448820376761907002265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104227632546917841271334843 156341448820376761907002265)
      ·
        refine ⟨117256086615282571430251699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156341448820376761907002265 117256086615282571430251699)
        ·
          refine ⟨175884129922923857145377549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117256086615282571430251699 175884129922923857145377549)
          ·
            refine ⟨65956548721096446429516581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 175884129922923857145377549 65956548721096446429516581)
            ·
              refine ⟨12366852885205583705534359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65956548721096446429516581 12366852885205583705534359)
              ·
                refine ⟨18550279327808375558301539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12366852885205583705534359 18550279327808375558301539)
                ·
                  refine ⟨27825418991712563337452309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18550279327808375558301539 27825418991712563337452309)
                  ·
                    refine ⟨1304316515236526406443077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27825418991712563337452309 1304316515236526406443077)
                    ·
                      rfl

theorem cell23_7620442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 4, 1, 1, 6].length) (baseStart_7620442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7620442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7620442 prefixEnd_7620442 := by exact prefixLift 7620442
  have htrace : WordTrace (prefixWord ++ tailWord_7620442) baseStart_7620442 baseEnd_7620442 := by
    simpa [prefixWord, tailWord_7620442, baseEnd_7620442] using wordTrace_append hprefix tailTrace_7620442
  have hstable : (prefixWord ++ tailWord_7620442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7620442).length < 2 ^ (prefixWord ++ tailWord_7620442).sum := by decide
  have hdescent : baseEnd_7620442 < baseStart_7620442 := by decide
  rcases family_descends (prefixWord ++ tailWord_7620442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7620475 : List Nat := [1, 1, 1, 1, 1, 5, 1, 2, 2, 2, 6]
def baseStart_7620475 : Nat := 118140960795 + 7620475 * 2 ^ 59
def prefixEnd_7620475 : Nat := 4983230072969 + 3 ^ 40 * 7620475 * 2
def baseEnd_7620475 : Nat := 3912966490571177590216579

theorem tailTrace_7620475 : CollatzResearch.WordTrace tailWord_7620475 prefixEnd_7620475 3912966490571177590216579 := by
  unfold tailWord_7620475
  simp only [CollatzResearch.WordTrace]
  refine ⟨277941557067328023359510879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185294371378218682239673919 277941557067328023359510879)
  ·
    refine ⟨416912335600992035039266319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277941557067328023359510879 416912335600992035039266319)
    ·
      refine ⟨625368503401488052558899479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 416912335600992035039266319 625368503401488052558899479)
      ·
        refine ⟨938052755102232078838349219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 625368503401488052558899479 938052755102232078838349219)
        ·
          refine ⟨1407079132653348118257523829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 938052755102232078838349219 1407079132653348118257523829)
          ·
            refine ⟨131913668686251386086642859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1407079132653348118257523829 131913668686251386086642859)
            ·
              refine ⟨197870503029377079129964289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131913668686251386086642859 197870503029377079129964289)
              ·
                refine ⟨148402877272032809347473217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 197870503029377079129964289 148402877272032809347473217)
                ·
                  refine ⟨111302157954024607010604913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 148402877272032809347473217 111302157954024607010604913)
                  ·
                    refine ⟨83476618465518455257953685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 111302157954024607010604913 83476618465518455257953685)
                    ·
                      refine ⟨3912966490571177590216579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83476618465518455257953685 3912966490571177590216579)
                      ·
                        rfl

theorem cell23_7620475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 2, 2, 6].length) (baseStart_7620475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7620475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7620475 prefixEnd_7620475 := by exact prefixLift 7620475
  have htrace : WordTrace (prefixWord ++ tailWord_7620475) baseStart_7620475 baseEnd_7620475 := by
    simpa [prefixWord, tailWord_7620475, baseEnd_7620475] using wordTrace_append hprefix tailTrace_7620475
  have hstable : (prefixWord ++ tailWord_7620475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7620475).length < 2 ^ (prefixWord ++ tailWord_7620475).sum := by decide
  have hdescent : baseEnd_7620475 < baseStart_7620475 := by decide
  rcases family_descends (prefixWord ++ tailWord_7620475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7620483 : List Nat := [1, 1, 1, 3, 4, 2, 2, 4, 1, 2, 2]
def baseStart_7620483 : Nat := 118140960795 + 7620483 * 2 ^ 59
def prefixEnd_7620483 : Nat := 4983230072969 + 3 ^ 40 * 7620483 * 2
def baseEnd_7620483 : Nat := 3912970598416413558916543

theorem tailTrace_7620483 : CollatzResearch.WordTrace tailWord_7620483 prefixEnd_7620483 3912970598416413558916543 := by
  unfold tailWord_7620483
  simp only [CollatzResearch.WordTrace]
  refine ⟨277941848851299040725802103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185294565900866027150534735 277941848851299040725802103)
  ·
    refine ⟨416912773276948561088703155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277941848851299040725802103 416912773276948561088703155)
    ·
      refine ⟨625369159915422841633054733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 416912773276948561088703155 625369159915422841633054733)
      ·
        refine ⟨234513434968283565612395525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 625369159915422841633054733 234513434968283565612395525)
        ·
          refine ⟨43971269056553168552324161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 234513434968283565612395525 43971269056553168552324161)
          ·
            refine ⟨32978451792414876414243121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43971269056553168552324161 32978451792414876414243121)
            ·
              refine ⟨24733838844311157310682341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32978451792414876414243121 24733838844311157310682341)
              ·
                refine ⟨4637594783308341995752939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24733838844311157310682341 4637594783308341995752939)
                ·
                  refine ⟨6956392174962512993629409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4637594783308341995752939 6956392174962512993629409)
                  ·
                    refine ⟨5217294131221884745222057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6956392174962512993629409 5217294131221884745222057)
                    ·
                      refine ⟨3912970598416413558916543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5217294131221884745222057 3912970598416413558916543)
                      ·
                        rfl

theorem cell23_7620483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 4, 1, 2, 2].length) (baseStart_7620483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7620483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7620483 prefixEnd_7620483 := by exact prefixLift 7620483
  have htrace : WordTrace (prefixWord ++ tailWord_7620483) baseStart_7620483 baseEnd_7620483 := by
    simpa [prefixWord, tailWord_7620483, baseEnd_7620483] using wordTrace_append hprefix tailTrace_7620483
  have hstable : (prefixWord ++ tailWord_7620483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7620483).length < 2 ^ (prefixWord ++ tailWord_7620483).sum := by decide
  have hdescent : baseEnd_7620483 < baseStart_7620483 := by decide
  rcases family_descends (prefixWord ++ tailWord_7620483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7620573 : List Nat := [1, 4, 3, 1, 3, 1, 1, 2, 1, 4, 2]
def baseStart_7620573 : Nat := 118140960795 + 7620573 * 2 ^ 59
def prefixEnd_7620573 : Nat := 4983230072969 + 3 ^ 40 * 7620573 * 2
def baseEnd_7620573 : Nat := 3913016811675318206791129

theorem tailTrace_7620573 : CollatzResearch.WordTrace tailWord_7620573 prefixEnd_7620573 3913016811675318206791129 := by
  unfold tailWord_7620573
  simp only [CollatzResearch.WordTrace]
  refine ⟨277945131420972986096578373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185296754280648657397718915 277945131420972986096578373)
  ·
    refine ⟨52114712141432434893108445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 277945131420972986096578373 52114712141432434893108445)
    ·
      refine ⟨19543017053037163084915667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52114712141432434893108445 19543017053037163084915667)
      ·
        refine ⟨29314525579555744627373501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19543017053037163084915667 29314525579555744627373501)
        ·
          refine ⟨10992947092333404235265063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29314525579555744627373501 10992947092333404235265063)
          ·
            refine ⟨16489420638500106352897595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10992947092333404235265063 16489420638500106352897595)
            ·
              refine ⟨24734130957750159529346393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16489420638500106352897595 24734130957750159529346393)
              ·
                refine ⟨18550598218312619647009795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24734130957750159529346393 18550598218312619647009795)
                ·
                  refine ⟨27825897327468929470514693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18550598218312619647009795 27825897327468929470514693)
                  ·
                    refine ⟨5217355748900424275721505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27825897327468929470514693 5217355748900424275721505)
                    ·
                      refine ⟨3913016811675318206791129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5217355748900424275721505 3913016811675318206791129)
                      ·
                        rfl

theorem cell23_7620573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 2, 1, 4, 2].length) (baseStart_7620573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7620573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7620573 prefixEnd_7620573 := by exact prefixLift 7620573
  have htrace : WordTrace (prefixWord ++ tailWord_7620573) baseStart_7620573 baseEnd_7620573 := by
    simpa [prefixWord, tailWord_7620573, baseEnd_7620573] using wordTrace_append hprefix tailTrace_7620573
  have hstable : (prefixWord ++ tailWord_7620573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7620573).length < 2 ^ (prefixWord ++ tailWord_7620573).sum := by decide
  have hdescent : baseEnd_7620573 < baseStart_7620573 := by decide
  rcases family_descends (prefixWord ++ tailWord_7620573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7620590 : List Nat := [4, 1, 2, 1, 3, 2, 2, 2, 2, 2, 2]
def baseStart_7620590 : Nat := 118140960795 + 7620590 * 2 ^ 59
def prefixEnd_7620590 : Nat := 4983230072969 + 3 ^ 40 * 7620590 * 2
def baseEnd_7620590 : Nat := 3913025540846444640278551

theorem tailTrace_7620590 : CollatzResearch.WordTrace tailWord_7620590 prefixEnd_7620590 3913025540846444640278551 := by
  unfold tailWord_7620590
  simp only [CollatzResearch.WordTrace]
  refine ⟨34743218932738924749993403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185297167641274265333298149 34743218932738924749993403)
  ·
    refine ⟨52114828399108387124990105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34743218932738924749993403 52114828399108387124990105)
    ·
      refine ⟨39086121299331290343742579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52114828399108387124990105 39086121299331290343742579)
      ·
        refine ⟨58629181948996935515613869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39086121299331290343742579 58629181948996935515613869)
        ·
          refine ⟨21985943230873850818355201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58629181948996935515613869 21985943230873850818355201)
          ·
            refine ⟨16489457423155388113766401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21985943230873850818355201 16489457423155388113766401)
            ·
              refine ⟨12367093067366541085324801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16489457423155388113766401 12367093067366541085324801)
              ·
                refine ⟨9275319800524905813993601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12367093067366541085324801 9275319800524905813993601)
                ·
                  refine ⟨6956489850393679360495201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9275319800524905813993601 6956489850393679360495201)
                  ·
                    refine ⟨5217367387795259520371401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6956489850393679360495201 5217367387795259520371401)
                    ·
                      refine ⟨3913025540846444640278551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5217367387795259520371401 3913025540846444640278551)
                      ·
                        rfl

theorem cell23_7620590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 2, 2, 2, 2, 2].length) (baseStart_7620590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7620590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7620590 prefixEnd_7620590 := by exact prefixLift 7620590
  have htrace : WordTrace (prefixWord ++ tailWord_7620590) baseStart_7620590 baseEnd_7620590 := by
    simpa [prefixWord, tailWord_7620590, baseEnd_7620590] using wordTrace_append hprefix tailTrace_7620590
  have hstable : (prefixWord ++ tailWord_7620590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7620590).length < 2 ^ (prefixWord ++ tailWord_7620590).sum := by decide
  have hdescent : baseEnd_7620590 < baseStart_7620590 := by decide
  rcases family_descends (prefixWord ++ tailWord_7620590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7620606 : List Nat := [4, 2, 2, 2, 1, 1, 1, 1, 1, 5, 3]
def baseStart_7620606 : Nat := 118140960795 + 7620606 * 2 ^ 59
def prefixEnd_7620606 : Nat := 4983230072969 + 3 ^ 40 * 7620606 * 2
def baseEnd_7620606 : Nat := 3913033756536916577678477

theorem tailTrace_7620606 : CollatzResearch.WordTrace tailWord_7620606 prefixEnd_7620606 3913033756536916577678477 := by
  unfold tailWord_7620606
  simp only [CollatzResearch.WordTrace]
  refine ⟨34743291878731679091566209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185297556686568955155019781 34743291878731679091566209)
  ·
    refine ⟨26057468909048759318674657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34743291878731679091566209 26057468909048759318674657)
    ·
      refine ⟨19543101681786569489005993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26057468909048759318674657 19543101681786569489005993)
      ·
        refine ⟨14657326261339927116754495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19543101681786569489005993 14657326261339927116754495)
        ·
          refine ⟨21985989392009890675131743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14657326261339927116754495 21985989392009890675131743)
          ·
            refine ⟨32978984088014836012697615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21985989392009890675131743 32978984088014836012697615)
            ·
              refine ⟨49468476132022254019046423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32978984088014836012697615 49468476132022254019046423)
              ·
                refine ⟨74202714198033381028569635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49468476132022254019046423 74202714198033381028569635)
                ·
                  refine ⟨111304071297050071542854453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74202714198033381028569635 111304071297050071542854453)
                  ·
                    refine ⟨10434756684098444207142605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 111304071297050071542854453 10434756684098444207142605)
                    ·
                      refine ⟨3913033756536916577678477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10434756684098444207142605 3913033756536916577678477)
                      ·
                        rfl

theorem cell23_7620606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_7620606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7620606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7620606 prefixEnd_7620606 := by exact prefixLift 7620606
  have htrace : WordTrace (prefixWord ++ tailWord_7620606) baseStart_7620606 baseEnd_7620606 := by
    simpa [prefixWord, tailWord_7620606, baseEnd_7620606] using wordTrace_append hprefix tailTrace_7620606
  have hstable : (prefixWord ++ tailWord_7620606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7620606).length < 2 ^ (prefixWord ++ tailWord_7620606).sum := by decide
  have hdescent : baseEnd_7620606 < baseStart_7620606 := by decide
  rcases family_descends (prefixWord ++ tailWord_7620606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7620639 : List Nat := [1, 1, 2, 4, 1, 2, 1, 2, 5, 4]
def baseStart_7620639 : Nat := 118140960795 + 7620639 * 2 ^ 59
def prefixEnd_7620639 : Nat := 4983230072969 + 3 ^ 40 * 7620639 * 2
def baseEnd_7620639 : Nat := 1304350233799504982855275

theorem tailTrace_7620639 : CollatzResearch.WordTrace tailWord_7620639 prefixEnd_7620639 1304350233799504982855275 := by
  unfold tailWord_7620639
  simp only [CollatzResearch.WordTrace]
  refine ⟨277947538638733879368480971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185298359092489252912320647 277947538638733879368480971)
  ·
    refine ⟨416921307958100819052721457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277947538638733879368480971 416921307958100819052721457)
    ·
      refine ⟨312690980968575614289541093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 416921307958100819052721457 312690980968575614289541093)
      ·
        refine ⟨58629558931607927679288955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 312690980968575614289541093 58629558931607927679288955)
        ·
          refine ⟨87944338397411891518933433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58629558931607927679288955 87944338397411891518933433)
          ·
            refine ⟨65958253798058918639200075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87944338397411891518933433 65958253798058918639200075)
            ·
              refine ⟨98937380697088377958800113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65958253798058918639200075 98937380697088377958800113)
              ·
                refine ⟨74203035522816283469100085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98937380697088377958800113 74203035522816283469100085)
                ·
                  refine ⟨6956534580264026575228133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74203035522816283469100085 6956534580264026575228133)
                  ·
                    refine ⟨1304350233799504982855275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6956534580264026575228133 1304350233799504982855275)
                    ·
                      rfl

theorem cell23_7620639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 2, 5, 4].length) (baseStart_7620639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7620639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7620639 prefixEnd_7620639 := by exact prefixLift 7620639
  have htrace : WordTrace (prefixWord ++ tailWord_7620639) baseStart_7620639 baseEnd_7620639 := by
    simpa [prefixWord, tailWord_7620639, baseEnd_7620639] using wordTrace_append hprefix tailTrace_7620639
  have hstable : (prefixWord ++ tailWord_7620639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7620639).length < 2 ^ (prefixWord ++ tailWord_7620639).sum := by decide
  have hdescent : baseEnd_7620639 < baseStart_7620639 := by decide
  rcases family_descends (prefixWord ++ tailWord_7620639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7620656 : List Nat := [2, 1, 1, 1, 2, 6, 2, 1, 3, 4]
def baseStart_7620656 : Nat := 118140960795 + 7620656 * 2 ^ 59
def prefixEnd_7620656 : Nat := 4983230072969 + 3 ^ 40 * 7620656 * 2
def baseEnd_7620656 : Nat := 1304353143523213794017749

theorem tailTrace_7620656 : CollatzResearch.WordTrace tailWord_7620656 prefixEnd_7620656 1304353143523213794017749 := by
  unfold tailWord_7620656
  simp only [CollatzResearch.WordTrace]
  refine ⟨138974079339836145635924911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185298772453114860847899881 138974079339836145635924911)
  ·
    refine ⟨208461119009754218453887367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138974079339836145635924911 208461119009754218453887367)
    ·
      refine ⟨312691678514631327680831051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208461119009754218453887367 312691678514631327680831051)
      ·
        refine ⟨469037517771946991521246577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312691678514631327680831051 469037517771946991521246577)
        ·
          refine ⟨351778138328960243640934933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 469037517771946991521246577 351778138328960243640934933)
          ·
            refine ⟨16489600234170011420668825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 351778138328960243640934933 16489600234170011420668825)
            ·
              refine ⟨12367200175627508565501619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16489600234170011420668825 12367200175627508565501619)
              ·
                refine ⟨18550800263441262848252429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12367200175627508565501619 18550800263441262848252429)
                ·
                  refine ⟨6956550098790473568094661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18550800263441262848252429 6956550098790473568094661)
                  ·
                    refine ⟨1304353143523213794017749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6956550098790473568094661 1304353143523213794017749)
                    ·
                      rfl

theorem cell23_7620656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 2, 1, 3, 4].length) (baseStart_7620656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7620656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7620656 prefixEnd_7620656 := by exact prefixLift 7620656
  have htrace : WordTrace (prefixWord ++ tailWord_7620656) baseStart_7620656 baseEnd_7620656 := by
    simpa [prefixWord, tailWord_7620656, baseEnd_7620656] using wordTrace_append hprefix tailTrace_7620656
  have hstable : (prefixWord ++ tailWord_7620656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7620656).length < 2 ^ (prefixWord ++ tailWord_7620656).sum := by decide
  have hdescent : baseEnd_7620656 < baseStart_7620656 := by decide
  rcases family_descends (prefixWord ++ tailWord_7620656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7620679 : List Nat := [1, 1, 4, 1, 3, 1, 1, 1, 2, 5, 3]
def baseStart_7620679 : Nat := 118140960795 + 7620679 * 2 ^ 59
def prefixEnd_7620679 : Nat := 4983230072969 + 3 ^ 40 * 7620679 * 2
def baseEnd_7620679 : Nat := 3913071240624694792065641

theorem tailTrace_7620679 : CollatzResearch.WordTrace tailWord_7620679 prefixEnd_7620679 3913071240624694792065641 := by
  unfold tailWord_7620679
  simp only [CollatzResearch.WordTrace]
  refine ⟨277948997558588966199937091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185299331705725977466624727 277948997558588966199937091)
  ·
    refine ⟨416923496337883449299905637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277948997558588966199937091 416923496337883449299905637)
    ·
      refine ⟨78173155563353146743732307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 416923496337883449299905637 78173155563353146743732307)
      ·
        refine ⟨117259733345029720115598461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78173155563353146743732307 117259733345029720115598461)
        ·
          refine ⟨43972400004386145043349423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117259733345029720115598461 43972400004386145043349423)
          ·
            refine ⟨65958600006579217565024135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43972400004386145043349423 65958600006579217565024135)
            ·
              refine ⟨98937900009868826347536203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65958600006579217565024135 98937900009868826347536203)
              ·
                refine ⟨148406850014803239521304305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98937900009868826347536203 148406850014803239521304305)
                ·
                  refine ⟨111305137511102429640978229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 148406850014803239521304305 111305137511102429640978229)
                  ·
                    refine ⟨10434856641665852778841709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 111305137511102429640978229 10434856641665852778841709)
                    ·
                      refine ⟨3913071240624694792065641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10434856641665852778841709 3913071240624694792065641)
                      ·
                        rfl

theorem cell23_7620679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 2, 5, 3].length) (baseStart_7620679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7620679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7620679 prefixEnd_7620679 := by exact prefixLift 7620679
  have htrace : WordTrace (prefixWord ++ tailWord_7620679) baseStart_7620679 baseEnd_7620679 := by
    simpa [prefixWord, tailWord_7620679, baseEnd_7620679] using wordTrace_append hprefix tailTrace_7620679
  have hstable : (prefixWord ++ tailWord_7620679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7620679).length < 2 ^ (prefixWord ++ tailWord_7620679).sum := by decide
  have hdescent : baseEnd_7620679 < baseStart_7620679 := by decide
  rcases family_descends (prefixWord ++ tailWord_7620679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7620733 : List Nat := [1, 4, 1, 1, 3, 4, 1, 2, 1, 5]
def baseStart_7620733 : Nat := 118140960795 + 7620733 * 2 ^ 59
def prefixEnd_7620733 : Nat := 4983230072969 + 3 ^ 40 * 7620733 * 2
def baseEnd_7620733 : Nat := 1304366322860012526930131

theorem tailTrace_7620733 : CollatzResearch.WordTrace tailWord_7620733 prefixEnd_7620733 1304366322860012526930131 := by
  unfold tailWord_7620733
  simp only [CollatzResearch.WordTrace]
  refine ⟨277950967100393333422402853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185300644733595555614935235 277950967100393333422402853)
  ·
    refine ⟨52115806331323750016700535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 277950967100393333422402853 52115806331323750016700535)
    ·
      refine ⟨78173709496985625025050803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52115806331323750016700535 78173709496985625025050803)
      ·
        refine ⟨117260564245478437537576205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78173709496985625025050803 117260564245478437537576205)
        ·
          refine ⟨43972711592054414076591077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117260564245478437537576205 43972711592054414076591077)
          ·
            refine ⟨8244883423510202639360827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43972711592054414076591077 8244883423510202639360827)
            ·
              refine ⟨12367325135265303959041241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8244883423510202639360827 12367325135265303959041241)
              ·
                refine ⟨9275493851448977969280931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12367325135265303959041241 9275493851448977969280931)
                ·
                  refine ⟨13913240777173466953921397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9275493851448977969280931 13913240777173466953921397)
                  ·
                    refine ⟨1304366322860012526930131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13913240777173466953921397 1304366322860012526930131)
                    ·
                      rfl

theorem cell23_7620733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 1, 2, 1, 5].length) (baseStart_7620733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7620733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7620733 prefixEnd_7620733 := by exact prefixLift 7620733
  have htrace : WordTrace (prefixWord ++ tailWord_7620733) baseStart_7620733 baseEnd_7620733 := by
    simpa [prefixWord, tailWord_7620733, baseEnd_7620733] using wordTrace_append hprefix tailTrace_7620733
  have hstable : (prefixWord ++ tailWord_7620733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7620733).length < 2 ^ (prefixWord ++ tailWord_7620733).sum := by decide
  have hdescent : baseEnd_7620733 < baseStart_7620733 := by decide
  rcases family_descends (prefixWord ++ tailWord_7620733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7620746 : List Nat := [3, 1, 2, 3, 1, 3, 1, 2, 1, 6]
def baseStart_7620746 : Nat := 118140960795 + 7620746 * 2 ^ 59
def prefixEnd_7620746 : Nat := 4983230072969 + 3 ^ 40 * 7620746 * 2
def baseEnd_7620746 : Nat := 1304368547942848676642611

theorem tailTrace_7620746 : CollatzResearch.WordTrace tailWord_7620746 prefixEnd_7620746 1304368547942848676642611 := by
  unfold tailWord_7620746
  simp only [CollatzResearch.WordTrace]
  refine ⟨69487860312336559160656523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185300960832897491095084061 69487860312336559160656523)
  ·
    refine ⟨104231790468504838740984785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69487860312336559160656523 104231790468504838740984785)
    ·
      refine ⟨78173842851378629055738589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104231790468504838740984785 78173842851378629055738589)
      ·
        refine ⟨29315191069266985895901971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78173842851378629055738589 29315191069266985895901971)
        ·
          refine ⟨43972786603900478843852957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29315191069266985895901971 43972786603900478843852957)
          ·
            refine ⟨16489794976462679566444859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43972786603900478843852957 16489794976462679566444859)
            ·
              refine ⟨24734692464694019349667289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16489794976462679566444859 24734692464694019349667289)
              ·
                refine ⟨18551019348520514512250467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24734692464694019349667289 18551019348520514512250467)
                ·
                  refine ⟨27826529022780771768375701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18551019348520514512250467 27826529022780771768375701)
                  ·
                    refine ⟨1304368547942848676642611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27826529022780771768375701 1304368547942848676642611)
                    ·
                      rfl

theorem cell23_7620746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 2, 1, 6].length) (baseStart_7620746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7620746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7620746 prefixEnd_7620746 := by exact prefixLift 7620746
  have htrace : WordTrace (prefixWord ++ tailWord_7620746) baseStart_7620746 baseEnd_7620746 := by
    simpa [prefixWord, tailWord_7620746, baseEnd_7620746] using wordTrace_append hprefix tailTrace_7620746
  have hstable : (prefixWord ++ tailWord_7620746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7620746).length < 2 ^ (prefixWord ++ tailWord_7620746).sum := by decide
  have hdescent : baseEnd_7620746 < baseStart_7620746 := by decide
  rcases family_descends (prefixWord ++ tailWord_7620746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7620750 : List Nat := [4, 1, 1, 3, 3, 1, 3, 1, 1, 5]
def baseStart_7620750 : Nat := 118140960795 + 7620750 * 2 ^ 59
def prefixEnd_7620750 : Nat := 4983230072969 + 3 ^ 40 * 7620750 * 2
def baseEnd_7620750 : Nat := 1304369232583721338092605

theorem tailTrace_7620750 : CollatzResearch.WordTrace tailWord_7620750 prefixEnd_7620750 1304369232583721338092605 := by
  unfold tailWord_7620750
  simp only [CollatzResearch.WordTrace]
  refine ⟨34743948392666468165721463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185301058094221163550514469 34743948392666468165721463)
  ·
    refine ⟨52115922588999702248582195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34743948392666468165721463 52115922588999702248582195)
    ·
      refine ⟨78173883883499553372873293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52115922588999702248582195 78173883883499553372873293)
      ·
        refine ⟨29315206456312332514827485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78173883883499553372873293 29315206456312332514827485)
        ·
          refine ⟨10993202421117124693060307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29315206456312332514827485 10993202421117124693060307)
          ·
            refine ⟨16489803631675687039590461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10993202421117124693060307 16489803631675687039590461)
            ·
              refine ⟨6183676361878382639846423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16489803631675687039590461 6183676361878382639846423)
              ·
                refine ⟨9275514542817573959769635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6183676361878382639846423 9275514542817573959769635)
                ·
                  refine ⟨13913271814226360939654453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9275514542817573959769635 13913271814226360939654453)
                  ·
                    refine ⟨1304369232583721338092605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13913271814226360939654453 1304369232583721338092605)
                    ·
                      rfl

theorem cell23_7620750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 3, 1, 1, 5].length) (baseStart_7620750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7620750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7620750 prefixEnd_7620750 := by exact prefixLift 7620750
  have htrace : WordTrace (prefixWord ++ tailWord_7620750) baseStart_7620750 baseEnd_7620750 := by
    simpa [prefixWord, tailWord_7620750, baseEnd_7620750] using wordTrace_append hprefix tailTrace_7620750
  have hstable : (prefixWord ++ tailWord_7620750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7620750).length < 2 ^ (prefixWord ++ tailWord_7620750).sum := by decide
  have hdescent : baseEnd_7620750 < baseStart_7620750 := by decide
  rcases family_descends (prefixWord ++ tailWord_7620750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7620759 : List Nat := [1, 1, 3, 3, 4, 11]
def baseStart_7620759 : Nat := 118140960795 + 7620759 * 2 ^ 59
def prefixEnd_7620759 : Nat := 4983230072969 + 3 ^ 40 * 7620759 * 2
def baseEnd_7620759 : Nat := 16103342876860306498211

theorem tailTrace_7620759 : CollatzResearch.WordTrace tailWord_7620759 prefixEnd_7620759 16103342876860306498211 := by
  unfold tailWord_7620759
  simp only [CollatzResearch.WordTrace]
  refine ⟨277951915398299139862849331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185301276932199426575232887 277951915398299139862849331)
  ·
    refine ⟨416927873097448709794273997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277951915398299139862849331 416927873097448709794273997)
    ·
      refine ⟨156347952411543266172852749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 416927873097448709794273997 156347952411543266172852749)
      ·
        refine ⟨58630482154328724814819781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156347952411543266172852749 58630482154328724814819781)
        ·
          refine ⟨10993215403936635902778709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58630482154328724814819781 10993215403936635902778709)
          ·
            refine ⟨16103342876860306498211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 10993215403936635902778709 16103342876860306498211)
            ·
              rfl

theorem cell23_7620759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 11].length) (baseStart_7620759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7620759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7620759 prefixEnd_7620759 := by exact prefixLift 7620759
  have htrace : WordTrace (prefixWord ++ tailWord_7620759) baseStart_7620759 baseEnd_7620759 := by
    simpa [prefixWord, tailWord_7620759, baseEnd_7620759] using wordTrace_append hprefix tailTrace_7620759
  have hstable : (prefixWord ++ tailWord_7620759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7620759).length < 2 ^ (prefixWord ++ tailWord_7620759).sum := by decide
  have hdescent : baseEnd_7620759 < baseStart_7620759 := by decide
  rcases family_descends (prefixWord ++ tailWord_7620759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7620799 : List Nat := [1, 1, 2, 2, 2, 2, 1, 3, 2, 2, 5]
def baseStart_7620799 : Nat := 118140960795 + 7620799 * 2 ^ 59
def prefixEnd_7620799 : Nat := 4983230072969 + 3 ^ 40 * 7620799 * 2
def baseEnd_7620799 : Nat := 3913132858303234322565089

theorem tailTrace_7620799 : CollatzResearch.WordTrace tailWord_7620799 prefixEnd_7620799 3913132858303234322565089 := by
  unfold tailWord_7620799
  simp only [CollatzResearch.WordTrace]
  refine ⟨277953374318154226694305451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185302249545436151129536967 277953374318154226694305451)
  ·
    refine ⟨416930061477231340041458177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277953374318154226694305451 416930061477231340041458177)
    ·
      refine ⟨312697546107923505031093633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 416930061477231340041458177 312697546107923505031093633)
      ·
        refine ⟨234523159580942628773320225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 312697546107923505031093633 234523159580942628773320225)
        ·
          refine ⟨175892369685706971579990169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234523159580942628773320225 175892369685706971579990169)
          ·
            refine ⟨131919277264280228684992627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175892369685706971579990169 131919277264280228684992627)
            ·
              refine ⟨197878915896420343027488941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131919277264280228684992627 197878915896420343027488941)
              ·
                refine ⟨74204593461157628635308353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 197878915896420343027488941 74204593461157628635308353)
                ·
                  refine ⟨55653445095868221476481265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74204593461157628635308353 55653445095868221476481265)
                  ·
                    refine ⟨41740083821901166107360949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55653445095868221476481265 41740083821901166107360949)
                    ·
                      refine ⟨3913132858303234322565089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41740083821901166107360949 3913132858303234322565089)
                      ·
                        rfl

theorem cell23_7620799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 3, 2, 2, 5].length) (baseStart_7620799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7620799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7620799 prefixEnd_7620799 := by exact prefixLift 7620799
  have htrace : WordTrace (prefixWord ++ tailWord_7620799) baseStart_7620799 baseEnd_7620799 := by
    simpa [prefixWord, tailWord_7620799, baseEnd_7620799] using wordTrace_append hprefix tailTrace_7620799
  have hstable : (prefixWord ++ tailWord_7620799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7620799).length < 2 ^ (prefixWord ++ tailWord_7620799).sum := by decide
  have hdescent : baseEnd_7620799 < baseStart_7620799 := by decide
  rcases family_descends (prefixWord ++ tailWord_7620799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7620804 : List Nat := [2, 3, 3, 1, 2, 2, 2, 3, 1, 2, 2]
def baseStart_7620804 : Nat := 118140960795 + 7620804 * 2 ^ 59
def prefixEnd_7620804 : Nat := 4983230072969 + 3 ^ 40 * 7620804 * 2
def baseEnd_7620804 : Nat := 3913135425706506803002567

theorem tailTrace_7620804 : CollatzResearch.WordTrace tailWord_7620804 prefixEnd_7620804 3913135425706506803002567 := by
  unfold tailWord_7620804
  simp only [CollatzResearch.WordTrace]
  refine ⟨138976778341568056274118733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185302371122090741698824977 138976778341568056274118733)
  ·
    refine ⟨52116291878088021102794525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138976778341568056274118733 52116291878088021102794525)
    ·
      refine ⟨19543609454283007913547947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52116291878088021102794525 19543609454283007913547947)
      ·
        refine ⟨29315414181424511870321921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19543609454283007913547947 29315414181424511870321921)
        ·
          refine ⟨21986560636068383902741441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29315414181424511870321921 21986560636068383902741441)
          ·
            refine ⟨16489920477051287927056081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21986560636068383902741441 16489920477051287927056081)
            ·
              refine ⟨12367440357788465945292061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16489920477051287927056081 12367440357788465945292061)
              ·
                refine ⟨4637790134170674729484523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12367440357788465945292061 4637790134170674729484523)
                ·
                  refine ⟨6956685201256012094226785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4637790134170674729484523 6956685201256012094226785)
                  ·
                    refine ⟨5217513900942009070670089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6956685201256012094226785 5217513900942009070670089)
                    ·
                      refine ⟨3913135425706506803002567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5217513900942009070670089 3913135425706506803002567)
                      ·
                        rfl

theorem cell23_7620804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 2, 3, 1, 2, 2].length) (baseStart_7620804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7620804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7620804 prefixEnd_7620804 := by exact prefixLift 7620804
  have htrace : WordTrace (prefixWord ++ tailWord_7620804) baseStart_7620804 baseEnd_7620804 := by
    simpa [prefixWord, tailWord_7620804, baseEnd_7620804] using wordTrace_append hprefix tailTrace_7620804
  have hstable : (prefixWord ++ tailWord_7620804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7620804).length < 2 ^ (prefixWord ++ tailWord_7620804).sum := by decide
  have hdescent : baseEnd_7620804 < baseStart_7620804 := by decide
  rcases family_descends (prefixWord ++ tailWord_7620804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7620809 : List Nat := [1, 2, 1, 1, 2, 1, 1, 4, 1, 5, 4]
def baseStart_7620809 : Nat := 118140960795 + 7620809 * 2 ^ 59
def prefixEnd_7620809 : Nat := 4983230072969 + 3 ^ 40 * 7620809 * 2
def baseEnd_7620809 : Nat := 3913137993109779283440043

theorem tailTrace_7620809 : CollatzResearch.WordTrace tailWord_7620809 prefixEnd_7620809 3913137993109779283440043 := by
  unfold tailWord_7620809
  simp only [CollatzResearch.WordTrace]
  refine ⟨277953739048117998402169481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185302492698745332268112987 277953739048117998402169481)
  ·
    refine ⟨208465304286088498801627111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277953739048117998402169481 208465304286088498801627111)
    ·
      refine ⟨312697956429132748202440667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208465304286088498801627111 312697956429132748202440667)
      ·
        refine ⟨469046934643699122303661001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312697956429132748202440667 469046934643699122303661001)
        ·
          refine ⟨351785200982774341727745751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 469046934643699122303661001 351785200982774341727745751)
          ·
            refine ⟨527677801474161512591618627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 351785200982774341727745751 527677801474161512591618627)
            ·
              refine ⟨791516702211242268887427941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 527677801474161512591618627 791516702211242268887427941)
              ·
                refine ⟨148409381664607925416392739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 791516702211242268887427941 148409381664607925416392739)
                ·
                  refine ⟨222614072496911888124589109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 148409381664607925416392739 222614072496911888124589109)
                  ·
                    refine ⟨20870069296585489511680229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 222614072496911888124589109 20870069296585489511680229)
                    ·
                      refine ⟨3913137993109779283440043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20870069296585489511680229 3913137993109779283440043)
                      ·
                        rfl

theorem cell23_7620809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 5, 4].length) (baseStart_7620809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7620809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7620809 prefixEnd_7620809 := by exact prefixLift 7620809
  have htrace : WordTrace (prefixWord ++ tailWord_7620809) baseStart_7620809 baseEnd_7620809 := by
    simpa [prefixWord, tailWord_7620809, baseEnd_7620809] using wordTrace_append hprefix tailTrace_7620809
  have hstable : (prefixWord ++ tailWord_7620809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7620809).length < 2 ^ (prefixWord ++ tailWord_7620809).sum := by decide
  have hdescent : baseEnd_7620809 < baseStart_7620809 := by decide
  rcases family_descends (prefixWord ++ tailWord_7620809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7620834 : List Nat := [3, 3, 4, 1, 1, 2, 1, 1, 1, 2, 4]
def baseStart_7620834 : Nat := 118140960795 + 7620834 * 2 ^ 59
def prefixEnd_7620834 : Nat := 4983230072969 + 3 ^ 40 * 7620834 * 2
def baseEnd_7620834 : Nat := 3913150830126141685627429

theorem tailTrace_7620834 : CollatzResearch.WordTrace tailWord_7620834 prefixEnd_7620834 3913150830126141685627429 := by
  unfold tailWord_7620834
  simp only [CollatzResearch.WordTrace]
  refine ⟨69488662718256856917957389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185303100582018285114553037 69488662718256856917957389)
  ·
    refine ⟨26058248519346321344234021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69488662718256856917957389 26058248519346321344234021)
    ·
      refine ⟨4885921597377435252043879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26058248519346321344234021 4885921597377435252043879)
      ·
        refine ⟨7328882396066152878065819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4885921597377435252043879 7328882396066152878065819)
        ·
          refine ⟨10993323594099229317098729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7328882396066152878065819 10993323594099229317098729)
          ·
            refine ⟨8244992695574421987824047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10993323594099229317098729 8244992695574421987824047)
            ·
              refine ⟨12367489043361632981736071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8244992695574421987824047 12367489043361632981736071)
              ·
                refine ⟨18551233565042449472604107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12367489043361632981736071 18551233565042449472604107)
                ·
                  refine ⟨27826850347563674208906161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18551233565042449472604107 27826850347563674208906161)
                  ·
                    refine ⟨20870137760672755656679621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27826850347563674208906161 20870137760672755656679621)
                    ·
                      refine ⟨3913150830126141685627429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20870137760672755656679621 3913150830126141685627429)
                      ·
                        rfl

theorem cell23_7620834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_7620834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7620834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7620834 prefixEnd_7620834 := by exact prefixLift 7620834
  have htrace : WordTrace (prefixWord ++ tailWord_7620834) baseStart_7620834 baseEnd_7620834 := by
    simpa [prefixWord, tailWord_7620834, baseEnd_7620834] using wordTrace_append hprefix tailTrace_7620834
  have hstable : (prefixWord ++ tailWord_7620834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7620834).length < 2 ^ (prefixWord ++ tailWord_7620834).sum := by decide
  have hdescent : baseEnd_7620834 < baseStart_7620834 := by decide
  rcases family_descends (prefixWord ++ tailWord_7620834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7620837 : List Nat := [1, 3, 1, 4, 2, 2, 3, 1, 2, 1, 3]
def baseStart_7620837 : Nat := 118140960795 + 7620837 * 2 ^ 59
def prefixEnd_7620837 : Nat := 4983230072969 + 3 ^ 40 * 7620837 * 2
def baseEnd_7620837 : Nat := 3913152370568105173889915

theorem tailTrace_7620837 : CollatzResearch.WordTrace tailWord_7620837 prefixEnd_7620837 3913152370568105173889915 := by
  unfold tailWord_7620837
  simp only [CollatzResearch.WordTrace]
  refine ⟨277954760292016559184188765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185303173528011039456125843 277954760292016559184188765)
  ·
    refine ⟨104233035109506209694070787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 277954760292016559184188765 104233035109506209694070787)
    ·
      refine ⟨156349552664259314541106181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104233035109506209694070787 156349552664259314541106181)
      ·
        refine ⟨29315541124548621476457409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 156349552664259314541106181 29315541124548621476457409)
        ·
          refine ⟨21986655843411466107343057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29315541124548621476457409 21986655843411466107343057)
          ·
            refine ⟨16489991882558599580507293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21986655843411466107343057 16489991882558599580507293)
            ·
              refine ⟨6183746955959474842690235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16489991882558599580507293 6183746955959474842690235)
              ·
                refine ⟨9275620433939212264035353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6183746955959474842690235 9275620433939212264035353)
                ·
                  refine ⟨6956715325454409198026515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9275620433939212264035353 6956715325454409198026515)
                  ·
                    refine ⟨10435072988181613797039773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6956715325454409198026515 10435072988181613797039773)
                    ·
                      refine ⟨3913152370568105173889915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10435072988181613797039773 3913152370568105173889915)
                      ·
                        rfl

theorem cell23_7620837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 3, 1, 2, 1, 3].length) (baseStart_7620837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7620837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7620837 prefixEnd_7620837 := by exact prefixLift 7620837
  have htrace : WordTrace (prefixWord ++ tailWord_7620837) baseStart_7620837 baseEnd_7620837 := by
    simpa [prefixWord, tailWord_7620837, baseEnd_7620837] using wordTrace_append hprefix tailTrace_7620837
  have hstable : (prefixWord ++ tailWord_7620837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7620837).length < 2 ^ (prefixWord ++ tailWord_7620837).sum := by decide
  have hdescent : baseEnd_7620837 < baseStart_7620837 := by decide
  rcases family_descends (prefixWord ++ tailWord_7620837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7620846 : List Nat := [4, 1, 2, 1, 1, 1, 1, 4, 2, 1, 5]
def baseStart_7620846 : Nat := 118140960795 + 7620846 * 2 ^ 59
def prefixEnd_7620846 : Nat := 4983230072969 + 3 ^ 40 * 7620846 * 2
def baseEnd_7620846 : Nat := 3913156991893995638677373

theorem tailTrace_7620846 : CollatzResearch.WordTrace tailWord_7620846 prefixEnd_7620846 3913156991893995638677373 := by
  unfold tailWord_7620846
  simp only [CollatzResearch.WordTrace]
  refine ⟨34744386068622994215158299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185303392365989302480844261 34744386068622994215158299)
  ·
    refine ⟨52116579102934491322737449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34744386068622994215158299 52116579102934491322737449)
    ·
      refine ⟨39087434327200868492053087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52116579102934491322737449 39087434327200868492053087)
      ·
        refine ⟨58631151490801302738079631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39087434327200868492053087 58631151490801302738079631)
        ·
          refine ⟨87946727236201954107119447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58631151490801302738079631 87946727236201954107119447)
          ·
            refine ⟨131920090854302931160679171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87946727236201954107119447 131920090854302931160679171)
            ·
              refine ⟨197880136281454396741018757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131920090854302931160679171 197880136281454396741018757)
              ·
                refine ⟨37102525552772699388941017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 197880136281454396741018757 37102525552772699388941017)
                ·
                  refine ⟨27826894164579524541705763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37102525552772699388941017 27826894164579524541705763)
                  ·
                    refine ⟨41740341246869286812558645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27826894164579524541705763 41740341246869286812558645)
                    ·
                      refine ⟨3913156991893995638677373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41740341246869286812558645 3913156991893995638677373)
                      ·
                        rfl

theorem cell23_7620846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 4, 2, 1, 5].length) (baseStart_7620846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7620846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7620846 prefixEnd_7620846 := by exact prefixLift 7620846
  have htrace : WordTrace (prefixWord ++ tailWord_7620846) baseStart_7620846 baseEnd_7620846 := by
    simpa [prefixWord, tailWord_7620846, baseEnd_7620846] using wordTrace_append hprefix tailTrace_7620846
  have hstable : (prefixWord ++ tailWord_7620846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7620846).length < 2 ^ (prefixWord ++ tailWord_7620846).sum := by decide
  have hdescent : baseEnd_7620846 < baseStart_7620846 := by decide
  rcases family_descends (prefixWord ++ tailWord_7620846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7620860 : List Nat := [2, 2, 2, 1, 4, 1, 1, 2, 4, 2, 2]
def baseStart_7620860 : Nat := 118140960795 + 7620860 * 2 ^ 59
def prefixEnd_7620860 : Nat := 4983230072969 + 3 ^ 40 * 7620860 * 2
def baseEnd_7620860 : Nat := 3913164180623158583902309

theorem tailTrace_7620860 : CollatzResearch.WordTrace tailWord_7620860 prefixEnd_7620860 3913164180623158583902309 := by
  unfold tailWord_7620860
  simp only [CollatzResearch.WordTrace]
  refine ⟨138977799585466617056138017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185303732780622156074850689 138977799585466617056138017)
  ·
    refine ⟨104233349689099962792103513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138977799585466617056138017 104233349689099962792103513)
    ·
      refine ⟨78175012266824972094077635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104233349689099962792103513 78175012266824972094077635)
      ·
        refine ⟨117262518400237458141116453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78175012266824972094077635 117262518400237458141116453)
        ·
          refine ⟨21986722200044523401459335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 117262518400237458141116453 21986722200044523401459335)
          ·
            refine ⟨32980083300066785102189003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21986722200044523401459335 32980083300066785102189003)
            ·
              refine ⟨49470124950100177653283505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32980083300066785102189003 49470124950100177653283505)
              ·
                refine ⟨37102593712575133239962629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49470124950100177653283505 37102593712575133239962629)
                ·
                  refine ⟨6956736321107837482492993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37102593712575133239962629 6956736321107837482492993)
                  ·
                    refine ⟨5217552240830878111869745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6956736321107837482492993 5217552240830878111869745)
                    ·
                      refine ⟨3913164180623158583902309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5217552240830878111869745 3913164180623158583902309)
                      ·
                        rfl

theorem cell23_7620860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 2, 4, 2, 2].length) (baseStart_7620860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7620860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7620860 prefixEnd_7620860 := by exact prefixLift 7620860
  have htrace : WordTrace (prefixWord ++ tailWord_7620860) baseStart_7620860 baseEnd_7620860 := by
    simpa [prefixWord, tailWord_7620860, baseEnd_7620860] using wordTrace_append hprefix tailTrace_7620860
  have hstable : (prefixWord ++ tailWord_7620860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7620860).length < 2 ^ (prefixWord ++ tailWord_7620860).sum := by decide
  have hdescent : baseEnd_7620860 < baseStart_7620860 := by decide
  rcases family_descends (prefixWord ++ tailWord_7620860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7620960 : List Nat := [2, 1, 1, 3, 5, 1, 1, 2, 3, 4]
def baseStart_7620960 : Nat := 118140960795 + 7620960 * 2 ^ 59
def prefixEnd_7620960 : Nat := 4983230072969 + 3 ^ 40 * 7620960 * 2
def baseEnd_7620960 : Nat := 1304405176229536064217283

theorem tailTrace_7620960 : CollatzResearch.WordTrace tailWord_7620960 prefixEnd_7620960 1304405176229536064217283 := by
  unfold tailWord_7620960
  simp only [CollatzResearch.WordTrace]
  refine ⟨138979623235285475595458167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185306164313713967460610889 138979623235285475595458167)
  ·
    refine ⟨208469434852928213393187251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138979623235285475595458167 208469434852928213393187251)
    ·
      refine ⟨312704152279392320089780877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208469434852928213393187251 312704152279392320089780877)
      ·
        refine ⟨117264057104772120033667829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 312704152279392320089780877 117264057104772120033667829)
        ·
          refine ⟨10993505353572386253156359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 117264057104772120033667829 10993505353572386253156359)
          ·
            refine ⟨16490258030358579379734539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10993505353572386253156359 16490258030358579379734539)
            ·
              refine ⟨24735387045537869069601809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16490258030358579379734539 24735387045537869069601809)
              ·
                refine ⟨18551540284153401802201357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24735387045537869069601809 18551540284153401802201357)
                ·
                  refine ⟨6956827606557525675825509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18551540284153401802201357 6956827606557525675825509)
                  ·
                    refine ⟨1304405176229536064217283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6956827606557525675825509 1304405176229536064217283)
                    ·
                      rfl

theorem cell23_7620960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 2, 3, 4].length) (baseStart_7620960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7620960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7620960 prefixEnd_7620960 := by exact prefixLift 7620960
  have htrace : WordTrace (prefixWord ++ tailWord_7620960) baseStart_7620960 baseEnd_7620960 := by
    simpa [prefixWord, tailWord_7620960, baseEnd_7620960] using wordTrace_append hprefix tailTrace_7620960
  have hstable : (prefixWord ++ tailWord_7620960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7620960).length < 2 ^ (prefixWord ++ tailWord_7620960).sum := by decide
  have hdescent : baseEnd_7620960 < baseStart_7620960 := by decide
  rcases family_descends (prefixWord ++ tailWord_7620960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7620970 : List Nat := [3, 1, 3, 3, 1, 2, 1, 1, 1, 4, 3]
def baseStart_7620970 : Nat := 118140960795 + 7620970 * 2 ^ 59
def prefixEnd_7620970 : Nat := 4983230072969 + 3 ^ 40 * 7620970 * 2
def baseEnd_7620970 : Nat := 3913220663495153153526803

theorem tailTrace_7620970 : CollatzResearch.WordTrace tailWord_7620970 prefixEnd_7620970 3913220663495153153526803 := by
  unfold tailWord_7620970
  simp only [CollatzResearch.WordTrace]
  refine ⟨69489902800133680724695091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185306407467023148599186909 69489902800133680724695091)
  ·
    refine ⟨104234854200200521087042637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69489902800133680724695091 104234854200200521087042637)
    ·
      refine ⟨39088070325075195407640989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104234854200200521087042637 39088070325075195407640989)
      ·
        refine ⟨14658026371903198277865371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39088070325075195407640989 14658026371903198277865371)
        ·
          refine ⟨21987039557854797416798057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14658026371903198277865371 21987039557854797416798057)
          ·
            refine ⟨16490279668391098062598543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21987039557854797416798057 16490279668391098062598543)
            ·
              refine ⟨24735419502586647093897815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16490279668391098062598543 24735419502586647093897815)
              ·
                refine ⟨37103129253879970640846723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24735419502586647093897815 37103129253879970640846723)
                ·
                  refine ⟨55654693880819955961270085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37103129253879970640846723 55654693880819955961270085)
                  ·
                    refine ⟨10435255102653741742738141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55654693880819955961270085 10435255102653741742738141)
                    ·
                      refine ⟨3913220663495153153526803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10435255102653741742738141 3913220663495153153526803)
                      ·
                        rfl

theorem cell23_7620970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_7620970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7620970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7620970 prefixEnd_7620970 := by exact prefixLift 7620970
  have htrace : WordTrace (prefixWord ++ tailWord_7620970) baseStart_7620970 baseEnd_7620970 := by
    simpa [prefixWord, tailWord_7620970, baseEnd_7620970] using wordTrace_append hprefix tailTrace_7620970
  have hstable : (prefixWord ++ tailWord_7620970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7620970).length < 2 ^ (prefixWord ++ tailWord_7620970).sum := by decide
  have hdescent : baseEnd_7620970 < baseStart_7620970 := by decide
  rcases family_descends (prefixWord ++ tailWord_7620970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7620993 : List Nat := [1, 2, 4, 3, 1, 1, 1, 1, 1, 2, 6]
def baseStart_7620993 : Nat := 118140960795 + 7620993 * 2 ^ 59
def prefixEnd_7620993 : Nat := 4983230072969 + 3 ^ 40 * 7620993 * 2
def baseEnd_7620993 : Nat := 3913232473550206563539197

theorem tailTrace_7620993 : CollatzResearch.WordTrace tailWord_7620993 prefixEnd_7620993 3913232473550206563539197 := by
  unfold tailWord_7620993
  simp only [CollatzResearch.WordTrace]
  refine ⟨277960450079451397826867633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185306966719634265217911755 277960450079451397826867633)
  ·
    refine ⟨208470337559588548370150725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277960450079451397826867633 208470337559588548370150725)
    ·
      refine ⟨39088188292422852819403261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 208470337559588548370150725 39088188292422852819403261)
      ·
        refine ⟨14658070609658569807276223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39088188292422852819403261 14658070609658569807276223)
        ·
          refine ⟨21987105914487854710914335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14658070609658569807276223 21987105914487854710914335)
          ·
            refine ⟨32980658871731782066371503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21987105914487854710914335 32980658871731782066371503)
            ·
              refine ⟨49470988307597673099557255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32980658871731782066371503 49470988307597673099557255)
              ·
                refine ⟨74206482461396509649335883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49470988307597673099557255 74206482461396509649335883)
                ·
                  refine ⟨111309723692094764474003825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74206482461396509649335883 111309723692094764474003825)
                  ·
                    refine ⟨83482292769071073355502869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 111309723692094764474003825 83482292769071073355502869)
                    ·
                      refine ⟨3913232473550206563539197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83482292769071073355502869 3913232473550206563539197)
                      ·
                        rfl

theorem cell23_7620993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_7620993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7620993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7620993 prefixEnd_7620993 := by exact prefixLift 7620993
  have htrace : WordTrace (prefixWord ++ tailWord_7620993) baseStart_7620993 baseEnd_7620993 := by
    simpa [prefixWord, tailWord_7620993, baseEnd_7620993] using wordTrace_append hprefix tailTrace_7620993
  have hstable : (prefixWord ++ tailWord_7620993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7620993).length < 2 ^ (prefixWord ++ tailWord_7620993).sum := by decide
  have hdescent : baseEnd_7620993 < baseStart_7620993 := by decide
  rcases family_descends (prefixWord ++ tailWord_7620993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7620994 : List Nat := [3, 4, 2, 1, 2, 1, 2, 1, 3, 4]
def baseStart_7620994 : Nat := 118140960795 + 7620994 * 2 ^ 59
def prefixEnd_7620994 : Nat := 4983230072969 + 3 ^ 40 * 7620994 * 2
def baseEnd_7620994 : Nat := 1304410995676953686542231

theorem tailTrace_7620994 : CollatzResearch.WordTrace tailWord_7620994 prefixEnd_7620994 1304410995676953686542231 := by
  unfold tailWord_7620994
  simp only [CollatzResearch.WordTrace]
  refine ⟨69490121638111943749413509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185306991034965183331769357 69490121638111943749413509)
  ·
    refine ⟨13029397807145989453015033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69490121638111943749413509 13029397807145989453015033)
    ·
      refine ⟨9772048355359492089761275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13029397807145989453015033 9772048355359492089761275)
      ·
        refine ⟨14658072533039238134641913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9772048355359492089761275 14658072533039238134641913)
        ·
          refine ⟨10993554399779428600981435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14658072533039238134641913 10993554399779428600981435)
          ·
            refine ⟨16490331599669142901472153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10993554399779428600981435 16490331599669142901472153)
            ·
              refine ⟨12367748699751857176104115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16490331599669142901472153 12367748699751857176104115)
              ·
                refine ⟨18551623049627785764156173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12367748699751857176104115 18551623049627785764156173)
                ·
                  refine ⟨6956858643610419661558565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18551623049627785764156173 6956858643610419661558565)
                  ·
                    refine ⟨1304410995676953686542231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6956858643610419661558565 1304410995676953686542231)
                    ·
                      rfl

theorem cell23_7620994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_7620994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7620994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7620994 prefixEnd_7620994 := by exact prefixLift 7620994
  have htrace : WordTrace (prefixWord ++ tailWord_7620994) baseStart_7620994 baseEnd_7620994 := by
    simpa [prefixWord, tailWord_7620994, baseEnd_7620994] using wordTrace_append hprefix tailTrace_7620994
  have hstable : (prefixWord ++ tailWord_7620994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7620994).length < 2 ^ (prefixWord ++ tailWord_7620994).sum := by decide
  have hdescent : baseEnd_7620994 < baseStart_7620994 := by decide
  rcases family_descends (prefixWord ++ tailWord_7620994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7621043 : List Nat := [1, 1, 1, 2, 3, 1, 1, 1, 7, 2, 3]
def baseStart_7621043 : Nat := 118140960795 + 7621043 * 2 ^ 59
def prefixEnd_7621043 : Nat := 4983230072969 + 3 ^ 40 * 7621043 * 2
def baseEnd_7621043 : Nat := 3913258147582931367913967

theorem tailTrace_7621043 : CollatzResearch.WordTrace tailWord_7621043 prefixEnd_7621043 3913258147582931367913967 := by
  unfold tailWord_7621043
  simp only [CollatzResearch.WordTrace]
  refine ⟨277962273729270256366187783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185308182486180170910791855 277962273729270256366187783)
  ·
    refine ⟨416943410593905384549281675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277962273729270256366187783 416943410593905384549281675)
    ·
      refine ⟨625415115890858076823922513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 416943410593905384549281675 625415115890858076823922513)
      ·
        refine ⟨469061336918143557617941885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 625415115890858076823922513 469061336918143557617941885)
        ·
          refine ⟨175898001344303834106728207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 469061336918143557617941885 175898001344303834106728207)
          ·
            refine ⟨263847002016455751160092311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175898001344303834106728207 263847002016455751160092311)
            ·
              refine ⟨395770503024683626740138467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 263847002016455751160092311 395770503024683626740138467)
              ·
                refine ⟨593655754537025440110207701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 395770503024683626740138467 593655754537025440110207701)
                ·
                  refine ⟨13913806746961533752582993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 593655754537025440110207701 13913806746961533752582993)
                  ·
                    refine ⟨10435355060221150314437245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13913806746961533752582993 10435355060221150314437245)
                    ·
                      refine ⟨3913258147582931367913967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10435355060221150314437245 3913258147582931367913967)
                      ·
                        rfl

theorem cell23_7621043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 7, 2, 3].length) (baseStart_7621043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7621043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7621043 prefixEnd_7621043 := by exact prefixLift 7621043
  have htrace : WordTrace (prefixWord ++ tailWord_7621043) baseStart_7621043 baseEnd_7621043 := by
    simpa [prefixWord, tailWord_7621043, baseEnd_7621043] using wordTrace_append hprefix tailTrace_7621043
  have hstable : (prefixWord ++ tailWord_7621043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7621043).length < 2 ^ (prefixWord ++ tailWord_7621043).sum := by decide
  have hdescent : baseEnd_7621043 < baseStart_7621043 := by decide
  rcases family_descends (prefixWord ++ tailWord_7621043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7621053 : List Nat := [1, 4, 1, 2, 2, 2, 1, 2, 1, 1, 6]
def baseStart_7621053 : Nat := 118140960795 + 7621053 * 2 ^ 59
def prefixEnd_7621053 : Nat := 4983230072969 + 3 ^ 40 * 7621053 * 2
def baseEnd_7621053 : Nat := 3913263282389476328788921

theorem tailTrace_7621053 : CollatzResearch.WordTrace tailWord_7621053 prefixEnd_7621053 3913263282389476328788921 := by
  unfold tailWord_7621053
  simp only [CollatzResearch.WordTrace]
  refine ⟨277962638459234028074051813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185308425639489352049367875 277962638459234028074051813)
  ·
    refine ⟨52117994711106380263884715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 277962638459234028074051813 52117994711106380263884715)
    ·
      refine ⟨78176992066659570395827073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52117994711106380263884715 78176992066659570395827073)
      ·
        refine ⟨58632744049994677796870305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78176992066659570395827073 58632744049994677796870305)
        ·
          refine ⟨43974558037496008347652729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58632744049994677796870305 43974558037496008347652729)
          ·
            refine ⟨32980918528122006260739547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43974558037496008347652729 32980918528122006260739547)
            ·
              refine ⟨49471377792183009391109321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32980918528122006260739547 49471377792183009391109321)
              ·
                refine ⟨37103533344137257043331991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49471377792183009391109321 37103533344137257043331991)
                ·
                  refine ⟨55655300016205885564997987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37103533344137257043331991 55655300016205885564997987)
                  ·
                    refine ⟨83482950024308828347496981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55655300016205885564997987 83482950024308828347496981)
                    ·
                      refine ⟨3913263282389476328788921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83482950024308828347496981 3913263282389476328788921)
                      ·
                        rfl

theorem cell23_7621053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 2, 1, 1, 6].length) (baseStart_7621053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7621053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7621053 prefixEnd_7621053 := by exact prefixLift 7621053
  have htrace : WordTrace (prefixWord ++ tailWord_7621053) baseStart_7621053 baseEnd_7621053 := by
    simpa [prefixWord, tailWord_7621053, baseEnd_7621053] using wordTrace_append hprefix tailTrace_7621053
  have hstable : (prefixWord ++ tailWord_7621053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7621053).length < 2 ^ (prefixWord ++ tailWord_7621053).sum := by decide
  have hdescent : baseEnd_7621053 < baseStart_7621053 := by decide
  rcases family_descends (prefixWord ++ tailWord_7621053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7621063 : List Nat := [1, 1, 4, 1, 1, 5, 2, 8]
def baseStart_7621063 : Nat := 118140960795 + 7621063 * 2 ^ 59
def prefixEnd_7621063 : Nat := 4983230072969 + 3 ^ 40 * 7621063 * 2
def baseEnd_7621063 : Nat := 144935867303556344061625

theorem tailTrace_7621063 : CollatzResearch.WordTrace tailWord_7621063 prefixEnd_7621063 144935867303556344061625 := by
  unfold tailWord_7621063
  simp only [CollatzResearch.WordTrace]
  refine ⟨277963003189197799781915843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185308668792798533187943895 277963003189197799781915843)
  ·
    refine ⟨416944504783796699672873765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277963003189197799781915843 416944504783796699672873765)
    ·
      refine ⟨78177094646961881188663831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 416944504783796699672873765 78177094646961881188663831)
      ·
        refine ⟨117265641970442821782995747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78177094646961881188663831 117265641970442821782995747)
        ·
          refine ⟨175898462955664232674493621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117265641970442821782995747 175898462955664232674493621)
          ·
            refine ⟨16490480902093521813233777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 175898462955664232674493621 16490480902093521813233777)
            ·
              refine ⟨12367860676570141359925333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16490480902093521813233777 12367860676570141359925333)
              ·
                refine ⟨144935867303556344061625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12367860676570141359925333 144935867303556344061625)
                ·
                  rfl

theorem cell23_7621063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 2, 8].length) (baseStart_7621063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7621063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7621063 prefixEnd_7621063 := by exact prefixLift 7621063
  have htrace : WordTrace (prefixWord ++ tailWord_7621063) baseStart_7621063 baseEnd_7621063 := by
    simpa [prefixWord, tailWord_7621063, baseEnd_7621063] using wordTrace_append hprefix tailTrace_7621063
  have hstable : (prefixWord ++ tailWord_7621063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7621063).length < 2 ^ (prefixWord ++ tailWord_7621063).sum := by decide
  have hdescent : baseEnd_7621063 < baseStart_7621063 := by decide
  rcases family_descends (prefixWord ++ tailWord_7621063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7621073 : List Nat := [1, 2, 2, 1, 2, 1, 1, 2, 5, 3, 3]
def baseStart_7621073 : Nat := 118140960795 + 7621073 * 2 ^ 59
def prefixEnd_7621073 : Nat := 4983230072969 + 3 ^ 40 * 7621073 * 2
def baseEnd_7621073 : Nat := 3913273552002566250538829

theorem tailTrace_7621073 : CollatzResearch.WordTrace tailWord_7621073 prefixEnd_7621073 3913273552002566250538829 := by
  unfold tailWord_7621073
  simp only [CollatzResearch.WordTrace]
  refine ⟨277963367919161571489779873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185308911946107714326519915 277963367919161571489779873)
  ·
    refine ⟨208472525939371178617334905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277963367919161571489779873 208472525939371178617334905)
    ·
      refine ⟨156354394454528383963001179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208472525939371178617334905 156354394454528383963001179)
      ·
        refine ⟨234531591681792575944501769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156354394454528383963001179 234531591681792575944501769)
        ·
          refine ⟨175898693761344431958376327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234531591681792575944501769 175898693761344431958376327)
          ·
            refine ⟨263848040642016647937564491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175898693761344431958376327 263848040642016647937564491)
            ·
              refine ⟨395772060963024971906346737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 263848040642016647937564491 395772060963024971906346737)
              ·
                refine ⟨296829045722268728929760053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 395772060963024971906346737 296829045722268728929760053)
                ·
                  refine ⟨27827723036462693337165005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 296829045722268728929760053 27827723036462693337165005)
                  ·
                    refine ⟨10435396138673510001436877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27827723036462693337165005 10435396138673510001436877)
                    ·
                      refine ⟨3913273552002566250538829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10435396138673510001436877 3913273552002566250538829)
                      ·
                        rfl

theorem cell23_7621073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 5, 3, 3].length) (baseStart_7621073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7621073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7621073 prefixEnd_7621073 := by exact prefixLift 7621073
  have htrace : WordTrace (prefixWord ++ tailWord_7621073) baseStart_7621073 baseEnd_7621073 := by
    simpa [prefixWord, tailWord_7621073, baseEnd_7621073] using wordTrace_append hprefix tailTrace_7621073
  have hstable : (prefixWord ++ tailWord_7621073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7621073).length < 2 ^ (prefixWord ++ tailWord_7621073).sum := by decide
  have hdescent : baseEnd_7621073 < baseStart_7621073 := by decide
  rcases family_descends (prefixWord ++ tailWord_7621073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7621077 : List Nat := [1, 3, 2, 3, 1, 2, 3, 2, 1, 2, 3]
def baseStart_7621077 : Nat := 118140960795 + 7621077 * 2 ^ 59
def prefixEnd_7621077 : Nat := 4983230072969 + 3 ^ 40 * 7621077 * 2
def baseEnd_7621077 : Nat := 3913275605925184234888811

theorem tailTrace_7621077 : CollatzResearch.WordTrace tailWord_7621077 prefixEnd_7621077 3913275605925184234888811 := by
  unfold tailWord_7621077
  simp only [CollatzResearch.WordTrace]
  refine ⟨277963513811147080172925485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185309009207431386781950323 277963513811147080172925485)
  ·
    refine ⟨104236317679180155064847057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 277963513811147080172925485 104236317679180155064847057)
    ·
      refine ⟨78177238259385116298635293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104236317679180155064847057 78177238259385116298635293)
      ·
        refine ⟨29316464347269418611988235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78177238259385116298635293 29316464347269418611988235)
        ·
          refine ⟨43974696520904127917982353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29316464347269418611988235 43974696520904127917982353)
          ·
            refine ⟨32981022390678095938486765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43974696520904127917982353 32981022390678095938486765)
            ·
              refine ⟨12367883396504285976932537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32981022390678095938486765 12367883396504285976932537)
              ·
                refine ⟨9275912547378214482699403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12367883396504285976932537 9275912547378214482699403)
                ·
                  refine ⟨13913868821067321724049105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9275912547378214482699403 13913868821067321724049105)
                  ·
                    refine ⟨10435401615800491293036829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13913868821067321724049105 10435401615800491293036829)
                    ·
                      refine ⟨3913275605925184234888811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10435401615800491293036829 3913275605925184234888811)
                      ·
                        rfl

theorem cell23_7621077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 3, 2, 1, 2, 3].length) (baseStart_7621077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7621077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7621077 prefixEnd_7621077 := by exact prefixLift 7621077
  have htrace : WordTrace (prefixWord ++ tailWord_7621077) baseStart_7621077 baseEnd_7621077 := by
    simpa [prefixWord, tailWord_7621077, baseEnd_7621077] using wordTrace_append hprefix tailTrace_7621077
  have hstable : (prefixWord ++ tailWord_7621077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7621077).length < 2 ^ (prefixWord ++ tailWord_7621077).sum := by decide
  have hdescent : baseEnd_7621077 < baseStart_7621077 := by decide
  rcases family_descends (prefixWord ++ tailWord_7621077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7621107 : List Nat := [1, 1, 1, 2, 2, 2, 6, 2, 2, 1, 3]
def baseStart_7621107 : Nat := 118140960795 + 7621107 * 2 ^ 59
def prefixEnd_7621107 : Nat := 4983230072969 + 3 ^ 40 * 7621107 * 2
def baseEnd_7621107 : Nat := 3913291010344819117513673

theorem tailTrace_7621107 : CollatzResearch.WordTrace tailWord_7621107 prefixEnd_7621107 3913291010344819117513673 := by
  unfold tailWord_7621107
  simp only [CollatzResearch.WordTrace]
  refine ⟨277964608001038395296517575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185309738667358930197678383 277964608001038395296517575)
  ·
    refine ⟨416946912001557592944776363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277964608001038395296517575 416946912001557592944776363)
    ·
      refine ⟨625420368002336389417164545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 416946912001557592944776363 625420368002336389417164545)
      ·
        refine ⟨469065276001752292062873409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 625420368002336389417164545 469065276001752292062873409)
        ·
          refine ⟨351798957001314219047155057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 469065276001752292062873409 351798957001314219047155057)
          ·
            refine ⟨263849217750985664285366293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 351798957001314219047155057 263849217750985664285366293)
            ·
              refine ⟨12367932082077453013376545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 263849217750985664285366293 12367932082077453013376545)
              ·
                refine ⟨9275949061558089760032409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12367932082077453013376545 9275949061558089760032409)
                ·
                  refine ⟨6956961796168567320024307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9275949061558089760032409 6956961796168567320024307)
                  ·
                    refine ⟨10435442694252850980036461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6956961796168567320024307 10435442694252850980036461)
                    ·
                      refine ⟨3913291010344819117513673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10435442694252850980036461 3913291010344819117513673)
                      ·
                        rfl

theorem cell23_7621107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 6, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 6, 2, 2, 1, 3].length) (baseStart_7621107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7621107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7621107 prefixEnd_7621107 := by exact prefixLift 7621107
  have htrace : WordTrace (prefixWord ++ tailWord_7621107) baseStart_7621107 baseEnd_7621107 := by
    simpa [prefixWord, tailWord_7621107, baseEnd_7621107] using wordTrace_append hprefix tailTrace_7621107
  have hstable : (prefixWord ++ tailWord_7621107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7621107).length < 2 ^ (prefixWord ++ tailWord_7621107).sum := by decide
  have hdescent : baseEnd_7621107 < baseStart_7621107 := by decide
  rcases family_descends (prefixWord ++ tailWord_7621107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7621113 : List Nat := [1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 4]
def baseStart_7621113 : Nat := 118140960795 + 7621113 * 2 ^ 59
def prefixEnd_7621113 : Nat := 4983230072969 + 3 ^ 40 * 7621113 * 2
def baseEnd_7621113 : Nat := 3913294091228746094038645

theorem tailTrace_7621113 : CollatzResearch.WordTrace tailWord_7621113 prefixEnd_7621113 3913294091228746094038645 := by
  unfold tailWord_7621113
  simp only [CollatzResearch.WordTrace]
  refine ⟨277964826839016658321235993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185309884559344438880823995 277964826839016658321235993)
  ·
    refine ⟨208473620129262493740926995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277964826839016658321235993 208473620129262493740926995)
    ·
      refine ⟨312710430193893740611390493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208473620129262493740926995 312710430193893740611390493)
      ·
        refine ⟨117266411322710152729271435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 312710430193893740611390493 117266411322710152729271435)
        ·
          refine ⟨175899616984065229093907153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117266411322710152729271435 175899616984065229093907153)
          ·
            refine ⟨131924712738048921820430365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175899616984065229093907153 131924712738048921820430365)
            ·
              refine ⟨49471767276768345682661387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131924712738048921820430365 49471767276768345682661387)
              ·
                refine ⟨74207650915152518523992081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49471767276768345682661387 74207650915152518523992081)
                ·
                  refine ⟨55655738186364388892994061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74207650915152518523992081 55655738186364388892994061)
                  ·
                    refine ⟨20870901819886645834872773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55655738186364388892994061 20870901819886645834872773)
                    ·
                      refine ⟨3913294091228746094038645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20870901819886645834872773 3913294091228746094038645)
                      ·
                        rfl

theorem cell23_7621113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 4].length) (baseStart_7621113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7621113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7621113 prefixEnd_7621113 := by exact prefixLift 7621113
  have htrace : WordTrace (prefixWord ++ tailWord_7621113) baseStart_7621113 baseEnd_7621113 := by
    simpa [prefixWord, tailWord_7621113, baseEnd_7621113] using wordTrace_append hprefix tailTrace_7621113
  have hstable : (prefixWord ++ tailWord_7621113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7621113).length < 2 ^ (prefixWord ++ tailWord_7621113).sum := by decide
  have hdescent : baseEnd_7621113 < baseStart_7621113 := by decide
  rcases family_descends (prefixWord ++ tailWord_7621113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7621123 : List Nat := [1, 1, 1, 3, 2, 1, 5, 1, 2, 6]
def baseStart_7621123 : Nat := 118140960795 + 7621123 * 2 ^ 59
def prefixEnd_7621123 : Nat := 4983230072969 + 3 ^ 40 * 7621123 * 2
def baseEnd_7621123 : Nat := 1304433075345097018304533

theorem tailTrace_7621123 : CollatzResearch.WordTrace tailWord_7621123 prefixEnd_7621123 1304433075345097018304533 := by
  unfold tailWord_7621123
  simp only [CollatzResearch.WordTrace]
  refine ⟨277965191568980430029100023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185310127712653620019400015 277965191568980430029100023)
  ·
    refine ⟨416947787353470645043650035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277965191568980430029100023 416947787353470645043650035)
    ·
      refine ⟨625421681030205967565475053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 416947787353470645043650035 625421681030205967565475053)
      ·
        refine ⟨234533130386327237837053145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 625421681030205967565475053 234533130386327237837053145)
        ·
          refine ⟨175899847789745428377789859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234533130386327237837053145 175899847789745428377789859)
          ·
            refine ⟨263849771684618142566684789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175899847789745428377789859 263849771684618142566684789)
            ·
              refine ⟨24735916095432950865626699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 263849771684618142566684789 24735916095432950865626699)
              ·
                refine ⟨37103874143149426298440049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24735916095432950865626699 37103874143149426298440049)
                ·
                  refine ⟨27827905607362069723830037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37103874143149426298440049 27827905607362069723830037)
                  ·
                    refine ⟨1304433075345097018304533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27827905607362069723830037 1304433075345097018304533)
                    ·
                      rfl

theorem cell23_7621123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 1, 2, 6].length) (baseStart_7621123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7621123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7621123 prefixEnd_7621123 := by exact prefixLift 7621123
  have htrace : WordTrace (prefixWord ++ tailWord_7621123) baseStart_7621123 baseEnd_7621123 := by
    simpa [prefixWord, tailWord_7621123, baseEnd_7621123] using wordTrace_append hprefix tailTrace_7621123
  have hstable : (prefixWord ++ tailWord_7621123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7621123).length < 2 ^ (prefixWord ++ tailWord_7621123).sum := by decide
  have hdescent : baseEnd_7621123 < baseStart_7621123 := by decide
  rcases family_descends (prefixWord ++ tailWord_7621123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7621124 : List Nat := [2, 3, 2, 3, 1, 1, 2, 3, 2, 1, 3]
def baseStart_7621124 : Nat := 118140960795 + 7621124 * 2 ^ 59
def prefixEnd_7621124 : Nat := 4983230072969 + 3 ^ 40 * 7621124 * 2
def baseEnd_7621124 : Nat := 3913299739515945551001095

theorem tailTrace_7621124 : CollatzResearch.WordTrace tailWord_7621124 prefixEnd_7621124 3913299739515945551001095 := by
  unfold tailWord_7621124
  simp only [CollatzResearch.WordTrace]
  refine ⟨138982614020988403599943213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185310152027984538133257617 138982614020988403599943213)
  ·
    refine ⟨52118480257870651349978705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138982614020988403599943213 52118480257870651349978705)
    ·
      refine ⟨39088860193402988512484029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52118480257870651349978705 39088860193402988512484029)
      ·
        refine ⟨14658322572526120692181511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39088860193402988512484029 14658322572526120692181511)
        ·
          refine ⟨21987483858789181038272267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14658322572526120692181511 21987483858789181038272267)
          ·
            refine ⟨32981225788183771557408401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21987483858789181038272267 32981225788183771557408401)
            ·
              refine ⟨24735919341137828668056301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32981225788183771557408401 24735919341137828668056301)
              ·
                refine ⟨9275969752926685750521113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24735919341137828668056301 9275969752926685750521113)
                ·
                  refine ⟨6956977314695014312890835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9275969752926685750521113 6956977314695014312890835)
                  ·
                    refine ⟨10435465972042521469336253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6956977314695014312890835 10435465972042521469336253)
                    ·
                      refine ⟨3913299739515945551001095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10435465972042521469336253 3913299739515945551001095)
                      ·
                        rfl

theorem cell23_7621124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_7621124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7621124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7621124 prefixEnd_7621124 := by exact prefixLift 7621124
  have htrace : WordTrace (prefixWord ++ tailWord_7621124) baseStart_7621124 baseEnd_7621124 := by
    simpa [prefixWord, tailWord_7621124, baseEnd_7621124] using wordTrace_append hprefix tailTrace_7621124
  have hstable : (prefixWord ++ tailWord_7621124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7621124).length < 2 ^ (prefixWord ++ tailWord_7621124).sum := by decide
  have hdescent : baseEnd_7621124 < baseStart_7621124 := by decide
  rcases family_descends (prefixWord ++ tailWord_7621124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7621153 : List Nat := [1, 2, 3, 2, 2, 1, 1, 2, 9]
def baseStart_7621153 : Nat := 118140960795 + 7621153 * 2 ^ 59
def prefixEnd_7621153 : Nat := 4983230072969 + 3 ^ 40 * 7621153 * 2
def baseEnd_7621153 : Nat := 434812736717213993059829

theorem tailTrace_7621153 : CollatzResearch.WordTrace tailWord_7621153 prefixEnd_7621153 434812736717213993059829 := by
  unfold tailWord_7621153
  simp only [CollatzResearch.WordTrace]
  refine ⟨277966285758871745152692113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185310857172581163435128075 277966285758871745152692113)
  ·
    refine ⟨208474714319153808864519085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277966285758871745152692113 208474714319153808864519085)
    ·
      refine ⟨78178017869682678324194657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208474714319153808864519085 78178017869682678324194657)
      ·
        refine ⟨58633513402262008743145993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78178017869682678324194657 58633513402262008743145993)
        ·
          refine ⟨43975135051696506557359495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58633513402262008743145993 43975135051696506557359495)
          ·
            refine ⟨65962702577544759836039243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43975135051696506557359495 65962702577544759836039243)
            ·
              refine ⟨98944053866317139754058865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65962702577544759836039243 98944053866317139754058865)
              ·
                refine ⟨74208040399737854815544149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98944053866317139754058865 74208040399737854815544149)
                ·
                  refine ⟨434812736717213993059829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 74208040399737854815544149 434812736717213993059829)
                  ·
                    rfl

theorem cell23_7621153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 2, 9].length) (baseStart_7621153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7621153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7621153 prefixEnd_7621153 := by exact prefixLift 7621153
  have htrace : WordTrace (prefixWord ++ tailWord_7621153) baseStart_7621153 baseEnd_7621153 := by
    simpa [prefixWord, tailWord_7621153, baseEnd_7621153] using wordTrace_append hprefix tailTrace_7621153
  have hstable : (prefixWord ++ tailWord_7621153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7621153).length < 2 ^ (prefixWord ++ tailWord_7621153).sum := by decide
  have hdescent : baseEnd_7621153 < baseStart_7621153 := by decide
  rcases family_descends (prefixWord ++ tailWord_7621153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7621183 : List Nat := [1, 1, 2, 2, 3, 2, 1, 1, 3, 7]
def baseStart_7621183 : Nat := 118140960795 + 7621183 * 2 ^ 59
def prefixEnd_7621183 : Nat := 4983230072969 + 3 ^ 40 * 7621183 * 2
def baseEnd_7621183 : Nat := 1304443344958186940054441

theorem tailTrace_7621183 : CollatzResearch.WordTrace tailWord_7621183 prefixEnd_7621183 1304443344958186940054441 := by
  unfold tailWord_7621183
  simp only [CollatzResearch.WordTrace]
  refine ⟨277967379948763060276284203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185311586632508706850856135 277967379948763060276284203)
  ·
    refine ⟨416951069923144590414426305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277967379948763060276284203 416951069923144590414426305)
    ·
      refine ⟨312713302442358442810819729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 416951069923144590414426305 312713302442358442810819729)
      ·
        refine ⟨234534976831768832108114797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 312713302442358442810819729 234534976831768832108114797)
        ·
          refine ⟨87950616311913312040543049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 234534976831768832108114797 87950616311913312040543049)
          ·
            refine ⟨65962962233934984030407287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87950616311913312040543049 65962962233934984030407287)
            ·
              refine ⟨98944443350902476045610931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65962962233934984030407287 98944443350902476045610931)
              ·
                refine ⟨148416665026353714068416397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98944443350902476045610931 148416665026353714068416397)
                ·
                  refine ⟨55656249384882642775656149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 148416665026353714068416397 55656249384882642775656149)
                  ·
                    refine ⟨1304443344958186940054441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55656249384882642775656149 1304443344958186940054441)
                    ·
                      rfl

theorem cell23_7621183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 3, 7].length) (baseStart_7621183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7621183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7621183 prefixEnd_7621183 := by exact prefixLift 7621183
  have htrace : WordTrace (prefixWord ++ tailWord_7621183) baseStart_7621183 baseEnd_7621183 := by
    simpa [prefixWord, tailWord_7621183, baseEnd_7621183] using wordTrace_append hprefix tailTrace_7621183
  have hstable : (prefixWord ++ tailWord_7621183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7621183).length < 2 ^ (prefixWord ++ tailWord_7621183).sum := by decide
  have hdescent : baseEnd_7621183 < baseStart_7621183 := by decide
  rcases family_descends (prefixWord ++ tailWord_7621183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7621193 : List Nat := [1, 2, 1, 1, 2, 2, 1, 1, 5, 2, 5]
def baseStart_7621193 : Nat := 118140960795 + 7621193 * 2 ^ 59
def prefixEnd_7621193 : Nat := 4983230072969 + 3 ^ 40 * 7621193 * 2
def baseEnd_7621193 : Nat := 3913335169681105781038277

theorem tailTrace_7621193 : CollatzResearch.WordTrace tailWord_7621193 prefixEnd_7621193 3913335169681105781038277 := by
  unfold tailWord_7621193
  simp only [CollatzResearch.WordTrace]
  refine ⟨277967744678726831984148233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185311829785817887989432155 277967744678726831984148233)
  ·
    refine ⟨208475808509045123988111175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277967744678726831984148233 208475808509045123988111175)
    ·
      refine ⟨312713712763567685982166763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208475808509045123988111175 312713712763567685982166763)
      ·
        refine ⟨469070569145351528973250145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312713712763567685982166763 469070569145351528973250145)
        ·
          refine ⟨351802926859013646729937609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 469070569145351528973250145 351802926859013646729937609)
          ·
            refine ⟨263852195144260235047453207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 351802926859013646729937609 263852195144260235047453207)
            ·
              refine ⟨395778292716390352571179811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 263852195144260235047453207 395778292716390352571179811)
              ·
                refine ⟨593667439074585528856769717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 395778292716390352571179811 593667439074585528856769717)
                ·
                  refine ⟨55656322413242393330322161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 593667439074585528856769717 55656322413242393330322161)
                  ·
                    refine ⟨41742241809931794997741621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55656322413242393330322161 41742241809931794997741621)
                    ·
                      refine ⟨3913335169681105781038277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41742241809931794997741621 3913335169681105781038277)
                      ·
                        rfl

theorem cell23_7621193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 5, 2, 5].length) (baseStart_7621193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7621193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7621193 prefixEnd_7621193 := by exact prefixLift 7621193
  have htrace : WordTrace (prefixWord ++ tailWord_7621193) baseStart_7621193 baseEnd_7621193 := by
    simpa [prefixWord, tailWord_7621193, baseEnd_7621193] using wordTrace_append hprefix tailTrace_7621193
  have hstable : (prefixWord ++ tailWord_7621193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7621193).length < 2 ^ (prefixWord ++ tailWord_7621193).sum := by decide
  have hdescent : baseEnd_7621193 < baseStart_7621193 := by decide
  rcases family_descends (prefixWord ++ tailWord_7621193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7621204 : List Nat := [2, 4, 1, 1, 1, 5, 1, 3, 5]
def baseStart_7621204 : Nat := 118140960795 + 7621204 * 2 ^ 59
def prefixEnd_7621204 : Nat := 4983230072969 + 3 ^ 40 * 7621204 * 2
def baseEnd_7621204 : Nat := 434815646440922804222303

theorem tailTrace_7621204 : CollatzResearch.WordTrace tailWord_7621204 prefixEnd_7621204 434815646440922804222303 := by
  unfold tailWord_7621204
  simp only [CollatzResearch.WordTrace]
  refine ⟨138984072940843490431399333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185312097254457987241865777 138984072940843490431399333)
  ·
    refine ⟨26059513676408154455887375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138984072940843490431399333 26059513676408154455887375)
    ·
      refine ⟨39089270514612231683831063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26059513676408154455887375 39089270514612231683831063)
      ·
        refine ⟨58633905771918347525746595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39089270514612231683831063 58633905771918347525746595)
        ·
          refine ⟨87950858657877521288619893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58633905771918347525746595 87950858657877521288619893)
          ·
            refine ⟨8245392999176017620808115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 87950858657877521288619893 8245392999176017620808115)
            ·
              refine ⟨12368089498764026431212173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8245392999176017620808115 12368089498764026431212173)
              ·
                refine ⟨4638033562036509911704565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12368089498764026431212173 4638033562036509911704565)
                ·
                  refine ⟨434815646440922804222303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4638033562036509911704565 434815646440922804222303)
                  ·
                    rfl

theorem cell23_7621204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 1, 3, 5].length) (baseStart_7621204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7621204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7621204 prefixEnd_7621204 := by exact prefixLift 7621204
  have htrace : WordTrace (prefixWord ++ tailWord_7621204) baseStart_7621204 baseEnd_7621204 := by
    simpa [prefixWord, tailWord_7621204, baseEnd_7621204] using wordTrace_append hprefix tailTrace_7621204
  have hstable : (prefixWord ++ tailWord_7621204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7621204).length < 2 ^ (prefixWord ++ tailWord_7621204).sum := by decide
  have hdescent : baseEnd_7621204 < baseStart_7621204 := by decide
  rcases family_descends (prefixWord ++ tailWord_7621204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7621243 : List Nat := [1, 1, 1, 1, 1, 4, 2, 2, 10]
def baseStart_7621243 : Nat := 118140960795 + 7621243 * 2 ^ 59
def prefixEnd_7621243 : Nat := 4983230072969 + 3 ^ 40 * 7621243 * 2
def baseEnd_7621243 : Nat := 434817871523758953934783

theorem tailTrace_7621243 : CollatzResearch.WordTrace tailWord_7621243 prefixEnd_7621243 434817871523758953934783 := by
  unfold tailWord_7621243
  simp only [CollatzResearch.WordTrace]
  refine ⟨277969568328545690523468383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185313045552363793682312255 277969568328545690523468383)
  ·
    refine ⟨416954352492818535785202575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277969568328545690523468383 416954352492818535785202575)
    ·
      refine ⟨625431528739227803677803863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 416954352492818535785202575 625431528739227803677803863)
      ·
        refine ⟨938147293108841705516705795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 625431528739227803677803863 938147293108841705516705795)
        ·
          refine ⟨1407220939663262558275058693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 938147293108841705516705795 1407220939663262558275058693)
          ·
            refine ⟨263853926186861729676573505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1407220939663262558275058693 263853926186861729676573505)
            ·
              refine ⟨197890444640146297257430129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 263853926186861729676573505 197890444640146297257430129)
              ·
                refine ⟨148417833480109722943072597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 197890444640146297257430129 148417833480109722943072597)
                ·
                  refine ⟨434817871523758953934783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 148417833480109722943072597 434817871523758953934783)
                  ·
                    rfl

theorem cell23_7621243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 10].length) (baseStart_7621243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7621243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7621243 prefixEnd_7621243 := by exact prefixLift 7621243
  have htrace : WordTrace (prefixWord ++ tailWord_7621243) baseStart_7621243 baseEnd_7621243 := by
    simpa [prefixWord, tailWord_7621243, baseEnd_7621243] using wordTrace_append hprefix tailTrace_7621243
  have hstable : (prefixWord ++ tailWord_7621243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7621243).length < 2 ^ (prefixWord ++ tailWord_7621243).sum := by decide
  have hdescent : baseEnd_7621243 < baseStart_7621243 := by decide
  rcases family_descends (prefixWord ++ tailWord_7621243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7621281 : List Nat := [1, 2, 3, 3, 3, 1, 1, 4, 1, 4]
def baseStart_7621281 : Nat := 118140960795 + 7621281 * 2 ^ 59
def prefixEnd_7621281 : Nat := 4983230072969 + 3 ^ 40 * 7621281 * 2
def baseEnd_7621281 : Nat := 1304460118659567145579291

theorem tailTrace_7621281 : CollatzResearch.WordTrace tailWord_7621281 prefixEnd_7621281 1304460118659567145579291 := by
  unfold tailWord_7621281
  simp only [CollatzResearch.WordTrace]
  refine ⟨277970954302408023013351697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185313969534938682008901131 277970954302408023013351697)
  ·
    refine ⟨208478215726806017260013773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277970954302408023013351697 208478215726806017260013773)
    ·
      refine ⟨78179330897552256472505165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208478215726806017260013773 78179330897552256472505165)
      ·
        refine ⟨29317249086582096177189437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78179330897552256472505165 29317249086582096177189437)
        ·
          refine ⟨10993968407468286066446039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29317249086582096177189437 10993968407468286066446039)
          ·
            refine ⟨16490952611202429099669059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10993968407468286066446039 16490952611202429099669059)
            ·
              refine ⟨24736428916803643649503589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16490952611202429099669059 24736428916803643649503589)
              ·
                refine ⟨4638080421900683184281923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24736428916803643649503589 4638080421900683184281923)
                ·
                  refine ⟨6957120632851024776422885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4638080421900683184281923 6957120632851024776422885)
                  ·
                    refine ⟨1304460118659567145579291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6957120632851024776422885 1304460118659567145579291)
                    ·
                      rfl

theorem cell23_7621281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 4, 1, 4].length) (baseStart_7621281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7621281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7621281 prefixEnd_7621281 := by exact prefixLift 7621281
  have htrace : WordTrace (prefixWord ++ tailWord_7621281) baseStart_7621281 baseEnd_7621281 := by
    simpa [prefixWord, tailWord_7621281, baseEnd_7621281] using wordTrace_append hprefix tailTrace_7621281
  have hstable : (prefixWord ++ tailWord_7621281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7621281).length < 2 ^ (prefixWord ++ tailWord_7621281).sum := by decide
  have hdescent : baseEnd_7621281 < baseStart_7621281 := by decide
  rcases family_descends (prefixWord ++ tailWord_7621281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7621294 : List Nat := [4, 1, 4, 1, 1, 1, 2, 3, 6]
def baseStart_7621294 : Nat := 118140960795 + 7621294 * 2 ^ 59
def prefixEnd_7621294 : Nat := 4983230072969 + 3 ^ 40 * 7621294 * 2
def baseEnd_7621294 : Nat := 434820781247467765097257

theorem tailTrace_7621294 : CollatzResearch.WordTrace tailWord_7621294 prefixEnd_7621294 434820781247467765097257 := by
  unfold tailWord_7621294
  simp only [CollatzResearch.WordTrace]
  refine ⟨34746428556420115779196867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185314285634240617489049957 34746428556420115779196867)
  ·
    refine ⟨52119642834630173668795301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34746428556420115779196867 52119642834630173668795301)
    ·
      refine ⟨9772433031493157562899119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52119642834630173668795301 9772433031493157562899119)
      ·
        refine ⟨14658649547239736344348679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9772433031493157562899119 14658649547239736344348679)
        ·
          refine ⟨21987974320859604516523019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14658649547239736344348679 21987974320859604516523019)
          ·
            refine ⟨32981961481289406774784529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21987974320859604516523019 32981961481289406774784529)
            ·
              refine ⟨24736471110967055081088397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32981961481289406774784529 24736471110967055081088397)
              ·
                refine ⟨9276176666612645655408149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24736471110967055081088397 9276176666612645655408149)
                ·
                  refine ⟨434820781247467765097257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9276176666612645655408149 434820781247467765097257)
                  ·
                    rfl

theorem cell23_7621294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 3, 6].length) (baseStart_7621294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7621294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7621294 prefixEnd_7621294 := by exact prefixLift 7621294
  have htrace : WordTrace (prefixWord ++ tailWord_7621294) baseStart_7621294 baseEnd_7621294 := by
    simpa [prefixWord, tailWord_7621294, baseEnd_7621294] using wordTrace_append hprefix tailTrace_7621294
  have hstable : (prefixWord ++ tailWord_7621294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7621294).length < 2 ^ (prefixWord ++ tailWord_7621294).sum := by decide
  have hdescent : baseEnd_7621294 < baseStart_7621294 := by decide
  rcases family_descends (prefixWord ++ tailWord_7621294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7621324 : List Nat := [2, 2, 1, 5, 1, 2, 1, 3, 1, 5]
def baseStart_7621324 : Nat := 118140960795 + 7621324 * 2 ^ 59
def prefixEnd_7621324 : Nat := 4983230072969 + 3 ^ 40 * 7621324 * 2
def baseEnd_7621324 : Nat := 1304467478548948256166725

theorem tailTrace_7621324 : CollatzResearch.WordTrace tailWord_7621324 prefixEnd_7621324 1304467478548948256166725 := by
  unfold tailWord_7621324
  simp only [CollatzResearch.WordTrace]
  refine ⟨138986261320626120678583513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185315015094168160904778017 138986261320626120678583513)
  ·
    refine ⟨104239695990469590508937635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138986261320626120678583513 104239695990469590508937635)
    ·
      refine ⟨156359543985704385763406453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104239695990469590508937635 156359543985704385763406453)
      ·
        refine ⟨14658707248659786165319355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 156359543985704385763406453 14658707248659786165319355)
        ·
          refine ⟨21988060872989679247979033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14658707248659786165319355 21988060872989679247979033)
          ·
            refine ⟨16491045654742259435984275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21988060872989679247979033 16491045654742259435984275)
            ·
              refine ⟨24736568482113389153976413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16491045654742259435984275 24736568482113389153976413)
              ·
                refine ⟨9276213180792520932741155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24736568482113389153976413 9276213180792520932741155)
                ·
                  refine ⟨13914319771188781399111733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9276213180792520932741155 13914319771188781399111733)
                  ·
                    refine ⟨1304467478548948256166725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13914319771188781399111733 1304467478548948256166725)
                    ·
                      rfl

theorem cell23_7621324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 3, 1, 5].length) (baseStart_7621324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7621324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7621324 prefixEnd_7621324 := by exact prefixLift 7621324
  have htrace : WordTrace (prefixWord ++ tailWord_7621324) baseStart_7621324 baseEnd_7621324 := by
    simpa [prefixWord, tailWord_7621324, baseEnd_7621324] using wordTrace_append hprefix tailTrace_7621324
  have hstable : (prefixWord ++ tailWord_7621324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7621324).length < 2 ^ (prefixWord ++ tailWord_7621324).sum := by decide
  have hdescent : baseEnd_7621324 < baseStart_7621324 := by decide
  rcases family_descends (prefixWord ++ tailWord_7621324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7621337 : List Nat := [1, 2, 1, 2, 3, 2, 3, 1, 4, 4]
def baseStart_7621337 : Nat := 118140960795 + 7621337 * 2 ^ 59
def prefixEnd_7621337 : Nat := 4983230072969 + 3 ^ 40 * 7621337 * 2
def baseEnd_7621337 : Nat := 1304469703631784405879205

theorem tailTrace_7621337 : CollatzResearch.WordTrace tailWord_7621337 prefixEnd_7621337 1304469703631784405879205 := by
  unfold tailWord_7621337
  simp only [CollatzResearch.WordTrace]
  refine ⟨277972996790205144577390265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185315331193470096384926843 277972996790205144577390265)
  ·
    refine ⟨208479747592653858433042699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277972996790205144577390265 208479747592653858433042699)
    ·
      refine ⟨312719621388980787649564049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208479747592653858433042699 312719621388980787649564049)
      ·
        refine ⟨234539716041735590737173037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 312719621388980787649564049 234539716041735590737173037)
        ·
          refine ⟨87952393515650846526439889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 234539716041735590737173037 87952393515650846526439889)
          ·
            refine ⟨65964295136738134894829917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87952393515650846526439889 65964295136738134894829917)
            ·
              refine ⟨24736610676276800585561219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65964295136738134894829917 24736610676276800585561219)
              ·
                refine ⟨37104916014415200878341829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24736610676276800585561219 37104916014415200878341829)
                ·
                  refine ⟨6957171752702850164689093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37104916014415200878341829 6957171752702850164689093)
                  ·
                    refine ⟨1304469703631784405879205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6957171752702850164689093 1304469703631784405879205)
                    ·
                      rfl

theorem cell23_7621337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 1, 4, 4].length) (baseStart_7621337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7621337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7621337 prefixEnd_7621337 := by exact prefixLift 7621337
  have htrace : WordTrace (prefixWord ++ tailWord_7621337) baseStart_7621337 baseEnd_7621337 := by
    simpa [prefixWord, tailWord_7621337, baseEnd_7621337] using wordTrace_append hprefix tailTrace_7621337
  have hstable : (prefixWord ++ tailWord_7621337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7621337).length < 2 ^ (prefixWord ++ tailWord_7621337).sum := by decide
  have hdescent : baseEnd_7621337 < baseStart_7621337 := by decide
  rcases family_descends (prefixWord ++ tailWord_7621337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7621347 : List Nat := [1, 1, 1, 7, 1, 1, 1, 1, 3, 1, 5]
def baseStart_7621347 : Nat := 118140960795 + 7621347 * 2 ^ 59
def prefixEnd_7621347 : Nat := 4983230072969 + 3 ^ 40 * 7621347 * 2
def baseEnd_7621347 : Nat := 3913414245701898178512569

theorem tailTrace_7621347 : CollatzResearch.WordTrace tailWord_7621347 prefixEnd_7621347 3913414245701898178512569 := by
  unfold tailWord_7621347
  simp only [CollatzResearch.WordTrace]
  refine ⟨277973361520168916285254295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185315574346779277523502863 277973361520168916285254295)
  ·
    refine ⟨416960042280253374427881443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277973361520168916285254295 416960042280253374427881443)
    ·
      refine ⟨625440063420380061641822165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 416960042280253374427881443 625440063420380061641822165)
      ·
        refine ⟨14658751486415157694730207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 625440063420380061641822165 14658751486415157694730207)
        ·
          refine ⟨21988127229622736542095311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14658751486415157694730207 21988127229622736542095311)
          ·
            refine ⟨32982190844434104813142967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21988127229622736542095311 32982190844434104813142967)
            ·
              refine ⟨49473286266651157219714451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32982190844434104813142967 49473286266651157219714451)
              ·
                refine ⟨74209929399976735829571677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49473286266651157219714451 74209929399976735829571677)
                ·
                  refine ⟨27828723524991275936089379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74209929399976735829571677 27828723524991275936089379)
                  ·
                    refine ⟨41743085287486913904134069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27828723524991275936089379 41743085287486913904134069)
                    ·
                      refine ⟨3913414245701898178512569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41743085287486913904134069 3913414245701898178512569)
                      ·
                        rfl

theorem cell23_7621347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_7621347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7621347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7621347 prefixEnd_7621347 := by exact prefixLift 7621347
  have htrace : WordTrace (prefixWord ++ tailWord_7621347) baseStart_7621347 baseEnd_7621347 := by
    simpa [prefixWord, tailWord_7621347, baseEnd_7621347] using wordTrace_append hprefix tailTrace_7621347
  have hstable : (prefixWord ++ tailWord_7621347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7621347).length < 2 ^ (prefixWord ++ tailWord_7621347).sum := by decide
  have hdescent : baseEnd_7621347 < baseStart_7621347 := by decide
  rcases family_descends (prefixWord ++ tailWord_7621347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7621357 : List Nat := [1, 5, 1, 2, 1, 1, 3, 1, 1, 1, 6]
def baseStart_7621357 : Nat := 118140960795 + 7621357 * 2 ^ 59
def prefixEnd_7621357 : Nat := 4983230072969 + 3 ^ 40 * 7621357 * 2
def baseEnd_7621357 : Nat := 3913419380508443139387523

theorem tailTrace_7621357 : CollatzResearch.WordTrace tailWord_7621357 prefixEnd_7621357 3913419380508443139387523 := by
  unfold tailWord_7621357
  simp only [CollatzResearch.WordTrace]
  refine ⟨277973726250132687993118325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185315817500088458662078883 277973726250132687993118325)
  ·
    refine ⟨26060036835949939499354843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 277973726250132687993118325 26060036835949939499354843)
    ·
      refine ⟨39090055253924909249032265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26060036835949939499354843 39090055253924909249032265)
      ·
        refine ⟨29317541440443681936774199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39090055253924909249032265 29317541440443681936774199)
        ·
          refine ⟨43976312160665522905161299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29317541440443681936774199 43976312160665522905161299)
          ·
            refine ⟨65964468240998284357741949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43976312160665522905161299 65964468240998284357741949)
            ·
              refine ⟨24736675590374356634153231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65964468240998284357741949 24736675590374356634153231)
              ·
                refine ⟨37105013385561534951229847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24736675590374356634153231 37105013385561534951229847)
                ·
                  refine ⟨55657520078342302426844771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37105013385561534951229847 55657520078342302426844771)
                  ·
                    refine ⟨83486280117513453640267157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55657520078342302426844771 83486280117513453640267157)
                    ·
                      refine ⟨3913419380508443139387523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83486280117513453640267157 3913419380508443139387523)
                      ·
                        rfl

theorem cell23_7621357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_7621357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7621357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7621357 prefixEnd_7621357 := by exact prefixLift 7621357
  have htrace : WordTrace (prefixWord ++ tailWord_7621357) baseStart_7621357 baseEnd_7621357 := by
    simpa [prefixWord, tailWord_7621357, baseEnd_7621357] using wordTrace_append hprefix tailTrace_7621357
  have hstable : (prefixWord ++ tailWord_7621357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7621357).length < 2 ^ (prefixWord ++ tailWord_7621357).sum := by decide
  have hdescent : baseEnd_7621357 < baseStart_7621357 := by decide
  rcases family_descends (prefixWord ++ tailWord_7621357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7621377 : List Nat := [1, 2, 4, 1, 1, 1, 1, 3, 3, 3, 3]
def baseStart_7621377 : Nat := 118140960795 + 7621377 * 2 ^ 59
def prefixEnd_7621377 : Nat := 4983230072969 + 3 ^ 40 * 7621377 * 2
def baseEnd_7621377 : Nat := 3913429650121533061137431

theorem tailTrace_7621377 : CollatzResearch.WordTrace tailWord_7621377 prefixEnd_7621377 3913429650121533061137431 := by
  unfold tailWord_7621377
  simp only [CollatzResearch.WordTrace]
  refine ⟨277974455710060231408846385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185316303806706820939230923 277974455710060231408846385)
  ·
    refine ⟨208480841782545173556634789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277974455710060231408846385 208480841782545173556634789)
    ·
      refine ⟨39090157834227220041869023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 208480841782545173556634789 39090157834227220041869023)
      ·
        refine ⟨58635236751340830062803535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39090157834227220041869023 58635236751340830062803535)
        ·
          refine ⟨87952855127011245094205303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58635236751340830062803535 87952855127011245094205303)
          ·
            refine ⟨131929282690516867641307955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87952855127011245094205303 131929282690516867641307955)
            ·
              refine ⟨197893924035775301461961933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131929282690516867641307955 197893924035775301461961933)
              ·
                refine ⟨74210221513415738048235725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 197893924035775301461961933 74210221513415738048235725)
                ·
                  refine ⟨27828833067530901768088397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74210221513415738048235725 27828833067530901768088397)
                  ·
                    refine ⟨10435812400324088163033149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27828833067530901768088397 10435812400324088163033149)
                    ·
                      refine ⟨3913429650121533061137431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10435812400324088163033149 3913429650121533061137431)
                      ·
                        rfl

theorem cell23_7621377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 3, 3, 3, 3].length) (baseStart_7621377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7621377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7621377 prefixEnd_7621377 := by exact prefixLift 7621377
  have htrace : WordTrace (prefixWord ++ tailWord_7621377) baseStart_7621377 baseEnd_7621377 := by
    simpa [prefixWord, tailWord_7621377, baseEnd_7621377] using wordTrace_append hprefix tailTrace_7621377
  have hstable : (prefixWord ++ tailWord_7621377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7621377).length < 2 ^ (prefixWord ++ tailWord_7621377).sum := by decide
  have hdescent : baseEnd_7621377 < baseStart_7621377 := by decide
  rcases family_descends (prefixWord ++ tailWord_7621377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7621405 : List Nat := [1, 4, 2, 4, 1, 2, 2, 1, 2, 4]
def baseStart_7621405 : Nat := 118140960795 + 7621405 * 2 ^ 59
def prefixEnd_7621405 : Nat := 4983230072969 + 3 ^ 40 * 7621405 * 2
def baseEnd_7621405 : Nat := 1304481342526619650529101

theorem tailTrace_7621405 : CollatzResearch.WordTrace tailWord_7621405 prefixEnd_7621405 1304481342526619650529101 := by
  unfold tailWord_7621405
  simp only [CollatzResearch.WordTrace]
  refine ⟨277975476953958792190865669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185316984635972528127243779 277975476953958792190865669)
  ·
    refine ⟨52120401928867273535787313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 277975476953958792190865669 52120401928867273535787313)
    ·
      refine ⟨39090301446650455151840485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52120401928867273535787313 39090301446650455151840485)
      ·
        refine ⟨7329431521246960340970091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39090301446650455151840485 7329431521246960340970091)
        ·
          refine ⟨10994147281870440511455137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7329431521246960340970091 10994147281870440511455137)
          ·
            refine ⟨8245610461402830383591353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10994147281870440511455137 8245610461402830383591353)
            ·
              refine ⟨6184207846052122787693515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8245610461402830383591353 6184207846052122787693515)
              ·
                refine ⟨9276311769078184181540273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6184207846052122787693515 9276311769078184181540273)
                ·
                  refine ⟨6957233826808638136155205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9276311769078184181540273 6957233826808638136155205)
                  ·
                    refine ⟨1304481342526619650529101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6957233826808638136155205 1304481342526619650529101)
                    ·
                      rfl

theorem cell23_7621405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 2, 1, 2, 4].length) (baseStart_7621405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7621405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7621405 prefixEnd_7621405 := by exact prefixLift 7621405
  have htrace : WordTrace (prefixWord ++ tailWord_7621405) baseStart_7621405 baseEnd_7621405 := by
    simpa [prefixWord, tailWord_7621405, baseEnd_7621405] using wordTrace_append hprefix tailTrace_7621405
  have hstable : (prefixWord ++ tailWord_7621405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7621405).length < 2 ^ (prefixWord ++ tailWord_7621405).sum := by decide
  have hdescent : baseEnd_7621405 < baseStart_7621405 := by decide
  rcases family_descends (prefixWord ++ tailWord_7621405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7621446 : List Nat := [6, 1, 1, 2, 2, 2, 2, 2, 1, 2, 2]
def baseStart_7621446 : Nat := 118140960795 + 7621446 * 2 ^ 59
def prefixEnd_7621446 : Nat := 4983230072969 + 3 ^ 40 * 7621446 * 2
def baseEnd_7621446 : Nat := 3913465080286693291174615

theorem tailTrace_7621446 : CollatzResearch.WordTrace tailWord_7621446 prefixEnd_7621446 3913465080286693291174615 := by
  unfold tailWord_7621446
  simp only [CollatzResearch.WordTrace]
  refine ⟨8686780385837820506034631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 185317981564540170795405461 8686780385837820506034631)
  ·
    refine ⟨13030170578756730759051947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8686780385837820506034631 13030170578756730759051947)
    ·
      refine ⟨19545255868135096138577921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13030170578756730759051947 19545255868135096138577921)
      ·
        refine ⟨14658941901101322103933441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19545255868135096138577921 14658941901101322103933441)
        ·
          refine ⟨10994206425825991577950081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14658941901101322103933441 10994206425825991577950081)
          ·
            refine ⟨8245654819369493683462561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10994206425825991577950081 8245654819369493683462561)
            ·
              refine ⟨6184241114527120262596921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8245654819369493683462561 6184241114527120262596921)
              ·
                refine ⟨4638180835895340196947691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6184241114527120262596921 4638180835895340196947691)
                ·
                  refine ⟨6957271253843010295421537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4638180835895340196947691 6957271253843010295421537)
                  ·
                    refine ⟨5217953440382257721566153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6957271253843010295421537 5217953440382257721566153)
                    ·
                      refine ⟨3913465080286693291174615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5217953440382257721566153 3913465080286693291174615)
                      ·
                        rfl

theorem cell23_7621446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 2, 2, 1, 2, 2].length) (baseStart_7621446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7621446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7621446 prefixEnd_7621446 := by exact prefixLift 7621446
  have htrace : WordTrace (prefixWord ++ tailWord_7621446) baseStart_7621446 baseEnd_7621446 := by
    simpa [prefixWord, tailWord_7621446, baseEnd_7621446] using wordTrace_append hprefix tailTrace_7621446
  have hstable : (prefixWord ++ tailWord_7621446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7621446).length < 2 ^ (prefixWord ++ tailWord_7621446).sum := by decide
  have hdescent : baseEnd_7621446 < baseStart_7621446 := by decide
  rcases family_descends (prefixWord ++ tailWord_7621446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7621447 : List Nat := [1, 1, 4, 1, 2, 1, 1, 4, 2, 2, 4]
def baseStart_7621447 : Nat := 118140960795 + 7621447 * 2 ^ 59
def prefixEnd_7621447 : Nat := 4983230072969 + 3 ^ 40 * 7621447 * 2
def baseEnd_7621447 : Nat := 3913465593767347787262109

theorem tailTrace_7621447 : CollatzResearch.WordTrace tailWord_7621447 prefixEnd_7621447 3913465593767347787262109 := by
  unfold tailWord_7621447
  simp only [CollatzResearch.WordTrace]
  refine ⟨277977008819806633363894595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185318005879871088909263063 277977008819806633363894595)
  ·
    refine ⟨416965513229709950045841893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277977008819806633363894595 416965513229709950045841893)
    ·
      refine ⟨78181033730570615633595355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 416965513229709950045841893 78181033730570615633595355)
      ·
        refine ⟨117271550595855923450393033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78181033730570615633595355 117271550595855923450393033)
        ·
          refine ⟨87953662946891942587794775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117271550595855923450393033 87953662946891942587794775)
          ·
            refine ⟨131930494420337913881692163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87953662946891942587794775 131930494420337913881692163)
            ·
              refine ⟨197895741630506870822538245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131930494420337913881692163 197895741630506870822538245)
              ·
                refine ⟨37105451555720038279225921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 197895741630506870822538245 37105451555720038279225921)
                ·
                  refine ⟨27829088666790028709419441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37105451555720038279225921 27829088666790028709419441)
                  ·
                    refine ⟨20871816500092521532064581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27829088666790028709419441 20871816500092521532064581)
                    ·
                      refine ⟨3913465593767347787262109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20871816500092521532064581 3913465593767347787262109)
                      ·
                        rfl

theorem cell23_7621447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 4, 2, 2, 4].length) (baseStart_7621447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7621447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7621447 prefixEnd_7621447 := by exact prefixLift 7621447
  have htrace : WordTrace (prefixWord ++ tailWord_7621447) baseStart_7621447 baseEnd_7621447 := by
    simpa [prefixWord, tailWord_7621447, baseEnd_7621447] using wordTrace_append hprefix tailTrace_7621447
  have hstable : (prefixWord ++ tailWord_7621447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7621447).length < 2 ^ (prefixWord ++ tailWord_7621447).sum := by decide
  have hdescent : baseEnd_7621447 < baseStart_7621447 := by decide
  rcases family_descends (prefixWord ++ tailWord_7621447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7621468 : List Nat := [2, 2, 4, 2, 1, 2, 2, 1, 1, 4, 2]
def baseStart_7621468 : Nat := 118140960795 + 7621468 * 2 ^ 59
def prefixEnd_7621468 : Nat := 4983230072969 + 3 ^ 40 * 7621468 * 2
def baseEnd_7621468 : Nat := 3913476376861092205099513

theorem tailTrace_7621468 : CollatzResearch.WordTrace tailWord_7621468 prefixEnd_7621468 3913476376861092205099513 := by
  unfold tailWord_7621468
  simp only [CollatzResearch.WordTrace]
  refine ⟨138988887376365276975204529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185318516501820369300272705 138988887376365276975204529)
  ·
    refine ⟨104241665532273957731403397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138988887376365276975204529 104241665532273957731403397)
    ·
      refine ⟨19545312287301367074638137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104241665532273957731403397 19545312287301367074638137)
      ·
        refine ⟨14658984215476025305978603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19545312287301367074638137 14658984215476025305978603)
        ·
          refine ⟨21988476323214037958967905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14658984215476025305978603 21988476323214037958967905)
          ·
            refine ⟨16491357242410528469225929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21988476323214037958967905 16491357242410528469225929)
            ·
              refine ⟨12368517931807896351919447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16491357242410528469225929 12368517931807896351919447)
              ·
                refine ⟨18552776897711844527879171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12368517931807896351919447 18552776897711844527879171)
                ·
                  refine ⟨27829165346567766791818757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18552776897711844527879171 27829165346567766791818757)
                  ·
                    refine ⟨5217968502481456273466017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27829165346567766791818757 5217968502481456273466017)
                    ·
                      refine ⟨3913476376861092205099513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5217968502481456273466017 3913476376861092205099513)
                      ·
                        rfl

theorem cell23_7621468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 2, 1, 1, 4, 2].length) (baseStart_7621468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7621468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7621468 prefixEnd_7621468 := by exact prefixLift 7621468
  have htrace : WordTrace (prefixWord ++ tailWord_7621468) baseStart_7621468 baseEnd_7621468 := by
    simpa [prefixWord, tailWord_7621468, baseEnd_7621468] using wordTrace_append hprefix tailTrace_7621468
  have hstable : (prefixWord ++ tailWord_7621468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7621468).length < 2 ^ (prefixWord ++ tailWord_7621468).sum := by decide
  have hdescent : baseEnd_7621468 < baseStart_7621468 := by decide
  rcases family_descends (prefixWord ++ tailWord_7621468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7621524 : List Nat := [2, 4, 2, 1, 1, 1, 1, 1, 3, 3, 4]
def baseStart_7621524 : Nat := 118140960795 + 7621524 * 2 ^ 59
def prefixEnd_7621524 : Nat := 4983230072969 + 3 ^ 40 * 7621524 * 2
def baseEnd_7621524 : Nat := 3913505131777743985999255

theorem tailTrace_7621524 : CollatzResearch.WordTrace tailWord_7621524 prefixEnd_7621524 3913505131777743985999255 := by
  unfold tailWord_7621524
  simp only [CollatzResearch.WordTrace]
  refine ⟨138989908620263837757223813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185319878160351783676298417 138989908620263837757223813)
  ·
    refine ⟨26060607866299469579479465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138989908620263837757223813 26060607866299469579479465)
    ·
      refine ⟨19545455899724602184609599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26060607866299469579479465 19545455899724602184609599)
      ·
        refine ⟨29318183849586903276914399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19545455899724602184609599 29318183849586903276914399)
        ·
          refine ⟨43977275774380354915371599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29318183849586903276914399 43977275774380354915371599)
          ·
            refine ⟨65965913661570532373057399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43977275774380354915371599 65965913661570532373057399)
            ·
              refine ⟨98948870492355798559586099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65965913661570532373057399 98948870492355798559586099)
              ·
                refine ⟨148423305738533697839379149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98948870492355798559586099 148423305738533697839379149)
                ·
                  refine ⟨55658739651950136689767181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 148423305738533697839379149 55658739651950136689767181)
                  ·
                    refine ⟨20872027369481301258662693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55658739651950136689767181 20872027369481301258662693)
                    ·
                      refine ⟨3913505131777743985999255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20872027369481301258662693 3913505131777743985999255)
                      ·
                        rfl

theorem cell23_7621524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_7621524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7621524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7621524 prefixEnd_7621524 := by exact prefixLift 7621524
  have htrace : WordTrace (prefixWord ++ tailWord_7621524) baseStart_7621524 baseEnd_7621524 := by
    simpa [prefixWord, tailWord_7621524, baseEnd_7621524] using wordTrace_append hprefix tailTrace_7621524
  have hstable : (prefixWord ++ tailWord_7621524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7621524).length < 2 ^ (prefixWord ++ tailWord_7621524).sum := by decide
  have hdescent : baseEnd_7621524 < baseStart_7621524 := by decide
  rcases family_descends (prefixWord ++ tailWord_7621524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7621551 : List Nat := [1, 1, 2, 1, 2, 2, 2, 7, 1, 4]
def baseStart_7621551 : Nat := 118140960795 + 7621551 * 2 ^ 59
def prefixEnd_7621551 : Nat := 4983230072969 + 3 ^ 40 * 7621551 * 2
def baseEnd_7621551 : Nat := 1304506331918471793453877

theorem tailTrace_7621551 : CollatzResearch.WordTrace tailWord_7621551 prefixEnd_7621551 1304506331918471793453877 := by
  unfold tailWord_7621551
  simp only [CollatzResearch.WordTrace]
  refine ⟨277980802011429859125680507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185320534674286572750453671 277980802011429859125680507)
  ·
    refine ⟨416971203017144788688520761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277980802011429859125680507 416971203017144788688520761)
    ·
      refine ⟨312728402262858591516390571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 416971203017144788688520761 312728402262858591516390571)
      ·
        refine ⟨469092603394287887274585857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312728402262858591516390571 469092603394287887274585857)
        ·
          refine ⟨351819452545715915455939393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 469092603394287887274585857 351819452545715915455939393)
          ·
            refine ⟨263864589409286936591954545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 351819452545715915455939393 263864589409286936591954545)
            ·
              refine ⟨197898442056965202443965909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 263864589409286936591954545 197898442056965202443965909)
              ·
                refine ⟨4638244735710121932280451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 197898442056965202443965909 4638244735710121932280451)
                ·
                  refine ⟨6957367103565182898420677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4638244735710121932280451 6957367103565182898420677)
                  ·
                    refine ⟨1304506331918471793453877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6957367103565182898420677 1304506331918471793453877)
                    ·
                      rfl

theorem cell23_7621551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 7, 1, 4].length) (baseStart_7621551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7621551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7621551 prefixEnd_7621551 := by exact prefixLift 7621551
  have htrace : WordTrace (prefixWord ++ tailWord_7621551) baseStart_7621551 baseEnd_7621551 := by
    simpa [prefixWord, tailWord_7621551, baseEnd_7621551] using wordTrace_append hprefix tailTrace_7621551
  have hstable : (prefixWord ++ tailWord_7621551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7621551).length < 2 ^ (prefixWord ++ tailWord_7621551).sum := by decide
  have hdescent : baseEnd_7621551 < baseStart_7621551 := by decide
  rcases family_descends (prefixWord ++ tailWord_7621551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7621561 : List Nat := [1, 2, 1, 4, 2, 3, 1, 2, 2, 2, 3]
def baseStart_7621561 : Nat := 118140960795 + 7621561 * 2 ^ 59
def prefixEnd_7621561 : Nat := 4983230072969 + 3 ^ 40 * 7621561 * 2
def baseEnd_7621561 : Nat := 3913524130561960341236585

theorem tailTrace_7621561 : CollatzResearch.WordTrace tailWord_7621561 prefixEnd_7621561 3913524130561960341236585 := by
  unfold tailWord_7621561
  simp only [CollatzResearch.WordTrace]
  refine ⟨277981166741393630833544537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185320777827595753889029691 277981166741393630833544537)
  ·
    refine ⟨208485875056045223125158403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277981166741393630833544537 208485875056045223125158403)
    ·
      refine ⟨312728812584067834687737605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208485875056045223125158403 312728812584067834687737605)
      ·
        refine ⟨58636652359512719003950801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 312728812584067834687737605 58636652359512719003950801)
        ·
          refine ⟨43977489269634539252963101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58636652359512719003950801 43977489269634539252963101)
          ·
            refine ⟨16491558476112952219861163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43977489269634539252963101 16491558476112952219861163)
            ·
              refine ⟨24737337714169428329791745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16491558476112952219861163 24737337714169428329791745)
              ·
                refine ⟨18553003285627071247343809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24737337714169428329791745 18553003285627071247343809)
                ·
                  refine ⟨13914752464220303435507857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18553003285627071247343809 13914752464220303435507857)
                  ·
                    refine ⟨10436064348165227576630893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13914752464220303435507857 10436064348165227576630893)
                    ·
                      refine ⟨3913524130561960341236585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10436064348165227576630893 3913524130561960341236585)
                      ·
                        rfl

theorem cell23_7621561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 2, 2, 2, 3].length) (baseStart_7621561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7621561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7621561 prefixEnd_7621561 := by exact prefixLift 7621561
  have htrace : WordTrace (prefixWord ++ tailWord_7621561) baseStart_7621561 baseEnd_7621561 := by
    simpa [prefixWord, tailWord_7621561, baseEnd_7621561] using wordTrace_append hprefix tailTrace_7621561
  have hstable : (prefixWord ++ tailWord_7621561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7621561).length < 2 ^ (prefixWord ++ tailWord_7621561).sum := by decide
  have hdescent : baseEnd_7621561 < baseStart_7621561 := by decide
  rcases family_descends (prefixWord ++ tailWord_7621561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7621567 : List Nat := [1, 1, 2, 2, 2, 1, 2, 3, 1, 2, 6]
def baseStart_7621567 : Nat := 118140960795 + 7621567 * 2 ^ 59
def prefixEnd_7621567 : Nat := 4983230072969 + 3 ^ 40 * 7621567 * 2
def baseEnd_7621567 : Nat := 3913527211445887317761557

theorem tailTrace_7621567 : CollatzResearch.WordTrace tailWord_7621567 prefixEnd_7621567 3913527211445887317761557 := by
  unfold tailWord_7621567
  simp only [CollatzResearch.WordTrace]
  refine ⟨277981385579371893858262955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185320923719581262572175303 277981385579371893858262955)
  ·
    refine ⟨416972078369057840787394433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277981385579371893858262955 416972078369057840787394433)
    ·
      refine ⟨312729058776793380590545825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 416972078369057840787394433 312729058776793380590545825)
      ·
        refine ⟨234546794082595035442909369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 312729058776793380590545825 234546794082595035442909369)
        ·
          refine ⟨175910095561946276582182027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234546794082595035442909369 175910095561946276582182027)
          ·
            refine ⟨263865143342919414873273041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175910095561946276582182027 263865143342919414873273041)
            ·
              refine ⟨197898857507189561154954781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 263865143342919414873273041 197898857507189561154954781)
              ·
                refine ⟨74212071565196085433108043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 197898857507189561154954781 74212071565196085433108043)
                ·
                  refine ⟨111318107347794128149662065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74212071565196085433108043 111318107347794128149662065)
                  ·
                    refine ⟨83488580510845596112246549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 111318107347794128149662065 83488580510845596112246549)
                    ·
                      refine ⟨3913527211445887317761557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83488580510845596112246549 3913527211445887317761557)
                      ·
                        rfl

theorem cell23_7621567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 3, 1, 2, 6].length) (baseStart_7621567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7621567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7621567 prefixEnd_7621567 := by exact prefixLift 7621567
  have htrace : WordTrace (prefixWord ++ tailWord_7621567) baseStart_7621567 baseEnd_7621567 := by
    simpa [prefixWord, tailWord_7621567, baseEnd_7621567] using wordTrace_append hprefix tailTrace_7621567
  have hstable : (prefixWord ++ tailWord_7621567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7621567).length < 2 ^ (prefixWord ++ tailWord_7621567).sum := by decide
  have hdescent : baseEnd_7621567 < baseStart_7621567 := by decide
  rcases family_descends (prefixWord ++ tailWord_7621567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7621651 : List Nat := [1, 1, 1, 2, 1, 4, 1, 6, 1, 2, 3]
def baseStart_7621651 : Nat := 118140960795 + 7621651 * 2 ^ 59
def prefixEnd_7621651 : Nat := 4983230072969 + 3 ^ 40 * 7621651 * 2
def baseEnd_7621651 : Nat := 3913570343820864989111171

theorem tailTrace_7621651 : CollatzResearch.WordTrace tailWord_7621651 prefixEnd_7621651 3913570343820864989111171 := by
  unfold tailWord_7621651
  simp only [CollatzResearch.WordTrace]
  refine ⟨277984449311067576204320807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185322966207378384136213871 277984449311067576204320807)
  ·
    refine ⟨416976673966601364306481211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277984449311067576204320807 416976673966601364306481211)
    ·
      refine ⟨625465010949902046459721817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 416976673966601364306481211 625465010949902046459721817)
      ·
        refine ⟨469098758212426534844791363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 625465010949902046459721817 469098758212426534844791363)
        ·
          refine ⟨703648137318639802267187045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 469098758212426534844791363 703648137318639802267187045)
          ·
            refine ⟨131934025747244962925097571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 703648137318639802267187045 131934025747244962925097571)
            ·
              refine ⟨197901038620867444387646357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131934025747244962925097571 197901038620867444387646357)
              ·
                refine ⟨9276611185353161455670923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 197901038620867444387646357 9276611185353161455670923)
                ·
                  refine ⟨13914916778029742183506385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9276611185353161455670923 13914916778029742183506385)
                  ·
                    refine ⟨10436187583522306637629789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13914916778029742183506385 10436187583522306637629789)
                    ·
                      refine ⟨3913570343820864989111171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10436187583522306637629789 3913570343820864989111171)
                      ·
                        rfl

theorem cell23_7621651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 6, 1, 2, 3].length) (baseStart_7621651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7621651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7621651 prefixEnd_7621651 := by exact prefixLift 7621651
  have htrace : WordTrace (prefixWord ++ tailWord_7621651) baseStart_7621651 baseEnd_7621651 := by
    simpa [prefixWord, tailWord_7621651, baseEnd_7621651] using wordTrace_append hprefix tailTrace_7621651
  have hstable : (prefixWord ++ tailWord_7621651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7621651).length < 2 ^ (prefixWord ++ tailWord_7621651).sum := by decide
  have hdescent : baseEnd_7621651 < baseStart_7621651 := by decide
  rcases family_descends (prefixWord ++ tailWord_7621651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7621665 : List Nat := [1, 2, 3, 2, 3, 3, 2, 1, 1, 1, 4]
def baseStart_7621665 : Nat := 118140960795 + 7621665 * 2 ^ 59
def prefixEnd_7621665 : Nat := 4983230072969 + 3 ^ 40 * 7621665 * 2
def baseEnd_7621665 : Nat := 3913577532550027934336107

theorem tailTrace_7621665 : CollatzResearch.WordTrace tailWord_7621665 prefixEnd_7621665 3913577532550027934336107 := by
  unfold tailWord_7621665
  simp only [CollatzResearch.WordTrace]
  refine ⟨277984959933016856595330449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185323306622011237730220299 277984959933016856595330449)
  ·
    refine ⟨208488719949762642446497837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277984959933016856595330449 208488719949762642446497837)
    ·
      refine ⟨78183269981160990917436689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208488719949762642446497837 78183269981160990917436689)
      ·
        refine ⟨58637452485870743188077517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78183269981160990917436689 58637452485870743188077517)
        ·
          refine ⟨21989044682201528695529069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58637452485870743188077517 21989044682201528695529069)
          ·
            refine ⟨8245891755825573260823401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21989044682201528695529069 8245891755825573260823401)
            ·
              refine ⟨6184418816869179945617551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8245891755825573260823401 6184418816869179945617551)
              ·
                refine ⟨9276628225303769918426327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6184418816869179945617551 9276628225303769918426327)
                ·
                  refine ⟨13914942337955654877639491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9276628225303769918426327 13914942337955654877639491)
                  ·
                    refine ⟨20872413506933482316459237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13914942337955654877639491 20872413506933482316459237)
                    ·
                      refine ⟨3913577532550027934336107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20872413506933482316459237 3913577532550027934336107)
                      ·
                        rfl

theorem cell23_7621665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 2, 1, 1, 1, 4].length) (baseStart_7621665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7621665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7621665 prefixEnd_7621665 := by exact prefixLift 7621665
  have htrace : WordTrace (prefixWord ++ tailWord_7621665) baseStart_7621665 baseEnd_7621665 := by
    simpa [prefixWord, tailWord_7621665, baseEnd_7621665] using wordTrace_append hprefix tailTrace_7621665
  have hstable : (prefixWord ++ tailWord_7621665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7621665).length < 2 ^ (prefixWord ++ tailWord_7621665).sum := by decide
  have hdescent : baseEnd_7621665 < baseStart_7621665 := by decide
  rcases family_descends (prefixWord ++ tailWord_7621665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7621671 : List Nat := [1, 1, 7, 1, 1, 2, 10]
def baseStart_7621671 : Nat := 118140960795 + 7621671 * 2 ^ 59
def prefixEnd_7621671 : Nat := 4983230072969 + 3 ^ 40 * 7621671 * 2
def baseEnd_7621671 : Nat := 48315810042394505072359

theorem tailTrace_7621671 : CollatzResearch.WordTrace tailWord_7621671 prefixEnd_7621671 48315810042394505072359 := by
  unfold tailWord_7621671
  simp only [CollatzResearch.WordTrace]
  refine ⟨277985178770995119620048867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185323452513996746413365911 277985178770995119620048867)
  ·
    refine ⟨416977768156492679430073301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277985178770995119620048867 416977768156492679430073301)
    ·
      refine ⟨9772916441167797174142343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 416977768156492679430073301 9772916441167797174142343)
      ·
        refine ⟨14659374661751695761213515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9772916441167797174142343 14659374661751695761213515)
        ·
          refine ⟨21989061992627543641820273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14659374661751695761213515 21989061992627543641820273)
          ·
            refine ⟨16491796494470657731365205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21989061992627543641820273 16491796494470657731365205)
            ·
              refine ⟨48315810042394505072359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 16491796494470657731365205 48315810042394505072359)
              ·
                rfl

theorem cell23_7621671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 10].length) (baseStart_7621671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7621671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7621671 prefixEnd_7621671 := by exact prefixLift 7621671
  have htrace : WordTrace (prefixWord ++ tailWord_7621671) baseStart_7621671 baseEnd_7621671 := by
    simpa [prefixWord, tailWord_7621671, baseEnd_7621671] using wordTrace_append hprefix tailTrace_7621671
  have hstable : (prefixWord ++ tailWord_7621671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7621671).length < 2 ^ (prefixWord ++ tailWord_7621671).sum := by decide
  have hdescent : baseEnd_7621671 < baseStart_7621671 := by decide
  rcases family_descends (prefixWord ++ tailWord_7621671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7621702 : List Nat := [6, 1, 1, 1, 1, 3, 2, 2, 1, 2, 3]
def baseStart_7621702 : Nat := 118140960795 + 7621702 * 2 ^ 59
def prefixEnd_7621702 : Nat := 4983230072969 + 3 ^ 40 * 7621702 * 2
def baseEnd_7621702 : Nat := 3913596531334244289573437

theorem tailTrace_7621702 : CollatzResearch.WordTrace tailWord_7621702 prefixEnd_7621702 3913596531334244289573437 := by
  unfold tailWord_7621702
  simp only [CollatzResearch.WordTrace]
  refine ⟨8687072169808837872325855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 185324206289255207942951573 8687072169808837872325855)
  ·
    refine ⟨13030608254713256808488783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8687072169808837872325855 13030608254713256808488783)
    ·
      refine ⟨19545912382069885212733175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13030608254713256808488783 19545912382069885212733175)
      ·
        refine ⟨29318868573104827819099763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19545912382069885212733175 29318868573104827819099763)
        ·
          refine ⟨43978302859657241728649645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29318868573104827819099763 43978302859657241728649645)
          ·
            refine ⟨16491863572371465648243617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43978302859657241728649645 16491863572371465648243617)
            ·
              refine ⟨12368897679278599236182713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16491863572371465648243617 12368897679278599236182713)
              ·
                refine ⟨9276673259458949427137035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12368897679278599236182713 9276673259458949427137035)
                ·
                  refine ⟨13915009889188424140705553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9276673259458949427137035 13915009889188424140705553)
                  ·
                    refine ⟨10436257416891318105529165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13915009889188424140705553 10436257416891318105529165)
                    ·
                      refine ⟨3913596531334244289573437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10436257416891318105529165 3913596531334244289573437)
                      ·
                        rfl

theorem cell23_7621702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 2, 2, 1, 2, 3].length) (baseStart_7621702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7621702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7621702 prefixEnd_7621702 := by exact prefixLift 7621702
  have htrace : WordTrace (prefixWord ++ tailWord_7621702) baseStart_7621702 baseEnd_7621702 := by
    simpa [prefixWord, tailWord_7621702, baseEnd_7621702] using wordTrace_append hprefix tailTrace_7621702
  have hstable : (prefixWord ++ tailWord_7621702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7621702).length < 2 ^ (prefixWord ++ tailWord_7621702).sum := by decide
  have hdescent : baseEnd_7621702 < baseStart_7621702 := by decide
  rcases family_descends (prefixWord ++ tailWord_7621702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7621805 : List Nat := [1, 5, 2, 1, 3, 1, 1, 1, 2, 3, 3]
def baseStart_7621805 : Nat := 118140960795 + 7621805 * 2 ^ 59
def prefixEnd_7621805 : Nat := 4983230072969 + 3 ^ 40 * 7621805 * 2
def baseEnd_7621805 : Nat := 3913649419841657386585463

theorem tailTrace_7621805 : CollatzResearch.WordTrace tailWord_7621805 prefixEnd_7621805 3913649419841657386585463 := by
  unfold tailWord_7621805
  simp only [CollatzResearch.WordTrace]
  refine ⟨277990066152509660505426869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185326710768339773670284579 277990066152509660505426869)
  ·
    refine ⟨26061568701797780672383769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 277990066152509660505426869 26061568701797780672383769)
    ·
      refine ⟨19546176526348335504287827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26061568701797780672383769 19546176526348335504287827)
      ·
        refine ⟨29319264789522503256431741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19546176526348335504287827 29319264789522503256431741)
        ·
          refine ⟨10994724296070938721161903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29319264789522503256431741 10994724296070938721161903)
          ·
            refine ⟨16492086444106408081742855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10994724296070938721161903 16492086444106408081742855)
            ·
              refine ⟨24738129666159612122614283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16492086444106408081742855 24738129666159612122614283)
              ·
                refine ⟨37107194499239418183921425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24738129666159612122614283 37107194499239418183921425)
                ·
                  refine ⟨27830395874429563637941069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37107194499239418183921425 27830395874429563637941069)
                  ·
                    refine ⟨10436398452911086364227901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27830395874429563637941069 10436398452911086364227901)
                    ·
                      refine ⟨3913649419841657386585463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10436398452911086364227901 3913649419841657386585463)
                      ·
                        rfl

theorem cell23_7621805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 1, 2, 3, 3].length) (baseStart_7621805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7621805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7621805 prefixEnd_7621805 := by exact prefixLift 7621805
  have htrace : WordTrace (prefixWord ++ tailWord_7621805) baseStart_7621805 baseEnd_7621805 := by
    simpa [prefixWord, tailWord_7621805, baseEnd_7621805] using wordTrace_append hprefix tailTrace_7621805
  have hstable : (prefixWord ++ tailWord_7621805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7621805).length < 2 ^ (prefixWord ++ tailWord_7621805).sum := by decide
  have hdescent : baseEnd_7621805 < baseStart_7621805 := by decide
  rcases family_descends (prefixWord ++ tailWord_7621805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7621811 : List Nat := [1, 1, 1, 2, 3, 2, 2, 2, 4, 1, 4]
def baseStart_7621811 : Nat := 118140960795 + 7621811 * 2 ^ 59
def prefixEnd_7621811 : Nat := 4983230072969 + 3 ^ 40 * 7621811 * 2
def baseEnd_7621811 : Nat := 3913652500725584363110435

theorem tailTrace_7621811 : CollatzResearch.WordTrace tailWord_7621811 prefixEnd_7621811 3913652500725584363110435 := by
  unfold tailWord_7621811
  simp only [CollatzResearch.WordTrace]
  refine ⟨277990284990487923530145287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185326856660325282353430191 277990284990487923530145287)
  ·
    refine ⟨416985427485731885295217931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277990284990487923530145287 416985427485731885295217931)
    ·
      refine ⟨625478141228597827942826897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 416985427485731885295217931 625478141228597827942826897)
      ·
        refine ⟨469108605921448370957120173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 625478141228597827942826897 469108605921448370957120173)
        ·
          refine ⟨175915727220543139108920065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 469108605921448370957120173 175915727220543139108920065)
          ·
            refine ⟨131936795415407354331690049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175915727220543139108920065 131936795415407354331690049)
            ·
              refine ⟨98952596561555515748767537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131936795415407354331690049 98952596561555515748767537)
              ·
                refine ⟨74214447421166636811575653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98952596561555515748767537 74214447421166636811575653)
                ·
                  refine ⟨13915208891468744402170435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74214447421166636811575653 13915208891468744402170435)
                  ·
                    refine ⟨20872813337203116603255653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13915208891468744402170435 20872813337203116603255653)
                    ·
                      refine ⟨3913652500725584363110435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20872813337203116603255653 3913652500725584363110435)
                      ·
                        rfl

theorem cell23_7621811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 2, 4, 1, 4].length) (baseStart_7621811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7621811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7621811 prefixEnd_7621811 := by exact prefixLift 7621811
  have htrace : WordTrace (prefixWord ++ tailWord_7621811) baseStart_7621811 baseEnd_7621811 := by
    simpa [prefixWord, tailWord_7621811, baseEnd_7621811] using wordTrace_append hprefix tailTrace_7621811
  have hstable : (prefixWord ++ tailWord_7621811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7621811).length < 2 ^ (prefixWord ++ tailWord_7621811).sum := by decide
  have hdescent : baseEnd_7621811 < baseStart_7621811 := by decide
  rcases family_descends (prefixWord ++ tailWord_7621811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7621825 : List Nat := [1, 2, 6, 1, 1, 1, 3, 1, 2, 5]
def baseStart_7621825 : Nat := 118140960795 + 7621825 * 2 ^ 59
def prefixEnd_7621825 : Nat := 4983230072969 + 3 ^ 40 * 7621825 * 2
def baseEnd_7621825 : Nat := 1304553229818249102778457

theorem tailTrace_7621825 : CollatzResearch.WordTrace tailWord_7621825 prefixEnd_7621825 1304553229818249102778457 := by
  unfold tailWord_7621825
  simp only [CollatzResearch.WordTrace]
  refine ⟨277990795612437203921154929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185327197074958135947436619 277990795612437203921154929)
  ·
    refine ⟨208493096709327902940866197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277990795612437203921154929 208493096709327902940866197)
    ·
      refine ⟨9773113908249745450353103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 208493096709327902940866197 9773113908249745450353103)
      ·
        refine ⟨14659670862374618175529655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9773113908249745450353103 14659670862374618175529655)
        ·
          refine ⟨21989506293561927263294483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14659670862374618175529655 21989506293561927263294483)
          ·
            refine ⟨32984259440342890894941725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21989506293561927263294483 32984259440342890894941725)
            ·
              refine ⟨12369097290128584085603147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32984259440342890894941725 12369097290128584085603147)
              ·
                refine ⟨18553645935192876128404721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12369097290128584085603147 18553645935192876128404721)
                ·
                  refine ⟨13915234451394657096303541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18553645935192876128404721 13915234451394657096303541)
                  ·
                    refine ⟨1304553229818249102778457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13915234451394657096303541 1304553229818249102778457)
                    ·
                      rfl

theorem cell23_7621825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_7621825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7621825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7621825 prefixEnd_7621825 := by exact prefixLift 7621825
  have htrace : WordTrace (prefixWord ++ tailWord_7621825) baseStart_7621825 baseEnd_7621825 := by
    simpa [prefixWord, tailWord_7621825, baseEnd_7621825] using wordTrace_append hprefix tailTrace_7621825
  have hstable : (prefixWord ++ tailWord_7621825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7621825).length < 2 ^ (prefixWord ++ tailWord_7621825).sum := by decide
  have hdescent : baseEnd_7621825 < baseStart_7621825 := by decide
  rcases family_descends (prefixWord ++ tailWord_7621825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7621845 : List Nat := [1, 3, 2, 4, 1, 1, 1, 2, 2, 4, 2]
def baseStart_7621845 : Nat := 118140960795 + 7621845 * 2 ^ 59
def prefixEnd_7621845 : Nat := 4983230072969 + 3 ^ 40 * 7621845 * 2
def baseEnd_7621845 : Nat := 3913669959067837230085279

theorem tailTrace_7621845 : CollatzResearch.WordTrace tailWord_7621845 prefixEnd_7621845 3913669959067837230085279 := by
  unfold tailWord_7621845
  simp only [CollatzResearch.WordTrace]
  refine ⟨277991525072364747336882989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185327683381576498224588659 277991525072364747336882989)
  ·
    refine ⟨104246821902136780251331121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 277991525072364747336882989 104246821902136780251331121)
    ·
      refine ⟨78185116426602585188498341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104246821902136780251331121 78185116426602585188498341)
      ·
        refine ⟨14659709329987984722843439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78185116426602585188498341 14659709329987984722843439)
        ·
          refine ⟨21989563994981977084265159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14659709329987984722843439 21989563994981977084265159)
          ·
            refine ⟨32984345992472965626397739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21989563994981977084265159 32984345992472965626397739)
            ·
              refine ⟨49476518988709448439596609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32984345992472965626397739 49476518988709448439596609)
              ·
                refine ⟨37107389241532086329697457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49476518988709448439596609 37107389241532086329697457)
                ·
                  refine ⟨27830541931149064747273093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37107389241532086329697457 27830541931149064747273093)
                  ·
                    refine ⟨5218226612090449640113705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27830541931149064747273093 5218226612090449640113705)
                    ·
                      refine ⟨3913669959067837230085279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5218226612090449640113705 3913669959067837230085279)
                      ·
                        rfl

theorem cell23_7621845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 2, 2, 4, 2].length) (baseStart_7621845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7621845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7621845 prefixEnd_7621845 := by exact prefixLift 7621845
  have htrace : WordTrace (prefixWord ++ tailWord_7621845) baseStart_7621845 baseEnd_7621845 := by
    simpa [prefixWord, tailWord_7621845, baseEnd_7621845] using wordTrace_append hprefix tailTrace_7621845
  have hstable : (prefixWord ++ tailWord_7621845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7621845).length < 2 ^ (prefixWord ++ tailWord_7621845).sum := by decide
  have hdescent : baseEnd_7621845 < baseStart_7621845 := by decide
  rcases family_descends (prefixWord ++ tailWord_7621845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7621855 : List Nat := [1, 1, 2, 3, 2, 1, 4, 4, 1, 4]
def baseStart_7621855 : Nat := 118140960795 + 7621855 * 2 ^ 59
def prefixEnd_7621855 : Nat := 4983230072969 + 3 ^ 40 * 7621855 * 2
def baseEnd_7621855 : Nat := 1304558364624794063653411

theorem tailTrace_7621855 : CollatzResearch.WordTrace tailWord_7621855 prefixEnd_7621855 1304558364624794063653411 := by
  unfold tailWord_7621855
  simp only [CollatzResearch.WordTrace]
  refine ⟨277991889802328519044747019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185327926534885679363164679 277991889802328519044747019)
  ·
    refine ⟨416987834703492778567120529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277991889802328519044747019 416987834703492778567120529)
    ·
      refine ⟨312740876027619583925340397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 416987834703492778567120529 312740876027619583925340397)
      ·
        refine ⟨117277828510357343972002649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 312740876027619583925340397 117277828510357343972002649)
        ·
          refine ⟨87958371382768007979001987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117277828510357343972002649 87958371382768007979001987)
          ·
            refine ⟨131937557074152011968502981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87958371382768007979001987 131937557074152011968502981)
            ·
              refine ⟨24738291951403502244094309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 131937557074152011968502981 24738291951403502244094309)
              ·
                refine ⟨4638429740888156670767683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24738291951403502244094309 4638429740888156670767683)
                ·
                  refine ⟨6957644611332235006151525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4638429740888156670767683 6957644611332235006151525)
                  ·
                    refine ⟨1304558364624794063653411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6957644611332235006151525 1304558364624794063653411)
                    ·
                      rfl

theorem cell23_7621855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 4, 1, 4].length) (baseStart_7621855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7621855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7621855 prefixEnd_7621855 := by exact prefixLift 7621855
  have htrace : WordTrace (prefixWord ++ tailWord_7621855) baseStart_7621855 baseEnd_7621855 := by
    simpa [prefixWord, tailWord_7621855, baseEnd_7621855] using wordTrace_append hprefix tailTrace_7621855
  have hstable : (prefixWord ++ tailWord_7621855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7621855).length < 2 ^ (prefixWord ++ tailWord_7621855).sum := by decide
  have hdescent : baseEnd_7621855 < baseStart_7621855 := by decide
  rcases family_descends (prefixWord ++ tailWord_7621855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7621878 : List Nat := [5, 1, 1, 1, 1, 1, 1, 1, 1, 7, 3]
def baseStart_7621878 : Nat := 118140960795 + 7621878 * 2 ^ 59
def prefixEnd_7621878 : Nat := 4983230072969 + 3 ^ 40 * 7621878 * 2
def baseEnd_7621878 : Nat := 3913686903929435600972627

theorem tailTrace_7621878 : CollatzResearch.WordTrace tailWord_7621878 prefixEnd_7621878 3913686903929435600972627 := by
  unfold tailWord_7621878
  simp only [CollatzResearch.WordTrace]
  refine ⟨17374545542577824623302143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 185328485787496795981889525 17374545542577824623302143)
  ·
    refine ⟨26061818313866736934953215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17374545542577824623302143 26061818313866736934953215)
    ·
      refine ⟨39092727470800105402429823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26061818313866736934953215 39092727470800105402429823)
      ·
        refine ⟨58639091206200158103644735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39092727470800105402429823 58639091206200158103644735)
        ·
          refine ⟨87958636809300237155467103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58639091206200158103644735 87958636809300237155467103)
          ·
            refine ⟨131937955213950355733200655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87958636809300237155467103 131937955213950355733200655)
            ·
              refine ⟨197906932820925533599800983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131937955213950355733200655 197906932820925533599800983)
              ·
                refine ⟨296860399231388300399701475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 197906932820925533599800983 296860399231388300399701475)
                ·
                  refine ⟨445290598847082450599552213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 296860399231388300399701475 445290598847082450599552213)
                  ·
                    refine ⟨10436498410478494935927005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 445290598847082450599552213 10436498410478494935927005)
                    ·
                      refine ⟨3913686903929435600972627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10436498410478494935927005 3913686903929435600972627)
                      ·
                        rfl

theorem cell23_7621878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 1, 7, 3].length) (baseStart_7621878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7621878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7621878 prefixEnd_7621878 := by exact prefixLift 7621878
  have htrace : WordTrace (prefixWord ++ tailWord_7621878) baseStart_7621878 baseEnd_7621878 := by
    simpa [prefixWord, tailWord_7621878, baseEnd_7621878] using wordTrace_append hprefix tailTrace_7621878
  have hstable : (prefixWord ++ tailWord_7621878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7621878).length < 2 ^ (prefixWord ++ tailWord_7621878).sum := by decide
  have hdescent : baseEnd_7621878 < baseStart_7621878 := by decide
  rcases family_descends (prefixWord ++ tailWord_7621878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7621905 : List Nat := [1, 2, 2, 1, 1, 4, 3, 2, 2, 3, 2]
def baseStart_7621905 : Nat := 118140960795 + 7621905 * 2 ^ 59
def prefixEnd_7621905 : Nat := 4983230072969 + 3 ^ 40 * 7621905 * 2
def baseEnd_7621905 : Nat := 3913700767907106995335003

theorem tailTrace_7621905 : CollatzResearch.WordTrace tailWord_7621905 prefixEnd_7621905 3913700767907106995335003 := by
  unfold tailWord_7621905
  simp only [CollatzResearch.WordTrace]
  refine ⟨277993713452147377584067169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185329142301431585056044779 277993713452147377584067169)
  ·
    refine ⟨208495285089110533188050377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277993713452147377584067169 208495285089110533188050377)
    ·
      refine ⟨156371463816832899891037783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208495285089110533188050377 156371463816832899891037783)
      ·
        refine ⟨234557195725249349836556675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156371463816832899891037783 234557195725249349836556675)
        ·
          refine ⟨351835793587874024754835013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234557195725249349836556675 351835793587874024754835013)
          ·
            refine ⟨65969211297726379641531565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 351835793587874024754835013 65969211297726379641531565)
            ·
              refine ⟨24738454236647392365574337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65969211297726379641531565 24738454236647392365574337)
              ·
                refine ⟨18553840677485544274180753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24738454236647392365574337 18553840677485544274180753)
                ·
                  refine ⟨13915380508114158205635565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18553840677485544274180753 13915380508114158205635565)
                  ·
                    refine ⟨5218267690542809327113337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13915380508114158205635565 5218267690542809327113337)
                    ·
                      refine ⟨3913700767907106995335003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5218267690542809327113337 3913700767907106995335003)
                      ·
                        rfl

theorem cell23_7621905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 3, 2].length) (baseStart_7621905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7621905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7621905 prefixEnd_7621905 := by exact prefixLift 7621905
  have htrace : WordTrace (prefixWord ++ tailWord_7621905) baseStart_7621905 baseEnd_7621905 := by
    simpa [prefixWord, tailWord_7621905, baseEnd_7621905] using wordTrace_append hprefix tailTrace_7621905
  have hstable : (prefixWord ++ tailWord_7621905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7621905).length < 2 ^ (prefixWord ++ tailWord_7621905).sum := by decide
  have hdescent : baseEnd_7621905 < baseStart_7621905 := by decide
  rcases family_descends (prefixWord ++ tailWord_7621905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7621906 : List Nat := [3, 2, 4, 2, 2, 1, 1, 1, 3, 4]
def baseStart_7621906 : Nat := 118140960795 + 7621906 * 2 ^ 59
def prefixEnd_7621906 : Nat := 4983230072969 + 3 ^ 40 * 7621906 * 2
def baseEnd_7621906 : Nat := 1304567093795920497140833

theorem tailTrace_7621906 : CollatzResearch.WordTrace tailWord_7621906 prefixEnd_7621906 1304567093795920497140833 := by
  unfold tailWord_7621906
  simp only [CollatzResearch.WordTrace]
  refine ⟨69498437481285938688713393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185329166616762503169902381 69498437481285938688713393)
  ·
    refine ⟨52123828110964454016535045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69498437481285938688713393 52123828110964454016535045)
    ·
      refine ⟨9773217770805835128100321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52123828110964454016535045 9773217770805835128100321)
      ·
        refine ⟨7329913328104376346075241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9773217770805835128100321 7329913328104376346075241)
        ·
          refine ⟨5497434996078282259556431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7329913328104376346075241 5497434996078282259556431)
          ·
            refine ⟨8246152494117423389334647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5497434996078282259556431 8246152494117423389334647)
            ·
              refine ⟨12369228741176135084001971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8246152494117423389334647 12369228741176135084001971)
              ·
                refine ⟨18553843111764202626002957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12369228741176135084001971 18553843111764202626002957)
                ·
                  refine ⟨6957691166911575984751109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18553843111764202626002957 6957691166911575984751109)
                  ·
                    refine ⟨1304567093795920497140833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6957691166911575984751109 1304567093795920497140833)
                    ·
                      rfl

theorem cell23_7621906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_7621906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7621906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7621906 prefixEnd_7621906 := by exact prefixLift 7621906
  have htrace : WordTrace (prefixWord ++ tailWord_7621906) baseStart_7621906 baseEnd_7621906 := by
    simpa [prefixWord, tailWord_7621906, baseEnd_7621906] using wordTrace_append hprefix tailTrace_7621906
  have hstable : (prefixWord ++ tailWord_7621906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7621906).length < 2 ^ (prefixWord ++ tailWord_7621906).sum := by decide
  have hdescent : baseEnd_7621906 < baseStart_7621906 := by decide
  rcases family_descends (prefixWord ++ tailWord_7621906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7621912 : List Nat := [2, 1, 2, 3, 1, 5, 1, 1, 3, 1, 3]
def baseStart_7621912 : Nat := 118140960795 + 7621912 * 2 ^ 59
def prefixEnd_7621912 : Nat := 4983230072969 + 3 ^ 40 * 7621912 * 2
def baseEnd_7621912 : Nat := 3913704362271688467947471

theorem tailTrace_7621912 : CollatzResearch.WordTrace tailWord_7621912 prefixEnd_7621912 3913704362271688467947471 := by
  unfold tailWord_7621912
  simp only [CollatzResearch.WordTrace]
  refine ⟨138996984381561008889785995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185329312508748011853047993 138996984381561008889785995)
  ·
    refine ⟨208495476572341513334678993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138996984381561008889785995 208495476572341513334678993)
    ·
      refine ⟨156371607429256135001009245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208495476572341513334678993 156371607429256135001009245)
      ·
        refine ⟨58639352785971050625378467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156371607429256135001009245 58639352785971050625378467)
        ·
          refine ⟨87959029178956575938067701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58639352785971050625378467 87959029178956575938067701)
          ·
            refine ⟨8246158985527178994193847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 87959029178956575938067701 8246158985527178994193847)
            ·
              refine ⟨12369238478290768491290771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8246158985527178994193847 12369238478290768491290771)
              ·
                refine ⟨18553857717436152736936157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12369238478290768491290771 18553857717436152736936157)
                ·
                  refine ⟨6957696644038557276351059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18553857717436152736936157 6957696644038557276351059)
                  ·
                    refine ⟨10436544966057835914526589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6957696644038557276351059 10436544966057835914526589)
                    ·
                      refine ⟨3913704362271688467947471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10436544966057835914526589 3913704362271688467947471)
                      ·
                        rfl

theorem cell23_7621912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 1, 1, 3, 1, 3].length) (baseStart_7621912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7621912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7621912 prefixEnd_7621912 := by exact prefixLift 7621912
  have htrace : WordTrace (prefixWord ++ tailWord_7621912) baseStart_7621912 baseEnd_7621912 := by
    simpa [prefixWord, tailWord_7621912, baseEnd_7621912] using wordTrace_append hprefix tailTrace_7621912
  have hstable : (prefixWord ++ tailWord_7621912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7621912).length < 2 ^ (prefixWord ++ tailWord_7621912).sum := by decide
  have hdescent : baseEnd_7621912 < baseStart_7621912 := by decide
  rcases family_descends (prefixWord ++ tailWord_7621912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7621935 : List Nat := [1, 1, 2, 1, 2, 1, 3, 3, 5, 2, 2]
def baseStart_7621935 : Nat := 118140960795 + 7621935 * 2 ^ 59
def prefixEnd_7621935 : Nat := 4983230072969 + 3 ^ 40 * 7621935 * 2
def baseEnd_7621935 : Nat := 3913716172326741877959865

theorem tailTrace_7621935 : CollatzResearch.WordTrace tailWord_7621935 prefixEnd_7621935 3913716172326741877959865 := by
  unfold tailWord_7621935
  simp only [CollatzResearch.WordTrace]
  refine ⟨277994807642038692707659259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185329871761359128471772839 277994807642038692707659259)
  ·
    refine ⟨416992211463058039061488889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277994807642038692707659259 416992211463058039061488889)
    ·
      refine ⟨312744158597293529296116667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 416992211463058039061488889 312744158597293529296116667)
      ·
        refine ⟨469116237895940293944175001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312744158597293529296116667 469116237895940293944175001)
        ·
          refine ⟨351837178421955220458131251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 469116237895940293944175001 351837178421955220458131251)
          ·
            refine ⟨527755767632932830687196877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 351837178421955220458131251 527755767632932830687196877)
            ·
              refine ⟨197908412862349811507698829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 527755767632932830687196877 197908412862349811507698829)
              ·
                refine ⟨74215654823381179315387061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 197908412862349811507698829 74215654823381179315387061)
                ·
                  refine ⟨6957717639691985560817537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74215654823381179315387061 6957717639691985560817537)
                  ·
                    refine ⟨5218288229768989170613153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6957717639691985560817537 5218288229768989170613153)
                    ·
                      refine ⟨3913716172326741877959865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5218288229768989170613153 3913716172326741877959865)
                      ·
                        rfl

theorem cell23_7621935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 3, 5, 2, 2].length) (baseStart_7621935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7621935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7621935 prefixEnd_7621935 := by exact prefixLift 7621935
  have htrace : WordTrace (prefixWord ++ tailWord_7621935) baseStart_7621935 baseEnd_7621935 := by
    simpa [prefixWord, tailWord_7621935, baseEnd_7621935] using wordTrace_append hprefix tailTrace_7621935
  have hstable : (prefixWord ++ tailWord_7621935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7621935).length < 2 ^ (prefixWord ++ tailWord_7621935).sum := by decide
  have hdescent : baseEnd_7621935 < baseStart_7621935 := by decide
  rcases family_descends (prefixWord ++ tailWord_7621935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7621945 : List Nat := [1, 2, 1, 6, 2, 1, 1, 2, 1, 6]
def baseStart_7621945 : Nat := 118140960795 + 7621945 * 2 ^ 59
def prefixEnd_7621945 : Nat := 4983230072969 + 3 ^ 40 * 7621945 * 2
def baseEnd_7621945 : Nat := 1304573769044428946278273

theorem tailTrace_7621945 : CollatzResearch.WordTrace tailWord_7621945 prefixEnd_7621945 1304573769044428946278273 := by
  unfold tailWord_7621945
  simp only [CollatzResearch.WordTrace]
  refine ⟨277995172372002464415523289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185330114914668309610348859 277995172372002464415523289)
  ·
    refine ⟨208496379279001848311642467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277995172372002464415523289 208496379279001848311642467)
    ·
      refine ⟨312744568918502772467463701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208496379279001848311642467 312744568918502772467463701)
      ·
        refine ⟨14659901668054817459412361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 312744568918502772467463701 14659901668054817459412361)
        ·
          refine ⟨10994926251041113094559271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14659901668054817459412361 10994926251041113094559271)
          ·
            refine ⟨16492389376561669641838907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10994926251041113094559271 16492389376561669641838907)
            ·
              refine ⟨24738584064842504462758361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16492389376561669641838907 24738584064842504462758361)
              ·
                refine ⟨18553938048631878347068771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24738584064842504462758361 18553938048631878347068771)
                ·
                  refine ⟨27830907072947817520603157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18553938048631878347068771 27830907072947817520603157)
                  ·
                    refine ⟨1304573769044428946278273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27830907072947817520603157 1304573769044428946278273)
                    ·
                      rfl

theorem cell23_7621945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 2, 1, 6].length) (baseStart_7621945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7621945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7621945 prefixEnd_7621945 := by exact prefixLift 7621945
  have htrace : WordTrace (prefixWord ++ tailWord_7621945) baseStart_7621945 baseEnd_7621945 := by
    simpa [prefixWord, tailWord_7621945, baseEnd_7621945] using wordTrace_append hprefix tailTrace_7621945
  have hstable : (prefixWord ++ tailWord_7621945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7621945).length < 2 ^ (prefixWord ++ tailWord_7621945).sum := by decide
  have hdescent : baseEnd_7621945 < baseStart_7621945 := by decide
  rcases family_descends (prefixWord ++ tailWord_7621945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7621948 : List Nat := [2, 2, 2, 2, 1, 3, 1, 1, 3, 2, 4]
def baseStart_7621948 : Nat := 118140960795 + 7621948 * 2 ^ 59
def prefixEnd_7621948 : Nat := 4983230072969 + 3 ^ 40 * 7621948 * 2
def baseEnd_7621948 : Nat := 3913722847575250327097305

theorem tailTrace_7621948 : CollatzResearch.WordTrace tailWord_7621948 prefixEnd_7621948 3913722847575250327097305 := by
  unfold tailWord_7621948
  simp only [CollatzResearch.WordTrace]
  refine ⟨138997640895495797963941249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185330187860661063951921665 138997640895495797963941249)
  ·
    refine ⟨104248230671621848472955937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138997640895495797963941249 104248230671621848472955937)
    ·
      refine ⟨78186173003716386354716953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104248230671621848472955937 78186173003716386354716953)
      ·
        refine ⟨58639629752787289766037715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78186173003716386354716953 58639629752787289766037715)
        ·
          refine ⟨87959444629180934649056573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58639629752787289766037715 87959444629180934649056573)
          ·
            refine ⟨32984791735942850493396215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87959444629180934649056573 32984791735942850493396215)
            ·
              refine ⟨49477187603914275740094323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32984791735942850493396215 49477187603914275740094323)
              ·
                refine ⟨74215781405871413610141485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49477187603914275740094323 74215781405871413610141485)
                ·
                  refine ⟨27830918027201780103803057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74215781405871413610141485 27830918027201780103803057)
                  ·
                    refine ⟨20873188520401335077852293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27830918027201780103803057 20873188520401335077852293)
                    ·
                      refine ⟨3913722847575250327097305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20873188520401335077852293 3913722847575250327097305)
                      ·
                        rfl

theorem cell23_7621948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 1, 3, 2, 4].length) (baseStart_7621948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7621948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7621948 prefixEnd_7621948 := by exact prefixLift 7621948
  have htrace : WordTrace (prefixWord ++ tailWord_7621948) baseStart_7621948 baseEnd_7621948 := by
    simpa [prefixWord, tailWord_7621948, baseEnd_7621948] using wordTrace_append hprefix tailTrace_7621948
  have hstable : (prefixWord ++ tailWord_7621948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7621948).length < 2 ^ (prefixWord ++ tailWord_7621948).sum := by decide
  have hdescent : baseEnd_7621948 < baseStart_7621948 := by decide
  rcases family_descends (prefixWord ++ tailWord_7621948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7621949 : List Nat := [1, 4, 1, 5, 1, 1, 3, 1, 1, 5]
def baseStart_7621949 : Nat := 118140960795 + 7621949 * 2 ^ 59
def prefixEnd_7621949 : Nat := 4983230072969 + 3 ^ 40 * 7621949 * 2
def baseEnd_7621949 : Nat := 1304574453685301607728267

theorem tailTrace_7621949 : CollatzResearch.WordTrace tailWord_7621949 prefixEnd_7621949 1304574453685301607728267 := by
  unfold tailWord_7621949
  simp only [CollatzResearch.WordTrace]
  refine ⟨277995318263987973098668901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185330212175991982065779267 277995318263987973098668901)
  ·
    refine ⟨52124122174497744956000419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 277995318263987973098668901 52124122174497744956000419)
    ·
      refine ⟨78186183261746617434000629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52124122174497744956000419 78186183261746617434000629)
      ·
        refine ⟨7329954680788745384437559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 78186183261746617434000629 7329954680788745384437559)
        ·
          refine ⟨10994932021183118076656339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7329954680788745384437559 10994932021183118076656339)
          ·
            refine ⟨16492398031774677114984509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10994932021183118076656339 16492398031774677114984509)
            ·
              refine ⟨6184649261915503918119191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16492398031774677114984509 6184649261915503918119191)
              ·
                refine ⟨9276973892873255877178787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6184649261915503918119191 9276973892873255877178787)
                ·
                  refine ⟨13915460839309883815768181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9276973892873255877178787 13915460839309883815768181)
                  ·
                    refine ⟨1304574453685301607728267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13915460839309883815768181 1304574453685301607728267)
                    ·
                      rfl

theorem cell23_7621949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 3, 1, 1, 5].length) (baseStart_7621949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7621949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7621949 prefixEnd_7621949 := by exact prefixLift 7621949
  have htrace : WordTrace (prefixWord ++ tailWord_7621949) baseStart_7621949 baseEnd_7621949 := by
    simpa [prefixWord, tailWord_7621949, baseEnd_7621949] using wordTrace_append hprefix tailTrace_7621949
  have hstable : (prefixWord ++ tailWord_7621949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7621949).length < 2 ^ (prefixWord ++ tailWord_7621949).sum := by decide
  have hdescent : baseEnd_7621949 < baseStart_7621949 := by decide
  rcases family_descends (prefixWord ++ tailWord_7621949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7621968 : List Nat := [2, 1, 1, 1, 1, 5, 1, 2, 3, 3, 3]
def baseStart_7621968 : Nat := 118140960795 + 7621968 * 2 ^ 59
def prefixEnd_7621968 : Nat := 4983230072969 + 3 ^ 40 * 7621968 * 2
def baseEnd_7621968 : Nat := 3913733117188340248847213

theorem tailTrace_7621968 : CollatzResearch.WordTrace tailWord_7621968 prefixEnd_7621968 3913733117188340248847213 := by
  unfold tailWord_7621968
  simp only [CollatzResearch.WordTrace]
  refine ⟨138998005625459569671805279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185330674167279426229073705 138998005625459569671805279)
  ·
    refine ⟨208497008438189354507707919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138998005625459569671805279 208497008438189354507707919)
    ·
      refine ⟨312745512657284031761561879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208497008438189354507707919 312745512657284031761561879)
      ·
        refine ⟨469118268985926047642342819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312745512657284031761561879 469118268985926047642342819)
        ·
          refine ⟨703677403478889071463514229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 469118268985926047642342819 703677403478889071463514229)
          ·
            refine ⟨65969756576145850449704459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 703677403478889071463514229 65969756576145850449704459)
            ·
              refine ⟨98954634864218775674556689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65969756576145850449704459 98954634864218775674556689)
              ·
                refine ⟨74215976148164081755917517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98954634864218775674556689 74215976148164081755917517)
                ·
                  refine ⟨27830991055561530658469069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74215976148164081755917517 27830991055561530658469069)
                  ·
                    refine ⟨10436621645835573996925901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27830991055561530658469069 10436621645835573996925901)
                    ·
                      refine ⟨3913733117188340248847213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10436621645835573996925901 3913733117188340248847213)
                      ·
                        rfl

theorem cell23_7621968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 2, 3, 3, 3].length) (baseStart_7621968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7621968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7621968 prefixEnd_7621968 := by exact prefixLift 7621968
  have htrace : WordTrace (prefixWord ++ tailWord_7621968) baseStart_7621968 baseEnd_7621968 := by
    simpa [prefixWord, tailWord_7621968, baseEnd_7621968] using wordTrace_append hprefix tailTrace_7621968
  have hstable : (prefixWord ++ tailWord_7621968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7621968).length < 2 ^ (prefixWord ++ tailWord_7621968).sum := by decide
  have hdescent : baseEnd_7621968 < baseStart_7621968 := by decide
  rcases family_descends (prefixWord ++ tailWord_7621968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7621969 : List Nat := [1, 2, 2, 1, 4, 1, 3, 4, 1, 2, 2]
def baseStart_7621969 : Nat := 118140960795 + 7621969 * 2 ^ 59
def prefixEnd_7621969 : Nat := 4983230072969 + 3 ^ 40 * 7621969 * 2
def baseEnd_7621969 : Nat := 3913733630668994744934709

theorem tailTrace_7621969 : CollatzResearch.WordTrace tailWord_7621969 prefixEnd_7621969 3913733630668994744934709 := by
  unfold tailWord_7621969
  simp only [CollatzResearch.WordTrace]
  refine ⟨277996047723915516514396961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185330698482610344342931307 277996047723915516514396961)
  ·
    refine ⟨208497035792936637385797721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277996047723915516514396961 208497035792936637385797721)
    ·
      refine ⟨156372776844702478039348291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208497035792936637385797721 156372776844702478039348291)
      ·
        refine ⟨234559165267053717059022437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156372776844702478039348291 234559165267053717059022437)
        ·
          refine ⟨43979843487572571948566707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 234559165267053717059022437 43979843487572571948566707)
          ·
            refine ⟨65969765231358857922850061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43979843487572571948566707 65969765231358857922850061)
            ·
              refine ⟨24738661961759571721068773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65969765231358857922850061 24738661961759571721068773)
              ·
                refine ⟨4638499117829919697700395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24738661961759571721068773 4638499117829919697700395)
                ·
                  refine ⟨6957748676744879546550593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4638499117829919697700395 6957748676744879546550593)
                  ·
                    refine ⟨5218311507558659659912945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6957748676744879546550593 5218311507558659659912945)
                    ·
                      refine ⟨3913733630668994744934709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5218311507558659659912945 3913733630668994744934709)
                      ·
                        rfl

theorem cell23_7621969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 4, 1, 2, 2].length) (baseStart_7621969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7621969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7621969 prefixEnd_7621969 := by exact prefixLift 7621969
  have htrace : WordTrace (prefixWord ++ tailWord_7621969) baseStart_7621969 baseEnd_7621969 := by
    simpa [prefixWord, tailWord_7621969, baseEnd_7621969] using wordTrace_append hprefix tailTrace_7621969
  have hstable : (prefixWord ++ tailWord_7621969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7621969).length < 2 ^ (prefixWord ++ tailWord_7621969).sum := by decide
  have hdescent : baseEnd_7621969 < baseStart_7621969 := by decide
  rcases family_descends (prefixWord ++ tailWord_7621969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7621971 : List Nat := [1, 1, 1, 2, 1, 1, 5, 1, 1, 9]
def baseStart_7621971 : Nat := 118140960795 + 7621971 * 2 ^ 59
def prefixEnd_7621971 : Nat := 4983230072969 + 3 ^ 40 * 7621971 * 2
def baseEnd_7621971 : Nat := 1304578219210101245703233

theorem tailTrace_7621971 : CollatzResearch.WordTrace tailWord_7621971 prefixEnd_7621971 1304578219210101245703233 := by
  unfold tailWord_7621971
  simp only [CollatzResearch.WordTrace]
  refine ⟨277996120669908270855969767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185330747113272180570646511 277996120669908270855969767)
  ·
    refine ⟨416994181004862406283954651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277996120669908270855969767 416994181004862406283954651)
    ·
      refine ⟨625491271507293609425931977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 416994181004862406283954651 625491271507293609425931977)
      ·
        refine ⟨469118453630470207069448983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 625491271507293609425931977 469118453630470207069448983)
        ·
          refine ⟨703677680445705310604173475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 469118453630470207069448983 703677680445705310604173475)
          ·
            refine ⟨1055516520668557965906260213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 703677680445705310604173475 1055516520668557965906260213)
            ·
              refine ⟨98954673812677309303711895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1055516520668557965906260213 98954673812677309303711895)
              ·
                refine ⟨148432010719015963955567843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98954673812677309303711895 148432010719015963955567843)
                ·
                  refine ⟨222648016078523945933351765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 148432010719015963955567843 222648016078523945933351765)
                  ·
                    refine ⟨1304578219210101245703233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 222648016078523945933351765 1304578219210101245703233)
                    ·
                      rfl

theorem cell23_7621971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 9].length) (baseStart_7621971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7621971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7621971 prefixEnd_7621971 := by exact prefixLift 7621971
  have htrace : WordTrace (prefixWord ++ tailWord_7621971) baseStart_7621971 baseEnd_7621971 := by
    simpa [prefixWord, tailWord_7621971, baseEnd_7621971] using wordTrace_append hprefix tailTrace_7621971
  have hstable : (prefixWord ++ tailWord_7621971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7621971).length < 2 ^ (prefixWord ++ tailWord_7621971).sum := by decide
  have hdescent : baseEnd_7621971 < baseStart_7621971 := by decide
  rcases family_descends (prefixWord ++ tailWord_7621971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7622012 : List Nat := [2, 2, 2, 1, 1, 1, 5, 3, 1, 3, 2]
def baseStart_7622012 : Nat := 118140960795 + 7622012 * 2 ^ 59
def prefixEnd_7622012 : Nat := 4983230072969 + 3 ^ 40 * 7622012 * 2
def baseEnd_7622012 : Nat := 3913755710337138076697011

theorem tailTrace_7622012 : CollatzResearch.WordTrace tailWord_7622012 prefixEnd_7622012 3913755710337138076697011 := by
  unfold tailWord_7622012
  simp only [CollatzResearch.WordTrace]
  refine ⟨138998808031379867429106145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185331744041839823238808193 138998808031379867429106145)
  ·
    refine ⟨104249106023534900571829609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138998808031379867429106145 104249106023534900571829609)
    ·
      refine ⟨78186829517651175428872207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104249106023534900571829609 78186829517651175428872207)
      ·
        refine ⟨117280244276476763143308311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78186829517651175428872207 117280244276476763143308311)
        ·
          refine ⟨175920366414715144714962467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117280244276476763143308311 175920366414715144714962467)
          ·
            refine ⟨263880549622072717072443701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175920366414715144714962467 263880549622072717072443701)
            ·
              refine ⟨24738801527069317225541597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 263880549622072717072443701 24738801527069317225541597)
              ·
                refine ⟨9277050572650993959578099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24738801527069317225541597 9277050572650993959578099)
                ·
                  refine ⟨13915575858976490939367149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9277050572650993959578099 13915575858976490939367149)
                  ·
                    refine ⟨5218340947116184102262681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13915575858976490939367149 5218340947116184102262681)
                    ·
                      refine ⟨3913755710337138076697011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5218340947116184102262681 3913755710337138076697011)
                      ·
                        rfl

theorem cell23_7622012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 3, 1, 3, 2].length) (baseStart_7622012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7622012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7622012 prefixEnd_7622012 := by exact prefixLift 7622012
  have htrace : WordTrace (prefixWord ++ tailWord_7622012) baseStart_7622012 baseEnd_7622012 := by
    simpa [prefixWord, tailWord_7622012, baseEnd_7622012] using wordTrace_append hprefix tailTrace_7622012
  have hstable : (prefixWord ++ tailWord_7622012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7622012).length < 2 ^ (prefixWord ++ tailWord_7622012).sum := by decide
  have hdescent : baseEnd_7622012 < baseStart_7622012 := by decide
  rcases family_descends (prefixWord ++ tailWord_7622012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7622019 : List Nat := [1, 1, 1, 3, 5, 3, 1, 2, 2, 1, 3]
def baseStart_7622019 : Nat := 118140960795 + 7622019 * 2 ^ 59
def prefixEnd_7622019 : Nat := 4983230072969 + 3 ^ 40 * 7622019 * 2
def baseEnd_7622019 : Nat := 3913759304701719549309479

theorem tailTrace_7622019 : CollatzResearch.WordTrace tailWord_7622019 prefixEnd_7622019 3913759304701719549309479 := by
  unfold tailWord_7622019
  simp only [CollatzResearch.WordTrace]
  refine ⟨277997871373734375053717111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185331914249156250035811407 277997871373734375053717111)
  ·
    refine ⟨416996807060601562580575667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277997871373734375053717111 416996807060601562580575667)
    ·
      refine ⟨625495210590902343870863501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 416996807060601562580575667 625495210590902343870863501)
      ·
        refine ⟨234560703971588378951573813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 625495210590902343870863501 234560703971588378951573813)
        ·
          refine ⟨21990065997336410526710045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 234560703971588378951573813 21990065997336410526710045)
          ·
            refine ⟨8246274749001153947516267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21990065997336410526710045 8246274749001153947516267)
            ·
              refine ⟨12369412123501730921274401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8246274749001153947516267 12369412123501730921274401)
              ·
                refine ⟨9277059092626298190955801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12369412123501730921274401 9277059092626298190955801)
                ·
                  refine ⟨6957794319469723643216851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9277059092626298190955801 6957794319469723643216851)
                  ·
                    refine ⟨10436691479204585464825277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6957794319469723643216851 10436691479204585464825277)
                    ·
                      refine ⟨3913759304701719549309479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10436691479204585464825277 3913759304701719549309479)
                      ·
                        rfl

theorem cell23_7622019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 1, 2, 2, 1, 3].length) (baseStart_7622019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7622019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7622019 prefixEnd_7622019 := by exact prefixLift 7622019
  have htrace : WordTrace (prefixWord ++ tailWord_7622019) baseStart_7622019 baseEnd_7622019 := by
    simpa [prefixWord, tailWord_7622019, baseEnd_7622019] using wordTrace_append hprefix tailTrace_7622019
  have hstable : (prefixWord ++ tailWord_7622019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7622019).length < 2 ^ (prefixWord ++ tailWord_7622019).sum := by decide
  have hdescent : baseEnd_7622019 < baseStart_7622019 := by decide
  rcases family_descends (prefixWord ++ tailWord_7622019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7622036 : List Nat := [2, 4, 2, 1, 2, 2, 3, 1, 2, 1, 3]
def baseStart_7622036 : Nat := 118140960795 + 7622036 * 2 ^ 59
def prefixEnd_7622036 : Nat := 4983230072969 + 3 ^ 40 * 7622036 * 2
def baseEnd_7622036 : Nat := 3913768033872845982796901

theorem tailTrace_7622036 : CollatzResearch.WordTrace tailWord_7622036 prefixEnd_7622036 3913768033872845982796901 := by
  unfold tailWord_7622036
  simp only [CollatzResearch.WordTrace]
  refine ⟨138999245707336393478542981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185332327609781857971390641 138999245707336393478542981)
  ·
    refine ⟨26062358570125573777226809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138999245707336393478542981 26062358570125573777226809)
    ·
      refine ⟨19546768927594180332920107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26062358570125573777226809 19546768927594180332920107)
      ·
        refine ⟨29320153391391270499380161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19546768927594180332920107 29320153391391270499380161)
        ·
          refine ⟨21990115043543452874535121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29320153391391270499380161 21990115043543452874535121)
          ·
            refine ⟨16492586282657589655901341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21990115043543452874535121 16492586282657589655901341)
            ·
              refine ⟨6184719855996596120963003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16492586282657589655901341 6184719855996596120963003)
              ·
                refine ⟨9277079783994894181444505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6184719855996596120963003 9277079783994894181444505)
                ·
                  refine ⟨6957809837996170636083379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9277079783994894181444505 6957809837996170636083379)
                  ·
                    refine ⟨10436714756994255954125069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6957809837996170636083379 10436714756994255954125069)
                    ·
                      refine ⟨3913768033872845982796901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10436714756994255954125069 3913768033872845982796901)
                      ·
                        rfl

theorem cell23_7622036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 3, 1, 2, 1, 3].length) (baseStart_7622036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7622036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7622036 prefixEnd_7622036 := by exact prefixLift 7622036
  have htrace : WordTrace (prefixWord ++ tailWord_7622036) baseStart_7622036 baseEnd_7622036 := by
    simpa [prefixWord, tailWord_7622036, baseEnd_7622036] using wordTrace_append hprefix tailTrace_7622036
  have hstable : (prefixWord ++ tailWord_7622036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7622036).length < 2 ^ (prefixWord ++ tailWord_7622036).sum := by decide
  have hdescent : baseEnd_7622036 < baseStart_7622036 := by decide
  rcases family_descends (prefixWord ++ tailWord_7622036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7622048 : List Nat := [2, 1, 1, 4, 1, 2, 1, 4, 7]
def baseStart_7622048 : Nat := 118140960795 + 7622048 * 2 ^ 59
def prefixEnd_7622048 : Nat := 4983230072969 + 3 ^ 40 * 7622048 * 2
def baseEnd_7622048 : Nat := 434863799515633326205205

theorem tailTrace_7622048 : CollatzResearch.WordTrace tailWord_7622048 prefixEnd_7622048 434863799515633326205205 := by
  unfold tailWord_7622048
  simp only [CollatzResearch.WordTrace]
  refine ⟨138999464545314656503261399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185332619393752875337681865 138999464545314656503261399)
  ·
    refine ⟨208499196817971984754892099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138999464545314656503261399 208499196817971984754892099)
    ·
      refine ⟨312748795226957977132338149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208499196817971984754892099 312748795226957977132338149)
      ·
        refine ⟨58640399105054620712313403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 312748795226957977132338149 58640399105054620712313403)
        ·
          refine ⟨87960598657581931068470105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58640399105054620712313403 87960598657581931068470105)
          ·
            refine ⟨65970448993186448301352579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87960598657581931068470105 65970448993186448301352579)
            ·
              refine ⟨98955673489779672452028869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65970448993186448301352579 98955673489779672452028869)
              ·
                refine ⟨18554188779333688584755413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98955673489779672452028869 18554188779333688584755413)
                ·
                  refine ⟨434863799515633326205205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18554188779333688584755413 434863799515633326205205)
                  ·
                    rfl

theorem cell23_7622048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 4, 7].length) (baseStart_7622048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7622048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7622048 prefixEnd_7622048 := by exact prefixLift 7622048
  have htrace : WordTrace (prefixWord ++ tailWord_7622048) baseStart_7622048 baseEnd_7622048 := by
    simpa [prefixWord, tailWord_7622048, baseEnd_7622048] using wordTrace_append hprefix tailTrace_7622048
  have hstable : (prefixWord ++ tailWord_7622048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7622048).length < 2 ^ (prefixWord ++ tailWord_7622048).sum := by decide
  have hdescent : baseEnd_7622048 < baseStart_7622048 := by decide
  rcases family_descends (prefixWord ++ tailWord_7622048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7622135 : List Nat := [1, 1, 3, 1, 1, 1, 1, 5, 4, 2, 3]
def baseStart_7622135 : Nat := 118140960795 + 7622135 * 2 ^ 59
def prefixEnd_7622135 : Nat := 4983230072969 + 3 ^ 40 * 7622135 * 2
def baseEnd_7622135 : Nat := 3913818868457641095458945

theorem tailTrace_7622135 : CollatzResearch.WordTrace tailWord_7622135 prefixEnd_7622135 3913818868457641095458945 := by
  unfold tailWord_7622135
  simp only [CollatzResearch.WordTrace]
  refine ⟨278002102241314126864939859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185334734827542751243293239 278002102241314126864939859)
  ·
    refine ⟨417003153361971190297409789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278002102241314126864939859 417003153361971190297409789)
    ·
      refine ⟨156376182510739196361528671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 417003153361971190297409789 156376182510739196361528671)
      ·
        refine ⟨234564273766108794542293007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156376182510739196361528671 234564273766108794542293007)
        ·
          refine ⟨351846410649163191813439511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234564273766108794542293007 351846410649163191813439511)
          ·
            refine ⟨527769615973744787720159267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 351846410649163191813439511 527769615973744787720159267)
            ·
              refine ⟨791654423960617181580238901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 527769615973744787720159267 791654423960617181580238901)
              ·
                refine ⟨74217602246307860773147397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 791654423960617181580238901 74217602246307860773147397)
                ·
                  refine ⟨13915800421182723894965137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74217602246307860773147397 13915800421182723894965137)
                  ·
                    refine ⟨10436850315887042921223853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13915800421182723894965137 10436850315887042921223853)
                    ·
                      refine ⟨3913818868457641095458945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10436850315887042921223853 3913818868457641095458945)
                      ·
                        rfl

theorem cell23_7622135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 5, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 5, 4, 2, 3].length) (baseStart_7622135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7622135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7622135 prefixEnd_7622135 := by exact prefixLift 7622135
  have htrace : WordTrace (prefixWord ++ tailWord_7622135) baseStart_7622135 baseEnd_7622135 := by
    simpa [prefixWord, tailWord_7622135, baseEnd_7622135] using wordTrace_append hprefix tailTrace_7622135
  have hstable : (prefixWord ++ tailWord_7622135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7622135).length < 2 ^ (prefixWord ++ tailWord_7622135).sum := by decide
  have hdescent : baseEnd_7622135 < baseStart_7622135 := by decide
  rcases family_descends (prefixWord ++ tailWord_7622135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7622176 : List Nat := [2, 1, 1, 6, 1, 2, 2, 3, 1, 4]
def baseStart_7622176 : Nat := 118140960795 + 7622176 * 2 ^ 59
def prefixEnd_7622176 : Nat := 4983230072969 + 3 ^ 40 * 7622176 * 2
def baseEnd_7622176 : Nat := 1304613307054825145015419

theorem tailTrace_7622176 : CollatzResearch.WordTrace tailWord_7622176 prefixEnd_7622176 1304613307054825145015419 := by
  unfold tailWord_7622176
  simp only [CollatzResearch.WordTrace]
  refine ⟨139001798817082795433591191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185335731756110393911454921 139001798817082795433591191)
  ·
    refine ⟨208502698225624193150386787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139001798817082795433591191 208502698225624193150386787)
    ·
      refine ⟨312754047338436289725580181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208502698225624193150386787 312754047338436289725580181)
      ·
        refine ⟨14660345968989201080886571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 312754047338436289725580181 14660345968989201080886571)
        ·
          refine ⟨21990518953483801621329857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14660345968989201080886571 21990518953483801621329857)
          ·
            refine ⟨16492889215112851215997393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21990518953483801621329857 16492889215112851215997393)
            ·
              refine ⟨12369666911334638411998045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16492889215112851215997393 12369666911334638411998045)
              ·
                refine ⟨4638625091750489404499267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12369666911334638411998045 4638625091750489404499267)
                ·
                  refine ⟨6957937637625734106748901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4638625091750489404499267 6957937637625734106748901)
                  ·
                    refine ⟨1304613307054825145015419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6957937637625734106748901 1304613307054825145015419)
                    ·
                      rfl

theorem cell23_7622176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 2, 3, 1, 4].length) (baseStart_7622176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7622176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7622176 prefixEnd_7622176 := by exact prefixLift 7622176
  have htrace : WordTrace (prefixWord ++ tailWord_7622176) baseStart_7622176 baseEnd_7622176 := by
    simpa [prefixWord, tailWord_7622176, baseEnd_7622176] using wordTrace_append hprefix tailTrace_7622176
  have hstable : (prefixWord ++ tailWord_7622176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7622176).length < 2 ^ (prefixWord ++ tailWord_7622176).sum := by decide
  have hdescent : baseEnd_7622176 < baseStart_7622176 := by decide
  rcases family_descends (prefixWord ++ tailWord_7622176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7622192 : List Nat := [2, 1, 1, 1, 2, 3, 1, 3, 4, 3, 2]
def baseStart_7622192 : Nat := 118140960795 + 7622192 * 2 ^ 59
def prefixEnd_7622192 : Nat := 4983230072969 + 3 ^ 40 * 7622192 * 2
def baseEnd_7622192 : Nat := 3913848136854947372446183

theorem tailTrace_7622192 : CollatzResearch.WordTrace tailWord_7622192 prefixEnd_7622192 3913848136854947372446183 := by
  unfold tailWord_7622192
  simp only [CollatzResearch.WordTrace]
  refine ⟨139002090601053812799882415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185336120801405083733176553 139002090601053812799882415)
  ·
    refine ⟨208503135901580719199823623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139002090601053812799882415 208503135901580719199823623)
    ·
      refine ⟨312754703852371078799735435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208503135901580719199823623 312754703852371078799735435)
      ·
        refine ⟨469132055778556618199603153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312754703852371078799735435 469132055778556618199603153)
        ·
          refine ⟨351849041833917463649702365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 469132055778556618199603153 351849041833917463649702365)
          ·
            refine ⟨131943390687719048868638387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 351849041833917463649702365 131943390687719048868638387)
            ·
              refine ⟨197915086031578573302957581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131943390687719048868638387 197915086031578573302957581)
              ·
                refine ⟨74218157261841964988609093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 197915086031578573302957581 74218157261841964988609093)
                ·
                  refine ⟨13915904486595368435364205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74218157261841964988609093 13915904486595368435364205)
                  ·
                    refine ⟨5218464182473263163261577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13915904486595368435364205 5218464182473263163261577)
                    ·
                      refine ⟨3913848136854947372446183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5218464182473263163261577 3913848136854947372446183)
                      ·
                        rfl

theorem cell23_7622192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 3, 4, 3, 2].length) (baseStart_7622192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7622192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7622192 prefixEnd_7622192 := by exact prefixLift 7622192
  have htrace : WordTrace (prefixWord ++ tailWord_7622192) baseStart_7622192 baseEnd_7622192 := by
    simpa [prefixWord, tailWord_7622192, baseEnd_7622192] using wordTrace_append hprefix tailTrace_7622192
  have hstable : (prefixWord ++ tailWord_7622192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7622192).length < 2 ^ (prefixWord ++ tailWord_7622192).sum := by decide
  have hdescent : baseEnd_7622192 < baseStart_7622192 := by decide
  rcases family_descends (prefixWord ++ tailWord_7622192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7622199 : List Nat := [1, 1, 3, 1, 2, 5, 2, 1, 3, 1, 3]
def baseStart_7622199 : Nat := 118140960795 + 7622199 * 2 ^ 59
def prefixEnd_7622199 : Nat := 4983230072969 + 3 ^ 40 * 7622199 * 2
def baseEnd_7622199 : Nat := 3913851731219528845058651

theorem tailTrace_7622199 : CollatzResearch.WordTrace tailWord_7622199 prefixEnd_7622199 3913851731219528845058651 := by
  unfold tailWord_7622199
  simp only [CollatzResearch.WordTrace]
  refine ⟨278004436513082265795269651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185336291008721510530179767 278004436513082265795269651)
  ·
    refine ⟨417006654769623398692904477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278004436513082265795269651 417006654769623398692904477)
    ·
      refine ⟨156377495538608774509839179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 417006654769623398692904477 156377495538608774509839179)
      ·
        refine ⟨234566243307913161764758769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156377495538608774509839179 234566243307913161764758769)
        ·
          refine ⟨175924682480934871323569077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234566243307913161764758769 175924682480934871323569077)
          ·
            refine ⟨16492938982587644186584601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 175924682480934871323569077 16492938982587644186584601)
            ·
              refine ⟨12369704236940733139938451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16492938982587644186584601 12369704236940733139938451)
              ·
                refine ⟨18554556355411099709907677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12369704236940733139938451 18554556355411099709907677)
                ·
                  refine ⟨6957958633279162391215379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18554556355411099709907677 6957958633279162391215379)
                  ·
                    refine ⟨10436937949918743586823069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6957958633279162391215379 10436937949918743586823069)
                    ·
                      refine ⟨3913851731219528845058651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10436937949918743586823069 3913851731219528845058651)
                      ·
                        rfl

theorem cell23_7622199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 2, 1, 3, 1, 3].length) (baseStart_7622199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7622199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7622199 prefixEnd_7622199 := by exact prefixLift 7622199
  have htrace : WordTrace (prefixWord ++ tailWord_7622199) baseStart_7622199 baseEnd_7622199 := by
    simpa [prefixWord, tailWord_7622199, baseEnd_7622199] using wordTrace_append hprefix tailTrace_7622199
  have hstable : (prefixWord ++ tailWord_7622199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7622199).length < 2 ^ (prefixWord ++ tailWord_7622199).sum := by decide
  have hdescent : baseEnd_7622199 < baseStart_7622199 := by decide
  rcases family_descends (prefixWord ++ tailWord_7622199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7622222 : List Nat := [4, 1, 1, 1, 1, 2, 1, 1, 1, 8, 2]
def baseStart_7622222 : Nat := 118140960795 + 7622222 * 2 ^ 59
def prefixEnd_7622222 : Nat := 4983230072969 + 3 ^ 40 * 7622222 * 2
def baseEnd_7622222 : Nat := 3913863541274582255071045

theorem tailTrace_7622222 : CollatzResearch.WordTrace tailWord_7622222 prefixEnd_7622222 3913863541274582255071045 := by
  unfold tailWord_7622222
  simp only [CollatzResearch.WordTrace]
  refine ⟨34750659423999867590419615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185336850261332627148904613 34750659423999867590419615)
  ·
    refine ⟨52125989135999801385629423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34750659423999867590419615 52125989135999801385629423)
    ·
      refine ⟨78188983703999702078444135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52125989135999801385629423 78188983703999702078444135)
      ·
        refine ⟨117283475555999553117666203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78188983703999702078444135 117283475555999553117666203)
        ·
          refine ⟨175925213333999329676499305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117283475555999553117666203 175925213333999329676499305)
          ·
            refine ⟨131943910000499497257374479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175925213333999329676499305 131943910000499497257374479)
            ·
              refine ⟨197915865000749245886061719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131943910000499497257374479 197915865000749245886061719)
              ·
                refine ⟨296873797501123868829092579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 197915865000749245886061719 296873797501123868829092579)
                ·
                  refine ⟨445310696251685803243638869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 296873797501123868829092579 445310696251685803243638869)
                  ·
                    refine ⟨5218484721699443006761393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 445310696251685803243638869 5218484721699443006761393)
                    ·
                      refine ⟨3913863541274582255071045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5218484721699443006761393 3913863541274582255071045)
                      ·
                        rfl

theorem cell23_7622222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 1, 8, 2].length) (baseStart_7622222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7622222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7622222 prefixEnd_7622222 := by exact prefixLift 7622222
  have htrace : WordTrace (prefixWord ++ tailWord_7622222) baseStart_7622222 baseEnd_7622222 := by
    simpa [prefixWord, tailWord_7622222, baseEnd_7622222] using wordTrace_append hprefix tailTrace_7622222
  have hstable : (prefixWord ++ tailWord_7622222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7622222).length < 2 ^ (prefixWord ++ tailWord_7622222).sum := by decide
  have hdescent : baseEnd_7622222 < baseStart_7622222 := by decide
  rcases family_descends (prefixWord ++ tailWord_7622222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7622225 : List Nat := [1, 2, 2, 1, 3, 2, 1, 2, 3, 1, 5]
def baseStart_7622225 : Nat := 118140960795 + 7622225 * 2 ^ 59
def prefixEnd_7622225 : Nat := 4983230072969 + 3 ^ 40 * 7622225 * 2
def baseEnd_7622225 : Nat := 3913865081716545743333531

theorem tailTrace_7622225 : CollatzResearch.WordTrace tailWord_7622225 prefixEnd_7622225 3913865081716545743333531 := by
  unfold tailWord_7622225
  simp only [CollatzResearch.WordTrace]
  refine ⟨278005384810988072235716129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185336923207325381490477419 278005384810988072235716129)
  ·
    refine ⟨208504038608241054176787097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278005384810988072235716129 208504038608241054176787097)
    ·
      refine ⟨156378028956180790632590323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208504038608241054176787097 156378028956180790632590323)
      ·
        refine ⟨234567043434271185948885485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156378028956180790632590323 234567043434271185948885485)
        ·
          refine ⟨87962641287851694730832057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 234567043434271185948885485 87962641287851694730832057)
          ·
            refine ⟨65971980965888771048124043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87962641287851694730832057 65971980965888771048124043)
            ·
              refine ⟨98957971448833156572186065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65971980965888771048124043 98957971448833156572186065)
              ·
                refine ⟨74218478586624867429139549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98957971448833156572186065 74218478586624867429139549)
                ·
                  refine ⟨27831929469984325285927331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74218478586624867429139549 27831929469984325285927331)
                  ·
                    refine ⟨41747894204976487928890997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27831929469984325285927331 41747894204976487928890997)
                    ·
                      refine ⟨3913865081716545743333531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41747894204976487928890997 3913865081716545743333531)
                      ·
                        rfl

theorem cell23_7622225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 2, 3, 1, 5].length) (baseStart_7622225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7622225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7622225 prefixEnd_7622225 := by exact prefixLift 7622225
  have htrace : WordTrace (prefixWord ++ tailWord_7622225) baseStart_7622225 baseEnd_7622225 := by
    simpa [prefixWord, tailWord_7622225, baseEnd_7622225] using wordTrace_append hprefix tailTrace_7622225
  have hstable : (prefixWord ++ tailWord_7622225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7622225).length < 2 ^ (prefixWord ++ tailWord_7622225).sum := by decide
  have hdescent : baseEnd_7622225 < baseStart_7622225 := by decide
  rcases family_descends (prefixWord ++ tailWord_7622225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7622245 : List Nat := [1, 3, 1, 3, 3, 1, 11]
def baseStart_7622245 : Nat := 118140960795 + 7622245 * 2 ^ 59
def prefixEnd_7622245 : Nat := 4983230072969 + 3 ^ 40 * 7622245 * 2
def baseEnd_7622245 : Nat := 48319448781847353889919

theorem tailTrace_7622245 : CollatzResearch.WordTrace tailWord_7622245 prefixEnd_7622245 48319448781847353889919 := by
  unfold tailWord_7622245
  simp only [CollatzResearch.WordTrace]
  refine ⟨278006114270915615651444189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185337409513943743767629459 278006114270915615651444189)
  ·
    refine ⟨104252292851593355869291571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 278006114270915615651444189 104252292851593355869291571)
    ·
      refine ⟨156378439277390033803937357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104252292851593355869291571 156378439277390033803937357)
      ·
        refine ⟨58641914729021262676476509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156378439277390033803937357 58641914729021262676476509)
        ·
          refine ⟨21990718023382973503678691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58641914729021262676476509 21990718023382973503678691)
          ·
            refine ⟨32986077035074460255518037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21990718023382973503678691 32986077035074460255518037)
            ·
              refine ⟨48319448781847353889919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 32986077035074460255518037 48319448781847353889919)
              ·
                rfl

theorem cell23_7622245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 11].length) (baseStart_7622245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7622245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7622245 prefixEnd_7622245 := by exact prefixLift 7622245
  have htrace : WordTrace (prefixWord ++ tailWord_7622245) baseStart_7622245 baseEnd_7622245 := by
    simpa [prefixWord, tailWord_7622245, baseEnd_7622245] using wordTrace_append hprefix tailTrace_7622245
  have hstable : (prefixWord ++ tailWord_7622245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7622245).length < 2 ^ (prefixWord ++ tailWord_7622245).sum := by decide
  have hdescent : baseEnd_7622245 < baseStart_7622245 := by decide
  rcases family_descends (prefixWord ++ tailWord_7622245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7622256 : List Nat := [2, 1, 1, 1, 6, 1, 3, 1, 3, 2, 2]
def baseStart_7622256 : Nat := 118140960795 + 7622256 * 2 ^ 59
def prefixEnd_7622256 : Nat := 4983230072969 + 3 ^ 40 * 7622256 * 2
def baseEnd_7622256 : Nat := 3913880999616835122045889

theorem tailTrace_7622256 : CollatzResearch.WordTrace tailWord_7622256 prefixEnd_7622256 3913880999616835122045889 := by
  unfold tailWord_7622256
  simp only [CollatzResearch.WordTrace]
  refine ⟨139003257736937882265047311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185337676982583843020063081 139003257736937882265047311)
  ·
    refine ⟨208504886605406823397570967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139003257736937882265047311 208504886605406823397570967)
    ·
      refine ⟨312757329908110235096356451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208504886605406823397570967 312757329908110235096356451)
      ·
        refine ⟨469135994862165352644534677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312757329908110235096356451 469135994862165352644534677)
        ·
          refine ⟨21990749759164000905212563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 469135994862165352644534677 21990749759164000905212563)
          ·
            refine ⟨32986124638746001357818845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21990749759164000905212563 32986124638746001357818845)
            ·
              refine ⟨12369796739529750509182067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32986124638746001357818845 12369796739529750509182067)
              ·
                refine ⟨18554695109294625763773101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12369796739529750509182067 18554695109294625763773101)
                ·
                  refine ⟨6958010665985484661414913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18554695109294625763773101 6958010665985484661414913)
                  ·
                    refine ⟨5218507999489113496061185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6958010665985484661414913 5218507999489113496061185)
                    ·
                      refine ⟨3913880999616835122045889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5218507999489113496061185 3913880999616835122045889)
                      ·
                        rfl

theorem cell23_7622256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 3, 1, 3, 2, 2].length) (baseStart_7622256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7622256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7622256 prefixEnd_7622256 := by exact prefixLift 7622256
  have htrace : WordTrace (prefixWord ++ tailWord_7622256) baseStart_7622256 baseEnd_7622256 := by
    simpa [prefixWord, tailWord_7622256, baseEnd_7622256] using wordTrace_append hprefix tailTrace_7622256
  have hstable : (prefixWord ++ tailWord_7622256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7622256).length < 2 ^ (prefixWord ++ tailWord_7622256).sum := by decide
  have hdescent : baseEnd_7622256 < baseStart_7622256 := by decide
  rcases family_descends (prefixWord ++ tailWord_7622256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7622262 : List Nat := [5, 1, 1, 2, 2, 1, 1, 10]
def baseStart_7622262 : Nat := 118140960795 + 7622262 * 2 ^ 59
def prefixEnd_7622262 : Nat := 4983230072969 + 3 ^ 40 * 7622262 * 2
def baseEnd_7622262 : Nat := 144958669648176374021143

theorem tailTrace_7622262 : CollatzResearch.WordTrace tailWord_7622262 prefixEnd_7622262 144958669648176374021143 := by
  unfold tailWord_7622262
  simp only [CollatzResearch.WordTrace]
  refine ⟨17375420894490876722175815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 185337822874569351703208693 17375420894490876722175815)
  ·
    refine ⟨26063131341736315083263723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17375420894490876722175815 26063131341736315083263723)
    ·
      refine ⟨39094697012604472624895585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26063131341736315083263723 39094697012604472624895585)
      ·
        refine ⟨29321022759453354468671689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39094697012604472624895585 29321022759453354468671689)
        ·
          refine ⟨21990767069590015851503767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29321022759453354468671689 21990767069590015851503767)
          ·
            refine ⟨32986150604385023777255651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21990767069590015851503767 32986150604385023777255651)
            ·
              refine ⟨49479225906577535665883477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32986150604385023777255651 49479225906577535665883477)
              ·
                refine ⟨144958669648176374021143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 49479225906577535665883477 144958669648176374021143)
                ·
                  rfl

theorem cell23_7622262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 10].length) (baseStart_7622262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7622262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7622262 prefixEnd_7622262 := by exact prefixLift 7622262
  have htrace : WordTrace (prefixWord ++ tailWord_7622262) baseStart_7622262 baseEnd_7622262 := by
    simpa [prefixWord, tailWord_7622262, baseEnd_7622262] using wordTrace_append hprefix tailTrace_7622262
  have hstable : (prefixWord ++ tailWord_7622262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7622262).length < 2 ^ (prefixWord ++ tailWord_7622262).sum := by decide
  have hdescent : baseEnd_7622262 < baseStart_7622262 := by decide
  rcases family_descends (prefixWord ++ tailWord_7622262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7622265 : List Nat := [1, 2, 1, 3, 3, 1, 1, 1, 2, 2, 6]
def baseStart_7622265 : Nat := 118140960795 + 7622265 * 2 ^ 59
def prefixEnd_7622265 : Nat := 4983230072969 + 3 ^ 40 * 7622265 * 2
def baseEnd_7622265 : Nat := 3913885620942725586833347

theorem tailTrace_7622265 : CollatzResearch.WordTrace tailWord_7622265 prefixEnd_7622265 3913885620942725586833347 := by
  unfold tailWord_7622265
  simp only [CollatzResearch.WordTrace]
  refine ⟨278006843730843159067172249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185337895820562106044781499 278006843730843159067172249)
  ·
    refine ⟨208505132798132369300379187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278006843730843159067172249 208505132798132369300379187)
    ·
      refine ⟨312757699197198553950568781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208505132798132369300379187 312757699197198553950568781)
      ·
        refine ⟨117284137198949457731463293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 312757699197198553950568781 117284137198949457731463293)
        ·
          refine ⟨43981551449606046649298735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117284137198949457731463293 43981551449606046649298735)
          ·
            refine ⟨65972327174409069973948103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43981551449606046649298735 65972327174409069973948103)
            ·
              refine ⟨98958490761613604960922155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65972327174409069973948103 98958490761613604960922155)
              ·
                refine ⟨148437736142420407441383233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98958490761613604960922155 148437736142420407441383233)
                ·
                  refine ⟨111328302106815305581037425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 148437736142420407441383233 111328302106815305581037425)
                  ·
                    refine ⟨83496226580111479185778069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 111328302106815305581037425 83496226580111479185778069)
                    ·
                      refine ⟨3913885620942725586833347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83496226580111479185778069 3913885620942725586833347)
                      ·
                        rfl

theorem cell23_7622265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 2, 2, 6].length) (baseStart_7622265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7622265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7622265 prefixEnd_7622265 := by exact prefixLift 7622265
  have htrace : WordTrace (prefixWord ++ tailWord_7622265) baseStart_7622265 baseEnd_7622265 := by
    simpa [prefixWord, tailWord_7622265, baseEnd_7622265] using wordTrace_append hprefix tailTrace_7622265
  have hstable : (prefixWord ++ tailWord_7622265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7622265).length < 2 ^ (prefixWord ++ tailWord_7622265).sum := by decide
  have hdescent : baseEnd_7622265 < baseStart_7622265 := by decide
  rcases family_descends (prefixWord ++ tailWord_7622265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7622272 : List Nat := [2, 1, 1, 2, 1, 4, 2, 3, 1, 3, 3]
def baseStart_7622272 : Nat := 118140960795 + 7622272 * 2 ^ 59
def prefixEnd_7622272 : Nat := 4983230072969 + 3 ^ 40 * 7622272 * 2
def baseEnd_7622272 : Nat := 3913889215307307059445815

theorem tailTrace_7622272 : CollatzResearch.WordTrace tailWord_7622272 prefixEnd_7622272 3913889215307307059445815 := by
  unfold tailWord_7622272
  simp only [CollatzResearch.WordTrace]
  refine ⟨139003549520908899631338535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185338066027878532841784713 139003549520908899631338535)
  ·
    refine ⟨208505324281363349447007803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139003549520908899631338535 208505324281363349447007803)
    ·
      refine ⟨312757986422045024170511705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208505324281363349447007803 312757986422045024170511705)
      ·
        refine ⟨234568489816533768127883779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 312757986422045024170511705 234568489816533768127883779)
        ·
          refine ⟨351852734724800652191825669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234568489816533768127883779 351852734724800652191825669)
          ·
            refine ⟨65972387760900122285967313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 351852734724800652191825669 65972387760900122285967313)
            ·
              refine ⟨49479290820675091714475485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65972387760900122285967313 49479290820675091714475485)
              ·
                refine ⟨18554734057753159392928307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49479290820675091714475485 18554734057753159392928307)
                ·
                  refine ⟨27832101086629739089392461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18554734057753159392928307 27832101086629739089392461)
                  ·
                    refine ⟨10437037907486152158522173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27832101086629739089392461 10437037907486152158522173)
                    ·
                      refine ⟨3913889215307307059445815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10437037907486152158522173 3913889215307307059445815)
                      ·
                        rfl

theorem cell23_7622272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 3, 1, 3, 3].length) (baseStart_7622272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7622272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7622272 prefixEnd_7622272 := by exact prefixLift 7622272
  have htrace : WordTrace (prefixWord ++ tailWord_7622272) baseStart_7622272 baseEnd_7622272 := by
    simpa [prefixWord, tailWord_7622272, baseEnd_7622272] using wordTrace_append hprefix tailTrace_7622272
  have hstable : (prefixWord ++ tailWord_7622272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7622272).length < 2 ^ (prefixWord ++ tailWord_7622272).sum := by decide
  have hdescent : baseEnd_7622272 < baseStart_7622272 := by decide
  rcases family_descends (prefixWord ++ tailWord_7622272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7622329 : List Nat := [1, 2, 1, 4, 1, 1, 3, 3, 1, 4, 2]
def baseStart_7622329 : Nat := 118140960795 + 7622329 * 2 ^ 59
def prefixEnd_7622329 : Nat := 4983230072969 + 3 ^ 40 * 7622329 * 2
def baseEnd_7622329 : Nat := 3913918483704613336433053

theorem tailTrace_7622329 : CollatzResearch.WordTrace tailWord_7622329 prefixEnd_7622329 3913918483704613336433053 := by
  unfold tailWord_7622329
  simp only [CollatzResearch.WordTrace]
  refine ⟨278009178002611297997502041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185339452001740865331668027 278009178002611297997502041)
  ·
    refine ⟨208506883501958473498126531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278009178002611297997502041 208506883501958473498126531)
    ·
      refine ⟨312760325252937710247189797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208506883501958473498126531 312760325252937710247189797)
      ·
        refine ⟨58642560984925820671348087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 312760325252937710247189797 58642560984925820671348087)
        ·
          refine ⟨87963841477388731007022131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58642560984925820671348087 87963841477388731007022131)
          ·
            refine ⟨131945762216083096510533197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87963841477388731007022131 131945762216083096510533197)
            ·
              refine ⟨49479660831031161191449949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131945762216083096510533197 49479660831031161191449949)
              ·
                refine ⟨18554872811636685446793731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49479660831031161191449949 18554872811636685446793731)
                ·
                  refine ⟨27832309217455028170190597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18554872811636685446793731 27832309217455028170190597)
                  ·
                    refine ⟨5218557978272817781910737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27832309217455028170190597 5218557978272817781910737)
                    ·
                      refine ⟨3913918483704613336433053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5218557978272817781910737 3913918483704613336433053)
                      ·
                        rfl

theorem cell23_7622329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 3, 1, 4, 2].length) (baseStart_7622329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7622329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7622329 prefixEnd_7622329 := by exact prefixLift 7622329
  have htrace : WordTrace (prefixWord ++ tailWord_7622329) baseStart_7622329 baseEnd_7622329 := by
    simpa [prefixWord, tailWord_7622329, baseEnd_7622329] using wordTrace_append hprefix tailTrace_7622329
  have hstable : (prefixWord ++ tailWord_7622329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7622329).length < 2 ^ (prefixWord ++ tailWord_7622329).sum := by decide
  have hdescent : baseEnd_7622329 < baseStart_7622329 := by decide
  rcases family_descends (prefixWord ++ tailWord_7622329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7622355 : List Nat := [1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 8]
def baseStart_7622355 : Nat := 118140960795 + 7622355 * 2 ^ 59
def prefixEnd_7622355 : Nat := 4983230072969 + 3 ^ 40 * 7622355 * 2
def baseEnd_7622355 : Nat := 3913931834201630234707933

theorem tailTrace_7622355 : CollatzResearch.WordTrace tailWord_7622355 prefixEnd_7622355 3913931834201630234707933 := by
  unfold tailWord_7622355
  simp only [CollatzResearch.WordTrace]
  refine ⟨278010126300517104437948519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185340084200344736291965679 278010126300517104437948519)
  ·
    refine ⟨417015189450775656656922779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278010126300517104437948519 417015189450775656656922779)
    ·
      refine ⟨625522784176163484985384169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 417015189450775656656922779 625522784176163484985384169)
      ·
        refine ⟨469142088132122613739038127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 625522784176163484985384169 469142088132122613739038127)
        ·
          refine ⟨703713132198183920608557191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 469142088132122613739038127 703713132198183920608557191)
          ·
            refine ⟨1055569698297275880912835787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 703713132198183920608557191 1055569698297275880912835787)
            ·
              refine ⟨1583354547445913821369253681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1055569698297275880912835787 1583354547445913821369253681)
              ·
                refine ⟨1187515910584435366026940261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1583354547445913821369253681 1187515910584435366026940261)
                ·
                  refine ⟨222659233234581631130051299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1187515910584435366026940261 222659233234581631130051299)
                  ·
                    refine ⟨333988849851872446695076949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 222659233234581631130051299 333988849851872446695076949)
                    ·
                      refine ⟨3913931834201630234707933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 333988849851872446695076949 3913931834201630234707933)
                      ·
                        rfl

theorem cell23_7622355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 8].length) (baseStart_7622355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7622355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7622355 prefixEnd_7622355 := by exact prefixLift 7622355
  have htrace : WordTrace (prefixWord ++ tailWord_7622355) baseStart_7622355 baseEnd_7622355 := by
    simpa [prefixWord, tailWord_7622355, baseEnd_7622355] using wordTrace_append hprefix tailTrace_7622355
  have hstable : (prefixWord ++ tailWord_7622355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7622355).length < 2 ^ (prefixWord ++ tailWord_7622355).sum := by decide
  have hdescent : baseEnd_7622355 < baseStart_7622355 := by decide
  rcases family_descends (prefixWord ++ tailWord_7622355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7622369 : List Nat := [1, 2, 3, 1, 5, 1, 2, 1, 7]
def baseStart_7622369 : Nat := 118140960795 + 7622369 * 2 ^ 59
def prefixEnd_7622369 : Nat := 4983230072969 + 3 ^ 40 * 7622369 * 2
def baseEnd_7622369 : Nat := 434882113658977019992541

theorem tailTrace_7622369 : CollatzResearch.WordTrace tailWord_7622369 prefixEnd_7622369 434882113658977019992541 := by
  unfold tailWord_7622369
  simp only [CollatzResearch.WordTrace]
  refine ⟨278010636922466384828958161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185340424614977589885972107 278010636922466384828958161)
  ·
    refine ⟨208507977691849788621718621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278010636922466384828958161 208507977691849788621718621)
    ·
      refine ⟨78190491634443670733144483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208507977691849788621718621 78190491634443670733144483)
      ·
        refine ⟨117285737451665506099716725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78190491634443670733144483 117285737451665506099716725)
        ·
          refine ⟨10995537886093641196848443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 117285737451665506099716725 10995537886093641196848443)
          ·
            refine ⟨16493306829140461795272665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10995537886093641196848443 16493306829140461795272665)
            ·
              refine ⟨12369980121855346346454499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16493306829140461795272665 12369980121855346346454499)
              ·
                refine ⟨18554970182783019519681749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12369980121855346346454499 18554970182783019519681749)
                ·
                  refine ⟨434882113658977019992541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18554970182783019519681749 434882113658977019992541)
                  ·
                    rfl

theorem cell23_7622369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 2, 1, 7].length) (baseStart_7622369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7622369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7622369 prefixEnd_7622369 := by exact prefixLift 7622369
  have htrace : WordTrace (prefixWord ++ tailWord_7622369) baseStart_7622369 baseEnd_7622369 := by
    simpa [prefixWord, tailWord_7622369, baseEnd_7622369] using wordTrace_append hprefix tailTrace_7622369
  have hstable : (prefixWord ++ tailWord_7622369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7622369).length < 2 ^ (prefixWord ++ tailWord_7622369).sum := by decide
  have hdescent : baseEnd_7622369 < baseStart_7622369 := by decide
  rcases family_descends (prefixWord ++ tailWord_7622369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7622382 : List Nat := [4, 1, 2, 1, 1, 2, 1, 1, 3, 7]
def baseStart_7622382 : Nat := 118140960795 + 7622382 * 2 ^ 59
def prefixEnd_7622382 : Nat := 4983230072969 + 3 ^ 40 * 7622382 * 2
def baseEnd_7622382 : Nat := 1304648566059767209690103

theorem tailTrace_7622382 : CollatzResearch.WordTrace tailWord_7622382 prefixEnd_7622382 1304648566059767209690103 := by
  unfold tailWord_7622382
  simp only [CollatzResearch.WordTrace]
  refine ⟨34751388883927411006147675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185340740714279525366120933 34751388883927411006147675)
  ·
    refine ⟨52127083325891116509221513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34751388883927411006147675 52127083325891116509221513)
    ·
      refine ⟨39095312494418337381916135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52127083325891116509221513 39095312494418337381916135)
      ·
        refine ⟨58642968741627506072874203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39095312494418337381916135 58642968741627506072874203)
        ·
          refine ⟨87964453112441259109311305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58642968741627506072874203 87964453112441259109311305)
          ·
            refine ⟨65973339834330944331983479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87964453112441259109311305 65973339834330944331983479)
            ·
              refine ⟨98960009751496416497975219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65973339834330944331983479 98960009751496416497975219)
              ·
                refine ⟨148440014627244624746962829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98960009751496416497975219 148440014627244624746962829)
                ·
                  refine ⟨55665005485216734280111061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 148440014627244624746962829 55665005485216734280111061)
                  ·
                    refine ⟨1304648566059767209690103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55665005485216734280111061 1304648566059767209690103)
                    ·
                      rfl

theorem cell23_7622382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 3, 7].length) (baseStart_7622382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7622382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7622382 prefixEnd_7622382 := by exact prefixLift 7622382
  have htrace : WordTrace (prefixWord ++ tailWord_7622382) baseStart_7622382 baseEnd_7622382 := by
    simpa [prefixWord, tailWord_7622382, baseEnd_7622382] using wordTrace_append hprefix tailTrace_7622382
  have hstable : (prefixWord ++ tailWord_7622382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7622382).length < 2 ^ (prefixWord ++ tailWord_7622382).sum := by decide
  have hdescent : baseEnd_7622382 < baseStart_7622382 := by decide
  rcases family_descends (prefixWord ++ tailWord_7622382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7622419 : List Nat := [1, 1, 1, 2, 1, 3, 2, 4, 2, 4, 2]
def baseStart_7622419 : Nat := 118140960795 + 7622419 * 2 ^ 59
def prefixEnd_7622419 : Nat := 4983230072969 + 3 ^ 40 * 7622419 * 2
def baseEnd_7622419 : Nat := 3913964696963517984307639

theorem tailTrace_7622419 : CollatzResearch.WordTrace tailWord_7622419 prefixEnd_7622419 3913964696963517984307639 := by
  unfold tailWord_7622419
  simp only [CollatzResearch.WordTrace]
  refine ⟨278012460572285243368278311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185341640381523495578852207 278012460572285243368278311)
  ·
    refine ⟨417018690858427865052417467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278012460572285243368278311 417018690858427865052417467)
    ·
      refine ⟨625528036287641797578626201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 417018690858427865052417467 625528036287641797578626201)
      ·
        refine ⟨469146027215731348183969651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 625528036287641797578626201 469146027215731348183969651)
        ·
          refine ⟨703719040823597022275954477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 469146027215731348183969651 703719040823597022275954477)
          ·
            refine ⟨263894640308848883353482929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 703719040823597022275954477 263894640308848883353482929)
            ·
              refine ⟨197920980231636662515112197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 263894640308848883353482929 197920980231636662515112197)
              ·
                refine ⟨37110183793431874221583537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 197920980231636662515112197 37110183793431874221583537)
                ·
                  refine ⟨27832637845073905666187653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37110183793431874221583537 27832637845073905666187653)
                  ·
                    refine ⟨5218619595951357312410185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27832637845073905666187653 5218619595951357312410185)
                    ·
                      refine ⟨3913964696963517984307639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5218619595951357312410185 3913964696963517984307639)
                      ·
                        rfl

theorem cell23_7622419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 4, 2, 4, 2].length) (baseStart_7622419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7622419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7622419 prefixEnd_7622419 := by exact prefixLift 7622419
  have htrace : WordTrace (prefixWord ++ tailWord_7622419) baseStart_7622419 baseEnd_7622419 := by
    simpa [prefixWord, tailWord_7622419, baseEnd_7622419] using wordTrace_append hprefix tailTrace_7622419
  have hstable : (prefixWord ++ tailWord_7622419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7622419).length < 2 ^ (prefixWord ++ tailWord_7622419).sum := by decide
  have hdescent : baseEnd_7622419 < baseStart_7622419 := by decide
  rcases family_descends (prefixWord ++ tailWord_7622419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
