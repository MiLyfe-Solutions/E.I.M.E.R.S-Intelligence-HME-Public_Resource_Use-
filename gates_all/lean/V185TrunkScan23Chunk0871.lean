import V185TrunkScan23Chunk0870

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5154478 : List Nat := [4, 1, 4, 1, 13]
def baseStart_5154478 : Nat := 118140960795 + 5154478 * 2 ^ 59
def prefixEnd_5154478 : Nat := 4983230072969 + 3 ^ 40 * 5154478 * 2
def baseEnd_5154478 : Nat := 3630623781928380404417

theorem tailTrace_5154478 : CollatzResearch.WordTrace tailWord_5154478 prefixEnd_5154478 3630623781928380404417 := by
  unfold tailWord_5154478
  simp only [CollatzResearch.WordTrace]
  refine ⟨23499907177526749450259011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125332838280142663734714725 23499907177526749450259011)
  ·
    refine ⟨35249860766290124175388517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23499907177526749450259011 35249860766290124175388517)
    ·
      refine ⟨6609348893679398282885347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35249860766290124175388517 6609348893679398282885347)
      ·
        refine ⟨9914023340519097424328021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6609348893679398282885347 9914023340519097424328021)
        ·
          refine ⟨3630623781928380404417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 9914023340519097424328021 3630623781928380404417)
          ·
            rfl

theorem cell23_5154478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 13].length) (baseStart_5154478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5154478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5154478 prefixEnd_5154478 := by exact prefixLift 5154478
  have htrace : WordTrace (prefixWord ++ tailWord_5154478) baseStart_5154478 baseEnd_5154478 := by
    simpa [prefixWord, tailWord_5154478, baseEnd_5154478] using wordTrace_append hprefix tailTrace_5154478
  have hstable : (prefixWord ++ tailWord_5154478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5154478).length < 2 ^ (prefixWord ++ tailWord_5154478).sum := by decide
  have hdescent : baseEnd_5154478 < baseStart_5154478 := by decide
  rcases family_descends (prefixWord ++ tailWord_5154478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5154532 : List Nat := [2, 3, 1, 1, 1, 3, 3, 3, 1, 3, 2]
def baseStart_5154532 : Nat := 118140960795 + 5154532 * 2 ^ 59
def prefixEnd_5154532 : Nat := 4983230072969 + 3 ^ 40 * 5154532 * 2
def baseEnd_5154532 : Nat := 2646752464981132103544745

theorem tailTrace_5154532 : CollatzResearch.WordTrace tailWord_5154532 prefixEnd_5154532 2646752464981132103544745 := by
  unfold tailWord_5154532
  simp only [CollatzResearch.WordTrace]
  refine ⟨94000613481009181412268925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125334151308012241883025233 94000613481009181412268925)
  ·
    refine ⟨35250230055378443029600847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94000613481009181412268925 35250230055378443029600847)
    ·
      refine ⟨52875345083067664544401271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35250230055378443029600847 52875345083067664544401271)
      ·
        refine ⟨79313017624601496816601907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52875345083067664544401271 79313017624601496816601907)
        ·
          refine ⟨118969526436902245224902861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79313017624601496816601907 118969526436902245224902861)
          ·
            refine ⟨44613572413838341959338573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 118969526436902245224902861 44613572413838341959338573)
            ·
              refine ⟨16730089655189378234751965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44613572413838341959338573 16730089655189378234751965)
              ·
                refine ⟨6273783620696016838031987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16730089655189378234751965 6273783620696016838031987)
                ·
                  refine ⟨9410675431044025257047981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6273783620696016838031987 9410675431044025257047981)
                  ·
                    refine ⟨3529003286641509471392993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9410675431044025257047981 3529003286641509471392993)
                    ·
                      refine ⟨2646752464981132103544745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3529003286641509471392993 2646752464981132103544745)
                      ·
                        rfl

theorem cell23_5154532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 3, 1, 3, 2].length) (baseStart_5154532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5154532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5154532 prefixEnd_5154532 := by exact prefixLift 5154532
  have htrace : WordTrace (prefixWord ++ tailWord_5154532) baseStart_5154532 baseEnd_5154532 := by
    simpa [prefixWord, tailWord_5154532, baseEnd_5154532] using wordTrace_append hprefix tailTrace_5154532
  have hstable : (prefixWord ++ tailWord_5154532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5154532).length < 2 ^ (prefixWord ++ tailWord_5154532).sum := by decide
  have hdescent : baseEnd_5154532 < baseStart_5154532 := by decide
  rcases family_descends (prefixWord ++ tailWord_5154532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5154538 : List Nat := [3, 1, 3, 1, 1, 1, 3, 2, 2, 6]
def baseStart_5154538 : Nat := 118140960795 + 5154538 * 2 ^ 59
def prefixEnd_5154538 : Nat := 4983230072969 + 3 ^ 40 * 5154538 * 2
def baseEnd_5154538 : Nat := 882251848621686360023239

theorem tailTrace_5154538 : CollatzResearch.WordTrace tailWord_5154538 prefixEnd_5154538 882251848621686360023239 := by
  unfold tailWord_5154538
  simp only [CollatzResearch.WordTrace]
  refine ⟨47000361449999156462314067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125334297199997750566170845 47000361449999156462314067)
  ·
    refine ⟨70500542174998734693471101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47000361449999156462314067 70500542174998734693471101)
    ·
      refine ⟨26437703315624525510051663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70500542174998734693471101 26437703315624525510051663)
      ·
        refine ⟨39656554973436788265077495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26437703315624525510051663 39656554973436788265077495)
        ·
          refine ⟨59484832460155182397616243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39656554973436788265077495 59484832460155182397616243)
          ·
            refine ⟨89227248690232773596424365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59484832460155182397616243 89227248690232773596424365)
            ·
              refine ⟨33460218258837290098659137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89227248690232773596424365 33460218258837290098659137)
              ·
                refine ⟨25095163694127967573994353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33460218258837290098659137 25095163694127967573994353)
                ·
                  refine ⟨18821372770595975680495765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25095163694127967573994353 18821372770595975680495765)
                  ·
                    refine ⟨882251848621686360023239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18821372770595975680495765 882251848621686360023239)
                    ·
                      rfl

theorem cell23_5154538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 2, 2, 6].length) (baseStart_5154538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5154538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5154538 prefixEnd_5154538 := by exact prefixLift 5154538
  have htrace : WordTrace (prefixWord ++ tailWord_5154538) baseStart_5154538 baseEnd_5154538 := by
    simpa [prefixWord, tailWord_5154538, baseEnd_5154538] using wordTrace_append hprefix tailTrace_5154538
  have hstable : (prefixWord ++ tailWord_5154538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5154538).length < 2 ^ (prefixWord ++ tailWord_5154538).sum := by decide
  have hdescent : baseEnd_5154538 < baseStart_5154538 := by decide
  rcases family_descends (prefixWord ++ tailWord_5154538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5154568 : List Nat := [2, 1, 3, 2, 2, 1, 1, 4, 7]
def baseStart_5154568 : Nat := 118140960795 + 5154568 * 2 ^ 59
def prefixEnd_5154568 : Nat := 4983230072969 + 3 ^ 40 * 5154568 * 2
def baseEnd_5154568 : Nat := 294085661142743773632731

theorem tailTrace_5154568 : CollatzResearch.WordTrace tailWord_5154568 prefixEnd_5154568 294085661142743773632731 := by
  unfold tailWord_5154568
  simp only [CollatzResearch.WordTrace]
  refine ⟨94001269994943970486424179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125335026659925293981898905 94001269994943970486424179)
  ·
    refine ⟨141001904992415955729636269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94001269994943970486424179 141001904992415955729636269)
    ·
      refine ⟨52875714372155983398613601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141001904992415955729636269 52875714372155983398613601)
      ·
        refine ⟨39656785779116987548960201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52875714372155983398613601 39656785779116987548960201)
        ·
          refine ⟨29742589334337740661720151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39656785779116987548960201 29742589334337740661720151)
          ·
            refine ⟨44613884001506610992580227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29742589334337740661720151 44613884001506610992580227)
            ·
              refine ⟨66920826002259916488870341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44613884001506610992580227 66920826002259916488870341)
              ·
                refine ⟨12547654875423734341663189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 66920826002259916488870341 12547654875423734341663189)
                ·
                  refine ⟨294085661142743773632731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12547654875423734341663189 294085661142743773632731)
                  ·
                    rfl

theorem cell23_5154568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 4, 7].length) (baseStart_5154568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5154568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5154568 prefixEnd_5154568 := by exact prefixLift 5154568
  have htrace : WordTrace (prefixWord ++ tailWord_5154568) baseStart_5154568 baseEnd_5154568 := by
    simpa [prefixWord, tailWord_5154568, baseEnd_5154568] using wordTrace_append hprefix tailTrace_5154568
  have hstable : (prefixWord ++ tailWord_5154568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5154568).length < 2 ^ (prefixWord ++ tailWord_5154568).sum := by decide
  have hdescent : baseEnd_5154568 < baseStart_5154568 := by decide
  rcases family_descends (prefixWord ++ tailWord_5154568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5154613 : List Nat := [1, 3, 3, 1, 4, 2, 2, 1, 2, 2, 2]
def baseStart_5154613 : Nat := 118140960795 + 5154613 * 2 ^ 59
def prefixEnd_5154613 : Nat := 4983230072969 + 3 ^ 40 * 5154613 * 2
def baseEnd_5154613 : Nat := 2646794056914146286631873

theorem tailTrace_5154613 : CollatzResearch.WordTrace tailWord_5154613 prefixEnd_5154613 2646794056914146286631873 := by
  unfold tailWord_5154613
  simp only [CollatzResearch.WordTrace]
  refine ⟨188004181274724913658236493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125336120849816609105490995 188004181274724913658236493)
  ·
    refine ⟨70501567978021842621838685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 188004181274724913658236493 70501567978021842621838685)
    ·
      refine ⟨26438087991758190983189507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70501567978021842621838685 26438087991758190983189507)
      ·
        refine ⟨39657131987637286474784261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26438087991758190983189507 39657131987637286474784261)
        ·
          refine ⟨7435712247681991214022049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39657131987637286474784261 7435712247681991214022049)
          ·
            refine ⟨5576784185761493410516537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7435712247681991214022049 5576784185761493410516537)
            ·
              refine ⟨4182588139321120057887403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5576784185761493410516537 4182588139321120057887403)
              ·
                refine ⟨6273882208981680086831105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4182588139321120057887403 6273882208981680086831105)
                ·
                  refine ⟨4705411656736260065123329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6273882208981680086831105 4705411656736260065123329)
                  ·
                    refine ⟨3529058742552195048842497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4705411656736260065123329 3529058742552195048842497)
                    ·
                      refine ⟨2646794056914146286631873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3529058742552195048842497 2646794056914146286631873)
                      ·
                        rfl

theorem cell23_5154613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 2, 1, 2, 2, 2].length) (baseStart_5154613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5154613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5154613 prefixEnd_5154613 := by exact prefixLift 5154613
  have htrace : WordTrace (prefixWord ++ tailWord_5154613) baseStart_5154613 baseEnd_5154613 := by
    simpa [prefixWord, tailWord_5154613, baseEnd_5154613] using wordTrace_append hprefix tailTrace_5154613
  have hstable : (prefixWord ++ tailWord_5154613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5154613).length < 2 ^ (prefixWord ++ tailWord_5154613).sum := by decide
  have hdescent : baseEnd_5154613 < baseStart_5154613 := by decide
  rcases family_descends (prefixWord ++ tailWord_5154613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5154638 : List Nat := [4, 1, 1, 1, 1, 1, 1, 1, 1, 2, 9]
def baseStart_5154638 : Nat := 118140960795 + 5154638 * 2 ^ 59
def prefixEnd_5154638 : Nat := 4983230072969 + 3 ^ 40 * 5154638 * 2
def baseEnd_5154638 : Nat := 2646806893930508688819257

theorem tailTrace_5154638 : CollatzResearch.WordTrace tailWord_5154638 prefixEnd_5154638 2646806893930508688819257 := by
  unfold tailWord_5154638
  simp only [CollatzResearch.WordTrace]
  refine ⟨23500636637454292865987071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125336728733089561951931045 23500636637454292865987071)
  ·
    refine ⟨35250954956181439298980607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23500636637454292865987071 35250954956181439298980607)
    ·
      refine ⟨52876432434272158948470911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35250954956181439298980607 52876432434272158948470911)
      ·
        refine ⟨79314648651408238422706367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52876432434272158948470911 79314648651408238422706367)
        ·
          refine ⟨118971972977112357634059551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79314648651408238422706367 118971972977112357634059551)
          ·
            refine ⟨178457959465668536451089327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118971972977112357634059551 178457959465668536451089327)
            ·
              refine ⟨267686939198502804676633991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 178457959465668536451089327 267686939198502804676633991)
              ·
                refine ⟨401530408797754207014950987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 267686939198502804676633991 401530408797754207014950987)
                ·
                  refine ⟨602295613196631310522426481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 401530408797754207014950987 602295613196631310522426481)
                  ·
                    refine ⟨451721709897473482891819861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 602295613196631310522426481 451721709897473482891819861)
                    ·
                      refine ⟨2646806893930508688819257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 451721709897473482891819861 2646806893930508688819257)
                      ·
                        rfl

theorem cell23_5154638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 1, 2, 9].length) (baseStart_5154638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5154638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5154638 prefixEnd_5154638 := by exact prefixLift 5154638
  have htrace : WordTrace (prefixWord ++ tailWord_5154638) baseStart_5154638 baseEnd_5154638 := by
    simpa [prefixWord, tailWord_5154638, baseEnd_5154638] using wordTrace_append hprefix tailTrace_5154638
  have hstable : (prefixWord ++ tailWord_5154638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5154638).length < 2 ^ (prefixWord ++ tailWord_5154638).sum := by decide
  have hdescent : baseEnd_5154638 < baseStart_5154638 := by decide
  rcases family_descends (prefixWord ++ tailWord_5154638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5154686 : List Nat := [4, 2, 3, 1, 1, 3, 1, 1, 2, 1, 4]
def baseStart_5154686 : Nat := 118140960795 + 5154686 * 2 ^ 59
def prefixEnd_5154686 : Nat := 4983230072969 + 3 ^ 40 * 5154686 * 2
def baseEnd_5154686 : Nat := 2646831541001924501019037

theorem tailTrace_5154686 : CollatzResearch.WordTrace tailWord_5154686 prefixEnd_5154686 2646831541001924501019037 := by
  unfold tailWord_5154686
  simp only [CollatzResearch.WordTrace]
  refine ⟨23500855475432555890705489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125337895868973631417095941 23500855475432555890705489)
  ·
    refine ⟨17625641606574416918029117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23500855475432555890705489 17625641606574416918029117)
    ·
      refine ⟨6609615602465406344260919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17625641606574416918029117 6609615602465406344260919)
      ·
        refine ⟨9914423403698109516391379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6609615602465406344260919 9914423403698109516391379)
        ·
          refine ⟨14871635105547164274587069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9914423403698109516391379 14871635105547164274587069)
          ·
            refine ⟨5576863164580186602970151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14871635105547164274587069 5576863164580186602970151)
            ·
              refine ⟨8365294746870279904455227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5576863164580186602970151 8365294746870279904455227)
              ·
                refine ⟨12547942120305419856682841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8365294746870279904455227 12547942120305419856682841)
                ·
                  refine ⟨9410956590229064892512131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12547942120305419856682841 9410956590229064892512131)
                  ·
                    refine ⟨14116434885343597338768197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9410956590229064892512131 14116434885343597338768197)
                    ·
                      refine ⟨2646831541001924501019037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14116434885343597338768197 2646831541001924501019037)
                      ·
                        rfl

theorem cell23_5154686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_5154686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5154686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5154686 prefixEnd_5154686 := by exact prefixLift 5154686
  have htrace : WordTrace (prefixWord ++ tailWord_5154686) baseStart_5154686 baseEnd_5154686 := by
    simpa [prefixWord, tailWord_5154686, baseEnd_5154686] using wordTrace_append hprefix tailTrace_5154686
  have hstable : (prefixWord ++ tailWord_5154686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5154686).length < 2 ^ (prefixWord ++ tailWord_5154686).sum := by decide
  have hdescent : baseEnd_5154686 < baseStart_5154686 := by decide
  rcases family_descends (prefixWord ++ tailWord_5154686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5154689 : List Nat := [1, 2, 4, 4, 1, 1, 1, 1, 1, 4, 3]
def baseStart_5154689 : Nat := 118140960795 + 5154689 * 2 ^ 59
def prefixEnd_5154689 : Nat := 4983230072969 + 3 ^ 40 * 5154689 * 2
def baseEnd_5154689 : Nat := 2646833081443887989281523

theorem tailTrace_5154689 : CollatzResearch.WordTrace tailWord_5154689 prefixEnd_5154689 2646833081443887989281523 := by
  unfold tailWord_5154689
  simp only [CollatzResearch.WordTrace]
  refine ⟨188006953222449578638003121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125337968814966385758668747 188006953222449578638003121)
  ·
    refine ⟨141005214916837183978502341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188006953222449578638003121 141005214916837183978502341)
    ·
      refine ⟨26438477796906971995969189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 141005214916837183978502341 26438477796906971995969189)
      ·
        refine ⟨4957214586920057249244223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26438477796906971995969189 4957214586920057249244223)
        ·
          refine ⟨7435821880380085873866335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4957214586920057249244223 7435821880380085873866335)
          ·
            refine ⟨11153732820570128810799503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7435821880380085873866335 11153732820570128810799503)
            ·
              refine ⟨16730599230855193216199255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11153732820570128810799503 16730599230855193216199255)
              ·
                refine ⟨25095898846282789824298883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16730599230855193216199255 25095898846282789824298883)
                ·
                  refine ⟨37643848269424184736448325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25095898846282789824298883 37643848269424184736448325)
                  ·
                    refine ⟨7058221550517034638084061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37643848269424184736448325 7058221550517034638084061)
                    ·
                      refine ⟨2646833081443887989281523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7058221550517034638084061 2646833081443887989281523)
                      ·
                        rfl

theorem cell23_5154689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_5154689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5154689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5154689 prefixEnd_5154689 := by exact prefixLift 5154689
  have htrace : WordTrace (prefixWord ++ tailWord_5154689) baseStart_5154689 baseEnd_5154689 := by
    simpa [prefixWord, tailWord_5154689, baseEnd_5154689] using wordTrace_append hprefix tailTrace_5154689
  have hstable : (prefixWord ++ tailWord_5154689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5154689).length < 2 ^ (prefixWord ++ tailWord_5154689).sum := by decide
  have hdescent : baseEnd_5154689 < baseStart_5154689 := by decide
  rcases family_descends (prefixWord ++ tailWord_5154689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5154696 : List Nat := [2, 1, 3, 3, 3, 1, 2, 3, 1, 4]
def baseStart_5154696 : Nat := 118140960795 + 5154696 * 2 ^ 59
def prefixEnd_5154696 : Nat := 4983230072969 + 3 ^ 40 * 5154696 * 2
def baseEnd_5154696 : Nat := 882278891936156487297997

theorem tailTrace_5154696 : CollatzResearch.WordTrace tailWord_5154696 prefixEnd_5154696 882278891936156487297997 := by
  unfold tailWord_5154696
  simp only [CollatzResearch.WordTrace]
  refine ⟨94003604266712109416753971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125338139022282812555671961 94003604266712109416753971)
  ·
    refine ⟨141005406400068164125130957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94003604266712109416753971 141005406400068164125130957)
    ·
      refine ⟨52877027400025561546924109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141005406400068164125130957 52877027400025561546924109)
      ·
        refine ⟨19828885275009585580096541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52877027400025561546924109 19828885275009585580096541)
        ·
          refine ⟨7435831978128594592536203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19828885275009585580096541 7435831978128594592536203)
          ·
            refine ⟨11153747967192891888804305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7435831978128594592536203 11153747967192891888804305)
            ·
              refine ⟨8365310975394668916603229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11153747967192891888804305 8365310975394668916603229)
              ·
                refine ⟨3136991615773000843726211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8365310975394668916603229 3136991615773000843726211)
                ·
                  refine ⟨4705487423659501265589317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3136991615773000843726211 4705487423659501265589317)
                  ·
                    refine ⟨882278891936156487297997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4705487423659501265589317 882278891936156487297997)
                    ·
                      rfl

theorem cell23_5154696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 2, 3, 1, 4].length) (baseStart_5154696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5154696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5154696 prefixEnd_5154696 := by exact prefixLift 5154696
  have htrace : WordTrace (prefixWord ++ tailWord_5154696) baseStart_5154696 baseEnd_5154696 := by
    simpa [prefixWord, tailWord_5154696, baseEnd_5154696] using wordTrace_append hprefix tailTrace_5154696
  have hstable : (prefixWord ++ tailWord_5154696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5154696).length < 2 ^ (prefixWord ++ tailWord_5154696).sum := by decide
  have hdescent : baseEnd_5154696 < baseStart_5154696 := by decide
  rcases family_descends (prefixWord ++ tailWord_5154696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5154725 : List Nat := [1, 3, 1, 2, 1, 1, 1, 3, 5, 1, 4]
def baseStart_5154725 : Nat := 118140960795 + 5154725 * 2 ^ 59
def prefixEnd_5154725 : Nat := 4983230072969 + 3 ^ 40 * 5154725 * 2
def baseEnd_5154725 : Nat := 2646851566747449848431357

theorem tailTrace_5154725 : CollatzResearch.WordTrace tailWord_5154725 prefixEnd_5154725 2646851566747449848431357 := by
  unfold tailWord_5154725
  simp only [CollatzResearch.WordTrace]
  refine ⟨188008266250319156786313629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125338844166879437857542419 188008266250319156786313629)
  ·
    refine ⟨70503099843869683794867611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 188008266250319156786313629 70503099843869683794867611)
    ·
      refine ⟨105754649765804525692301417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70503099843869683794867611 105754649765804525692301417)
      ·
        refine ⟨79315987324353394269226063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105754649765804525692301417 79315987324353394269226063)
        ·
          refine ⟨118973980986530091403839095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79315987324353394269226063 118973980986530091403839095)
          ·
            refine ⟨178460971479795137105758643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118973980986530091403839095 178460971479795137105758643)
            ·
              refine ⟨267691457219692705658637965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 178460971479795137105758643 267691457219692705658637965)
              ·
                refine ⟨100384296457384764621989237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 267691457219692705658637965 100384296457384764621989237)
                ·
                  refine ⟨9411027792879821683311491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 100384296457384764621989237 9411027792879821683311491)
                  ·
                    refine ⟨14116541689319732524967237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9411027792879821683311491 14116541689319732524967237)
                    ·
                      refine ⟨2646851566747449848431357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14116541689319732524967237 2646851566747449848431357)
                      ·
                        rfl

theorem cell23_5154725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 5, 1, 4].length) (baseStart_5154725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5154725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5154725 prefixEnd_5154725 := by exact prefixLift 5154725
  have htrace : WordTrace (prefixWord ++ tailWord_5154725) baseStart_5154725 baseEnd_5154725 := by
    simpa [prefixWord, tailWord_5154725, baseEnd_5154725] using wordTrace_append hprefix tailTrace_5154725
  have hstable : (prefixWord ++ tailWord_5154725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5154725).length < 2 ^ (prefixWord ++ tailWord_5154725).sum := by decide
  have hdescent : baseEnd_5154725 < baseStart_5154725 := by decide
  rcases family_descends (prefixWord ++ tailWord_5154725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5154745 : List Nat := [1, 2, 1, 4, 2, 1, 1, 2, 3, 1, 5]
def baseStart_5154745 : Nat := 118140960795 + 5154745 * 2 ^ 59
def prefixEnd_5154745 : Nat := 4983230072969 + 3 ^ 40 * 5154745 * 2
def baseEnd_5154745 : Nat := 2646861836360539770181265

theorem tailTrace_5154745 : CollatzResearch.WordTrace tailWord_5154745 prefixEnd_5154745 2646861836360539770181265 := by
  unfold tailWord_5154745
  simp only [CollatzResearch.WordTrace]
  refine ⟨188008995710246700202041689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125339330473497800134694459 188008995710246700202041689)
  ·
    refine ⟨141006746782685025151531267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188008995710246700202041689 141006746782685025151531267)
    ·
      refine ⟨211510120174027537727296901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141006746782685025151531267 211510120174027537727296901)
      ·
        refine ⟨39658147532630163323868169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 211510120174027537727296901 39658147532630163323868169)
        ·
          refine ⟨29743610649472622492901127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39658147532630163323868169 29743610649472622492901127)
          ·
            refine ⟨44615415974208933739351691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29743610649472622492901127 44615415974208933739351691)
            ·
              refine ⟨66923123961313400609027537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44615415974208933739351691 66923123961313400609027537)
              ·
                refine ⟨50192342970985050456770653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66923123961313400609027537 50192342970985050456770653)
                ·
                  refine ⟨18822128614119393921288995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50192342970985050456770653 18822128614119393921288995)
                  ·
                    refine ⟨28233192921179090881933493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18822128614119393921288995 28233192921179090881933493)
                    ·
                      refine ⟨2646861836360539770181265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28233192921179090881933493 2646861836360539770181265)
                      ·
                        rfl

theorem cell23_5154745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 2, 3, 1, 5].length) (baseStart_5154745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5154745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5154745 prefixEnd_5154745 := by exact prefixLift 5154745
  have htrace : WordTrace (prefixWord ++ tailWord_5154745) baseStart_5154745 baseEnd_5154745 := by
    simpa [prefixWord, tailWord_5154745, baseEnd_5154745] using wordTrace_append hprefix tailTrace_5154745
  have hstable : (prefixWord ++ tailWord_5154745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5154745).length < 2 ^ (prefixWord ++ tailWord_5154745).sum := by decide
  have hdescent : baseEnd_5154745 < baseStart_5154745 := by decide
  rcases family_descends (prefixWord ++ tailWord_5154745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5154770 : List Nat := [3, 2, 2, 3, 2, 1, 3, 2, 1, 1, 3]
def baseStart_5154770 : Nat := 118140960795 + 5154770 * 2 ^ 59
def prefixEnd_5154770 : Nat := 4983230072969 + 3 ^ 40 * 5154770 * 2
def baseEnd_5154770 : Nat := 2646874673376902172368651

theorem tailTrace_5154770 : CollatzResearch.WordTrace tailWord_5154770 prefixEnd_5154770 2646874673376902172368651 := by
  unfold tailWord_5154770
  simp only [CollatzResearch.WordTrace]
  refine ⟨47002476883789032367925441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125339938356770752981134509 47002476883789032367925441)
  ·
    refine ⟨35251857662841774275944081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47002476883789032367925441 35251857662841774275944081)
    ·
      refine ⟨26438893247131330706958061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35251857662841774275944081 26438893247131330706958061)
      ·
        refine ⟨9914584967674249015109273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26438893247131330706958061 9914584967674249015109273)
        ·
          refine ⟨7435938725755686761331955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9914584967674249015109273 7435938725755686761331955)
          ·
            refine ⟨11153908088633530141997933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7435938725755686761331955 11153908088633530141997933)
            ·
              refine ⟨4182715533237573803249225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11153908088633530141997933 4182715533237573803249225)
              ·
                refine ⟨3137036649928180352436919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4182715533237573803249225 3137036649928180352436919)
                ·
                  refine ⟨4705554974892270528655379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3137036649928180352436919 4705554974892270528655379)
                  ·
                    refine ⟨7058332462338405792983069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4705554974892270528655379 7058332462338405792983069)
                    ·
                      refine ⟨2646874673376902172368651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7058332462338405792983069 2646874673376902172368651)
                      ·
                        rfl

theorem cell23_5154770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 3, 2, 1, 1, 3].length) (baseStart_5154770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5154770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5154770 prefixEnd_5154770 := by exact prefixLift 5154770
  have htrace : WordTrace (prefixWord ++ tailWord_5154770) baseStart_5154770 baseEnd_5154770 := by
    simpa [prefixWord, tailWord_5154770, baseEnd_5154770] using wordTrace_append hprefix tailTrace_5154770
  have hstable : (prefixWord ++ tailWord_5154770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5154770).length < 2 ^ (prefixWord ++ tailWord_5154770).sum := by decide
  have hdescent : baseEnd_5154770 < baseStart_5154770 := by decide
  rcases family_descends (prefixWord ++ tailWord_5154770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5154792 : List Nat := [2, 1, 4, 1, 1, 1, 1, 5, 1, 3, 3]
def baseStart_5154792 : Nat := 118140960795 + 5154792 * 2 ^ 59
def prefixEnd_5154792 : Nat := 4983230072969 + 3 ^ 40 * 5154792 * 2
def baseEnd_5154792 : Nat := 2646885969951301086293549

theorem tailTrace_5154792 : CollatzResearch.WordTrace tailWord_5154792 prefixEnd_5154792 2646885969951301086293549 := by
  unfold tailWord_5154792
  simp only [CollatzResearch.WordTrace]
  refine ⟨94005354970538213614501315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125340473294050951486001753 94005354970538213614501315)
  ·
    refine ⟨141008032455807320421751973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94005354970538213614501315 141008032455807320421751973)
    ·
      refine ⟨26439006085463872579078495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 141008032455807320421751973 26439006085463872579078495)
      ·
        refine ⟨39658509128195808868617743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26439006085463872579078495 39658509128195808868617743)
        ·
          refine ⟨59487763692293713302926615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39658509128195808868617743 59487763692293713302926615)
          ·
            refine ⟨89231645538440569954389923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59487763692293713302926615 89231645538440569954389923)
            ·
              refine ⟨133847468307660854931584885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89231645538440569954389923 133847468307660854931584885)
              ·
                refine ⟨12548200153843205149836083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 133847468307660854931584885 12548200153843205149836083)
                ·
                  refine ⟨18822300230764807724754125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12548200153843205149836083 18822300230764807724754125)
                  ·
                    refine ⟨7058362586536802896782797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18822300230764807724754125 7058362586536802896782797)
                    ·
                      refine ⟨2646885969951301086293549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7058362586536802896782797 2646885969951301086293549)
                      ·
                        rfl

theorem cell23_5154792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 5, 1, 3, 3].length) (baseStart_5154792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5154792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5154792 prefixEnd_5154792 := by exact prefixLift 5154792
  have htrace : WordTrace (prefixWord ++ tailWord_5154792) baseStart_5154792 baseEnd_5154792 := by
    simpa [prefixWord, tailWord_5154792, baseEnd_5154792] using wordTrace_append hprefix tailTrace_5154792
  have hstable : (prefixWord ++ tailWord_5154792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5154792).length < 2 ^ (prefixWord ++ tailWord_5154792).sum := by decide
  have hdescent : baseEnd_5154792 < baseStart_5154792 := by decide
  rcases family_descends (prefixWord ++ tailWord_5154792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5154815 : List Nat := [1, 1, 2, 2, 1, 2, 1, 2, 4, 3, 4]
def baseStart_5154815 : Nat := 118140960795 + 5154815 * 2 ^ 59
def prefixEnd_5154815 : Nat := 4983230072969 + 3 ^ 40 * 5154815 * 2
def baseEnd_5154815 : Nat := 2646897780006354496305943

theorem tailTrace_5154815 : CollatzResearch.WordTrace tailWord_5154815 prefixEnd_5154815 2646897780006354496305943 := by
  unfold tailWord_5154815
  simp only [CollatzResearch.WordTrace]
  refine ⟨188011548819993102157089899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125341032546662068104726599 188011548819993102157089899)
  ·
    refine ⟨282017323229989653235634849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188011548819993102157089899 282017323229989653235634849)
    ·
      refine ⟨211512992422492239926726137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 282017323229989653235634849 211512992422492239926726137)
      ·
        refine ⟨158634744316869179945044603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 211512992422492239926726137 158634744316869179945044603)
        ·
          refine ⟨237952116475303769917566905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158634744316869179945044603 237952116475303769917566905)
          ·
            refine ⟨178464087356477827438175179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 237952116475303769917566905 178464087356477827438175179)
            ·
              refine ⟨267696131034716741157262769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 178464087356477827438175179 267696131034716741157262769)
              ·
                refine ⟨200772098276037555867947077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 267696131034716741157262769 200772098276037555867947077)
                ·
                  refine ⟨37644768426757041725240077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 200772098276037555867947077 37644768426757041725240077)
                  ·
                    refine ⟨14116788160033890646965029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37644768426757041725240077 14116788160033890646965029)
                    ·
                      refine ⟨2646897780006354496305943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14116788160033890646965029 2646897780006354496305943)
                      ·
                        rfl

theorem cell23_5154815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 4, 3, 4].length) (baseStart_5154815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5154815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5154815 prefixEnd_5154815 := by exact prefixLift 5154815
  have htrace : WordTrace (prefixWord ++ tailWord_5154815) baseStart_5154815 baseEnd_5154815 := by
    simpa [prefixWord, tailWord_5154815, baseEnd_5154815] using wordTrace_append hprefix tailTrace_5154815
  have hstable : (prefixWord ++ tailWord_5154815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5154815).length < 2 ^ (prefixWord ++ tailWord_5154815).sum := by decide
  have hdescent : baseEnd_5154815 < baseStart_5154815 := by decide
  rcases family_descends (prefixWord ++ tailWord_5154815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5154819 : List Nat := [1, 1, 1, 3, 2, 1, 1, 7, 1, 3, 2]
def baseStart_5154819 : Nat := 118140960795 + 5154819 * 2 ^ 59
def prefixEnd_5154819 : Nat := 4983230072969 + 3 ^ 40 * 5154819 * 2
def baseEnd_5154819 : Nat := 2646899833928972480655925

theorem tailTrace_5154819 : CollatzResearch.WordTrace tailWord_5154819 prefixEnd_5154819 2646899833928972480655925 := by
  unfold tailWord_5154819
  simp only [CollatzResearch.WordTrace]
  refine ⟨188011694711978610840235511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125341129807985740560157007 188011694711978610840235511)
  ·
    refine ⟨282017542067967916260353267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188011694711978610840235511 282017542067967916260353267)
    ·
      refine ⟨423026313101951874390529901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 282017542067967916260353267 423026313101951874390529901)
      ·
        refine ⟨158634867413231952896448713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 423026313101951874390529901 158634867413231952896448713)
        ·
          refine ⟨118976150559923964672336535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 158634867413231952896448713 118976150559923964672336535)
          ·
            refine ⟨178464225839885947008504803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118976150559923964672336535 178464225839885947008504803)
            ·
              refine ⟨267696338759828920512757205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 178464225839885947008504803 267696338759828920512757205)
              ·
                refine ⟨6274132939683490324517747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 267696338759828920512757205 6274132939683490324517747)
                ·
                  refine ⟨9411199409525235486776621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6274132939683490324517747 9411199409525235486776621)
                  ·
                    refine ⟨3529199778571963307541233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9411199409525235486776621 3529199778571963307541233)
                    ·
                      refine ⟨2646899833928972480655925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3529199778571963307541233 2646899833928972480655925)
                      ·
                        rfl

theorem cell23_5154819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 7, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 7, 1, 3, 2].length) (baseStart_5154819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5154819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5154819 prefixEnd_5154819 := by exact prefixLift 5154819
  have htrace : WordTrace (prefixWord ++ tailWord_5154819) baseStart_5154819 baseEnd_5154819 := by
    simpa [prefixWord, tailWord_5154819, baseEnd_5154819] using wordTrace_append hprefix tailTrace_5154819
  have hstable : (prefixWord ++ tailWord_5154819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5154819).length < 2 ^ (prefixWord ++ tailWord_5154819).sum := by decide
  have hdescent : baseEnd_5154819 < baseStart_5154819 := by decide
  rcases family_descends (prefixWord ++ tailWord_5154819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5154835 : List Nat := [1, 1, 1, 2, 1, 4, 2, 2, 1, 3, 5]
def baseStart_5154835 : Nat := 118140960795 + 5154835 * 2 ^ 59
def prefixEnd_5154835 : Nat := 4983230072969 + 3 ^ 40 * 5154835 * 2
def baseEnd_5154835 : Nat := 2646908049619444418055851

theorem tailTrace_5154835 : CollatzResearch.WordTrace tailWord_5154835 prefixEnd_5154835 2646908049619444418055851 := by
  unfold tailWord_5154835
  simp only [CollatzResearch.WordTrace]
  refine ⟨188012278279920645572817959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125341518853280430381878639 188012278279920645572817959)
  ·
    refine ⟨282018417419880968359226939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188012278279920645572817959 282018417419880968359226939)
    ·
      refine ⟨423027626129821452538840409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 282018417419880968359226939 423027626129821452538840409)
      ·
        refine ⟨317270719597366089404130307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 423027626129821452538840409 317270719597366089404130307)
        ·
          refine ⟨475906079396049134106195461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 317270719597366089404130307 475906079396049134106195461)
          ·
            refine ⟨89232389886759212644911649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 475906079396049134106195461 89232389886759212644911649)
            ·
              refine ⟨66924292415069409483683737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89232389886759212644911649 66924292415069409483683737)
              ·
                refine ⟨50193219311302057112762803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66924292415069409483683737 50193219311302057112762803)
                ·
                  refine ⟨75289828966953085669144205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50193219311302057112762803 75289828966953085669144205)
                  ·
                    refine ⟨28233685862607407125929077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 75289828966953085669144205 28233685862607407125929077)
                    ·
                      refine ⟨2646908049619444418055851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28233685862607407125929077 2646908049619444418055851)
                      ·
                        rfl

theorem cell23_5154835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 2, 1, 3, 5].length) (baseStart_5154835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5154835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5154835 prefixEnd_5154835 := by exact prefixLift 5154835
  have htrace : WordTrace (prefixWord ++ tailWord_5154835) baseStart_5154835 baseEnd_5154835 := by
    simpa [prefixWord, tailWord_5154835, baseEnd_5154835] using wordTrace_append hprefix tailTrace_5154835
  have hstable : (prefixWord ++ tailWord_5154835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5154835).length < 2 ^ (prefixWord ++ tailWord_5154835).sum := by decide
  have hdescent : baseEnd_5154835 < baseStart_5154835 := by decide
  rcases family_descends (prefixWord ++ tailWord_5154835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5154842 : List Nat := [3, 1, 1, 3, 1, 4, 1, 1, 2, 6]
def baseStart_5154842 : Nat := 118140960795 + 5154842 * 2 ^ 59
def prefixEnd_5154842 : Nat := 4983230072969 + 3 ^ 40 * 5154842 * 2
def baseEnd_5154842 : Nat := 882303881328008630222773

theorem tailTrace_5154842 : CollatzResearch.WordTrace tailWord_5154842 prefixEnd_5154842 882303881328008630222773 := by
  unfold tailWord_5154842
  simp only [CollatzResearch.WordTrace]
  refine ⟨47003133397723821442080695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125341689060596857178881853 47003133397723821442080695)
  ·
    refine ⟨70504700096585732163121043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47003133397723821442080695 70504700096585732163121043)
    ·
      refine ⟨105757050144878598244681565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70504700096585732163121043 105757050144878598244681565)
      ·
        refine ⟨39658893804329474341755587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105757050144878598244681565 39658893804329474341755587)
        ·
          refine ⟨59488340706494211512633381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39658893804329474341755587 59488340706494211512633381)
          ·
            refine ⟨11154063882467664658618759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59488340706494211512633381 11154063882467664658618759)
            ·
              refine ⟨16731095823701496987928139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11154063882467664658618759 16731095823701496987928139)
              ·
                refine ⟨25096643735552245481892209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16731095823701496987928139 25096643735552245481892209)
                ·
                  refine ⟨18822482801664184111419157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25096643735552245481892209 18822482801664184111419157)
                  ·
                    refine ⟨882303881328008630222773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18822482801664184111419157 882303881328008630222773)
                    ·
                      rfl

theorem cell23_5154842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 1, 2, 6].length) (baseStart_5154842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5154842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5154842 prefixEnd_5154842 := by exact prefixLift 5154842
  have htrace : WordTrace (prefixWord ++ tailWord_5154842) baseStart_5154842 baseEnd_5154842 := by
    simpa [prefixWord, tailWord_5154842, baseEnd_5154842] using wordTrace_append hprefix tailTrace_5154842
  have hstable : (prefixWord ++ tailWord_5154842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5154842).length < 2 ^ (prefixWord ++ tailWord_5154842).sum := by decide
  have hdescent : baseEnd_5154842 < baseStart_5154842 := by decide
  rcases family_descends (prefixWord ++ tailWord_5154842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5154976 : List Nat := [2, 1, 1, 4, 2, 3, 2, 1, 2, 2, 3]
def baseStart_5154976 : Nat := 118140960795 + 5154976 * 2 ^ 59
def prefixEnd_5154976 : Nat := 4983230072969 + 3 ^ 40 * 5154976 * 2
def baseEnd_5154976 : Nat := 2646980450391728366392703

theorem tailTrace_5154976 : CollatzResearch.WordTrace tailWord_5154976 prefixEnd_5154976 2646980450391728366392703 := by
  unfold tailWord_5154976
  simp only [CollatzResearch.WordTrace]
  refine ⟨94008710486204913326850391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125344947314939884435800521 94008710486204913326850391)
  ·
    refine ⟨141013065729307369990275587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94008710486204913326850391 141013065729307369990275587)
    ·
      refine ⟨211519598593961054985413381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141013065729307369990275587 211519598593961054985413381)
      ·
        refine ⟨39659924736367697809765009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 211519598593961054985413381 39659924736367697809765009)
        ·
          refine ⟨29744943552275773357323757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39659924736367697809765009 29744943552275773357323757)
          ·
            refine ⟨11154353832103415008996409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29744943552275773357323757 11154353832103415008996409)
            ·
              refine ⟨8365765374077561256747307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11154353832103415008996409 8365765374077561256747307)
              ·
                refine ⟨12548648061116341885120961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8365765374077561256747307 12548648061116341885120961)
                ·
                  refine ⟨9411486045837256413840721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12548648061116341885120961 9411486045837256413840721)
                  ·
                    refine ⟨7058614534377942310380541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9411486045837256413840721 7058614534377942310380541)
                    ·
                      refine ⟨2646980450391728366392703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7058614534377942310380541 2646980450391728366392703)
                      ·
                        rfl

theorem cell23_5154976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 2, 1, 2, 2, 3].length) (baseStart_5154976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5154976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5154976 prefixEnd_5154976 := by exact prefixLift 5154976
  have htrace : WordTrace (prefixWord ++ tailWord_5154976) baseStart_5154976 baseEnd_5154976 := by
    simpa [prefixWord, tailWord_5154976, baseEnd_5154976] using wordTrace_append hprefix tailTrace_5154976
  have hstable : (prefixWord ++ tailWord_5154976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5154976).length < 2 ^ (prefixWord ++ tailWord_5154976).sum := by decide
  have hdescent : baseEnd_5154976 < baseStart_5154976 := by decide
  rcases family_descends (prefixWord ++ tailWord_5154976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5154992 : List Nat := [2, 1, 1, 1, 2, 1, 2, 1, 7, 5]
def baseStart_5154992 : Nat := 118140960795 + 5154992 * 2 ^ 59
def prefixEnd_5154992 : Nat := 4983230072969 + 3 ^ 40 * 5154992 * 2
def baseEnd_5154992 : Nat := 882329555360733434597543

theorem tailTrace_5154992 : CollatzResearch.WordTrace tailWord_5154992 prefixEnd_5154992 882329555360733434597543 := by
  unfold tailWord_5154992
  simp only [CollatzResearch.WordTrace]
  refine ⟨94009002270175930693141615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125345336360234574257522153 94009002270175930693141615)
  ·
    refine ⟨141013503405263896039712423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94009002270175930693141615 141013503405263896039712423)
    ·
      refine ⟨211520255107895844059568635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141013503405263896039712423 211520255107895844059568635)
      ·
        refine ⟨317280382661843766089352953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211520255107895844059568635 317280382661843766089352953)
        ·
          refine ⟨237960286996382824567014715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 317280382661843766089352953 237960286996382824567014715)
          ·
            refine ⟨356940430494574236850522073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 237960286996382824567014715 356940430494574236850522073)
            ·
              refine ⟨267705322870930677637891555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 356940430494574236850522073 267705322870930677637891555)
              ·
                refine ⟨401557984306396016456837333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 267705322870930677637891555 401557984306396016456837333)
                ·
                  refine ⟨9411515257181156635707125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 401557984306396016456837333 9411515257181156635707125)
                  ·
                    refine ⟨882329555360733434597543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9411515257181156635707125 882329555360733434597543)
                    ·
                      rfl

theorem cell23_5154992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 7, 5].length) (baseStart_5154992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5154992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5154992 prefixEnd_5154992 := by exact prefixLift 5154992
  have htrace : WordTrace (prefixWord ++ tailWord_5154992) baseStart_5154992 baseEnd_5154992 := by
    simpa [prefixWord, tailWord_5154992, baseEnd_5154992] using wordTrace_append hprefix tailTrace_5154992
  have hstable : (prefixWord ++ tailWord_5154992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5154992).length < 2 ^ (prefixWord ++ tailWord_5154992).sum := by decide
  have hdescent : baseEnd_5154992 < baseStart_5154992 := by decide
  rcases family_descends (prefixWord ++ tailWord_5154992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5155039 : List Nat := [1, 1, 2, 3, 2, 1, 1, 4, 4, 4]
def baseStart_5155039 : Nat := 118140960795 + 5155039 * 2 ^ 59
def prefixEnd_5155039 : Nat := 4983230072969 + 3 ^ 40 * 5155039 * 2
def baseEnd_5155039 : Nat := 882337599890987206634971

theorem tailTrace_5155039 : CollatzResearch.WordTrace tailWord_5155039 prefixEnd_5155039 882337599890987206634971 := by
  unfold tailWord_5155039
  simp only [CollatzResearch.WordTrace]
  refine ⟨188019718771181588413244171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125346479180787725608829447 188019718771181588413244171)
  ·
    refine ⟨282029578156772382619866257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188019718771181588413244171 282029578156772382619866257)
    ·
      refine ⟨211522183617579286964899693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 282029578156772382619866257 211522183617579286964899693)
      ·
        refine ⟨79320818856592232611837385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 211522183617579286964899693 79320818856592232611837385)
        ·
          refine ⟨59490614142444174458878039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79320818856592232611837385 59490614142444174458878039)
          ·
            refine ⟨89235921213666261688317059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59490614142444174458878039 89235921213666261688317059)
            ·
              refine ⟨133853881820499392532475589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89235921213666261688317059 133853881820499392532475589)
              ·
                refine ⟨25097602841343636099839173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 133853881820499392532475589 25097602841343636099839173)
                ·
                  refine ⟨4705800532751931768719845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25097602841343636099839173 4705800532751931768719845)
                  ·
                    refine ⟨882337599890987206634971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4705800532751931768719845 882337599890987206634971)
                    ·
                      rfl

theorem cell23_5155039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 4, 4, 4].length) (baseStart_5155039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5155039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5155039 prefixEnd_5155039 := by exact prefixLift 5155039
  have htrace : WordTrace (prefixWord ++ tailWord_5155039) baseStart_5155039 baseEnd_5155039 := by
    simpa [prefixWord, tailWord_5155039, baseEnd_5155039] using wordTrace_append hprefix tailTrace_5155039
  have hstable : (prefixWord ++ tailWord_5155039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5155039).length < 2 ^ (prefixWord ++ tailWord_5155039).sum := by decide
  have hdescent : baseEnd_5155039 < baseStart_5155039 := by decide
  rcases family_descends (prefixWord ++ tailWord_5155039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5155043 : List Nat := [1, 1, 1, 8, 1, 1, 1, 3, 1, 5]
def baseStart_5155043 : Nat := 118140960795 + 5155043 * 2 ^ 59
def prefixEnd_5155043 : Nat := 4983230072969 + 3 ^ 40 * 5155043 * 2
def baseEnd_5155043 : Nat := 882338284531859868084965

theorem tailTrace_5155043 : CollatzResearch.WordTrace tailWord_5155043 prefixEnd_5155043 882338284531859868084965 := by
  unfold tailWord_5155043
  simp only [CollatzResearch.WordTrace]
  refine ⟨188019864663167097096389783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125346576442111398064259855 188019864663167097096389783)
  ·
    refine ⟨282029796994750645644584675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188019864663167097096389783 282029796994750645644584675)
    ·
      refine ⟨423044695492125968466877013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 282029796994750645644584675 423044695492125968466877013)
      ·
        refine ⟨4957555025298351192971215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 423044695492125968466877013 4957555025298351192971215)
        ·
          refine ⟨7436332537947526789456823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4957555025298351192971215 7436332537947526789456823)
          ·
            refine ⟨11154498806921290184185235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7436332537947526789456823 11154498806921290184185235)
            ·
              refine ⟨16731748210381935276277853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11154498806921290184185235 16731748210381935276277853)
              ·
                refine ⟨6274405578893225728604195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16731748210381935276277853 6274405578893225728604195)
                ·
                  refine ⟨9411608368339838592906293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6274405578893225728604195 9411608368339838592906293)
                  ·
                    refine ⟨882338284531859868084965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9411608368339838592906293 882338284531859868084965)
                    ·
                      rfl

theorem cell23_5155043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 3, 1, 5].length) (baseStart_5155043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5155043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5155043 prefixEnd_5155043 := by exact prefixLift 5155043
  have htrace : WordTrace (prefixWord ++ tailWord_5155043) baseStart_5155043 baseEnd_5155043 := by
    simpa [prefixWord, tailWord_5155043, baseEnd_5155043] using wordTrace_append hprefix tailTrace_5155043
  have hstable : (prefixWord ++ tailWord_5155043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5155043).length < 2 ^ (prefixWord ++ tailWord_5155043).sum := by decide
  have hdescent : baseEnd_5155043 < baseStart_5155043 := by decide
  rcases family_descends (prefixWord ++ tailWord_5155043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5155052 : List Nat := [2, 2, 1, 1, 2, 3, 12]
def baseStart_5155052 : Nat := 118140960795 + 5155052 * 2 ^ 59
def prefixEnd_5155052 : Nat := 4983230072969 + 3 ^ 40 * 5155052 * 2
def baseEnd_5155052 : Nat := 32679252776808272457313

theorem tailTrace_5155052 : CollatzResearch.WordTrace tailWord_5155052 prefixEnd_5155052 32679252776808272457313 := by
  unfold tailWord_5155052
  simp only [CollatzResearch.WordTrace]
  refine ⟨94010096460067245816733705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125346795280089661088978273 94010096460067245816733705)
  ·
    refine ⟨70507572345050434362550279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94010096460067245816733705 70507572345050434362550279)
    ·
      refine ⟨105761358517575651543825419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70507572345050434362550279 105761358517575651543825419)
      ·
        refine ⟨158642037776363477315738129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105761358517575651543825419 158642037776363477315738129)
        ·
          refine ⟨118981528332272607986803597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 158642037776363477315738129 118981528332272607986803597)
          ·
            refine ⟨44618073124602227995051349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 118981528332272607986803597 44618073124602227995051349)
            ·
              refine ⟨32679252776808272457313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 44618073124602227995051349 32679252776808272457313)
              ·
                rfl

theorem cell23_5155052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 12].length) (baseStart_5155052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5155052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5155052 prefixEnd_5155052 := by exact prefixLift 5155052
  have htrace : WordTrace (prefixWord ++ tailWord_5155052) baseStart_5155052 baseEnd_5155052 := by
    simpa [prefixWord, tailWord_5155052, baseEnd_5155052] using wordTrace_append hprefix tailTrace_5155052
  have hstable : (prefixWord ++ tailWord_5155052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5155052).length < 2 ^ (prefixWord ++ tailWord_5155052).sum := by decide
  have hdescent : baseEnd_5155052 < baseStart_5155052 := by decide
  rcases family_descends (prefixWord ++ tailWord_5155052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5155073 : List Nat := [1, 2, 4, 1, 1, 2, 5, 1, 2, 4]
def baseStart_5155073 : Nat := 118140960795 + 5155073 * 2 ^ 59
def prefixEnd_5155073 : Nat := 4983230072969 + 3 ^ 40 * 5155073 * 2
def baseEnd_5155073 : Nat := 882343419338404828959919

theorem tailTrace_5155073 : CollatzResearch.WordTrace tailWord_5155073 prefixEnd_5155073 882343419338404828959919 := by
  unfold tailWord_5155073
  simp only [CollatzResearch.WordTrace]
  refine ⟨188020958853058412219981873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125347305902038941479987915 188020958853058412219981873)
  ·
    refine ⟨141015719139793809164986405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188020958853058412219981873 141015719139793809164986405)
    ·
      refine ⟨26440447338711339218434951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 141015719139793809164986405 26440447338711339218434951)
      ·
        refine ⟨39660671008067008827652427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26440447338711339218434951 39660671008067008827652427)
        ·
          refine ⟨59491006512100513241478641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39660671008067008827652427 59491006512100513241478641)
          ·
            refine ⟨44618254884075384931108981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59491006512100513241478641 44618254884075384931108981)
            ·
              refine ⟨4182961395382067337291467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44618254884075384931108981 4182961395382067337291467)
              ·
                refine ⟨6274442093073101005937201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4182961395382067337291467 6274442093073101005937201)
                ·
                  refine ⟨4705831569804825754452901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6274442093073101005937201 4705831569804825754452901)
                  ·
                    refine ⟨882343419338404828959919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4705831569804825754452901 882343419338404828959919)
                    ·
                      rfl

theorem cell23_5155073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 5, 1, 2, 4].length) (baseStart_5155073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5155073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5155073 prefixEnd_5155073 := by exact prefixLift 5155073
  have htrace : WordTrace (prefixWord ++ tailWord_5155073) baseStart_5155073 baseEnd_5155073 := by
    simpa [prefixWord, tailWord_5155073, baseEnd_5155073] using wordTrace_append hprefix tailTrace_5155073
  have hstable : (prefixWord ++ tailWord_5155073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5155073).length < 2 ^ (prefixWord ++ tailWord_5155073).sum := by decide
  have hdescent : baseEnd_5155073 < baseStart_5155073 := by decide
  rcases family_descends (prefixWord ++ tailWord_5155073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5155076 : List Nat := [2, 3, 2, 2, 3, 1, 1, 1, 1, 1, 6]
def baseStart_5155076 : Nat := 118140960795 + 5155076 * 2 ^ 59
def prefixEnd_5155076 : Nat := 4983230072969 + 3 ^ 40 * 5155076 * 2
def baseEnd_5155076 : Nat := 2647031798457177975142243

theorem tailTrace_5155076 : CollatzResearch.WordTrace tailWord_5155076 prefixEnd_5155076 2647031798457177975142243 := by
  unfold tailWord_5155076
  simp only [CollatzResearch.WordTrace]
  refine ⟨94010534136023771866170541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125347378848031695821560721 94010534136023771866170541)
  ·
    refine ⟨35253950301008914449813953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94010534136023771866170541 35253950301008914449813953)
    ·
      refine ⟨26440462725756685837360465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35253950301008914449813953 26440462725756685837360465)
      ·
        refine ⟨19830347044317514378020349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26440462725756685837360465 19830347044317514378020349)
        ·
          refine ⟨7436380141619067891757631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19830347044317514378020349 7436380141619067891757631)
          ·
            refine ⟨11154570212428601837636447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7436380141619067891757631 11154570212428601837636447)
            ·
              refine ⟨16731855318642902756454671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11154570212428601837636447 16731855318642902756454671)
              ·
                refine ⟨25097782977964354134682007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16731855318642902756454671 25097782977964354134682007)
                ·
                  refine ⟨37646674466946531202023011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25097782977964354134682007 37646674466946531202023011)
                  ·
                    refine ⟨56470011700419796803034517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37646674466946531202023011 56470011700419796803034517)
                    ·
                      refine ⟨2647031798457177975142243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56470011700419796803034517 2647031798457177975142243)
                      ·
                        rfl

theorem cell23_5155076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 1, 1, 1, 6].length) (baseStart_5155076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5155076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5155076 prefixEnd_5155076 := by exact prefixLift 5155076
  have htrace : WordTrace (prefixWord ++ tailWord_5155076) baseStart_5155076 baseEnd_5155076 := by
    simpa [prefixWord, tailWord_5155076, baseEnd_5155076] using wordTrace_append hprefix tailTrace_5155076
  have hstable : (prefixWord ++ tailWord_5155076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5155076).length < 2 ^ (prefixWord ++ tailWord_5155076).sum := by decide
  have hdescent : baseEnd_5155076 < baseStart_5155076 := by decide
  rcases family_descends (prefixWord ++ tailWord_5155076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5155096 : List Nat := [2, 1, 2, 3, 1, 2, 1, 1, 6, 1, 3]
def baseStart_5155096 : Nat := 118140960795 + 5155096 * 2 ^ 59
def prefixEnd_5155096 : Nat := 4983230072969 + 3 ^ 40 * 5155096 * 2
def baseEnd_5155096 : Nat := 2647042068070267896892151

theorem tailTrace_5155096 : CollatzResearch.WordTrace tailWord_5155096 prefixEnd_5155096 2647042068070267896892151 := by
  unfold tailWord_5155096
  simp only [CollatzResearch.WordTrace]
  refine ⟨94010898865987543574034571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125347865154650058098712761 94010898865987543574034571)
  ·
    refine ⟨141016348298981315361051857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94010898865987543574034571 141016348298981315361051857)
    ·
      refine ⟨105762261224235986520788893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141016348298981315361051857 105762261224235986520788893)
      ·
        refine ⟨39660847959088494945295835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105762261224235986520788893 39660847959088494945295835)
        ·
          refine ⟨59491271938632742417943753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39660847959088494945295835 59491271938632742417943753)
          ·
            refine ⟨44618453953974556813457815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59491271938632742417943753 44618453953974556813457815)
            ·
              refine ⟨66927680930961835220186723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44618453953974556813457815 66927680930961835220186723)
              ·
                refine ⟨100391521396442752830280085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66927680930961835220186723 100391521396442752830280085)
                ·
                  refine ⟨4705852565458254038919379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 100391521396442752830280085 4705852565458254038919379)
                  ·
                    refine ⟨7058778848187381058379069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4705852565458254038919379 7058778848187381058379069)
                    ·
                      refine ⟨2647042068070267896892151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7058778848187381058379069 2647042068070267896892151)
                      ·
                        rfl

theorem cell23_5155096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 6, 1, 3].length) (baseStart_5155096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5155096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5155096 prefixEnd_5155096 := by exact prefixLift 5155096
  have htrace : WordTrace (prefixWord ++ tailWord_5155096) baseStart_5155096 baseEnd_5155096 := by
    simpa [prefixWord, tailWord_5155096, baseEnd_5155096] using wordTrace_append hprefix tailTrace_5155096
  have hstable : (prefixWord ++ tailWord_5155096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5155096).length < 2 ^ (prefixWord ++ tailWord_5155096).sum := by decide
  have hdescent : baseEnd_5155096 < baseStart_5155096 := by decide
  rcases family_descends (prefixWord ++ tailWord_5155096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5155114 : List Nat := [3, 1, 4, 2, 3, 1, 1, 1, 3, 2, 2]
def baseStart_5155114 : Nat := 118140960795 + 5155114 * 2 ^ 59
def prefixEnd_5155114 : Nat := 4983230072969 + 3 ^ 40 * 5155114 * 2
def baseEnd_5155114 : Nat := 2647051310722048826467069

theorem tailTrace_5155114 : CollatzResearch.WordTrace tailWord_5155114 prefixEnd_5155114 2647051310722048826467069 := by
  unfold tailWord_5155114
  simp only [CollatzResearch.WordTrace]
  refine ⟨47005613561477469055556099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125348302830606584148149597 47005613561477469055556099)
  ·
    refine ⟨70508420342216203583334149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47005613561477469055556099 70508420342216203583334149)
    ·
      refine ⟨13220328814165538171875153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70508420342216203583334149 13220328814165538171875153)
      ·
        refine ⟨9915246610624153628906365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13220328814165538171875153 9915246610624153628906365)
        ·
          refine ⟨3718217478984057610839887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9915246610624153628906365 3718217478984057610839887)
          ·
            refine ⟨5577326218476086416259831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3718217478984057610839887 5577326218476086416259831)
            ·
              refine ⟨8365989327714129624389747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5577326218476086416259831 8365989327714129624389747)
              ·
                refine ⟨12548983991571194436584621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8365989327714129624389747 12548983991571194436584621)
                ·
                  refine ⟨4705868996839197913719233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12548983991571194436584621 4705868996839197913719233)
                  ·
                    refine ⟨3529401747629398435289425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4705868996839197913719233 3529401747629398435289425)
                    ·
                      refine ⟨2647051310722048826467069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3529401747629398435289425 2647051310722048826467069)
                      ·
                        rfl

theorem cell23_5155114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 1, 1, 3, 2, 2].length) (baseStart_5155114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5155114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5155114 prefixEnd_5155114 := by exact prefixLift 5155114
  have htrace : WordTrace (prefixWord ++ tailWord_5155114) baseStart_5155114 baseEnd_5155114 := by
    simpa [prefixWord, tailWord_5155114, baseEnd_5155114] using wordTrace_append hprefix tailTrace_5155114
  have hstable : (prefixWord ++ tailWord_5155114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5155114).length < 2 ^ (prefixWord ++ tailWord_5155114).sum := by decide
  have hdescent : baseEnd_5155114 < baseStart_5155114 := by decide
  rcases family_descends (prefixWord ++ tailWord_5155114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5155130 : List Nat := [3, 1, 1, 1, 4, 2, 4, 1, 2, 1, 3]
def baseStart_5155130 : Nat := 118140960795 + 5155130 * 2 ^ 59
def prefixEnd_5155130 : Nat := 4983230072969 + 3 ^ 40 * 5155130 * 2
def baseEnd_5155130 : Nat := 2647059526412520763866995

theorem tailTrace_5155130 : CollatzResearch.WordTrace tailWord_5155130 prefixEnd_5155130 2647059526412520763866995 := by
  unfold tailWord_5155130
  simp only [CollatzResearch.WordTrace]
  refine ⟨47005759453462977738701711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125348691875901273969871229 47005759453462977738701711)
  ·
    refine ⟨70508639180194466608052567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47005759453462977738701711 70508639180194466608052567)
    ·
      refine ⟨105762958770291699912078851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70508639180194466608052567 105762958770291699912078851)
      ·
        refine ⟨158644438155437549868118277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105762958770291699912078851 158644438155437549868118277)
        ·
          refine ⟨29745832154144540600272177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 158644438155437549868118277 29745832154144540600272177)
          ·
            refine ⟨22309374115608405450204133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29745832154144540600272177 22309374115608405450204133)
            ·
              refine ⟨4183007646676576021913275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22309374115608405450204133 4183007646676576021913275)
              ·
                refine ⟨6274511470014864032869913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4183007646676576021913275 6274511470014864032869913)
                ·
                  refine ⟨4705883602511148024652435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6274511470014864032869913 4705883602511148024652435)
                  ·
                    refine ⟨7058825403766722036978653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4705883602511148024652435 7058825403766722036978653)
                    ·
                      refine ⟨2647059526412520763866995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7058825403766722036978653 2647059526412520763866995)
                      ·
                        rfl

theorem cell23_5155130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 4, 1, 2, 1, 3].length) (baseStart_5155130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5155130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5155130 prefixEnd_5155130 := by exact prefixLift 5155130
  have htrace : WordTrace (prefixWord ++ tailWord_5155130) baseStart_5155130 baseEnd_5155130 := by
    simpa [prefixWord, tailWord_5155130, baseEnd_5155130] using wordTrace_append hprefix tailTrace_5155130
  have hstable : (prefixWord ++ tailWord_5155130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5155130).length < 2 ^ (prefixWord ++ tailWord_5155130).sum := by decide
  have hdescent : baseEnd_5155130 < baseStart_5155130 := by decide
  rcases family_descends (prefixWord ++ tailWord_5155130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5155139 : List Nat := [1, 1, 1, 3, 1, 3, 3, 2, 2, 1, 5]
def baseStart_5155139 : Nat := 118140960795 + 5155139 * 2 ^ 59
def prefixEnd_5155139 : Nat := 4983230072969 + 3 ^ 40 * 5155139 * 2
def baseEnd_5155139 : Nat := 2647064147738411228654453

theorem tailTrace_5155139 : CollatzResearch.WordTrace tailWord_5155139 prefixEnd_5155139 2647064147738411228654453 := by
  unfold tailWord_5155139
  simp only [CollatzResearch.WordTrace]
  refine ⟨188023366070819305491884471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125348910713879536994589647 188023366070819305491884471)
  ·
    refine ⟨282035049106228958237826707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188023366070819305491884471 282035049106228958237826707)
    ·
      refine ⟨423052573659343437356740061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 282035049106228958237826707 423052573659343437356740061)
      ·
        refine ⟨158644715122253789008777523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 423052573659343437356740061 158644715122253789008777523)
        ·
          refine ⟨237967072683380683513166285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158644715122253789008777523 237967072683380683513166285)
          ·
            refine ⟨89237652256267756317437357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 237967072683380683513166285 89237652256267756317437357)
            ·
              refine ⟨33464119596100408619039009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89237652256267756317437357 33464119596100408619039009)
              ·
                refine ⟨25098089697075306464279257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33464119596100408619039009 25098089697075306464279257)
                ·
                  refine ⟨18823567272806479848209443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25098089697075306464279257 18823567272806479848209443)
                  ·
                    refine ⟨28235350909209719772314165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18823567272806479848209443 28235350909209719772314165)
                    ·
                      refine ⟨2647064147738411228654453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28235350909209719772314165 2647064147738411228654453)
                      ·
                        rfl

theorem cell23_5155139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 2, 2, 1, 5].length) (baseStart_5155139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5155139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5155139 prefixEnd_5155139 := by exact prefixLift 5155139
  have htrace : WordTrace (prefixWord ++ tailWord_5155139) baseStart_5155139 baseEnd_5155139 := by
    simpa [prefixWord, tailWord_5155139, baseEnd_5155139] using wordTrace_append hprefix tailTrace_5155139
  have hstable : (prefixWord ++ tailWord_5155139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5155139).length < 2 ^ (prefixWord ++ tailWord_5155139).sum := by decide
  have hdescent : baseEnd_5155139 < baseStart_5155139 := by decide
  rcases family_descends (prefixWord ++ tailWord_5155139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5155153 : List Nat := [1, 2, 2, 1, 4, 3, 1, 2, 1, 4, 2]
def baseStart_5155153 : Nat := 118140960795 + 5155153 * 2 ^ 59
def prefixEnd_5155153 : Nat := 4983230072969 + 3 ^ 40 * 5155153 * 2
def baseEnd_5155153 : Nat := 2647071336467574173879389

theorem tailTrace_5155153 : CollatzResearch.WordTrace tailWord_5155153 prefixEnd_5155153 2647071336467574173879389 := by
  unfold tailWord_5155153
  simp only [CollatzResearch.WordTrace]
  refine ⟨188023876692768585882894113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125349251128512390588596075 188023876692768585882894113)
  ·
    refine ⟨141017907519576439412170585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188023876692768585882894113 141017907519576439412170585)
    ·
      refine ⟨105763430639682329559127939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141017907519576439412170585 105763430639682329559127939)
      ·
        refine ⟨158645145959523494338691909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105763430639682329559127939 158645145959523494338691909)
        ·
          refine ⟨29745964867410655188504733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 158645145959523494338691909 29745964867410655188504733)
          ·
            refine ⟨11154736825278995695689275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29745964867410655188504733 11154736825278995695689275)
            ·
              refine ⟨16732105237918493543533913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11154736825278995695689275 16732105237918493543533913)
              ·
                refine ⟨12549078928438870157650435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16732105237918493543533913 12549078928438870157650435)
                ·
                  refine ⟨18823618392658305236475653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12549078928438870157650435 18823618392658305236475653)
                  ·
                    refine ⟨3529428448623432231839185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18823618392658305236475653 3529428448623432231839185)
                    ·
                      refine ⟨2647071336467574173879389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3529428448623432231839185 2647071336467574173879389)
                      ·
                        rfl

theorem cell23_5155153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 2, 1, 4, 2].length) (baseStart_5155153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5155153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5155153 prefixEnd_5155153 := by exact prefixLift 5155153
  have htrace : WordTrace (prefixWord ++ tailWord_5155153) baseStart_5155153 baseEnd_5155153 := by
    simpa [prefixWord, tailWord_5155153, baseEnd_5155153] using wordTrace_append hprefix tailTrace_5155153
  have hstable : (prefixWord ++ tailWord_5155153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5155153).length < 2 ^ (prefixWord ++ tailWord_5155153).sum := by decide
  have hdescent : baseEnd_5155153 < baseStart_5155153 := by decide
  rcases family_descends (prefixWord ++ tailWord_5155153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5155156 : List Nat := [2, 4, 1, 1, 2, 2, 2, 1, 2, 1, 5]
def baseStart_5155156 : Nat := 118140960795 + 5155156 * 2 ^ 59
def prefixEnd_5155156 : Nat := 4983230072969 + 3 ^ 40 * 5155156 * 2
def baseEnd_5155156 : Nat := 2647072876909537662141875

theorem tailTrace_5155156 : CollatzResearch.WordTrace tailWord_5155156 prefixEnd_5155156 2647072876909537662141875 := by
  unfold tailWord_5155156
  simp only [CollatzResearch.WordTrace]
  refine ⟨94011993055878858697626661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125349324074505144930168881 94011993055878858697626661)
  ·
    refine ⟨17627248697977286005804999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94011993055878858697626661 17627248697977286005804999)
    ·
      refine ⟨26440873046965929008707499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17627248697977286005804999 26440873046965929008707499)
      ·
        refine ⟨39661309570448893513061249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26440873046965929008707499 39661309570448893513061249)
        ·
          refine ⟨29745982177836670134795937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39661309570448893513061249 29745982177836670134795937)
          ·
            refine ⟨22309486633377502601096953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29745982177836670134795937 22309486633377502601096953)
            ·
              refine ⟨16732114975033126950822715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22309486633377502601096953 16732114975033126950822715)
              ·
                refine ⟨25098172462549690426234073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16732114975033126950822715 25098172462549690426234073)
                ·
                  refine ⟨18823629346912267819675555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25098172462549690426234073 18823629346912267819675555)
                  ·
                    refine ⟨28235444020368401729513333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18823629346912267819675555 28235444020368401729513333)
                    ·
                      refine ⟨2647072876909537662141875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28235444020368401729513333 2647072876909537662141875)
                      ·
                        rfl

theorem cell23_5155156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 1, 2, 1, 5].length) (baseStart_5155156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5155156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5155156 prefixEnd_5155156 := by exact prefixLift 5155156
  have htrace : WordTrace (prefixWord ++ tailWord_5155156) baseStart_5155156 baseEnd_5155156 := by
    simpa [prefixWord, tailWord_5155156, baseEnd_5155156] using wordTrace_append hprefix tailTrace_5155156
  have hstable : (prefixWord ++ tailWord_5155156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5155156).length < 2 ^ (prefixWord ++ tailWord_5155156).sum := by decide
  have hdescent : baseEnd_5155156 < baseStart_5155156 := by decide
  rcases family_descends (prefixWord ++ tailWord_5155156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5155157 : List Nat := [1, 3, 2, 2, 4, 1, 3, 1, 1, 3, 2]
def baseStart_5155157 : Nat := 118140960795 + 5155157 * 2 ^ 59
def prefixEnd_5155157 : Nat := 4983230072969 + 3 ^ 40 * 5155157 * 2
def baseEnd_5155157 : Nat := 2647073390390192158229371

theorem tailTrace_5155157 : CollatzResearch.WordTrace tailWord_5155157 prefixEnd_5155157 2647073390390192158229371 := by
  unfold tailWord_5155157
  simp only [CollatzResearch.WordTrace]
  refine ⟨188024022584754094566039725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125349348389836063044026483 188024022584754094566039725)
  ·
    refine ⟨70509008469282785462264897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 188024022584754094566039725 70509008469282785462264897)
    ·
      refine ⟨52881756351962089096698673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70509008469282785462264897 52881756351962089096698673)
      ·
        refine ⟨39661317263971566822524005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52881756351962089096698673 39661317263971566822524005)
        ·
          refine ⟨7436496986994668779223251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39661317263971566822524005 7436496986994668779223251)
          ·
            refine ⟨11154745480492003168834877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7436496986994668779223251 11154745480492003168834877)
            ·
              refine ⟨4183029555184501188313079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11154745480492003168834877 4183029555184501188313079)
              ·
                refine ⟨6274544332776751782469619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4183029555184501188313079 6274544332776751782469619)
                ·
                  refine ⟨9411816499165127673704429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6274544332776751782469619 9411816499165127673704429)
                  ·
                    refine ⟨3529431187186922877639161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9411816499165127673704429 3529431187186922877639161)
                    ·
                      refine ⟨2647073390390192158229371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3529431187186922877639161 2647073390390192158229371)
                      ·
                        rfl

theorem cell23_5155157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 3, 1, 1, 3, 2].length) (baseStart_5155157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5155157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5155157 prefixEnd_5155157 := by exact prefixLift 5155157
  have htrace : WordTrace (prefixWord ++ tailWord_5155157) baseStart_5155157 baseEnd_5155157 := by
    simpa [prefixWord, tailWord_5155157, baseEnd_5155157] using wordTrace_append hprefix tailTrace_5155157
  have hstable : (prefixWord ++ tailWord_5155157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5155157).length < 2 ^ (prefixWord ++ tailWord_5155157).sum := by decide
  have hdescent : baseEnd_5155157 < baseStart_5155157 := by decide
  rcases family_descends (prefixWord ++ tailWord_5155157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5155186 : List Nat := [3, 2, 1, 2, 1, 3, 1, 1, 1, 5, 3]
def baseStart_5155186 : Nat := 118140960795 + 5155186 * 2 ^ 59
def prefixEnd_5155186 : Nat := 4983230072969 + 3 ^ 40 * 5155186 * 2
def baseEnd_5155186 : Nat := 2647088281329172544766737

theorem tailTrace_5155186 : CollatzResearch.WordTrace tailWord_5155186 prefixEnd_5155186 2647088281329172544766737 := by
  unfold tailWord_5155186
  simp only [CollatzResearch.WordTrace]
  refine ⟨47006270075412258129711353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125350053534432688345896941 47006270075412258129711353)
  ·
    refine ⟨35254702556559193597283515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47006270075412258129711353 35254702556559193597283515)
    ·
      refine ⟨52882053834838790395925273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35254702556559193597283515 52882053834838790395925273)
      ·
        refine ⟨39661540376129092796943955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52882053834838790395925273 39661540376129092796943955)
        ·
          refine ⟨59492310564193639195415933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39661540376129092796943955 59492310564193639195415933)
          ·
            refine ⟨22309616461572614698280975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59492310564193639195415933 22309616461572614698280975)
            ·
              refine ⟨33464424692358922047421463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22309616461572614698280975 33464424692358922047421463)
              ·
                refine ⟨50196637038538383071132195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33464424692358922047421463 50196637038538383071132195)
                ·
                  refine ⟨75294955557807574606698293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50196637038538383071132195 75294955557807574606698293)
                  ·
                    refine ⟨7058902083544460119377965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 75294955557807574606698293 7058902083544460119377965)
                    ·
                      refine ⟨2647088281329172544766737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7058902083544460119377965 2647088281329172544766737)
                      ·
                        rfl

theorem cell23_5155186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 1, 1, 5, 3].length) (baseStart_5155186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5155186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5155186 prefixEnd_5155186 := by exact prefixLift 5155186
  have htrace : WordTrace (prefixWord ++ tailWord_5155186) baseStart_5155186 baseEnd_5155186 := by
    simpa [prefixWord, tailWord_5155186, baseEnd_5155186] using wordTrace_append hprefix tailTrace_5155186
  have hstable : (prefixWord ++ tailWord_5155186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5155186).length < 2 ^ (prefixWord ++ tailWord_5155186).sum := by decide
  have hdescent : baseEnd_5155186 < baseStart_5155186 := by decide
  rcases family_descends (prefixWord ++ tailWord_5155186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5155296 : List Nat := [2, 1, 1, 3, 1, 1, 4, 2, 3, 5]
def baseStart_5155296 : Nat := 118140960795 + 5155296 * 2 ^ 59
def prefixEnd_5155296 : Nat := 4983230072969 + 3 ^ 40 * 5155296 * 2
def baseEnd_5155296 : Nat := 882381588067055704797077

theorem tailTrace_5155296 : CollatzResearch.WordTrace tailWord_5155296 prefixEnd_5155296 882381588067055704797077 := by
  unfold tailWord_5155296
  simp only [CollatzResearch.WordTrace]
  refine ⟨94014546165625260652674871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125352728220833680870233161 94014546165625260652674871)
  ·
    refine ⟨141021819248437890979012307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94014546165625260652674871 141021819248437890979012307)
    ·
      refine ⟨211532728872656836468518461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141021819248437890979012307 211532728872656836468518461)
      ·
        refine ⟨79324773327246313675694423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 211532728872656836468518461 79324773327246313675694423)
        ·
          refine ⟨118987159990869470513541635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79324773327246313675694423 118987159990869470513541635)
          ·
            refine ⟨178480739986304205770312453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118987159990869470513541635 178480739986304205770312453)
            ·
              refine ⟨33465138747432038581933585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 178480739986304205770312453 33465138747432038581933585)
              ·
                refine ⟨25098854060574028936450189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33465138747432038581933585 25098854060574028936450189)
                ·
                  refine ⟨9412070272715260851168821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25098854060574028936450189 9412070272715260851168821)
                  ·
                    refine ⟨882381588067055704797077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9412070272715260851168821 882381588067055704797077)
                    ·
                      rfl

theorem cell23_5155296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 2, 3, 5].length) (baseStart_5155296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5155296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5155296 prefixEnd_5155296 := by exact prefixLift 5155296
  have htrace : WordTrace (prefixWord ++ tailWord_5155296) baseStart_5155296 baseEnd_5155296 := by
    simpa [prefixWord, tailWord_5155296, baseEnd_5155296] using wordTrace_append hprefix tailTrace_5155296
  have hstable : (prefixWord ++ tailWord_5155296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5155296).length < 2 ^ (prefixWord ++ tailWord_5155296).sum := by decide
  have hdescent : baseEnd_5155296 < baseStart_5155296 := by decide
  rcases family_descends (prefixWord ++ tailWord_5155296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5155320 : List Nat := [2, 1, 2, 1, 1, 4, 4, 1, 2, 3, 2]
def baseStart_5155320 : Nat := 118140960795 + 5155320 * 2 ^ 59
def prefixEnd_5155320 : Nat := 4983230072969 + 3 ^ 40 * 5155320 * 2
def baseEnd_5155320 : Nat := 2647157087736875020491121

theorem tailTrace_5155320 : CollatzResearch.WordTrace tailWord_5155320 prefixEnd_5155320 2647157087736875020491121 := by
  unfold tailWord_5155320
  simp only [CollatzResearch.WordTrace]
  refine ⟨94014983841581786702111707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125353311788775715602815609 94014983841581786702111707)
  ·
    refine ⟨141022475762372680053167561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94014983841581786702111707 141022475762372680053167561)
    ·
      refine ⟨105766856821779510039875671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141022475762372680053167561 105766856821779510039875671)
      ·
        refine ⟨158650285232669265059813507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105766856821779510039875671 158650285232669265059813507)
        ·
          refine ⟨237975427849003897589720261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158650285232669265059813507 237975427849003897589720261)
          ·
            refine ⟨44620392721688230798072549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 237975427849003897589720261 44620392721688230798072549)
            ·
              refine ⟨8366323635316543274638603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44620392721688230798072549 8366323635316543274638603)
              ·
                refine ⟨12549485452974814911957905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8366323635316543274638603 12549485452974814911957905)
                ·
                  refine ⟨9412114089731111183968429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12549485452974814911957905 9412114089731111183968429)
                  ·
                    refine ⟨3529542783649166693988161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9412114089731111183968429 3529542783649166693988161)
                    ·
                      refine ⟨2647157087736875020491121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3529542783649166693988161 2647157087736875020491121)
                      ·
                        rfl

theorem cell23_5155320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 4, 1, 2, 3, 2].length) (baseStart_5155320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5155320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5155320 prefixEnd_5155320 := by exact prefixLift 5155320
  have htrace : WordTrace (prefixWord ++ tailWord_5155320) baseStart_5155320 baseEnd_5155320 := by
    simpa [prefixWord, tailWord_5155320, baseEnd_5155320] using wordTrace_append hprefix tailTrace_5155320
  have hstable : (prefixWord ++ tailWord_5155320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5155320).length < 2 ^ (prefixWord ++ tailWord_5155320).sum := by decide
  have hdescent : baseEnd_5155320 < baseStart_5155320 := by decide
  rcases family_descends (prefixWord ++ tailWord_5155320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5155333 : List Nat := [1, 3, 1, 1, 2, 2, 2, 5, 1, 1, 4]
def baseStart_5155333 : Nat := 118140960795 + 5155333 * 2 ^ 59
def prefixEnd_5155333 : Nat := 4983230072969 + 3 ^ 40 * 5155333 * 2
def baseEnd_5155333 : Nat := 2647163762985383469628561

theorem tailTrace_5155333 : CollatzResearch.WordTrace tailWord_5155333 prefixEnd_5155333 2647163762985383469628561 := by
  unfold tailWord_5155333
  simp only [CollatzResearch.WordTrace]
  refine ⟨188030441832116476624446653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125353627888077651082964435 188030441832116476624446653)
  ·
    refine ⟨70511415687043678734167495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 188030441832116476624446653 70511415687043678734167495)
    ·
      refine ⟨105767123530565518101251243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70511415687043678734167495 105767123530565518101251243)
      ·
        refine ⟨158650685295848277151876865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105767123530565518101251243 158650685295848277151876865)
        ·
          refine ⟨118988013971886207863907649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 158650685295848277151876865 118988013971886207863907649)
          ·
            refine ⟨89241010478914655897930737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118988013971886207863907649 89241010478914655897930737)
            ·
              refine ⟨66930757859185991923448053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89241010478914655897930737 66930757859185991923448053)
              ·
                refine ⟨6274758549298686742823255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 66930757859185991923448053 6274758549298686742823255)
                ·
                  refine ⟨9412137823948030114234883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6274758549298686742823255 9412137823948030114234883)
                  ·
                    refine ⟨14118206735922045171352325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9412137823948030114234883 14118206735922045171352325)
                    ·
                      refine ⟨2647163762985383469628561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14118206735922045171352325 2647163762985383469628561)
                      ·
                        rfl

theorem cell23_5155333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 5, 1, 1, 4].length) (baseStart_5155333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5155333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5155333 prefixEnd_5155333 := by exact prefixLift 5155333
  have htrace : WordTrace (prefixWord ++ tailWord_5155333) baseStart_5155333 baseEnd_5155333 := by
    simpa [prefixWord, tailWord_5155333, baseEnd_5155333] using wordTrace_append hprefix tailTrace_5155333
  have hstable : (prefixWord ++ tailWord_5155333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5155333).length < 2 ^ (prefixWord ++ tailWord_5155333).sum := by decide
  have hdescent : baseEnd_5155333 < baseStart_5155333 := by decide
  rcases family_descends (prefixWord ++ tailWord_5155333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5155334 : List Nat := [6, 2, 1, 1, 1, 2, 2, 2, 6]
def baseStart_5155334 : Nat := 118140960795 + 5155334 * 2 ^ 59
def prefixEnd_5155334 : Nat := 4983230072969 + 3 ^ 40 * 5155334 * 2
def baseEnd_5155334 : Nat := 294129364051781996190673

theorem tailTrace_5155334 : CollatzResearch.WordTrace tailWord_5155334 prefixEnd_5155334 294129364051781996190673 := by
  unfold tailWord_5155334
  simp only [CollatzResearch.WordTrace]
  refine ⟨5875952447034776681101033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 125353652203408569196822037 5875952447034776681101033)
  ·
    refine ⟨4406964335276082510825775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5875952447034776681101033 4406964335276082510825775)
    ·
      refine ⟨6610446502914123766238663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4406964335276082510825775 6610446502914123766238663)
      ·
        refine ⟨9915669754371185649357995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6610446502914123766238663 9915669754371185649357995)
        ·
          refine ⟨14873504631556778474036993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9915669754371185649357995 14873504631556778474036993)
          ·
            refine ⟨11155128473667583855527745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14873504631556778474036993 11155128473667583855527745)
            ·
              refine ⟨8366346355250687891645809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11155128473667583855527745 8366346355250687891645809)
              ·
                refine ⟨6274759766438015918734357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8366346355250687891645809 6274759766438015918734357)
                ·
                  refine ⟨294129364051781996190673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6274759766438015918734357 294129364051781996190673)
                  ·
                    rfl

theorem cell23_5155334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 2, 2, 6].length) (baseStart_5155334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5155334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5155334 prefixEnd_5155334 := by exact prefixLift 5155334
  have htrace : WordTrace (prefixWord ++ tailWord_5155334) baseStart_5155334 baseEnd_5155334 := by
    simpa [prefixWord, tailWord_5155334, baseEnd_5155334] using wordTrace_append hprefix tailTrace_5155334
  have hstable : (prefixWord ++ tailWord_5155334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5155334).length < 2 ^ (prefixWord ++ tailWord_5155334).sum := by decide
  have hdescent : baseEnd_5155334 < baseStart_5155334 := by decide
  rcases family_descends (prefixWord ++ tailWord_5155334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5155343 : List Nat := [1, 1, 2, 1, 1, 1, 2, 8, 2, 4]
def baseStart_5155343 : Nat := 118140960795 + 5155343 * 2 ^ 59
def prefixEnd_5155343 : Nat := 4983230072969 + 3 ^ 40 * 5155343 * 2
def baseEnd_5155343 : Nat := 882389632597309476834505

theorem tailTrace_5155343 : CollatzResearch.WordTrace tailWord_5155343 prefixEnd_5155343 882389632597309476834505 := by
  unfold tailWord_5155343
  simp only [CollatzResearch.WordTrace]
  refine ⟨188030806562080248332310683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125353871041386832221540455 188030806562080248332310683)
  ·
    refine ⟨282046209843120372498466025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188030806562080248332310683 282046209843120372498466025)
    ·
      refine ⟨211534657382340279373849519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 282046209843120372498466025 211534657382340279373849519)
      ·
        refine ⟨317301986073510419060774279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211534657382340279373849519 317301986073510419060774279)
        ·
          refine ⟨475952979110265628591161419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 317301986073510419060774279 475952979110265628591161419)
          ·
            refine ⟨713929468665398442886742129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 475952979110265628591161419 713929468665398442886742129)
            ·
              refine ⟨535447101499048832165056597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 713929468665398442886742129 535447101499048832165056597)
              ·
                refine ⟨6274770720691978501934257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 535447101499048832165056597 6274770720691978501934257)
                ·
                  refine ⟨4706078040518983876450693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6274770720691978501934257 4706078040518983876450693)
                  ·
                    refine ⟨882389632597309476834505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4706078040518983876450693 882389632597309476834505)
                    ·
                      rfl

theorem cell23_5155343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 8, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 8, 2, 4].length) (baseStart_5155343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5155343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5155343 prefixEnd_5155343 := by exact prefixLift 5155343
  have htrace : WordTrace (prefixWord ++ tailWord_5155343) baseStart_5155343 baseEnd_5155343 := by
    simpa [prefixWord, tailWord_5155343, baseEnd_5155343] using wordTrace_append hprefix tailTrace_5155343
  have hstable : (prefixWord ++ tailWord_5155343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5155343).length < 2 ^ (prefixWord ++ tailWord_5155343).sum := by decide
  have hdescent : baseEnd_5155343 < baseStart_5155343 := by decide
  rcases family_descends (prefixWord ++ tailWord_5155343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5155360 : List Nat := [2, 1, 1, 6, 2, 1, 2, 1, 1, 6]
def baseStart_5155360 : Nat := 118140960795 + 5155360 * 2 ^ 59
def prefixEnd_5155360 : Nat := 4983230072969 + 3 ^ 40 * 5155360 * 2
def baseEnd_5155360 : Nat := 882392542321018287996979

theorem tailTrace_5155360 : CollatzResearch.WordTrace tailWord_5155360 prefixEnd_5155360 882392542321018287996979 := by
  unfold tailWord_5155360
  simp only [CollatzResearch.WordTrace]
  refine ⟨94015713301509330117839767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125354284402012440157119689 94015713301509330117839767)
  ·
    refine ⟨141023569952263995176759651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94015713301509330117839767 141023569952263995176759651)
    ·
      refine ⟨211535354928395992765139477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141023569952263995176759651 211535354928395992765139477)
      ·
        refine ⟨9915719762268562160865913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 211535354928395992765139477 9915719762268562160865913)
        ·
          refine ⟨7436789821701421620649435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9915719762268562160865913 7436789821701421620649435)
          ·
            refine ⟨11155184732552132430974153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7436789821701421620649435 11155184732552132430974153)
            ·
              refine ⟨8366388549414099323230615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11155184732552132430974153 8366388549414099323230615)
              ·
                refine ⟨12549582824121148984845923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8366388549414099323230615 12549582824121148984845923)
                ·
                  refine ⟨18824374236181723477268885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12549582824121148984845923 18824374236181723477268885)
                  ·
                    refine ⟨882392542321018287996979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18824374236181723477268885 882392542321018287996979)
                    ·
                      rfl

theorem cell23_5155360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 2, 1, 1, 6].length) (baseStart_5155360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5155360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5155360 prefixEnd_5155360 := by exact prefixLift 5155360
  have htrace : WordTrace (prefixWord ++ tailWord_5155360) baseStart_5155360 baseEnd_5155360 := by
    simpa [prefixWord, tailWord_5155360, baseEnd_5155360] using wordTrace_append hprefix tailTrace_5155360
  have hstable : (prefixWord ++ tailWord_5155360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5155360).length < 2 ^ (prefixWord ++ tailWord_5155360).sum := by decide
  have hdescent : baseEnd_5155360 < baseStart_5155360 := by decide
  rcases family_descends (prefixWord ++ tailWord_5155360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5155363 : List Nat := [1, 1, 1, 4, 4, 1, 1, 3, 1, 2, 4]
def baseStart_5155363 : Nat := 118140960795 + 5155363 * 2 ^ 59
def prefixEnd_5155363 : Nat := 4983230072969 + 3 ^ 40 * 5155363 * 2
def baseEnd_5155363 : Nat := 2647179167405018352253423

theorem tailTrace_5155363 : CollatzResearch.WordTrace tailWord_5155363 prefixEnd_5155363 2647179167405018352253423 := by
  unfold tailWord_5155363
  simp only [CollatzResearch.WordTrace]
  refine ⟨188031536022007791748038743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125354357348005194498692495 188031536022007791748038743)
  ·
    refine ⟨282047304033011687622058115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188031536022007791748038743 282047304033011687622058115)
    ·
      refine ⟨423070956049517531433087173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 282047304033011687622058115 423070956049517531433087173)
      ·
        refine ⟨79325804259284537143703845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 423070956049517531433087173 79325804259284537143703845)
        ·
          refine ⟨14873588298615850714444471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 79325804259284537143703845 14873588298615850714444471)
          ·
            refine ⟨22310382447923776071666707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14873588298615850714444471 22310382447923776071666707)
            ·
              refine ⟨33465573671885664107500061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22310382447923776071666707 33465573671885664107500061)
              ·
                refine ⟨12549590126957124040312523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33465573671885664107500061 12549590126957124040312523)
                ·
                  refine ⟨18824385190435686060468785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12549590126957124040312523 18824385190435686060468785)
                  ·
                    refine ⟨14118288892826764545351589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18824385190435686060468785 14118288892826764545351589)
                    ·
                      refine ⟨2647179167405018352253423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14118288892826764545351589 2647179167405018352253423)
                      ·
                        rfl

theorem cell23_5155363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 3, 1, 2, 4].length) (baseStart_5155363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5155363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5155363 prefixEnd_5155363 := by exact prefixLift 5155363
  have htrace : WordTrace (prefixWord ++ tailWord_5155363) baseStart_5155363 baseEnd_5155363 := by
    simpa [prefixWord, tailWord_5155363, baseEnd_5155363] using wordTrace_append hprefix tailTrace_5155363
  have hstable : (prefixWord ++ tailWord_5155363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5155363).length < 2 ^ (prefixWord ++ tailWord_5155363).sum := by decide
  have hdescent : baseEnd_5155363 < baseStart_5155363 := by decide
  rcases family_descends (prefixWord ++ tailWord_5155363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5155370 : List Nat := [3, 1, 4, 1, 1, 2, 2, 1, 3, 2, 3]
def baseStart_5155370 : Nat := 118140960795 + 5155370 * 2 ^ 59
def prefixEnd_5155370 : Nat := 4983230072969 + 3 ^ 40 * 5155370 * 2
def baseEnd_5155370 : Nat := 2647182761769599824865891

theorem tailTrace_5155370 : CollatzResearch.WordTrace tailWord_5155370 prefixEnd_5155370 2647182761769599824865891 := by
  unfold tailWord_5155370
  simp only [CollatzResearch.WordTrace]
  refine ⟨47007947833245607985885891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125354527555321621295695709 47007947833245607985885891)
  ·
    refine ⟨70511921749868411978828837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47007947833245607985885891 70511921749868411978828837)
    ·
      refine ⟨13220985328100327246030407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70511921749868411978828837 13220985328100327246030407)
      ·
        refine ⟨19831477992150490869045611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13220985328100327246030407 19831477992150490869045611)
        ·
          refine ⟨29747216988225736303568417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19831477992150490869045611 29747216988225736303568417)
          ·
            refine ⟨22310412741169302227676313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29747216988225736303568417 22310412741169302227676313)
            ·
              refine ⟨16732809555876976670757235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22310412741169302227676313 16732809555876976670757235)
              ·
                refine ⟨25099214333815465006135853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16732809555876976670757235 25099214333815465006135853)
                ·
                  refine ⟨9412205375180799377300945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25099214333815465006135853 9412205375180799377300945)
                  ·
                    refine ⟨7059154031385599532975709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9412205375180799377300945 7059154031385599532975709)
                    ·
                      refine ⟨2647182761769599824865891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7059154031385599532975709 2647182761769599824865891)
                      ·
                        rfl

theorem cell23_5155370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 1, 3, 2, 3].length) (baseStart_5155370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5155370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5155370 prefixEnd_5155370 := by exact prefixLift 5155370
  have htrace : WordTrace (prefixWord ++ tailWord_5155370) baseStart_5155370 baseEnd_5155370 := by
    simpa [prefixWord, tailWord_5155370, baseEnd_5155370] using wordTrace_append hprefix tailTrace_5155370
  have hstable : (prefixWord ++ tailWord_5155370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5155370).length < 2 ^ (prefixWord ++ tailWord_5155370).sum := by decide
  have hdescent : baseEnd_5155370 < baseStart_5155370 := by decide
  rcases family_descends (prefixWord ++ tailWord_5155370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5155383 : List Nat := [1, 1, 3, 1, 2, 3, 1, 4, 1, 3, 3]
def baseStart_5155383 : Nat := 118140960795 + 5155383 * 2 ^ 59
def prefixEnd_5155383 : Nat := 4983230072969 + 3 ^ 40 * 5155383 * 2
def baseEnd_5155383 : Nat := 2647189437018108274003331

theorem tailTrace_5155383 : CollatzResearch.WordTrace tailWord_5155383 prefixEnd_5155383 2647189437018108274003331 := by
  unfold tailWord_5155383
  simp only [CollatzResearch.WordTrace]
  refine ⟨188032265481935335163766803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125354843654623556775844535 188032265481935335163766803)
  ·
    refine ⟨282048398222903002745650205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188032265481935335163766803 282048398222903002745650205)
    ·
      refine ⟨105768149333588626029618827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 282048398222903002745650205 105768149333588626029618827)
      ·
        refine ⟨158652224000382939044428241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105768149333588626029618827 158652224000382939044428241)
        ·
          refine ⟨118989168000287204283321181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 158652224000382939044428241 118989168000287204283321181)
          ·
            refine ⟨44620938000107701606245443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 118989168000287204283321181 44620938000107701606245443)
            ·
              refine ⟨66931407000161552409368165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44620938000107701606245443 66931407000161552409368165)
              ·
                refine ⟨12549638812530291076756531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 66931407000161552409368165 12549638812530291076756531)
                ·
                  refine ⟨18824458218795436615134797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12549638812530291076756531 18824458218795436615134797)
                  ·
                    refine ⟨7059171832048288730675549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18824458218795436615134797 7059171832048288730675549)
                    ·
                      refine ⟨2647189437018108274003331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7059171832048288730675549 2647189437018108274003331)
                      ·
                        rfl

theorem cell23_5155383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 4, 1, 3, 3].length) (baseStart_5155383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5155383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5155383 prefixEnd_5155383 := by exact prefixLift 5155383
  have htrace : WordTrace (prefixWord ++ tailWord_5155383) baseStart_5155383 baseEnd_5155383 := by
    simpa [prefixWord, tailWord_5155383, baseEnd_5155383] using wordTrace_append hprefix tailTrace_5155383
  have hstable : (prefixWord ++ tailWord_5155383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5155383).length < 2 ^ (prefixWord ++ tailWord_5155383).sum := by decide
  have hdescent : baseEnd_5155383 < baseStart_5155383 := by decide
  rcases family_descends (prefixWord ++ tailWord_5155383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5155384 : List Nat := [2, 1, 2, 1, 4, 1, 4, 3, 1, 2, 2]
def baseStart_5155384 : Nat := 118140960795 + 5155384 * 2 ^ 59
def prefixEnd_5155384 : Nat := 4983230072969 + 3 ^ 40 * 5155384 * 2
def baseEnd_5155384 : Nat := 2647189950498762770090827

theorem tailTrace_5155384 : CollatzResearch.WordTrace tailWord_5155384 prefixEnd_5155384 2647189950498762770090827 := by
  unfold tailWord_5155384
  simp only [CollatzResearch.WordTrace]
  refine ⟨94016150977465856167276603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125354867969954474889702137 94016150977465856167276603)
  ·
    refine ⟨141024226466198784250914905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94016150977465856167276603 141024226466198784250914905)
    ·
      refine ⟨105768169849649088188186179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141024226466198784250914905 105768169849649088188186179)
      ·
        refine ⟨158652254774473632282279269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105768169849649088188186179 158652254774473632282279269)
        ·
          refine ⟨29747297770213806052927363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 158652254774473632282279269 29747297770213806052927363)
          ·
            refine ⟨44620946655320709079391045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29747297770213806052927363 44620946655320709079391045)
            ·
              refine ⟨8366427497872632952385821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44620946655320709079391045 8366427497872632952385821)
              ·
                refine ⟨3137410311702237357144683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8366427497872632952385821 3137410311702237357144683)
                ·
                  refine ⟨4706115467553356035717025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3137410311702237357144683 4706115467553356035717025)
                  ·
                    refine ⟨3529586600665017026787769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4706115467553356035717025 3529586600665017026787769)
                    ·
                      refine ⟨2647189950498762770090827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3529586600665017026787769 2647189950498762770090827)
                      ·
                        rfl

theorem cell23_5155384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 4, 3, 1, 2, 2].length) (baseStart_5155384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5155384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5155384 prefixEnd_5155384 := by exact prefixLift 5155384
  have htrace : WordTrace (prefixWord ++ tailWord_5155384) baseStart_5155384 baseEnd_5155384 := by
    simpa [prefixWord, tailWord_5155384, baseEnd_5155384] using wordTrace_append hprefix tailTrace_5155384
  have hstable : (prefixWord ++ tailWord_5155384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5155384).length < 2 ^ (prefixWord ++ tailWord_5155384).sum := by decide
  have hdescent : baseEnd_5155384 < baseStart_5155384 := by decide
  rcases family_descends (prefixWord ++ tailWord_5155384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5155390 : List Nat := [4, 2, 1, 4, 1, 1, 10]
def baseStart_5155390 : Nat := 118140960795 + 5155390 * 2 ^ 59
def prefixEnd_5155390 : Nat := 4983230072969 + 3 ^ 40 * 5155390 * 2
def baseEnd_5155390 : Nat := 32681395449169009217479

theorem tailTrace_5155390 : CollatzResearch.WordTrace tailWord_5155390 prefixEnd_5155390 32681395449169009217479 := by
  unfold tailWord_5155390
  simp only [CollatzResearch.WordTrace]
  refine ⟨23504065099113746919908953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125355013861939983572847749 23504065099113746919908953)
  ·
    refine ⟨17628048824335310189931715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23504065099113746919908953 17628048824335310189931715)
    ·
      refine ⟨26442073236502965284897573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17628048824335310189931715 26442073236502965284897573)
      ·
        refine ⟨4957888731844305990918295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26442073236502965284897573 4957888731844305990918295)
        ·
          refine ⟨7436833097766458986377443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4957888731844305990918295 7436833097766458986377443)
          ·
            refine ⟨11155249646649688479566165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7436833097766458986377443 11155249646649688479566165)
            ·
              refine ⟨32681395449169009217479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 11155249646649688479566165 32681395449169009217479)
              ·
                rfl

theorem cell23_5155390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 10].length) (baseStart_5155390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5155390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5155390 prefixEnd_5155390 := by exact prefixLift 5155390
  have htrace : WordTrace (prefixWord ++ tailWord_5155390) baseStart_5155390 baseEnd_5155390 := by
    simpa [prefixWord, tailWord_5155390, baseEnd_5155390] using wordTrace_append hprefix tailTrace_5155390
  have hstable : (prefixWord ++ tailWord_5155390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5155390).length < 2 ^ (prefixWord ++ tailWord_5155390).sum := by decide
  have hdescent : baseEnd_5155390 < baseStart_5155390 := by decide
  rcases family_descends (prefixWord ++ tailWord_5155390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5155427 : List Nat := [1, 1, 1, 5, 1, 2, 4, 2, 1, 3, 2]
def baseStart_5155427 : Nat := 118140960795 + 5155427 * 2 ^ 59
def prefixEnd_5155427 : Nat := 4983230072969 + 3 ^ 40 * 5155427 * 2
def baseEnd_5155427 : Nat := 2647212030166906101853129

theorem tailTrace_5155427 : CollatzResearch.WordTrace tailWord_5155427 prefixEnd_5155427 2647212030166906101853129 := by
  unfold tailWord_5155427
  simp only [CollatzResearch.WordTrace]
  refine ⟨188033870293775930678368535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125355913529183953785579023 188033870293775930678368535)
  ·
    refine ⟨282050805440663896017552803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188033870293775930678368535 282050805440663896017552803)
    ·
      refine ⟨423076208160995844026329205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 282050805440663896017552803 423076208160995844026329205)
      ·
        refine ⟨39663394515093360377468363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 423076208160995844026329205 39663394515093360377468363)
        ·
          refine ⟨59495091772640040566202545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39663394515093360377468363 59495091772640040566202545)
          ·
            refine ⟨44621318829480030424651909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59495091772640040566202545 44621318829480030424651909)
            ·
              refine ⟨8366497280527505704622233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44621318829480030424651909 8366497280527505704622233)
              ·
                refine ⟨6274872960395629278466675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8366497280527505704622233 6274872960395629278466675)
                ·
                  refine ⟨9412309440593443917700013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6274872960395629278466675 9412309440593443917700013)
                  ·
                    refine ⟨3529616040222541469137505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9412309440593443917700013 3529616040222541469137505)
                    ·
                      refine ⟨2647212030166906101853129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3529616040222541469137505 2647212030166906101853129)
                      ·
                        rfl

theorem cell23_5155427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 4, 2, 1, 3, 2].length) (baseStart_5155427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5155427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5155427 prefixEnd_5155427 := by exact prefixLift 5155427
  have htrace : WordTrace (prefixWord ++ tailWord_5155427) baseStart_5155427 baseEnd_5155427 := by
    simpa [prefixWord, tailWord_5155427, baseEnd_5155427] using wordTrace_append hprefix tailTrace_5155427
  have hstable : (prefixWord ++ tailWord_5155427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5155427).length < 2 ^ (prefixWord ++ tailWord_5155427).sum := by decide
  have hdescent : baseEnd_5155427 < baseStart_5155427 := by decide
  rcases family_descends (prefixWord ++ tailWord_5155427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5155457 : List Nat := [1, 2, 4, 2, 1, 1, 1, 3, 4, 2, 2]
def baseStart_5155457 : Nat := 118140960795 + 5155457 * 2 ^ 59
def prefixEnd_5155457 : Nat := 4983230072969 + 3 ^ 40 * 5155457 * 2
def baseEnd_5155457 : Nat := 2647227434586540984477991

theorem tailTrace_5155457 : CollatzResearch.WordTrace tailWord_5155457 prefixEnd_5155457 2647227434586540984477991 := by
  unfold tailWord_5155457
  simp only [CollatzResearch.WordTrace]
  refine ⟨188034964483667245801960625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125356642989111497201307083 188034964483667245801960625)
  ·
    refine ⟨141026223362750434351470469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188034964483667245801960625 141026223362750434351470469)
    ·
      refine ⟨26442416880515706440900713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 141026223362750434351470469 26442416880515706440900713)
      ·
        refine ⟨19831812660386779830675535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26442416880515706440900713 19831812660386779830675535)
        ·
          refine ⟨29747718990580169746013303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19831812660386779830675535 29747718990580169746013303)
          ·
            refine ⟨44621578485870254619019955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29747718990580169746013303 44621578485870254619019955)
            ·
              refine ⟨66932367728805381928529933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44621578485870254619019955 66932367728805381928529933)
              ·
                refine ⟨25099637898302018223198725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66932367728805381928529933 25099637898302018223198725)
                ·
                  refine ⟨4706182105931628416849761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25099637898302018223198725 4706182105931628416849761)
                  ·
                    refine ⟨3529636579448721312637321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4706182105931628416849761 3529636579448721312637321)
                    ·
                      refine ⟨2647227434586540984477991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3529636579448721312637321 2647227434586540984477991)
                      ·
                        rfl

theorem cell23_5155457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 3, 4, 2, 2].length) (baseStart_5155457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5155457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5155457 prefixEnd_5155457 := by exact prefixLift 5155457
  have htrace : WordTrace (prefixWord ++ tailWord_5155457) baseStart_5155457 baseEnd_5155457 := by
    simpa [prefixWord, tailWord_5155457, baseEnd_5155457] using wordTrace_append hprefix tailTrace_5155457
  have hstable : (prefixWord ++ tailWord_5155457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5155457).length < 2 ^ (prefixWord ++ tailWord_5155457).sum := by decide
  have hdescent : baseEnd_5155457 < baseStart_5155457 := by decide
  rcases family_descends (prefixWord ++ tailWord_5155457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5155473 : List Nat := [1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 3]
def baseStart_5155473 : Nat := 118140960795 + 5155473 * 2 ^ 59
def prefixEnd_5155473 : Nat := 4983230072969 + 3 ^ 40 * 5155473 * 2
def baseEnd_5155473 : Nat := 2647235650277012921877917

theorem tailTrace_5155473 : CollatzResearch.WordTrace tailWord_5155473 prefixEnd_5155473 2647235650277012921877917 := by
  unfold tailWord_5155473
  simp only [CollatzResearch.WordTrace]
  refine ⟨188035548051609280534543073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125357032034406187023028715 188035548051609280534543073)
  ·
    refine ⟨141026661038706960400907305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188035548051609280534543073 141026661038706960400907305)
    ·
      refine ⟨105769995779030220300680479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141026661038706960400907305 105769995779030220300680479)
      ·
        refine ⟨158654993668545330451020719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105769995779030220300680479 158654993668545330451020719)
        ·
          refine ⟨237982490502817995676531079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158654993668545330451020719 237982490502817995676531079)
          ·
            refine ⟨356973735754226993514796619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 237982490502817995676531079 356973735754226993514796619)
            ·
              refine ⟨535460603631340490272194929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 356973735754226993514796619 535460603631340490272194929)
              ·
                refine ⟨401595452723505367704146197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 535460603631340490272194929 401595452723505367704146197)
                ·
                  refine ⟨18824786846414314111131853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 401595452723505367704146197 18824786846414314111131853)
                  ·
                    refine ⟨7059295067405367791674445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18824786846414314111131853 7059295067405367791674445)
                    ·
                      refine ⟨2647235650277012921877917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7059295067405367791674445 2647235650277012921877917)
                      ·
                        rfl

theorem cell23_5155473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 3].length) (baseStart_5155473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5155473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5155473 prefixEnd_5155473 := by exact prefixLift 5155473
  have htrace : WordTrace (prefixWord ++ tailWord_5155473) baseStart_5155473 baseEnd_5155473 := by
    simpa [prefixWord, tailWord_5155473, baseEnd_5155473] using wordTrace_append hprefix tailTrace_5155473
  have hstable : (prefixWord ++ tailWord_5155473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5155473).length < 2 ^ (prefixWord ++ tailWord_5155473).sum := by decide
  have hdescent : baseEnd_5155473 < baseStart_5155473 := by decide
  rcases family_descends (prefixWord ++ tailWord_5155473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5155503 : List Nat := [1, 1, 2, 1, 2, 5, 1, 2, 1, 2, 5]
def baseStart_5155503 : Nat := 118140960795 + 5155503 * 2 ^ 59
def prefixEnd_5155503 : Nat := 4983230072969 + 3 ^ 40 * 5155503 * 2
def baseEnd_5155503 : Nat := 2647251054696647804502779

theorem tailTrace_5155503 : CollatzResearch.WordTrace tailWord_5155503 prefixEnd_5155503 2647251054696647804502779 := by
  unfold tailWord_5155503
  simp only [CollatzResearch.WordTrace]
  refine ⟨188036642241500595658135163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125357761494333730438756775 188036642241500595658135163)
  ·
    refine ⟨282054963362250893487202745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188036642241500595658135163 282054963362250893487202745)
    ·
      refine ⟨211541222521688170115402059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 282054963362250893487202745 211541222521688170115402059)
      ·
        refine ⟨317311833782532255173103089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211541222521688170115402059 317311833782532255173103089)
        ·
          refine ⟨237983875336899191379827317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 317311833782532255173103089 237983875336899191379827317)
          ·
            refine ⟨22310988312834299191858811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 237983875336899191379827317 22310988312834299191858811)
            ·
              refine ⟨33466482469251448787788217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22310988312834299191858811 33466482469251448787788217)
              ·
                refine ⟨25099861851938586590841163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33466482469251448787788217 25099861851938586590841163)
                ·
                  refine ⟨37649792777907879886261745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25099861851938586590841163 37649792777907879886261745)
                  ·
                    refine ⟨28237344583430909914696309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37649792777907879886261745 28237344583430909914696309)
                    ·
                      refine ⟨2647251054696647804502779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28237344583430909914696309 2647251054696647804502779)
                      ·
                        rfl

theorem cell23_5155503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 2, 1, 2, 5].length) (baseStart_5155503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5155503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5155503 prefixEnd_5155503 := by exact prefixLift 5155503
  have htrace : WordTrace (prefixWord ++ tailWord_5155503) baseStart_5155503 baseEnd_5155503 := by
    simpa [prefixWord, tailWord_5155503, baseEnd_5155503] using wordTrace_append hprefix tailTrace_5155503
  have hstable : (prefixWord ++ tailWord_5155503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5155503).length < 2 ^ (prefixWord ++ tailWord_5155503).sum := by decide
  have hdescent : baseEnd_5155503 < baseStart_5155503 := by decide
  rcases family_descends (prefixWord ++ tailWord_5155503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5155513 : List Nat := [1, 2, 1, 4, 1, 1, 1, 2, 3, 3, 4]
def baseStart_5155513 : Nat := 118140960795 + 5155513 * 2 ^ 59
def prefixEnd_5155513 : Nat := 4983230072969 + 3 ^ 40 * 5155513 * 2
def baseEnd_5155513 : Nat := 2647256189503192765377733

theorem tailTrace_5155513 : CollatzResearch.WordTrace tailWord_5155513 prefixEnd_5155513 2647256189503192765377733 := by
  unfold tailWord_5155513
  simp only [CollatzResearch.WordTrace]
  refine ⟨188037006971464367365999193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125358004647642911577332795 188037006971464367365999193)
  ·
    refine ⟨141027755228598275524499395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188037006971464367365999193 141027755228598275524499395)
    ·
      refine ⟨211541632842897413286749093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141027755228598275524499395 211541632842897413286749093)
      ·
        refine ⟨39664056158043264991265455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 211541632842897413286749093 39664056158043264991265455)
        ·
          refine ⟨59496084237064897486898183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39664056158043264991265455 59496084237064897486898183)
          ·
            refine ⟨89244126355597346230347275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59496084237064897486898183 89244126355597346230347275)
            ·
              refine ⟨133866189533396019345520913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89244126355597346230347275 133866189533396019345520913)
              ·
                refine ⟨100399642150047014509140685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 133866189533396019345520913 100399642150047014509140685)
                ·
                  refine ⟨37649865806267630440927757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 100399642150047014509140685 37649865806267630440927757)
                  ·
                    refine ⟨14118699677350361415347909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37649865806267630440927757 14118699677350361415347909)
                    ·
                      refine ⟨2647256189503192765377733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14118699677350361415347909 2647256189503192765377733)
                      ·
                        rfl

theorem cell23_5155513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 3, 3, 4].length) (baseStart_5155513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5155513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5155513 prefixEnd_5155513 := by exact prefixLift 5155513
  have htrace : WordTrace (prefixWord ++ tailWord_5155513) baseStart_5155513 baseEnd_5155513 := by
    simpa [prefixWord, tailWord_5155513, baseEnd_5155513] using wordTrace_append hprefix tailTrace_5155513
  have hstable : (prefixWord ++ tailWord_5155513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5155513).length < 2 ^ (prefixWord ++ tailWord_5155513).sum := by decide
  have hdescent : baseEnd_5155513 < baseStart_5155513 := by decide
  rcases family_descends (prefixWord ++ tailWord_5155513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5155570 : List Nat := [3, 2, 1, 3, 1, 3, 1, 1, 8]
def baseStart_5155570 : Nat := 118140960795 + 5155570 * 2 ^ 59
def prefixEnd_5155570 : Nat := 4983230072969 + 3 ^ 40 * 5155570 * 2
def baseEnd_5155570 : Nat := 294142828655611004707219

theorem tailTrace_5155570 : CollatzResearch.WordTrace tailWord_5155570 prefixEnd_5155570 294142828655611004707219 := by
  unfold tailWord_5155570
  simp only [CollatzResearch.WordTrace]
  refine ⟨47009771483064466525206041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125359390621505244067216109 47009771483064466525206041)
  ·
    refine ⟨35257328612298349893904531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47009771483064466525206041 35257328612298349893904531)
    ·
      refine ⟨52885992918447524840856797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35257328612298349893904531 52885992918447524840856797)
      ·
        refine ⟨19832247344417821815321299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52885992918447524840856797 19832247344417821815321299)
        ·
          refine ⟨29748371016626732722981949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19832247344417821815321299 29748371016626732722981949)
          ·
            refine ⟨11155639131235024771118231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29748371016626732722981949 11155639131235024771118231)
            ·
              refine ⟨16733458696852537156677347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11155639131235024771118231 16733458696852537156677347)
              ·
                refine ⟨25100188045278805735016021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16733458696852537156677347 25100188045278805735016021)
                ·
                  refine ⟨294142828655611004707219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25100188045278805735016021 294142828655611004707219)
                  ·
                    rfl

theorem cell23_5155570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 1, 8].length) (baseStart_5155570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5155570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5155570 prefixEnd_5155570 := by exact prefixLift 5155570
  have htrace : WordTrace (prefixWord ++ tailWord_5155570) baseStart_5155570 baseEnd_5155570 := by
    simpa [prefixWord, tailWord_5155570, baseEnd_5155570] using wordTrace_append hprefix tailTrace_5155570
  have hstable : (prefixWord ++ tailWord_5155570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5155570).length < 2 ^ (prefixWord ++ tailWord_5155570).sum := by decide
  have hdescent : baseEnd_5155570 < baseStart_5155570 := by decide
  rcases family_descends (prefixWord ++ tailWord_5155570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5155574 : List Nat := [5, 1, 1, 1, 1, 2, 1, 6, 1, 4]
def baseStart_5155574 : Nat := 118140960795 + 5155574 * 2 ^ 59
def prefixEnd_5155574 : Nat := 4983230072969 + 3 ^ 40 * 5155574 * 2
def baseEnd_5155574 : Nat := 882429170607705675571651

theorem tailTrace_5155574 : CollatzResearch.WordTrace tailWord_5155574 prefixEnd_5155574 882429170607705675571651 := by
  unfold tailWord_5155574
  simp only [CollatzResearch.WordTrace]
  refine ⟨11752451989015210923998111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 125359487882828916522646517 11752451989015210923998111)
  ·
    refine ⟨17628677983522816385997167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11752451989015210923998111 17628677983522816385997167)
    ·
      refine ⟨26443016975284224578995751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17628677983522816385997167 26443016975284224578995751)
      ·
        refine ⟨39664525462926336868493627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26443016975284224578995751 39664525462926336868493627)
        ·
          refine ⟨59496788194389505302740441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39664525462926336868493627 59496788194389505302740441)
          ·
            refine ⟨44622591145792128977055331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59496788194389505302740441 44622591145792128977055331)
            ·
              refine ⟨66933886718688193465582997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44622591145792128977055331 66933886718688193465582997)
              ·
                refine ⟨3137525939938509068699203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 66933886718688193465582997 3137525939938509068699203)
                ·
                  refine ⟨4706288909907763603048805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3137525939938509068699203 4706288909907763603048805)
                  ·
                    refine ⟨882429170607705675571651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4706288909907763603048805 882429170607705675571651)
                    ·
                      rfl

theorem cell23_5155574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 6, 1, 4].length) (baseStart_5155574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5155574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5155574 prefixEnd_5155574 := by exact prefixLift 5155574
  have htrace : WordTrace (prefixWord ++ tailWord_5155574) baseStart_5155574 baseEnd_5155574 := by
    simpa [prefixWord, tailWord_5155574, baseEnd_5155574] using wordTrace_append hprefix tailTrace_5155574
  have hstable : (prefixWord ++ tailWord_5155574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5155574).length < 2 ^ (prefixWord ++ tailWord_5155574).sum := by decide
  have hdescent : baseEnd_5155574 < baseStart_5155574 := by decide
  rcases family_descends (prefixWord ++ tailWord_5155574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5155593 : List Nat := [1, 2, 1, 1, 3, 2, 2, 1, 2, 1, 7]
def baseStart_5155593 : Nat := 118140960795 + 5155593 * 2 ^ 59
def prefixEnd_5155593 : Nat := 4983230072969 + 3 ^ 40 * 5155593 * 2
def baseEnd_5155593 : Nat := 2647297267955552452377365

theorem tailTrace_5155593 : CollatzResearch.WordTrace tailWord_5155593 prefixEnd_5155593 2647297267955552452377365 := by
  unfold tailWord_5155593
  simp only [CollatzResearch.WordTrace]
  refine ⟨188039924811174541028911433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125359949874116360685940955 188039924811174541028911433)
  ·
    refine ⟨141029943608380905771683575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188039924811174541028911433 141029943608380905771683575)
    ·
      refine ⟨211544915412571358657525363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141029943608380905771683575 211544915412571358657525363)
      ·
        refine ⟨317317373118857037986288045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211544915412571358657525363 317317373118857037986288045)
        ·
          refine ⟨118994014919571389244858017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 317317373118857037986288045 118994014919571389244858017)
          ·
            refine ⟨89245511189678541933643513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118994014919571389244858017 89245511189678541933643513)
            ·
              refine ⟨66934133392258906450232635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89245511189678541933643513 66934133392258906450232635)
              ·
                refine ⟨100401200088388359675348953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66934133392258906450232635 100401200088388359675348953)
                ·
                  refine ⟨75300900066291269756511715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 100401200088388359675348953 75300900066291269756511715)
                  ·
                    refine ⟨112951350099436904634767573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 75300900066291269756511715 112951350099436904634767573)
                    ·
                      refine ⟨2647297267955552452377365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 112951350099436904634767573 2647297267955552452377365)
                      ·
                        rfl

theorem cell23_5155593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 2, 1, 7].length) (baseStart_5155593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5155593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5155593 prefixEnd_5155593 := by exact prefixLift 5155593
  have htrace : WordTrace (prefixWord ++ tailWord_5155593) baseStart_5155593 baseEnd_5155593 := by
    simpa [prefixWord, tailWord_5155593, baseEnd_5155593] using wordTrace_append hprefix tailTrace_5155593
  have hstable : (prefixWord ++ tailWord_5155593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5155593).length < 2 ^ (prefixWord ++ tailWord_5155593).sum := by decide
  have hdescent : baseEnd_5155593 < baseStart_5155593 := by decide
  rcases family_descends (prefixWord ++ tailWord_5155593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5155624 : List Nat := [2, 1, 5, 1, 1, 1, 3, 2, 2, 3, 2]
def baseStart_5155624 : Nat := 118140960795 + 5155624 * 2 ^ 59
def prefixEnd_5155624 : Nat := 4983230072969 + 3 ^ 40 * 5155624 * 2
def baseEnd_5155624 : Nat := 2647313185855841831089723

theorem tailTrace_5155624 : CollatzResearch.WordTrace tailWord_5155624 prefixEnd_5155624 2647313185855841831089723 := by
  unfold tailWord_5155624
  simp only [CollatzResearch.WordTrace]
  refine ⟨94020527737031116661644963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125360703649374822215526617 94020527737031116661644963)
  ·
    refine ⟨141030791605546674992467445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94020527737031116661644963 141030791605546674992467445)
    ·
      refine ⟨13221636713020000780543823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 141030791605546674992467445 13221636713020000780543823)
      ·
        refine ⟨19832455069530001170815735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13221636713020000780543823 19832455069530001170815735)
        ·
          refine ⟨29748682604295001756223603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19832455069530001170815735 29748682604295001756223603)
          ·
            refine ⟨44623023906442502634335405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29748682604295001756223603 44623023906442502634335405)
            ·
              refine ⟨16733633964915938487875777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44623023906442502634335405 16733633964915938487875777)
              ·
                refine ⟨12550225473686953865906833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16733633964915938487875777 12550225473686953865906833)
                ·
                  refine ⟨9412669105265215399430125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12550225473686953865906833 9412669105265215399430125)
                  ·
                    refine ⟨3529750914474455774786297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9412669105265215399430125 3529750914474455774786297)
                    ·
                      refine ⟨2647313185855841831089723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3529750914474455774786297 2647313185855841831089723)
                      ·
                        rfl

theorem cell23_5155624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 2, 2, 3, 2].length) (baseStart_5155624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5155624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5155624 prefixEnd_5155624 := by exact prefixLift 5155624
  have htrace : WordTrace (prefixWord ++ tailWord_5155624) baseStart_5155624 baseEnd_5155624 := by
    simpa [prefixWord, tailWord_5155624, baseEnd_5155624] using wordTrace_append hprefix tailTrace_5155624
  have hstable : (prefixWord ++ tailWord_5155624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5155624).length < 2 ^ (prefixWord ++ tailWord_5155624).sum := by decide
  have hdescent : baseEnd_5155624 < baseStart_5155624 := by decide
  rcases family_descends (prefixWord ++ tailWord_5155624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5155638 : List Nat := [5, 1, 2, 2, 3, 1, 2, 1, 6]
def baseStart_5155638 : Nat := 118140960795 + 5155638 * 2 ^ 59
def prefixEnd_5155638 : Nat := 4983230072969 + 3 ^ 40 * 5155638 * 2
def baseEnd_5155638 : Nat := 294146708287222752923851

theorem tailTrace_5155638 : CollatzResearch.WordTrace tailWord_5155638 prefixEnd_5155638 294146708287222752923851 := by
  unfold tailWord_5155638
  simp only [CollatzResearch.WordTrace]
  refine ⟨11752597881000719607143723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 125361044064007675809533045 11752597881000719607143723)
  ·
    refine ⟨17628896821501079410715585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11752597881000719607143723 17628896821501079410715585)
    ·
      refine ⟨13221672616125809558036689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17628896821501079410715585 13221672616125809558036689)
      ·
        refine ⟨9916254462094357168527517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13221672616125809558036689 9916254462094357168527517)
        ·
          refine ⟨3718595423285383938197819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9916254462094357168527517 3718595423285383938197819)
          ·
            refine ⟨5577893134928075907296729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3718595423285383938197819 5577893134928075907296729)
            ·
              refine ⟨4183419851196056930472547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5577893134928075907296729 4183419851196056930472547)
              ·
                refine ⟨6275129776794085395708821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4183419851196056930472547 6275129776794085395708821)
                ·
                  refine ⟨294146708287222752923851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6275129776794085395708821 294146708287222752923851)
                  ·
                    rfl

theorem cell23_5155638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 2, 1, 6].length) (baseStart_5155638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5155638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5155638 prefixEnd_5155638 := by exact prefixLift 5155638
  have htrace : WordTrace (prefixWord ++ tailWord_5155638) baseStart_5155638 baseEnd_5155638 := by
    simpa [prefixWord, tailWord_5155638, baseEnd_5155638] using wordTrace_append hprefix tailTrace_5155638
  have hstable : (prefixWord ++ tailWord_5155638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5155638).length < 2 ^ (prefixWord ++ tailWord_5155638).sum := by decide
  have hdescent : baseEnd_5155638 < baseStart_5155638 := by decide
  rcases family_descends (prefixWord ++ tailWord_5155638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5155640 : List Nat := [2, 1, 2, 1, 3, 2, 1, 4, 1, 1, 5]
def baseStart_5155640 : Nat := 118140960795 + 5155640 * 2 ^ 59
def prefixEnd_5155640 : Nat := 4983230072969 + 3 ^ 40 * 5155640 * 2
def baseEnd_5155640 : Nat := 2647321401546313768489649

theorem tailTrace_5155640 : CollatzResearch.WordTrace tailWord_5155640 prefixEnd_5155640 2647321401546313768489649 := by
  unfold tailWord_5155640
  simp only [CollatzResearch.WordTrace]
  refine ⟨94020819521002134027936187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125361092694669512037248249 94020819521002134027936187)
  ·
    refine ⟨141031229281503201041904281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94020819521002134027936187 141031229281503201041904281)
    ·
      refine ⟨105773421961127400781428211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141031229281503201041904281 105773421961127400781428211)
      ·
        refine ⟨158660132941691101172142317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105773421961127400781428211 158660132941691101172142317)
        ·
          refine ⟨59497549853134162939553369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 158660132941691101172142317 59497549853134162939553369)
          ·
            refine ⟨44623162389850622204665027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59497549853134162939553369 44623162389850622204665027)
            ·
              refine ⟨66934743584775933306997541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44623162389850622204665027 66934743584775933306997541)
              ·
                refine ⟨12550264422145487495062039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 66934743584775933306997541 12550264422145487495062039)
                ·
                  refine ⟨18825396633218231242593059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12550264422145487495062039 18825396633218231242593059)
                  ·
                    refine ⟨28238094949827346863889589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18825396633218231242593059 28238094949827346863889589)
                    ·
                      refine ⟨2647321401546313768489649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28238094949827346863889589 2647321401546313768489649)
                      ·
                        rfl

theorem cell23_5155640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 4, 1, 1, 5].length) (baseStart_5155640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5155640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5155640 prefixEnd_5155640 := by exact prefixLift 5155640
  have htrace : WordTrace (prefixWord ++ tailWord_5155640) baseStart_5155640 baseEnd_5155640 := by
    simpa [prefixWord, tailWord_5155640, baseEnd_5155640] using wordTrace_append hprefix tailTrace_5155640
  have hstable : (prefixWord ++ tailWord_5155640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5155640).length < 2 ^ (prefixWord ++ tailWord_5155640).sum := by decide
  have hdescent : baseEnd_5155640 < baseStart_5155640 := by decide
  rcases family_descends (prefixWord ++ tailWord_5155640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5155657 : List Nat := [1, 2, 1, 1, 2, 6, 1, 1, 3, 2, 3]
def baseStart_5155657 : Nat := 118140960795 + 5155657 * 2 ^ 59
def prefixEnd_5155657 : Nat := 4983230072969 + 3 ^ 40 * 5155657 * 2
def baseEnd_5155657 : Nat := 2647330130717440201977071

theorem tailTrace_5155657 : CollatzResearch.WordTrace tailWord_5155657 prefixEnd_5155657 2647330130717440201977071 := by
  unfold tailWord_5155657
  simp only [CollatzResearch.WordTrace]
  refine ⟨188042259082942679959241225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125361506055295119972827483 188042259082942679959241225)
  ·
    refine ⟨141031694312207009969430919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188042259082942679959241225 141031694312207009969430919)
    ·
      refine ⟨211547541468310514954146379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141031694312207009969430919 211547541468310514954146379)
      ·
        refine ⟨317321312202465772431219569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211547541468310514954146379 317321312202465772431219569)
        ·
          refine ⟨237990984151849329323414677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 317321312202465772431219569 237990984151849329323414677)
          ·
            refine ⟨11155827382117937312035063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 237990984151849329323414677 11155827382117937312035063)
            ·
              refine ⟨16733741073176905968052595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11155827382117937312035063 16733741073176905968052595)
              ·
                refine ⟨25100611609765358952078893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16733741073176905968052595 25100611609765358952078893)
                ·
                  refine ⟨9412729353662009607029585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25100611609765358952078893 9412729353662009607029585)
                  ·
                    refine ⟨7059547015246507205272189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9412729353662009607029585 7059547015246507205272189)
                    ·
                      refine ⟨2647330130717440201977071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7059547015246507205272189 2647330130717440201977071)
                      ·
                        rfl

theorem cell23_5155657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 1, 3, 2, 3].length) (baseStart_5155657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5155657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5155657 prefixEnd_5155657 := by exact prefixLift 5155657
  have htrace : WordTrace (prefixWord ++ tailWord_5155657) baseStart_5155657 baseEnd_5155657 := by
    simpa [prefixWord, tailWord_5155657, baseEnd_5155657] using wordTrace_append hprefix tailTrace_5155657
  have hstable : (prefixWord ++ tailWord_5155657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5155657).length < 2 ^ (prefixWord ++ tailWord_5155657).sum := by decide
  have hdescent : baseEnd_5155657 < baseStart_5155657 := by decide
  rcases family_descends (prefixWord ++ tailWord_5155657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5155660 : List Nat := [2, 2, 1, 3, 3, 1, 2, 9]
def baseStart_5155660 : Nat := 118140960795 + 5155660 * 2 ^ 59
def prefixEnd_5155660 : Nat := 4983230072969 + 3 ^ 40 * 5155660 * 2
def baseEnd_5155660 : Nat := 98049321154051988527391

theorem tailTrace_5155660 : CollatzResearch.WordTrace tailWord_5155660 prefixEnd_5155660 98049321154051988527391 := by
  unfold tailWord_5155660
  simp only [CollatzResearch.WordTrace]
  refine ⟨94021184250965905735800217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125361579001287874314400289 94021184250965905735800217)
  ·
    refine ⟨70515888188224429301850163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94021184250965905735800217 70515888188224429301850163)
    ·
      refine ⟨105773832282336643952775245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70515888188224429301850163 105773832282336643952775245)
      ·
        refine ⟨39665187105876241482290717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105773832282336643952775245 39665187105876241482290717)
        ·
          refine ⟨14874445164703590555859019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39665187105876241482290717 14874445164703590555859019)
          ·
            refine ⟨22311667747055385833788529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14874445164703590555859019 22311667747055385833788529)
            ·
              refine ⟨16733750810291539375341397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22311667747055385833788529 16733750810291539375341397)
              ·
                refine ⟨98049321154051988527391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16733750810291539375341397 98049321154051988527391)
                ·
                  rfl

theorem cell23_5155660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 9].length) (baseStart_5155660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5155660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5155660 prefixEnd_5155660 := by exact prefixLift 5155660
  have htrace : WordTrace (prefixWord ++ tailWord_5155660) baseStart_5155660 baseEnd_5155660 := by
    simpa [prefixWord, tailWord_5155660, baseEnd_5155660] using wordTrace_append hprefix tailTrace_5155660
  have hstable : (prefixWord ++ tailWord_5155660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5155660).length < 2 ^ (prefixWord ++ tailWord_5155660).sum := by decide
  have hdescent : baseEnd_5155660 < baseStart_5155660 := by decide
  rcases family_descends (prefixWord ++ tailWord_5155660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5155682 : List Nat := [3, 3, 2, 1, 4, 1, 2, 2, 1, 1, 3]
def baseStart_5155682 : Nat := 118140960795 + 5155682 * 2 ^ 59
def prefixEnd_5155682 : Nat := 4983230072969 + 3 ^ 40 * 5155682 * 2
def baseEnd_5155682 : Nat := 2647342967733802604164457

theorem tailTrace_5155682 : CollatzResearch.WordTrace tailWord_5155682 prefixEnd_5155682 2647342967733802604164457 := by
  unfold tailWord_5155682
  simp only [CollatzResearch.WordTrace]
  refine ⟨47010792726963027307225325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125362113938568072819267533 47010792726963027307225325)
  ·
    refine ⟨17629047272611135240209497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47010792726963027307225325 17629047272611135240209497)
    ·
      refine ⟨13221785454458351430157123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17629047272611135240209497 13221785454458351430157123)
      ·
        refine ⟨19832678181687527145235685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13221785454458351430157123 19832678181687527145235685)
        ·
          refine ⟨3718627159066411339731691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19832678181687527145235685 3718627159066411339731691)
          ·
            refine ⟨5577940738599617009597537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3718627159066411339731691 5577940738599617009597537)
            ·
              refine ⟨4183455553949712757198153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5577940738599617009597537 4183455553949712757198153)
              ·
                refine ⟨3137591665462284567898615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4183455553949712757198153 3137591665462284567898615)
                ·
                  refine ⟨4706387498193426851847923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3137591665462284567898615 4706387498193426851847923)
                  ·
                    refine ⟨7059581247290140277771885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4706387498193426851847923 7059581247290140277771885)
                    ·
                      refine ⟨2647342967733802604164457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7059581247290140277771885 2647342967733802604164457)
                      ·
                        rfl

theorem cell23_5155682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 2, 2, 1, 1, 3].length) (baseStart_5155682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5155682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5155682 prefixEnd_5155682 := by exact prefixLift 5155682
  have htrace : WordTrace (prefixWord ++ tailWord_5155682) baseStart_5155682 baseEnd_5155682 := by
    simpa [prefixWord, tailWord_5155682, baseEnd_5155682] using wordTrace_append hprefix tailTrace_5155682
  have hstable : (prefixWord ++ tailWord_5155682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5155682).length < 2 ^ (prefixWord ++ tailWord_5155682).sum := by decide
  have hdescent : baseEnd_5155682 < baseStart_5155682 := by decide
  rcases family_descends (prefixWord ++ tailWord_5155682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5155688 : List Nat := [2, 1, 4, 2, 1, 3, 1, 4, 1, 2, 2]
def baseStart_5155688 : Nat := 118140960795 + 5155688 * 2 ^ 59
def prefixEnd_5155688 : Nat := 4983230072969 + 3 ^ 40 * 5155688 * 2
def baseEnd_5155688 : Nat := 2647346048617729580689429

theorem tailTrace_5155688 : CollatzResearch.WordTrace tailWord_5155688 prefixEnd_5155688 2647346048617729580689429 := by
  unfold tailWord_5155688
  simp only [CollatzResearch.WordTrace]
  refine ⟨94021694872915186126809859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125362259830553581502413145 94021694872915186126809859)
  ·
    refine ⟨141032542309372779190214789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94021694872915186126809859 141032542309372779190214789)
    ·
      refine ⟨26443601683007396098165273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 141032542309372779190214789 26443601683007396098165273)
      ·
        refine ⟨19832701262255547073623955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26443601683007396098165273 19832701262255547073623955)
        ·
          refine ⟨29749051893383320610435933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19832701262255547073623955 29749051893383320610435933)
          ·
            refine ⟨11155894460018745228913475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29749051893383320610435933 11155894460018745228913475)
            ·
              refine ⟨16733841690028117843370213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11155894460018745228913475 16733841690028117843370213)
              ·
                refine ⟨3137595316880272095631915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16733841690028117843370213 3137595316880272095631915)
                ·
                  refine ⟨4706392975320408143447873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3137595316880272095631915 4706392975320408143447873)
                  ·
                    refine ⟨3529794731490306107585905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4706392975320408143447873 3529794731490306107585905)
                    ·
                      refine ⟨2647346048617729580689429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3529794731490306107585905 2647346048617729580689429)
                      ·
                        rfl

theorem cell23_5155688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 4, 1, 2, 2].length) (baseStart_5155688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5155688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5155688 prefixEnd_5155688 := by exact prefixLift 5155688
  have htrace : WordTrace (prefixWord ++ tailWord_5155688) baseStart_5155688 baseEnd_5155688 := by
    simpa [prefixWord, tailWord_5155688, baseEnd_5155688] using wordTrace_append hprefix tailTrace_5155688
  have hstable : (prefixWord ++ tailWord_5155688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5155688).length < 2 ^ (prefixWord ++ tailWord_5155688).sum := by decide
  have hdescent : baseEnd_5155688 < baseStart_5155688 := by decide
  rcases family_descends (prefixWord ++ tailWord_5155688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5155694 : List Nat := [4, 1, 2, 3, 2, 2, 1, 8]
def baseStart_5155694 : Nat := 118140960795 + 5155694 * 2 ^ 59
def prefixEnd_5155694 : Nat := 4983230072969 + 3 ^ 40 * 5155694 * 2
def baseEnd_5155694 : Nat := 98049967759320613230163

theorem tailTrace_5155694 : CollatzResearch.WordTrace tailWord_5155694 prefixEnd_5155694 98049967759320613230163 := by
  unfold tailWord_5155694
  simp only [CollatzResearch.WordTrace]
  refine ⟨23505451072976079409792267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125362405722539090185558757 23505451072976079409792267)
  ·
    refine ⟨35258176609464119114688401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23505451072976079409792267 35258176609464119114688401)
    ·
      refine ⟨26443632457098089336016301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35258176609464119114688401 26443632457098089336016301)
      ·
        refine ⟨9916362171411783501006113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26443632457098089336016301 9916362171411783501006113)
        ·
          refine ⟨7437271628558837625754585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9916362171411783501006113 7437271628558837625754585)
          ·
            refine ⟨5577953721419128219315939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7437271628558837625754585 5577953721419128219315939)
            ·
              refine ⟨8366930582128692328973909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5577953721419128219315939 8366930582128692328973909)
              ·
                refine ⟨98049967759320613230163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8366930582128692328973909 98049967759320613230163)
                ·
                  rfl

theorem cell23_5155694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 1, 8].length) (baseStart_5155694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5155694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5155694 prefixEnd_5155694 := by exact prefixLift 5155694
  have htrace : WordTrace (prefixWord ++ tailWord_5155694) baseStart_5155694 baseEnd_5155694 := by
    simpa [prefixWord, tailWord_5155694, baseEnd_5155694] using wordTrace_append hprefix tailTrace_5155694
  have hstable : (prefixWord ++ tailWord_5155694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5155694).length < 2 ^ (prefixWord ++ tailWord_5155694).sum := by decide
  have hdescent : baseEnd_5155694 < baseStart_5155694 := by decide
  rcases family_descends (prefixWord ++ tailWord_5155694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5155738 : List Nat := [3, 1, 1, 4, 3, 2, 1, 2, 2, 1, 3]
def baseStart_5155738 : Nat := 118140960795 + 5155738 * 2 ^ 59
def prefixEnd_5155738 : Nat := 4983230072969 + 3 ^ 40 * 5155738 * 2
def baseEnd_5155738 : Nat := 2647371722650454385064199

theorem tailTrace_5155738 : CollatzResearch.WordTrace tailWord_5155738 prefixEnd_5155738 2647371722650454385064199 := by
  unfold tailWord_5155738
  simp only [CollatzResearch.WordTrace]
  refine ⟨47011303348912307698234967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125363475597099487195293245 47011303348912307698234967)
  ·
    refine ⟨70516955023368461547352451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47011303348912307698234967 70516955023368461547352451)
    ·
      refine ⟨105775432535052692321028677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70516955023368461547352451 105775432535052692321028677)
      ·
        refine ⟨19832893600322379810192877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 105775432535052692321028677 19832893600322379810192877)
        ·
          refine ⟨7437335100120892428822329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19832893600322379810192877 7437335100120892428822329)
          ·
            refine ⟨5578001325090669321616747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7437335100120892428822329 5578001325090669321616747)
            ·
              refine ⟨8367001987636003982425121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5578001325090669321616747 8367001987636003982425121)
              ·
                refine ⟨6275251490727002986818841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8367001987636003982425121 6275251490727002986818841)
                ·
                  refine ⟨4706438618045252240114131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6275251490727002986818841 4706438618045252240114131)
                  ·
                    refine ⟨7059657927067878360171197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4706438618045252240114131 7059657927067878360171197)
                    ·
                      refine ⟨2647371722650454385064199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7059657927067878360171197 2647371722650454385064199)
                      ·
                        rfl

theorem cell23_5155738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 1, 2, 2, 1, 3].length) (baseStart_5155738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5155738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5155738 prefixEnd_5155738 := by exact prefixLift 5155738
  have htrace : WordTrace (prefixWord ++ tailWord_5155738) baseStart_5155738 baseEnd_5155738 := by
    simpa [prefixWord, tailWord_5155738, baseEnd_5155738] using wordTrace_append hprefix tailTrace_5155738
  have hstable : (prefixWord ++ tailWord_5155738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5155738).length < 2 ^ (prefixWord ++ tailWord_5155738).sum := by decide
  have hdescent : baseEnd_5155738 < baseStart_5155738 := by decide
  rcases family_descends (prefixWord ++ tailWord_5155738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5155801 : List Nat := [1, 2, 1, 2, 5, 2, 3, 2, 5]
def baseStart_5155801 : Nat := 118140960795 + 5155801 * 2 ^ 59
def prefixEnd_5155801 : Nat := 4983230072969 + 3 ^ 40 * 5155801 * 2
def baseEnd_5155801 : Nat := 294156007992409737619601

theorem tailTrace_5155801 : CollatzResearch.WordTrace tailWord_5155801 prefixEnd_5155801 294156007992409737619601 := by
  unfold tailWord_5155801
  simp only [CollatzResearch.WordTrace]
  refine ⟨188047511194420992552483257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125365007462947328368322171 188047511194420992552483257)
  ·
    refine ⟨141035633395815744414362443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188047511194420992552483257 141035633395815744414362443)
    ·
      refine ⟨211553450093723616621543665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141035633395815744414362443 211553450093723616621543665)
      ·
        refine ⟨158665087570292712466157749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 211553450093723616621543665 158665087570292712466157749)
        ·
          refine ⟨14874851959714941793702289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 158665087570292712466157749 14874851959714941793702289)
          ·
            refine ⟨11156138969786206345276717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14874851959714941793702289 11156138969786206345276717)
            ·
              refine ⟨4183552113669827379478769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11156138969786206345276717 4183552113669827379478769)
              ·
                refine ⟨3137664085252370534609077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4183552113669827379478769 3137664085252370534609077)
                ·
                  refine ⟨294156007992409737619601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3137664085252370534609077 294156007992409737619601)
                  ·
                    rfl

theorem cell23_5155801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 3, 2, 5].length) (baseStart_5155801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5155801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5155801 prefixEnd_5155801 := by exact prefixLift 5155801
  have htrace : WordTrace (prefixWord ++ tailWord_5155801) baseStart_5155801 baseEnd_5155801 := by
    simpa [prefixWord, tailWord_5155801, baseEnd_5155801] using wordTrace_append hprefix tailTrace_5155801
  have hstable : (prefixWord ++ tailWord_5155801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5155801).length < 2 ^ (prefixWord ++ tailWord_5155801).sum := by decide
  have hdescent : baseEnd_5155801 < baseStart_5155801 := by decide
  rcases family_descends (prefixWord ++ tailWord_5155801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5155847 : List Nat := [1, 1, 4, 3, 1, 1, 2, 1, 2, 1, 6]
def baseStart_5155847 : Nat := 118140960795 + 5155847 * 2 ^ 59
def prefixEnd_5155847 : Nat := 4983230072969 + 3 ^ 40 * 5155847 * 2
def baseEnd_5155847 : Nat := 2647427692041794458601197

theorem tailTrace_5155847 : CollatzResearch.WordTrace tailWord_5155847 prefixEnd_5155847 2647427692041794458601197 := by
  unfold tailWord_5155847
  simp only [CollatzResearch.WordTrace]
  refine ⟨188049188952254342408657795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125366125968169561605771863 188049188952254342408657795)
  ·
    refine ⟨282073783428381513612986693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188049188952254342408657795 282073783428381513612986693)
    ·
      refine ⟨52888834392821533802435005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 282073783428381513612986693 52888834392821533802435005)
      ·
        refine ⟨19833312897308075175913127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52888834392821533802435005 19833312897308075175913127)
        ·
          refine ⟨29749969345962112763869691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19833312897308075175913127 29749969345962112763869691)
          ·
            refine ⟨44624954018943169145804537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29749969345962112763869691 44624954018943169145804537)
            ·
              refine ⟨33468715514207376859353403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44624954018943169145804537 33468715514207376859353403)
              ·
                refine ⟨50203073271311065289030105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33468715514207376859353403 50203073271311065289030105)
                ·
                  refine ⟨37652304953483298966772579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50203073271311065289030105 37652304953483298966772579)
                  ·
                    refine ⟨56478457430224948450158869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37652304953483298966772579 56478457430224948450158869)
                    ·
                      refine ⟨2647427692041794458601197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56478457430224948450158869 2647427692041794458601197)
                      ·
                        rfl

theorem cell23_5155847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_5155847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5155847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5155847 prefixEnd_5155847 := by exact prefixLift 5155847
  have htrace : WordTrace (prefixWord ++ tailWord_5155847) baseStart_5155847 baseEnd_5155847 := by
    simpa [prefixWord, tailWord_5155847, baseEnd_5155847] using wordTrace_append hprefix tailTrace_5155847
  have hstable : (prefixWord ++ tailWord_5155847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5155847).length < 2 ^ (prefixWord ++ tailWord_5155847).sum := by decide
  have hdescent : baseEnd_5155847 < baseStart_5155847 := by decide
  rcases family_descends (prefixWord ++ tailWord_5155847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5155874 : List Nat := [3, 3, 1, 1, 1, 3, 2, 3, 6]
def baseStart_5155874 : Nat := 118140960795 + 5155874 * 2 ^ 59
def prefixEnd_5155874 : Nat := 4983230072969 + 3 ^ 40 * 5155874 * 2
def baseEnd_5155874 : Nat := 294160172891051761440397

theorem tailTrace_5155874 : CollatzResearch.WordTrace tailWord_5155874 prefixEnd_5155874 294160172891051761440397 := by
  unfold tailWord_5155874
  simp only [CollatzResearch.WordTrace]
  refine ⟨47012543430789131504972669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125366782482104350679927117 47012543430789131504972669)
  ·
    refine ⟨17629703786545924314364751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47012543430789131504972669 17629703786545924314364751)
    ·
      refine ⟨26444555679818886471547127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17629703786545924314364751 26444555679818886471547127)
      ·
        refine ⟨39666833519728329707320691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26444555679818886471547127 39666833519728329707320691)
        ·
          refine ⟨59500250279592494560981037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39666833519728329707320691 59500250279592494560981037)
          ·
            refine ⟨22312593854847185460367889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59500250279592494560981037 22312593854847185460367889)
            ·
              refine ⟨16734445391135389095275917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22312593854847185460367889 16734445391135389095275917)
              ·
                refine ⟨6275417021675770910728469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16734445391135389095275917 6275417021675770910728469)
                ·
                  refine ⟨294160172891051761440397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6275417021675770910728469 294160172891051761440397)
                  ·
                    rfl

theorem cell23_5155874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 3, 6].length) (baseStart_5155874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5155874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5155874 prefixEnd_5155874 := by exact prefixLift 5155874
  have htrace : WordTrace (prefixWord ++ tailWord_5155874) baseStart_5155874 baseEnd_5155874 := by
    simpa [prefixWord, tailWord_5155874, baseEnd_5155874] using wordTrace_append hprefix tailTrace_5155874
  have hstable : (prefixWord ++ tailWord_5155874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5155874).length < 2 ^ (prefixWord ++ tailWord_5155874).sum := by decide
  have hdescent : baseEnd_5155874 < baseStart_5155874 := by decide
  rcases family_descends (prefixWord ++ tailWord_5155874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5155904 : List Nat := [2, 1, 1, 2, 2, 3, 3, 3, 1, 5]
def baseStart_5155904 : Nat := 118140960795 + 5155904 * 2 ^ 59
def prefixEnd_5155904 : Nat := 4983230072969 + 3 ^ 40 * 5155904 * 2
def baseEnd_5155904 : Nat := 882485653479700245196145

theorem tailTrace_5155904 : CollatzResearch.WordTrace tailWord_5155904 prefixEnd_5155904 882485653479700245196145 := by
  unfold tailWord_5155904
  simp only [CollatzResearch.WordTrace]
  refine ⟨94025633956523920571741383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125367511942031894095655177 94025633956523920571741383)
  ·
    refine ⟨141038450934785880857612075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94025633956523920571741383 141038450934785880857612075)
    ·
      refine ⟨211557676402178821286418113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141038450934785880857612075 211557676402178821286418113)
      ·
        refine ⟨158668257301634115964813585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 211557676402178821286418113 158668257301634115964813585)
        ·
          refine ⟨119001192976225586973610189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 158668257301634115964813585 119001192976225586973610189)
          ·
            refine ⟨44625447366084595115103821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 119001192976225586973610189 44625447366084595115103821)
            ·
              refine ⟨16734542762281723168163933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44625447366084595115103821 16734542762281723168163933)
              ·
                refine ⟨6275453535855646188061475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16734542762281723168163933 6275453535855646188061475)
                ·
                  refine ⟨9413180303783469282092213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6275453535855646188061475 9413180303783469282092213)
                  ·
                    refine ⟨882485653479700245196145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9413180303783469282092213 882485653479700245196145)
                    ·
                      rfl

theorem cell23_5155904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 3, 1, 5].length) (baseStart_5155904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5155904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5155904 prefixEnd_5155904 := by exact prefixLift 5155904
  have htrace : WordTrace (prefixWord ++ tailWord_5155904) baseStart_5155904 baseEnd_5155904 := by
    simpa [prefixWord, tailWord_5155904, baseEnd_5155904] using wordTrace_append hprefix tailTrace_5155904
  have hstable : (prefixWord ++ tailWord_5155904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5155904).length < 2 ^ (prefixWord ++ tailWord_5155904).sum := by decide
  have hdescent : baseEnd_5155904 < baseStart_5155904 := by decide
  rcases family_descends (prefixWord ++ tailWord_5155904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5155918 : List Nat := [4, 1, 1, 1, 1, 3, 1, 6, 1, 1, 3]
def baseStart_5155918 : Nat := 118140960795 + 5155918 * 2 ^ 59
def prefixEnd_5155918 : Nat := 4983230072969 + 3 ^ 40 * 5155918 * 2
def baseEnd_5155918 : Nat := 2647464149168263680813371

theorem tailTrace_5155918 : CollatzResearch.WordTrace tailWord_5155918 prefixEnd_5155918 2647464149168263680813371 := by
  unfold tailWord_5155918
  simp only [CollatzResearch.WordTrace]
  refine ⟨23506472316874640191811551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125367852356664747689661605 23506472316874640191811551)
  ·
    refine ⟨35259708475311960287717327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23506472316874640191811551 35259708475311960287717327)
    ·
      refine ⟨52889562712967940431575991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35259708475311960287717327 52889562712967940431575991)
      ·
        refine ⟨79334344069451910647363987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52889562712967940431575991 79334344069451910647363987)
        ·
          refine ⟨119001516104177865971045981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79334344069451910647363987 119001516104177865971045981)
          ·
            refine ⟨44625568539066699739142243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 119001516104177865971045981 44625568539066699739142243)
            ·
              refine ⟨66938352808600049608713365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44625568539066699739142243 66938352808600049608713365)
              ·
                refine ⟨3137735287903127325408439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 66938352808600049608713365 3137735287903127325408439)
                ·
                  refine ⟨4706602931854690988112659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3137735287903127325408439 4706602931854690988112659)
                  ·
                    refine ⟨7059904397782036482168989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4706602931854690988112659 7059904397782036482168989)
                    ·
                      refine ⟨2647464149168263680813371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7059904397782036482168989 2647464149168263680813371)
                      ·
                        rfl

theorem cell23_5155918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 6, 1, 1, 3].length) (baseStart_5155918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5155918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5155918 prefixEnd_5155918 := by exact prefixLift 5155918
  have htrace : WordTrace (prefixWord ++ tailWord_5155918) baseStart_5155918 baseEnd_5155918 := by
    simpa [prefixWord, tailWord_5155918, baseEnd_5155918] using wordTrace_append hprefix tailTrace_5155918
  have hstable : (prefixWord ++ tailWord_5155918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5155918).length < 2 ^ (prefixWord ++ tailWord_5155918).sum := by decide
  have hdescent : baseEnd_5155918 < baseStart_5155918 := by decide
  rcases family_descends (prefixWord ++ tailWord_5155918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5155924 : List Nat := [2, 4, 1, 1, 1, 1, 2, 1, 5, 1, 4]
def baseStart_5155924 : Nat := 118140960795 + 5155924 * 2 ^ 59
def prefixEnd_5155924 : Nat := 4983230072969 + 3 ^ 40 * 5155924 * 2
def baseEnd_5155924 : Nat := 2647467230052190657338343

theorem tailTrace_5155924 : CollatzResearch.WordTrace tailWord_5155924 prefixEnd_5155924 2647467230052190657338343 := by
  unfold tailWord_5155924
  simp only [CollatzResearch.WordTrace]
  refine ⟨94025998686487692279605413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125367998248650256372807217 94025998686487692279605413)
  ·
    refine ⟨17629874753716442302426015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94025998686487692279605413 17629874753716442302426015)
    ·
      refine ⟨26444812130574663453639023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17629874753716442302426015 26444812130574663453639023)
      ·
        refine ⟨39667218195861995180458535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26444812130574663453639023 39667218195861995180458535)
        ·
          refine ⟨59500827293792992770687803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39667218195861995180458535 59500827293792992770687803)
          ·
            refine ⟨89251240940689489156031705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59500827293792992770687803 89251240940689489156031705)
            ·
              refine ⟨66938430705517116867023779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89251240940689489156031705 66938430705517116867023779)
              ·
                refine ⟨100407646058275675300535669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66938430705517116867023779 100407646058275675300535669)
                ·
                  refine ⟨9413216817963344559425219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 100407646058275675300535669 9413216817963344559425219)
                  ·
                    refine ⟨14119825226945016839137829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9413216817963344559425219 14119825226945016839137829)
                    ·
                      refine ⟨2647467230052190657338343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14119825226945016839137829 2647467230052190657338343)
                      ·
                        rfl

theorem cell23_5155924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 5, 1, 4].length) (baseStart_5155924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5155924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5155924 prefixEnd_5155924 := by exact prefixLift 5155924
  have htrace : WordTrace (prefixWord ++ tailWord_5155924) baseStart_5155924 baseEnd_5155924 := by
    simpa [prefixWord, tailWord_5155924, baseEnd_5155924] using wordTrace_append hprefix tailTrace_5155924
  have hstable : (prefixWord ++ tailWord_5155924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5155924).length < 2 ^ (prefixWord ++ tailWord_5155924).sum := by decide
  have hdescent : baseEnd_5155924 < baseStart_5155924 := by decide
  rcases family_descends (prefixWord ++ tailWord_5155924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5155938 : List Nat := [3, 3, 2, 2, 1, 2, 2, 2, 1, 5]
def baseStart_5155938 : Nat := 118140960795 + 5155938 * 2 ^ 59
def prefixEnd_5155938 : Nat := 4983230072969 + 3 ^ 40 * 5155938 * 2
def baseEnd_5155938 : Nat := 882491472927117867521093

theorem tailTrace_5155938 : CollatzResearch.WordTrace tailWord_5155938 prefixEnd_5155938 882491472927117867521093 := by
  unfold tailWord_5155938
  simp only [CollatzResearch.WordTrace]
  refine ⟨47013126998731166237555117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125368338663283109966813645 47013126998731166237555117)
  ·
    refine ⟨17629922624524187339083169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47013126998731166237555117 17629922624524187339083169)
    ·
      refine ⟨13222441968393140504312377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17629922624524187339083169 13222441968393140504312377)
      ·
        refine ⟨9916831476294855378234283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13222441968393140504312377 9916831476294855378234283)
        ·
          refine ⟨14875247214442283067351425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9916831476294855378234283 14875247214442283067351425)
          ·
            refine ⟨11156435410831712300513569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14875247214442283067351425 11156435410831712300513569)
            ·
              refine ⟨8367326558123784225385177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11156435410831712300513569 8367326558123784225385177)
              ·
                refine ⟨6275494918592838169038883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8367326558123784225385177 6275494918592838169038883)
                ·
                  refine ⟨9413242377889257253558325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6275494918592838169038883 9413242377889257253558325)
                  ·
                    refine ⟨882491472927117867521093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9413242377889257253558325 882491472927117867521093)
                    ·
                      rfl

theorem cell23_5155938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 2, 2, 1, 5].length) (baseStart_5155938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5155938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5155938 prefixEnd_5155938 := by exact prefixLift 5155938
  have htrace : WordTrace (prefixWord ++ tailWord_5155938) baseStart_5155938 baseEnd_5155938 := by
    simpa [prefixWord, tailWord_5155938, baseEnd_5155938] using wordTrace_append hprefix tailTrace_5155938
  have hstable : (prefixWord ++ tailWord_5155938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5155938).length < 2 ^ (prefixWord ++ tailWord_5155938).sum := by decide
  have hdescent : baseEnd_5155938 < baseStart_5155938 := by decide
  rcases family_descends (prefixWord ++ tailWord_5155938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5155941 : List Nat := [1, 3, 1, 3, 2, 1, 4, 2, 1, 1, 4]
def baseStart_5155941 : Nat := 118140960795 + 5155941 * 2 ^ 59
def prefixEnd_5155941 : Nat := 4983230072969 + 3 ^ 40 * 5155941 * 2
def baseEnd_5155941 : Nat := 2647475959223317090825765

theorem tailTrace_5155941 : CollatzResearch.WordTrace tailWord_5155941 prefixEnd_5155941 2647475959223317090825765 := by
  unfold tailWord_5155941
  simp only [CollatzResearch.WordTrace]
  refine ⟨188052617413913796462579677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125368411609275864308386451 188052617413913796462579677)
  ·
    refine ⟨70519731530217673673467379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 188052617413913796462579677 70519731530217673673467379)
    ·
      refine ⟨105779597295326510510201069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70519731530217673673467379 105779597295326510510201069)
      ·
        refine ⟨39667348985747441441325401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105779597295326510510201069 39667348985747441441325401)
        ·
          refine ⟨29750511739310581080994051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39667348985747441441325401 29750511739310581080994051)
          ·
            refine ⟨44625767608965871621491077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29750511739310581080994051 44625767608965871621491077)
            ·
              refine ⟨8367331426681100929029577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44625767608965871621491077 8367331426681100929029577)
              ·
                refine ⟨6275498570010825696772183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8367331426681100929029577 6275498570010825696772183)
                ·
                  refine ⟨9413247855016238545158275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6275498570010825696772183 9413247855016238545158275)
                  ·
                    refine ⟨14119871782524357817737413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9413247855016238545158275 14119871782524357817737413)
                    ·
                      refine ⟨2647475959223317090825765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14119871782524357817737413 2647475959223317090825765)
                      ·
                        rfl

theorem cell23_5155941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 4, 2, 1, 1, 4].length) (baseStart_5155941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5155941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5155941 prefixEnd_5155941 := by exact prefixLift 5155941
  have htrace : WordTrace (prefixWord ++ tailWord_5155941) baseStart_5155941 baseEnd_5155941 := by
    simpa [prefixWord, tailWord_5155941, baseEnd_5155941] using wordTrace_append hprefix tailTrace_5155941
  have hstable : (prefixWord ++ tailWord_5155941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5155941).length < 2 ^ (prefixWord ++ tailWord_5155941).sum := by decide
  have hdescent : baseEnd_5155941 < baseStart_5155941 := by decide
  rcases family_descends (prefixWord ++ tailWord_5155941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5155954 : List Nat := [3, 2, 1, 2, 2, 1, 2, 1, 3, 2, 4]
def baseStart_5155954 : Nat := 118140960795 + 5155954 * 2 ^ 59
def prefixEnd_5155954 : Nat := 4983230072969 + 3 ^ 40 * 5155954 * 2
def baseEnd_5155954 : Nat := 2647482634471825539963205

theorem tailTrace_5155954 : CollatzResearch.WordTrace tailWord_5155954 prefixEnd_5155954 2647482634471825539963205 := by
  unfold tailWord_5155954
  simp only [CollatzResearch.WordTrace]
  refine ⟨47013272890716674920700729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125368727708577799788535277 47013272890716674920700729)
  ·
    refine ⟨35259954668037506190525547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47013272890716674920700729 35259954668037506190525547)
    ·
      refine ⟨52889932002056259285788321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35259954668037506190525547 52889932002056259285788321)
      ·
        refine ⟨39667449001542194464341241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52889932002056259285788321 39667449001542194464341241)
        ·
          refine ⟨29750586751156645848255931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39667449001542194464341241 29750586751156645848255931)
          ·
            refine ⟨44625880126734968772383897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29750586751156645848255931 44625880126734968772383897)
            ·
              refine ⟨33469410095051226579287923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44625880126734968772383897 33469410095051226579287923)
              ·
                refine ⟨50204115142576839868931885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33469410095051226579287923 50204115142576839868931885)
                ·
                  refine ⟨18826543178466314950849457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50204115142576839868931885 18826543178466314950849457)
                  ·
                    refine ⟨14119907383849736213137093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18826543178466314950849457 14119907383849736213137093)
                    ·
                      refine ⟨2647482634471825539963205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14119907383849736213137093 2647482634471825539963205)
                      ·
                        rfl

theorem cell23_5155954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 1, 3, 2, 4].length) (baseStart_5155954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5155954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5155954 prefixEnd_5155954 := by exact prefixLift 5155954
  have htrace : WordTrace (prefixWord ++ tailWord_5155954) baseStart_5155954 baseEnd_5155954 := by
    simpa [prefixWord, tailWord_5155954, baseEnd_5155954] using wordTrace_append hprefix tailTrace_5155954
  have hstable : (prefixWord ++ tailWord_5155954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5155954).length < 2 ^ (prefixWord ++ tailWord_5155954).sum := by decide
  have hdescent : baseEnd_5155954 < baseStart_5155954 := by decide
  rcases family_descends (prefixWord ++ tailWord_5155954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5155961 : List Nat := [1, 2, 1, 3, 5, 1, 2, 1, 1, 1, 5]
def baseStart_5155961 : Nat := 118140960795 + 5155961 * 2 ^ 59
def prefixEnd_5155961 : Nat := 4983230072969 + 3 ^ 40 * 5155961 * 2
def baseEnd_5155961 : Nat := 2647486228836407012575673

theorem tailTrace_5155961 : CollatzResearch.WordTrace tailWord_5155961 prefixEnd_5155961 2647486228836407012575673 := by
  unfold tailWord_5155961
  simp only [CollatzResearch.WordTrace]
  refine ⟨188053346873841339878307737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125368897915894226585538491 188053346873841339878307737)
  ·
    refine ⟨141040010155381004908730803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188053346873841339878307737 141040010155381004908730803)
    ·
      refine ⟨211560015233071507363096205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141040010155381004908730803 211560015233071507363096205)
      ·
        refine ⟨79335005712401815261161077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 211560015233071507363096205 79335005712401815261161077)
        ·
          refine ⟨7437656785537670180733851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 79335005712401815261161077 7437656785537670180733851)
          ·
            refine ⟨11156485178306505271100777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7437656785537670180733851 11156485178306505271100777)
            ·
              refine ⟨8367363883729878953325583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11156485178306505271100777 8367363883729878953325583)
              ·
                refine ⟨12551045825594818429988375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8367363883729878953325583 12551045825594818429988375)
                ·
                  refine ⟨18826568738392227644982563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12551045825594818429988375 18826568738392227644982563)
                  ·
                    refine ⟨28239853107588341467473845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18826568738392227644982563 28239853107588341467473845)
                    ·
                      refine ⟨2647486228836407012575673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28239853107588341467473845 2647486228836407012575673)
                      ·
                        rfl

theorem cell23_5155961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 2, 1, 1, 1, 5].length) (baseStart_5155961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5155961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5155961 prefixEnd_5155961 := by exact prefixLift 5155961
  have htrace : WordTrace (prefixWord ++ tailWord_5155961) baseStart_5155961 baseEnd_5155961 := by
    simpa [prefixWord, tailWord_5155961, baseEnd_5155961] using wordTrace_append hprefix tailTrace_5155961
  have hstable : (prefixWord ++ tailWord_5155961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5155961).length < 2 ^ (prefixWord ++ tailWord_5155961).sum := by decide
  have hdescent : baseEnd_5155961 < baseStart_5155961 := by decide
  rcases family_descends (prefixWord ++ tailWord_5155961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5156069 : List Nat := [1, 3, 1, 4, 4, 1, 2, 1, 1, 3, 2]
def baseStart_5156069 : Nat := 118140960795 + 5156069 * 2 ^ 59
def prefixEnd_5156069 : Nat := 4983230072969 + 3 ^ 40 * 5156069 * 2
def baseEnd_5156069 : Nat := 2647541684747092590025177

theorem tailTrace_5156069 : CollatzResearch.WordTrace tailWord_5156069 prefixEnd_5156069 2647541684747092590025177 := by
  unfold tailWord_5156069
  simp only [CollatzResearch.WordTrace]
  refine ⟨188057285957450074323239261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125371523971633382882159507 188057285957450074323239261)
  ·
    refine ⟨70521482234043777871214723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 188057285957450074323239261 70521482234043777871214723)
    ·
      refine ⟨105782223351065666806822085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70521482234043777871214723 105782223351065666806822085)
      ·
        refine ⟨19834166878324812526279141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 105782223351065666806822085 19834166878324812526279141)
        ·
          refine ⟨3718906289685902348677339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19834166878324812526279141 3718906289685902348677339)
          ·
            refine ⟨5578359434528853523016009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3718906289685902348677339 5578359434528853523016009)
            ·
              refine ⟨4183769575896640142262007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5578359434528853523016009 4183769575896640142262007)
              ·
                refine ⟨6275654363844960213393011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4183769575896640142262007 6275654363844960213393011)
                ·
                  refine ⟨9413481545767440320089517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6275654363844960213393011 9413481545767440320089517)
                  ·
                    refine ⟨3530055579662790120033569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9413481545767440320089517 3530055579662790120033569)
                    ·
                      refine ⟨2647541684747092590025177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3530055579662790120033569 2647541684747092590025177)
                      ·
                        rfl

theorem cell23_5156069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 2, 1, 1, 3, 2].length) (baseStart_5156069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5156069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5156069 prefixEnd_5156069 := by exact prefixLift 5156069
  have htrace : WordTrace (prefixWord ++ tailWord_5156069) baseStart_5156069 baseEnd_5156069 := by
    simpa [prefixWord, tailWord_5156069, baseEnd_5156069] using wordTrace_append hprefix tailTrace_5156069
  have hstable : (prefixWord ++ tailWord_5156069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5156069).length < 2 ^ (prefixWord ++ tailWord_5156069).sum := by decide
  have hdescent : baseEnd_5156069 < baseStart_5156069 := by decide
  rcases family_descends (prefixWord ++ tailWord_5156069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5156138 : List Nat := [3, 1, 4, 2, 1, 1, 1, 1, 4, 1, 4]
def baseStart_5156138 : Nat := 118140960795 + 5156138 * 2 ^ 59
def prefixEnd_5156138 : Nat := 4983230072969 + 3 ^ 40 * 5156138 * 2
def baseEnd_5156138 : Nat := 2647577114912252820062359

theorem tailTrace_5156138 : CollatzResearch.WordTrace tailWord_5156138 prefixEnd_5156138 2647577114912252820062359 := by
  unfold tailWord_5156138
  simp only [CollatzResearch.WordTrace]
  refine ⟨47014950648550024776875267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125373201729466732738334045 47014950648550024776875267)
  ·
    refine ⟨70522425972825037165312901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47014950648550024776875267 70522425972825037165312901)
    ·
      refine ⟨13222954869904694468496169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70522425972825037165312901 13222954869904694468496169)
      ·
        refine ⟨9917216152428520851372127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13222954869904694468496169 9917216152428520851372127)
        ·
          refine ⟨14875824228642781277058191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9917216152428520851372127 14875824228642781277058191)
          ·
            refine ⟨22313736342964171915587287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14875824228642781277058191 22313736342964171915587287)
            ·
              refine ⟨33470604514446257873380931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22313736342964171915587287 33470604514446257873380931)
              ·
                refine ⟨50205906771669386810071397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33470604514446257873380931 50205906771669386810071397)
                ·
                  refine ⟨9413607519688010026888387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50205906771669386810071397 9413607519688010026888387)
                  ·
                    refine ⟨14120411279532015040332581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9413607519688010026888387 14120411279532015040332581)
                    ·
                      refine ⟨2647577114912252820062359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14120411279532015040332581 2647577114912252820062359)
                      ·
                        rfl

theorem cell23_5156138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_5156138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5156138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5156138 prefixEnd_5156138 := by exact prefixLift 5156138
  have htrace : WordTrace (prefixWord ++ tailWord_5156138) baseStart_5156138 baseEnd_5156138 := by
    simpa [prefixWord, tailWord_5156138, baseEnd_5156138] using wordTrace_append hprefix tailTrace_5156138
  have hstable : (prefixWord ++ tailWord_5156138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5156138).length < 2 ^ (prefixWord ++ tailWord_5156138).sum := by decide
  have hdescent : baseEnd_5156138 < baseStart_5156138 := by decide
  rcases family_descends (prefixWord ++ tailWord_5156138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5156144 : List Nat := [2, 1, 1, 1, 2, 2, 3, 3, 8]
def baseStart_5156144 : Nat := 118140960795 + 5156144 * 2 ^ 59
def prefixEnd_5156144 : Nat := 4983230072969 + 3 ^ 40 * 5156144 * 2
def baseEnd_5156144 : Nat := 294175577310686644065259

theorem tailTrace_5156144 : CollatzResearch.WordTrace tailWord_5156144 prefixEnd_5156144 294175577310686644065259 := by
  unfold tailWord_5156144
  simp only [CollatzResearch.WordTrace]
  refine ⟨94030010716089181066109743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125373347621452241421479657 94030010716089181066109743)
  ·
    refine ⟨141045016074133771599164615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94030010716089181066109743 141045016074133771599164615)
    ·
      refine ⟨211567524111200657398746923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141045016074133771599164615 211567524111200657398746923)
      ·
        refine ⟨317351286166800986098120385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211567524111200657398746923 317351286166800986098120385)
        ·
          refine ⟨238013464625100739573590289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 317351286166800986098120385 238013464625100739573590289)
          ·
            refine ⟨178510098468825554680192717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 238013464625100739573590289 178510098468825554680192717)
            ·
              refine ⟨66941286925809583005072269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 178510098468825554680192717 66941286925809583005072269)
              ·
                refine ⟨25102982597178593626902101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66941286925809583005072269 25102982597178593626902101)
                ·
                  refine ⟨294175577310686644065259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25102982597178593626902101 294175577310686644065259)
                  ·
                    rfl

theorem cell23_5156144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 3, 8].length) (baseStart_5156144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5156144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5156144 prefixEnd_5156144 := by exact prefixLift 5156144
  have htrace : WordTrace (prefixWord ++ tailWord_5156144) baseStart_5156144 baseEnd_5156144 := by
    simpa [prefixWord, tailWord_5156144, baseEnd_5156144] using wordTrace_append hprefix tailTrace_5156144
  have hstable : (prefixWord ++ tailWord_5156144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5156144).length < 2 ^ (prefixWord ++ tailWord_5156144).sum := by decide
  have hdescent : baseEnd_5156144 < baseStart_5156144 := by decide
  rcases family_descends (prefixWord ++ tailWord_5156144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5156158 : List Nat := [4, 2, 1, 2, 1, 1, 1, 2, 4, 2, 3]
def baseStart_5156158 : Nat := 118140960795 + 5156158 * 2 ^ 59
def prefixEnd_5156158 : Nat := 4983230072969 + 3 ^ 40 * 5156158 * 2
def baseEnd_5156158 : Nat := 2647587384525342741812267

theorem tailTrace_5156158 : CollatzResearch.WordTrace tailWord_5156158 prefixEnd_5156158 2647587384525342741812267 := by
  unfold tailWord_5156158
  simp only [CollatzResearch.WordTrace]
  refine ⟨23507566506765955315403641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125373688036085095015486085 23507566506765955315403641)
  ·
    refine ⟨17630674880074466486552731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23507566506765955315403641 17630674880074466486552731)
    ·
      refine ⟨26446012320111699729829097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17630674880074466486552731 26446012320111699729829097)
      ·
        refine ⟨19834509240083774797371823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26446012320111699729829097 19834509240083774797371823)
        ·
          refine ⟨29751763860125662196057735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19834509240083774797371823 29751763860125662196057735)
          ·
            refine ⟨44627645790188493294086603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29751763860125662196057735 44627645790188493294086603)
            ·
              refine ⟨66941468685282739941129905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44627645790188493294086603 66941468685282739941129905)
              ·
                refine ⟨50206101513962054955847429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66941468685282739941129905 50206101513962054955847429)
                ·
                  refine ⟨9413644033867885304221393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50206101513962054955847429 9413644033867885304221393)
                  ·
                    refine ⟨7060233025400913978166045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9413644033867885304221393 7060233025400913978166045)
                    ·
                      refine ⟨2647587384525342741812267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7060233025400913978166045 2647587384525342741812267)
                      ·
                        rfl

theorem cell23_5156158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 2, 4, 2, 3].length) (baseStart_5156158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5156158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5156158 prefixEnd_5156158 := by exact prefixLift 5156158
  have htrace : WordTrace (prefixWord ++ tailWord_5156158) baseStart_5156158 baseEnd_5156158 := by
    simpa [prefixWord, tailWord_5156158, baseEnd_5156158] using wordTrace_append hprefix tailTrace_5156158
  have hstable : (prefixWord ++ tailWord_5156158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5156158).length < 2 ^ (prefixWord ++ tailWord_5156158).sum := by decide
  have hdescent : baseEnd_5156158 < baseStart_5156158 := by decide
  rcases family_descends (prefixWord ++ tailWord_5156158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5156199 : List Nat := [1, 1, 5, 1, 4, 2, 2, 2, 1, 4]
def baseStart_5156199 : Nat := 118140960795 + 5156199 * 2 ^ 59
def prefixEnd_5156199 : Nat := 4983230072969 + 3 ^ 40 * 5156199 * 2
def baseEnd_5156199 : Nat := 882536145744059027133193

theorem tailTrace_5156199 : CollatzResearch.WordTrace tailWord_5156199 prefixEnd_5156199 882536145744059027133193 := by
  unfold tailWord_5156199
  simp only [CollatzResearch.WordTrace]
  refine ⟨188062027446979106525471651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125374684964652737683647767 188062027446979106525471651)
  ·
    refine ⟨282093041170468659788207477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188062027446979106525471651 282093041170468659788207477)
    ·
      refine ⟨26446222609731436855144451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 282093041170468659788207477 26446222609731436855144451)
      ·
        refine ⟨39669333914597155282716677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26446222609731436855144451 39669333914597155282716677)
        ·
          refine ⟨7438000108986966615509377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39669333914597155282716677 7438000108986966615509377)
          ·
            refine ⟨5578500081740224961632033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7438000108986966615509377 5578500081740224961632033)
            ·
              refine ⟨4183875061305168721224025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5578500081740224961632033 4183875061305168721224025)
              ·
                refine ⟨3137906295978876540918019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4183875061305168721224025 3137906295978876540918019)
                ·
                  refine ⟨4706859443968314811377029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3137906295978876540918019 4706859443968314811377029)
                  ·
                    refine ⟨882536145744059027133193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4706859443968314811377029 882536145744059027133193)
                    ·
                      rfl

theorem cell23_5156199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 2, 2, 1, 4].length) (baseStart_5156199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5156199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5156199 prefixEnd_5156199 := by exact prefixLift 5156199
  have htrace : WordTrace (prefixWord ++ tailWord_5156199) baseStart_5156199 baseEnd_5156199 := by
    simpa [prefixWord, tailWord_5156199, baseEnd_5156199] using wordTrace_append hprefix tailTrace_5156199
  have hstable : (prefixWord ++ tailWord_5156199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5156199).length < 2 ^ (prefixWord ++ tailWord_5156199).sum := by decide
  have hdescent : baseEnd_5156199 < baseStart_5156199 := by decide
  rcases family_descends (prefixWord ++ tailWord_5156199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5156228 : List Nat := [2, 3, 2, 1, 1, 3, 2, 1, 3, 1, 4]
def baseStart_5156228 : Nat := 118140960795 + 5156228 * 2 ^ 59
def prefixEnd_5156228 : Nat := 4983230072969 + 3 ^ 40 * 5156228 * 2
def baseEnd_5156228 : Nat := 2647623328171157467936945

theorem tailTrace_5156228 : CollatzResearch.WordTrace tailWord_5156228 prefixEnd_5156228 2647623328171157467936945 := by
  unfold tailWord_5156228
  simp only [CollatzResearch.WordTrace]
  refine ⟨94031542581937022239138669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125375390109249362985518225 94031542581937022239138669)
  ·
    refine ⟨35261828468226383339677001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94031542581937022239138669 35261828468226383339677001)
    ·
      refine ⟨26446371351169787504757751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35261828468226383339677001 26446371351169787504757751)
      ·
        refine ⟨39669557026754681257136627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26446371351169787504757751 39669557026754681257136627)
        ·
          refine ⟨59504335540132021885704941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39669557026754681257136627 59504335540132021885704941)
          ·
            refine ⟨22314125827549508207139353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59504335540132021885704941 22314125827549508207139353)
            ·
              refine ⟨16735594370662131155354515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22314125827549508207139353 16735594370662131155354515)
              ·
                refine ⟨25103391555993196733031773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16735594370662131155354515 25103391555993196733031773)
                ·
                  refine ⟨9413771833497448774886915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25103391555993196733031773 9413771833497448774886915)
                  ·
                    refine ⟨14120657750246173162330373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9413771833497448774886915 14120657750246173162330373)
                    ·
                      refine ⟨2647623328171157467936945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14120657750246173162330373 2647623328171157467936945)
                      ·
                        rfl

theorem cell23_5156228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 1, 3, 1, 4].length) (baseStart_5156228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5156228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5156228 prefixEnd_5156228 := by exact prefixLift 5156228
  have htrace : WordTrace (prefixWord ++ tailWord_5156228) baseStart_5156228 baseEnd_5156228 := by
    simpa [prefixWord, tailWord_5156228, baseEnd_5156228] using wordTrace_append hprefix tailTrace_5156228
  have hstable : (prefixWord ++ tailWord_5156228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5156228).length < 2 ^ (prefixWord ++ tailWord_5156228).sum := by decide
  have hdescent : baseEnd_5156228 < baseStart_5156228 := by decide
  rcases family_descends (prefixWord ++ tailWord_5156228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5156232 : List Nat := [2, 1, 3, 3, 1, 4, 1, 1, 2, 3, 2]
def baseStart_5156232 : Nat := 118140960795 + 5156232 * 2 ^ 59
def prefixEnd_5156232 : Nat := 4983230072969 + 3 ^ 40 * 5156232 * 2
def baseEnd_5156232 : Nat := 2647625382093775452286927

theorem tailTrace_5156232 : CollatzResearch.WordTrace tailWord_5156232 prefixEnd_5156232 2647625382093775452286927 := by
  unfold tailWord_5156232
  simp only [CollatzResearch.WordTrace]
  refine ⟨94031615527929776580711475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125375487370573035440948633 94031615527929776580711475)
  ·
    refine ⟨141047423291894664871067213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94031615527929776580711475 141047423291894664871067213)
    ·
      refine ⟨52892783734460499326650205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141047423291894664871067213 52892783734460499326650205)
      ·
        refine ⟨19834793900422687247493827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52892783734460499326650205 19834793900422687247493827)
        ·
          refine ⟨29752190850634030871240741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19834793900422687247493827 29752190850634030871240741)
          ·
            refine ⟨5578535784493880788357639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29752190850634030871240741 5578535784493880788357639)
            ·
              refine ⟨8367803676740821182536459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5578535784493880788357639 8367803676740821182536459)
              ·
                refine ⟨12551705515111231773804689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8367803676740821182536459 12551705515111231773804689)
                ·
                  refine ⟨9413779136333423830353517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12551705515111231773804689 9413779136333423830353517)
                  ·
                    refine ⟨3530167176125033936382569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9413779136333423830353517 3530167176125033936382569)
                    ·
                      refine ⟨2647625382093775452286927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3530167176125033936382569 2647625382093775452286927)
                      ·
                        rfl

theorem cell23_5156232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 1, 1, 2, 3, 2].length) (baseStart_5156232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5156232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5156232 prefixEnd_5156232 := by exact prefixLift 5156232
  have htrace : WordTrace (prefixWord ++ tailWord_5156232) baseStart_5156232 baseEnd_5156232 := by
    simpa [prefixWord, tailWord_5156232, baseEnd_5156232] using wordTrace_append hprefix tailTrace_5156232
  have hstable : (prefixWord ++ tailWord_5156232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5156232).length < 2 ^ (prefixWord ++ tailWord_5156232).sum := by decide
  have hdescent : baseEnd_5156232 < baseStart_5156232 := by decide
  rcases family_descends (prefixWord ++ tailWord_5156232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5156242 : List Nat := [3, 2, 3, 3, 1, 1, 1, 3, 1, 5]
def baseStart_5156242 : Nat := 118140960795 + 5156242 * 2 ^ 59
def prefixEnd_5156242 : Nat := 4983230072969 + 3 ^ 40 * 5156242 * 2
def baseEnd_5156242 : Nat := 882543505633440137720627

theorem tailTrace_5156242 : CollatzResearch.WordTrace tailWord_5156242 prefixEnd_5156242 882543505633440137720627 := by
  unfold tailWord_5156242
  simp only [CollatzResearch.WordTrace]
  refine ⟨47015898946455831217321745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125375730523882216579524653 47015898946455831217321745)
  ·
    refine ⟨35261924209841873412991309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47015898946455831217321745 35261924209841873412991309)
    ·
      refine ⟨13223221578690702529871741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35261924209841873412991309 13223221578690702529871741)
      ·
        refine ⟨4958708092009013448701903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13223221578690702529871741 4958708092009013448701903)
        ·
          refine ⟨7438062138013520173052855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4958708092009013448701903 7438062138013520173052855)
          ·
            refine ⟨11157093207020280259579283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7438062138013520173052855 11157093207020280259579283)
            ·
              refine ⟨16735639810530420389368925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11157093207020280259579283 16735639810530420389368925)
              ·
                refine ⟨6275864928948907646013347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16735639810530420389368925 6275864928948907646013347)
                ·
                  refine ⟨9413797393423361469020021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6275864928948907646013347 9413797393423361469020021)
                  ·
                    refine ⟨882543505633440137720627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9413797393423361469020021 882543505633440137720627)
                    ·
                      rfl

theorem cell23_5156242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 3, 1, 5].length) (baseStart_5156242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5156242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5156242 prefixEnd_5156242 := by exact prefixLift 5156242
  have htrace : WordTrace (prefixWord ++ tailWord_5156242) baseStart_5156242 baseEnd_5156242 := by
    simpa [prefixWord, tailWord_5156242, baseEnd_5156242] using wordTrace_append hprefix tailTrace_5156242
  have hstable : (prefixWord ++ tailWord_5156242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5156242).length < 2 ^ (prefixWord ++ tailWord_5156242).sum := by decide
  have hdescent : baseEnd_5156242 < baseStart_5156242 := by decide
  rcases family_descends (prefixWord ++ tailWord_5156242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5156245 : List Nat := [1, 3, 2, 1, 1, 2, 6, 1, 1, 1, 4]
def baseStart_5156245 : Nat := 118140960795 + 5156245 * 2 ^ 59
def prefixEnd_5156245 : Nat := 4983230072969 + 3 ^ 40 * 5156245 * 2
def baseEnd_5156245 : Nat := 2647632057342283901424367

theorem tailTrace_5156245 : CollatzResearch.WordTrace tailWord_5156245 prefixEnd_5156245 2647632057342283901424367 := by
  unfold tailWord_5156245
  simp only [CollatzResearch.WordTrace]
  refine ⟨188063705204812456381646189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125375803469874970921097459 188063705204812456381646189)
  ·
    refine ⟨70523889451804671143117321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 188063705204812456381646189 70523889451804671143117321)
    ·
      refine ⟨52892917088853503357337991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70523889451804671143117321 52892917088853503357337991)
      ·
        refine ⟨79339375633280255036006987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52892917088853503357337991 79339375633280255036006987)
        ·
          refine ⟨119009063449920382554010481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79339375633280255036006987 119009063449920382554010481)
          ·
            refine ⟨89256797587440286915507861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119009063449920382554010481 89256797587440286915507861)
            ·
              refine ⟨4183912386911263449164431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 89256797587440286915507861 4183912386911263449164431)
              ·
                refine ⟨6275868580366895173746647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4183912386911263449164431 6275868580366895173746647)
                ·
                  refine ⟨9413802870550342760619971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6275868580366895173746647 9413802870550342760619971)
                  ·
                    refine ⟨14120704305825514140929957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9413802870550342760619971 14120704305825514140929957)
                    ·
                      refine ⟨2647632057342283901424367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14120704305825514140929957 2647632057342283901424367)
                      ·
                        rfl

theorem cell23_5156245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 6, 1, 1, 1, 4].length) (baseStart_5156245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5156245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5156245 prefixEnd_5156245 := by exact prefixLift 5156245
  have htrace : WordTrace (prefixWord ++ tailWord_5156245) baseStart_5156245 baseEnd_5156245 := by
    simpa [prefixWord, tailWord_5156245, baseEnd_5156245] using wordTrace_append hprefix tailTrace_5156245
  have hstable : (prefixWord ++ tailWord_5156245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5156245).length < 2 ^ (prefixWord ++ tailWord_5156245).sum := by decide
  have hdescent : baseEnd_5156245 < baseStart_5156245 := by decide
  rcases family_descends (prefixWord ++ tailWord_5156245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5156255 : List Nat := [1, 1, 2, 5, 1, 2, 3, 2, 2, 4]
def baseStart_5156255 : Nat := 118140960795 + 5156255 * 2 ^ 59
def prefixEnd_5156255 : Nat := 4983230072969 + 3 ^ 40 * 5156255 * 2
def baseEnd_5156255 : Nat := 882545730716276287433107

theorem tailTrace_5156255 : CollatzResearch.WordTrace tailWord_5156255 prefixEnd_5156255 882545730716276287433107 := by
  unfold tailWord_5156255
  simp only [CollatzResearch.WordTrace]
  refine ⟨188064069934776228089510219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125376046623184152059673479 188064069934776228089510219)
  ·
    refine ⟨282096104902164342134265329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188064069934776228089510219 282096104902164342134265329)
    ·
      refine ⟨211572078676623256600698997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 282096104902164342134265329 211572078676623256600698997)
      ·
        refine ⟨19834882375933430306315531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 211572078676623256600698997 19834882375933430306315531)
        ·
          refine ⟨29752323563900145459473297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19834882375933430306315531 29752323563900145459473297)
          ·
            refine ⟨22314242672925109094604973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29752323563900145459473297 22314242672925109094604973)
            ·
              refine ⟨8367841002346915910476865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22314242672925109094604973 8367841002346915910476865)
              ·
                refine ⟨6275880751760186932857649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8367841002346915910476865 6275880751760186932857649)
                ·
                  refine ⟨4706910563820140199643237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6275880751760186932857649 4706910563820140199643237)
                  ·
                    refine ⟨882545730716276287433107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4706910563820140199643237 882545730716276287433107)
                    ·
                      rfl

theorem cell23_5156255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 3, 2, 2, 4].length) (baseStart_5156255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5156255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5156255 prefixEnd_5156255 := by exact prefixLift 5156255
  have htrace : WordTrace (prefixWord ++ tailWord_5156255) baseStart_5156255 baseEnd_5156255 := by
    simpa [prefixWord, tailWord_5156255, baseEnd_5156255] using wordTrace_append hprefix tailTrace_5156255
  have hstable : (prefixWord ++ tailWord_5156255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5156255).length < 2 ^ (prefixWord ++ tailWord_5156255).sum := by decide
  have hdescent : baseEnd_5156255 < baseStart_5156255 := by decide
  rcases family_descends (prefixWord ++ tailWord_5156255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5156291 : List Nat := [1, 1, 1, 3, 1, 1, 5, 1, 2, 2, 5]
def baseStart_5156291 : Nat := 118140960795 + 5156291 * 2 ^ 59
def prefixEnd_5156291 : Nat := 4983230072969 + 3 ^ 40 * 5156291 * 2
def baseEnd_5156291 : Nat := 2647655677452390721449155

theorem tailTrace_5156291 : CollatzResearch.WordTrace tailWord_5156291 prefixEnd_5156291 2647655677452390721449155 := by
  unfold tailWord_5156291
  simp only [CollatzResearch.WordTrace]
  refine ⟨188065382962645806237820727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125376921975097204158547151 188065382962645806237820727)
  ·
    refine ⟨282098074443968709356731091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188065382962645806237820727 282098074443968709356731091)
    ·
      refine ⟨423147111665953064035096637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 282098074443968709356731091 423147111665953064035096637)
      ·
        refine ⟨158680166874732399013161239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 423147111665953064035096637 158680166874732399013161239)
        ·
          refine ⟨238020250312098598519741859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158680166874732399013161239 238020250312098598519741859)
          ·
            refine ⟨357030375468147897779612789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 238020250312098598519741859 357030375468147897779612789)
            ·
              refine ⟨33471597700138865416838699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 357030375468147897779612789 33471597700138865416838699)
              ·
                refine ⟨50207396550208298125258049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33471597700138865416838699 50207396550208298125258049)
                ·
                  refine ⟨37655547412656223593943537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50207396550208298125258049 37655547412656223593943537)
                  ·
                    refine ⟨28241660559492167695457653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37655547412656223593943537 28241660559492167695457653)
                    ·
                      refine ⟨2647655677452390721449155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28241660559492167695457653 2647655677452390721449155)
                      ·
                        rfl

theorem cell23_5156291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 1, 2, 2, 5].length) (baseStart_5156291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5156291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5156291 prefixEnd_5156291 := by exact prefixLift 5156291
  have htrace : WordTrace (prefixWord ++ tailWord_5156291) baseStart_5156291 baseEnd_5156291 := by
    simpa [prefixWord, tailWord_5156291, baseEnd_5156291] using wordTrace_append hprefix tailTrace_5156291
  have hstable : (prefixWord ++ tailWord_5156291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5156291).length < 2 ^ (prefixWord ++ tailWord_5156291).sum := by decide
  have hdescent : baseEnd_5156291 < baseStart_5156291 := by decide
  rcases family_descends (prefixWord ++ tailWord_5156291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5156311 : List Nat := [1, 1, 3, 2, 1, 1, 1, 3, 4, 6]
def baseStart_5156311 : Nat := 118140960795 + 5156311 * 2 ^ 59
def prefixEnd_5156311 : Nat := 4983230072969 + 3 ^ 40 * 5156311 * 2
def baseEnd_5156311 : Nat := 882555315688493547733021

theorem tailTrace_5156311 : CollatzResearch.WordTrace tailWord_5156311 prefixEnd_5156311 882555315688493547733021 := by
  unfold tailWord_5156311
  simp only [CollatzResearch.WordTrace]
  refine ⟨188066112422573349653548787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125377408281715566435699191 188066112422573349653548787)
  ·
    refine ⟨282099168633860024480323181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188066112422573349653548787 282099168633860024480323181)
    ·
      refine ⟨105787188237697509180121193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 282099168633860024480323181 105787188237697509180121193)
      ·
        refine ⟨79340391178273131885090895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105787188237697509180121193 79340391178273131885090895)
        ·
          refine ⟨119010586767409697827636343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79340391178273131885090895 119010586767409697827636343)
          ·
            refine ⟨178515880151114546741454515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119010586767409697827636343 178515880151114546741454515)
            ·
              refine ⟨267773820226671820112181773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 178515880151114546741454515 267773820226671820112181773)
              ·
                refine ⟨100415182585001932542068165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 267773820226671820112181773 100415182585001932542068165)
                ·
                  refine ⟨18827846734687862351637781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 100415182585001932542068165 18827846734687862351637781)
                  ·
                    refine ⟨882555315688493547733021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18827846734687862351637781 882555315688493547733021)
                    ·
                      rfl

theorem cell23_5156311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 4, 6].length) (baseStart_5156311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5156311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5156311 prefixEnd_5156311 := by exact prefixLift 5156311
  have htrace : WordTrace (prefixWord ++ tailWord_5156311) baseStart_5156311 baseEnd_5156311 := by
    simpa [prefixWord, tailWord_5156311, baseEnd_5156311] using wordTrace_append hprefix tailTrace_5156311
  have hstable : (prefixWord ++ tailWord_5156311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5156311).length < 2 ^ (prefixWord ++ tailWord_5156311).sum := by decide
  have hdescent : baseEnd_5156311 < baseStart_5156311 := by decide
  rcases family_descends (prefixWord ++ tailWord_5156311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5156351 : List Nat := [1, 1, 2, 2, 1, 2, 2, 2, 1, 2, 7]
def baseStart_5156351 : Nat := 118140960795 + 5156351 * 2 ^ 59
def prefixEnd_5156351 : Nat := 4983230072969 + 3 ^ 40 * 5156351 * 2
def baseEnd_5156351 : Nat := 2647686486291660486698879

theorem tailTrace_5156351 : CollatzResearch.WordTrace tailWord_5156351 prefixEnd_5156351 2647686486291660486698879 := by
  unfold tailWord_5156351
  simp only [CollatzResearch.WordTrace]
  refine ⟨188067571342428436485004907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125378380894952290990003271 188067571342428436485004907)
  ·
    refine ⟨282101357013642654727507361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188067571342428436485004907 282101357013642654727507361)
    ·
      refine ⟨211576017760231991045630521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 282101357013642654727507361 211576017760231991045630521)
      ·
        refine ⟨158682013320173993284222891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 211576017760231991045630521 158682013320173993284222891)
        ·
          refine ⟨238023019980260989926334337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158682013320173993284222891 238023019980260989926334337)
          ·
            refine ⟨178517264985195742444750753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 238023019980260989926334337 178517264985195742444750753)
            ·
              refine ⟨133887948738896806833563065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 178517264985195742444750753 133887948738896806833563065)
              ·
                refine ⟨100415961554172605125172299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 133887948738896806833563065 100415961554172605125172299)
                ·
                  refine ⟨150623942331258907687758449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 100415961554172605125172299 150623942331258907687758449)
                  ·
                    refine ⟨112967956748444180765818837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 150623942331258907687758449 112967956748444180765818837)
                    ·
                      refine ⟨2647686486291660486698879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 112967956748444180765818837 2647686486291660486698879)
                      ·
                        rfl

theorem cell23_5156351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 2, 7].length) (baseStart_5156351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5156351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5156351 prefixEnd_5156351 := by exact prefixLift 5156351
  have htrace : WordTrace (prefixWord ++ tailWord_5156351) baseStart_5156351 baseEnd_5156351 := by
    simpa [prefixWord, tailWord_5156351, baseEnd_5156351] using wordTrace_append hprefix tailTrace_5156351
  have hstable : (prefixWord ++ tailWord_5156351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5156351).length < 2 ^ (prefixWord ++ tailWord_5156351).sum := by decide
  have hdescent : baseEnd_5156351 < baseStart_5156351 := by decide
  rcases family_descends (prefixWord ++ tailWord_5156351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5156356 : List Nat := [2, 3, 2, 3, 2, 1, 3, 1, 1, 3, 2]
def baseStart_5156356 : Nat := 118140960795 + 5156356 * 2 ^ 59
def prefixEnd_5156356 : Nat := 4983230072969 + 3 ^ 40 * 5156356 * 2
def baseEnd_5156356 : Nat := 2647689053694932967136357

theorem tailTrace_5156356 : CollatzResearch.WordTrace tailWord_5156356 prefixEnd_5156356 2647689053694932967136357 := by
  unfold tailWord_5156356
  simp only [CollatzResearch.WordTrace]
  refine ⟨94033876853705161169468461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125378502471606881559291281 94033876853705161169468461)
  ·
    refine ⟨35262703820139435438550673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94033876853705161169468461 35262703820139435438550673)
    ·
      refine ⟨26447027865104576578913005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35262703820139435438550673 26447027865104576578913005)
      ·
        refine ⟨9917635449414216217092377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26447027865104576578913005 9917635449414216217092377)
        ·
          refine ⟨7438226587060662162819283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9917635449414216217092377 7438226587060662162819283)
          ·
            refine ⟨11157339880590993244228925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7438226587060662162819283 11157339880590993244228925)
            ·
              refine ⟨4184002455221622466585847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11157339880590993244228925 4184002455221622466585847)
              ·
                refine ⟨6276003682832433699878771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4184002455221622466585847 6276003682832433699878771)
                ·
                  refine ⟨9414005524248650549818157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6276003682832433699878771 9414005524248650549818157)
                  ·
                    refine ⟨3530252071593243956181809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9414005524248650549818157 3530252071593243956181809)
                    ·
                      refine ⟨2647689053694932967136357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3530252071593243956181809 2647689053694932967136357)
                      ·
                        rfl

theorem cell23_5156356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 3, 1, 1, 3, 2].length) (baseStart_5156356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5156356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5156356 prefixEnd_5156356 := by exact prefixLift 5156356
  have htrace : WordTrace (prefixWord ++ tailWord_5156356) baseStart_5156356 baseEnd_5156356 := by
    simpa [prefixWord, tailWord_5156356, baseEnd_5156356] using wordTrace_append hprefix tailTrace_5156356
  have hstable : (prefixWord ++ tailWord_5156356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5156356).length < 2 ^ (prefixWord ++ tailWord_5156356).sum := by decide
  have hdescent : baseEnd_5156356 < baseStart_5156356 := by decide
  rcases family_descends (prefixWord ++ tailWord_5156356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5156385 : List Nat := [1, 2, 3, 2, 2, 3, 1, 1, 2, 3, 3]
def baseStart_5156385 : Nat := 118140960795 + 5156385 * 2 ^ 59
def prefixEnd_5156385 : Nat := 4983230072969 + 3 ^ 40 * 5156385 * 2
def baseEnd_5156385 : Nat := 2647703944633913353673723

theorem tailTrace_5156385 : CollatzResearch.WordTrace tailWord_5156385 prefixEnd_5156385 2647703944633913353673723 := by
  unfold tailWord_5156385
  simp only [CollatzResearch.WordTrace]
  refine ⟨188068811424305260291742609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125379207616203506861161739 188068811424305260291742609)
  ·
    refine ⟨141051608568228945218806957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188068811424305260291742609 141051608568228945218806957)
    ·
      refine ⟨52894353213085854457052609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141051608568228945218806957 52894353213085854457052609)
      ·
        refine ⟨39670764909814390842789457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52894353213085854457052609 39670764909814390842789457)
        ·
          refine ⟨29753073682360793132092093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39670764909814390842789457 29753073682360793132092093)
          ·
            refine ⟨11157402630885297424534535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29753073682360793132092093 11157402630885297424534535)
            ·
              refine ⟨16736103946327946136801803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11157402630885297424534535 16736103946327946136801803)
              ·
                refine ⟨25104155919491919205202705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16736103946327946136801803 25104155919491919205202705)
                ·
                  refine ⟨18828116939618939403902029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25104155919491919205202705 18828116939618939403902029)
                  ·
                    refine ⟨7060543852357102276463261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18828116939618939403902029 7060543852357102276463261)
                    ·
                      refine ⟨2647703944633913353673723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7060543852357102276463261 2647703944633913353673723)
                      ·
                        rfl

theorem cell23_5156385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 1, 2, 3, 3].length) (baseStart_5156385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5156385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5156385 prefixEnd_5156385 := by exact prefixLift 5156385
  have htrace : WordTrace (prefixWord ++ tailWord_5156385) baseStart_5156385 baseEnd_5156385 := by
    simpa [prefixWord, tailWord_5156385, baseEnd_5156385] using wordTrace_append hprefix tailTrace_5156385
  have hstable : (prefixWord ++ tailWord_5156385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5156385).length < 2 ^ (prefixWord ++ tailWord_5156385).sum := by decide
  have hdescent : baseEnd_5156385 < baseStart_5156385 := by decide
  rcases family_descends (prefixWord ++ tailWord_5156385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5156405 : List Nat := [1, 3, 3, 1, 1, 3, 3, 1, 2, 5]
def baseStart_5156405 : Nat := 118140960795 + 5156405 * 2 ^ 59
def prefixEnd_5156405 : Nat := 4983230072969 + 3 ^ 40 * 5156405 * 2
def baseEnd_5156405 : Nat := 882571404749001091807877

theorem tailTrace_5156405 : CollatzResearch.WordTrace tailWord_5156405 prefixEnd_5156405 882571404749001091807877 := by
  unfold tailWord_5156405
  simp only [CollatzResearch.WordTrace]
  refine ⟨188069540884232803707470669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125379693922821869138313779 188069540884232803707470669)
  ·
    refine ⟨70526077831587301390301501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 188069540884232803707470669 70526077831587301390301501)
    ·
      refine ⟨26447279186845238021363063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70526077831587301390301501 26447279186845238021363063)
      ·
        refine ⟨39670918780267857032044595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26447279186845238021363063 39670918780267857032044595)
        ·
          refine ⟨59506378170401785548066893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39670918780267857032044595 59506378170401785548066893)
          ·
            refine ⟨22314891813900669580525085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59506378170401785548066893 22314891813900669580525085)
            ·
              refine ⟨8368084430212751092696907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22314891813900669580525085 8368084430212751092696907)
              ·
                refine ⟨12552126645319126639045361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8368084430212751092696907 12552126645319126639045361)
                ·
                  refine ⟨9414094983989344979284021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12552126645319126639045361 9414094983989344979284021)
                  ·
                    refine ⟨882571404749001091807877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9414094983989344979284021 882571404749001091807877)
                    ·
                      rfl

theorem cell23_5156405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 3, 1, 2, 5].length) (baseStart_5156405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5156405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5156405 prefixEnd_5156405 := by exact prefixLift 5156405
  have htrace : WordTrace (prefixWord ++ tailWord_5156405) baseStart_5156405 baseEnd_5156405 := by
    simpa [prefixWord, tailWord_5156405, baseEnd_5156405] using wordTrace_append hprefix tailTrace_5156405
  have hstable : (prefixWord ++ tailWord_5156405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5156405).length < 2 ^ (prefixWord ++ tailWord_5156405).sum := by decide
  have hdescent : baseEnd_5156405 < baseStart_5156405 := by decide
  rcases family_descends (prefixWord ++ tailWord_5156405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5156512 : List Nat := [2, 1, 1, 4, 3, 1, 3, 2, 1, 5]
def baseStart_5156512 : Nat := 118140960795 + 5156512 * 2 ^ 59
def prefixEnd_5156512 : Nat := 4983230072969 + 3 ^ 40 * 5156512 * 2
def baseEnd_5156512 : Nat := 882589718892344785595213

theorem tailTrace_5156512 : CollatzResearch.WordTrace tailWord_5156512 prefixEnd_5156512 882589718892344785595213 := by
  unfold tailWord_5156512
  simp only [CollatzResearch.WordTrace]
  refine ⟨94036721747422580490807895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125382295663230107321077193 94036721747422580490807895)
  ·
    refine ⟨141055082621133870736211843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94036721747422580490807895 141055082621133870736211843)
    ·
      refine ⟨211582623931700806104317765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141055082621133870736211843 211582623931700806104317765)
      ·
        refine ⟨39671741987193901144559581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 211582623931700806104317765 39671741987193901144559581)
        ·
          refine ⟨14876903245197712929209843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39671741987193901144559581 14876903245197712929209843)
          ·
            refine ⟨22315354867796569393814765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14876903245197712929209843 22315354867796569393814765)
            ·
              refine ⟨8368258075423713522680537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22315354867796569393814765 8368258075423713522680537)
              ·
                refine ⟨6276193556567785142010403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8368258075423713522680537 6276193556567785142010403)
                ·
                  refine ⟨9414290334851677713015605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6276193556567785142010403 9414290334851677713015605)
                  ·
                    refine ⟨882589718892344785595213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9414290334851677713015605 882589718892344785595213)
                    ·
                      rfl

theorem cell23_5156512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 3, 2, 1, 5].length) (baseStart_5156512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5156512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5156512 prefixEnd_5156512 := by exact prefixLift 5156512
  have htrace : WordTrace (prefixWord ++ tailWord_5156512) baseStart_5156512 baseEnd_5156512 := by
    simpa [prefixWord, tailWord_5156512, baseEnd_5156512] using wordTrace_append hprefix tailTrace_5156512
  have hstable : (prefixWord ++ tailWord_5156512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5156512).length < 2 ^ (prefixWord ++ tailWord_5156512).sum := by decide
  have hdescent : baseEnd_5156512 < baseStart_5156512 := by decide
  rcases family_descends (prefixWord ++ tailWord_5156512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5156515 : List Nat := [1, 1, 1, 4, 1, 1, 5, 1, 3, 1, 4]
def baseStart_5156515 : Nat := 118140960795 + 5156515 * 2 ^ 59
def prefixEnd_5156515 : Nat := 4983230072969 + 3 ^ 40 * 5156515 * 2
def baseEnd_5156515 : Nat := 2647770697118997845048125

theorem tailTrace_5156515 : CollatzResearch.WordTrace tailWord_5156515 prefixEnd_5156515 2647770697118997845048125 := by
  unfold tailWord_5156515
  simp only [CollatzResearch.WordTrace]
  refine ⟨188073552913834292493974999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125382368609222861662649999 188073552913834292493974999)
  ·
    refine ⟨282110329370751438740962499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188073552913834292493974999 282110329370751438740962499)
    ·
      refine ⟨423165494056127158111443749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 282110329370751438740962499 423165494056127158111443749)
      ·
        refine ⟨79343530135523842145895703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 423165494056127158111443749 79343530135523842145895703)
        ·
          refine ⟨119015295203285763218843555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79343530135523842145895703 119015295203285763218843555)
          ·
            refine ⟨178522942804928644828265333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119015295203285763218843555 178522942804928644828265333)
            ·
              refine ⟨16736525887962060452649875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 178522942804928644828265333 16736525887962060452649875)
              ·
                refine ⟨25104788831943090678974813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16736525887962060452649875 25104788831943090678974813)
                ·
                  refine ⟨9414295811978659004615555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25104788831943090678974813 9414295811978659004615555)
                  ·
                    refine ⟨14121443717967988506923333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9414295811978659004615555 14121443717967988506923333)
                    ·
                      refine ⟨2647770697118997845048125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14121443717967988506923333 2647770697118997845048125)
                      ·
                        rfl

theorem cell23_5156515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 1, 3, 1, 4].length) (baseStart_5156515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5156515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5156515 prefixEnd_5156515 := by exact prefixLift 5156515
  have htrace : WordTrace (prefixWord ++ tailWord_5156515) baseStart_5156515 baseEnd_5156515 := by
    simpa [prefixWord, tailWord_5156515, baseEnd_5156515] using wordTrace_append hprefix tailTrace_5156515
  have hstable : (prefixWord ++ tailWord_5156515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5156515).length < 2 ^ (prefixWord ++ tailWord_5156515).sum := by decide
  have hdescent : baseEnd_5156515 < baseStart_5156515 := by decide
  rcases family_descends (prefixWord ++ tailWord_5156515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5156538 : List Nat := [3, 1, 1, 1, 2, 15]
def baseStart_5156538 : Nat := 118140960795 + 5156538 * 2 ^ 59
def prefixEnd_5156538 : Nat := 4983230072969 + 3 ^ 40 * 5156538 * 2
def baseEnd_5156538 : Nat := 10896224309358235617533

theorem tailTrace_5156538 : CollatzResearch.WordTrace tailWord_5156538 prefixEnd_5156538 10896224309358235617533 := by
  unfold tailWord_5156538
  simp only [CollatzResearch.WordTrace]
  refine ⟨47018597948187741855515567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125382927861833978281374845 47018597948187741855515567)
  ·
    refine ⟨70527896922281612783273351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47018597948187741855515567 70527896922281612783273351)
    ·
      refine ⟨105791845383422419174910027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70527896922281612783273351 105791845383422419174910027)
      ·
        refine ⟨158687768075133628762365041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105791845383422419174910027 158687768075133628762365041)
        ·
          refine ⟨119015826056350221571773781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 158687768075133628762365041 119015826056350221571773781)
          ·
            refine ⟨10896224309358235617533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 15 119015826056350221571773781 10896224309358235617533)
            ·
              rfl

theorem cell23_5156538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 15].length) (baseStart_5156538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5156538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5156538 prefixEnd_5156538 := by exact prefixLift 5156538
  have htrace : WordTrace (prefixWord ++ tailWord_5156538) baseStart_5156538 baseEnd_5156538 := by
    simpa [prefixWord, tailWord_5156538, baseEnd_5156538] using wordTrace_append hprefix tailTrace_5156538
  have hstable : (prefixWord ++ tailWord_5156538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5156538).length < 2 ^ (prefixWord ++ tailWord_5156538).sum := by decide
  have hdescent : baseEnd_5156538 < baseStart_5156538 := by decide
  rcases family_descends (prefixWord ++ tailWord_5156538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5156562 : List Nat := [3, 2, 2, 2, 2, 1, 1, 3, 1, 2, 4]
def baseStart_5156562 : Nat := 118140960795 + 5156562 * 2 ^ 59
def prefixEnd_5156562 : Nat := 4983230072969 + 3 ^ 40 * 5156562 * 2
def baseEnd_5156562 : Nat := 2647794830709759161160409

theorem tailTrace_5156562 : CollatzResearch.WordTrace tailWord_5156562 prefixEnd_5156562 2647794830709759161160409 := by
  unfold tailWord_5156562
  simp only [CollatzResearch.WordTrace]
  refine ⟨47018816786166004880233985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125383511429776013013957293 47018816786166004880233985)
  ·
    refine ⟨35264112589624503660175489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47018816786166004880233985 35264112589624503660175489)
    ·
      refine ⟨26448084442218377745131617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35264112589624503660175489 26448084442218377745131617)
      ·
        refine ⟨19836063331663783308848713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26448084442218377745131617 19836063331663783308848713)
        ·
          refine ⟨14877047498747837481636535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19836063331663783308848713 14877047498747837481636535)
          ·
            refine ⟨22315571248121756222454803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14877047498747837481636535 22315571248121756222454803)
            ·
              refine ⟨33473356872182634333682205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22315571248121756222454803 33473356872182634333682205)
              ·
                refine ⟨12552508827068487875130827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33473356872182634333682205 12552508827068487875130827)
                ·
                  refine ⟨18828763240602731812696241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12552508827068487875130827 18828763240602731812696241)
                  ·
                    refine ⟨14121572430452048859522181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18828763240602731812696241 14121572430452048859522181)
                    ·
                      refine ⟨2647794830709759161160409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14121572430452048859522181 2647794830709759161160409)
                      ·
                        rfl

theorem cell23_5156562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_5156562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5156562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5156562 prefixEnd_5156562 := by exact prefixLift 5156562
  have htrace : WordTrace (prefixWord ++ tailWord_5156562) baseStart_5156562 baseEnd_5156562 := by
    simpa [prefixWord, tailWord_5156562, baseEnd_5156562] using wordTrace_append hprefix tailTrace_5156562
  have hstable : (prefixWord ++ tailWord_5156562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5156562).length < 2 ^ (prefixWord ++ tailWord_5156562).sum := by decide
  have hdescent : baseEnd_5156562 < baseStart_5156562 := by decide
  rcases family_descends (prefixWord ++ tailWord_5156562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5156583 : List Nat := [1, 1, 5, 4, 1, 2, 2, 1, 1, 1, 4]
def baseStart_5156583 : Nat := 118140960795 + 5156583 * 2 ^ 59
def prefixEnd_5156583 : Nat := 4983230072969 + 3 ^ 40 * 5156583 * 2
def baseEnd_5156583 : Nat := 2647805613803503578997813

theorem tailTrace_5156583 : CollatzResearch.WordTrace tailWord_5156583 prefixEnd_5156583 2647805613803503578997813 := by
  unfold tailWord_5156583
  simp only [CollatzResearch.WordTrace]
  refine ⟨188076033077587940107450403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125384022051725293404966935 188076033077587940107450403)
  ·
    refine ⟨282114049616381910161175605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188076033077587940107450403 282114049616381910161175605)
    ·
      refine ⟨26448192151535804077610213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 282114049616381910161175605 26448192151535804077610213)
      ·
        refine ⟨4959036028412963264551915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26448192151535804077610213 4959036028412963264551915)
        ·
          refine ⟨7438554042619444896827873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4959036028412963264551915 7438554042619444896827873)
          ·
            refine ⟨5578915531964583672620905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7438554042619444896827873 5578915531964583672620905)
            ·
              refine ⟨4184186648973437754465679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5578915531964583672620905 4184186648973437754465679)
              ·
                refine ⟨6276279973460156631698519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4184186648973437754465679 6276279973460156631698519)
                ·
                  refine ⟨9414419960190234947547779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6276279973460156631698519 9414419960190234947547779)
                  ·
                    refine ⟨14121629940285352421321669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9414419960190234947547779 14121629940285352421321669)
                    ·
                      refine ⟨2647805613803503578997813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14121629940285352421321669 2647805613803503578997813)
                      ·
                        rfl

theorem cell23_5156583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_5156583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5156583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5156583 prefixEnd_5156583 := by exact prefixLift 5156583
  have htrace : WordTrace (prefixWord ++ tailWord_5156583) baseStart_5156583 baseEnd_5156583 := by
    simpa [prefixWord, tailWord_5156583, baseEnd_5156583] using wordTrace_append hprefix tailTrace_5156583
  have hstable : (prefixWord ++ tailWord_5156583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5156583).length < 2 ^ (prefixWord ++ tailWord_5156583).sum := by decide
  have hdescent : baseEnd_5156583 < baseStart_5156583 := by decide
  rcases family_descends (prefixWord ++ tailWord_5156583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5156592 : List Nat := [2, 1, 1, 1, 3, 1, 2, 2, 5, 3, 2]
def baseStart_5156592 : Nat := 118140960795 + 5156592 * 2 ^ 59
def prefixEnd_5156592 : Nat := 4983230072969 + 3 ^ 40 * 5156592 * 2
def baseEnd_5156592 : Nat := 2647810235129394043785271

theorem tailTrace_5156592 : CollatzResearch.WordTrace tailWord_5156592 prefixEnd_5156592 2647810235129394043785271 := by
  unfold tailWord_5156592
  simp only [CollatzResearch.WordTrace]
  refine ⟨94038180667277667322264015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125384240889703556429685353 94038180667277667322264015)
  ·
    refine ⟨141057271000916500983396023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94038180667277667322264015 141057271000916500983396023)
    ·
      refine ⟨211585906501374751475094035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141057271000916500983396023 211585906501374751475094035)
      ·
        refine ⟨317378859752062127212641053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211585906501374751475094035 317378859752062127212641053)
        ·
          refine ⟨119017072407023297704740395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 317378859752062127212641053 119017072407023297704740395)
          ·
            refine ⟨178525608610534946557110593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119017072407023297704740395 178525608610534946557110593)
            ·
              refine ⟨133894206457901209917832945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 178525608610534946557110593 133894206457901209917832945)
              ·
                refine ⟨100420654843425907438374709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 133894206457901209917832945 100420654843425907438374709)
                ·
                  refine ⟨9414436391571178822347629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 100420654843425907438374709 9414436391571178822347629)
                  ·
                    refine ⟨3530413646839192058380361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9414436391571178822347629 3530413646839192058380361)
                    ·
                      refine ⟨2647810235129394043785271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3530413646839192058380361 2647810235129394043785271)
                      ·
                        rfl

theorem cell23_5156592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 5, 3, 2].length) (baseStart_5156592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5156592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5156592 prefixEnd_5156592 := by exact prefixLift 5156592
  have htrace : WordTrace (prefixWord ++ tailWord_5156592) baseStart_5156592 baseEnd_5156592 := by
    simpa [prefixWord, tailWord_5156592, baseEnd_5156592] using wordTrace_append hprefix tailTrace_5156592
  have hstable : (prefixWord ++ tailWord_5156592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5156592).length < 2 ^ (prefixWord ++ tailWord_5156592).sum := by decide
  have hdescent : baseEnd_5156592 < baseStart_5156592 := by decide
  rcases family_descends (prefixWord ++ tailWord_5156592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5156599 : List Nat := [1, 1, 3, 1, 1, 1, 7, 2, 2, 1, 3]
def baseStart_5156599 : Nat := 118140960795 + 5156599 * 2 ^ 59
def prefixEnd_5156599 : Nat := 4983230072969 + 3 ^ 40 * 5156599 * 2
def baseEnd_5156599 : Nat := 2647813829493975516397739

theorem tailTrace_5156599 : CollatzResearch.WordTrace tailWord_5156599 prefixEnd_5156599 2647813829493975516397739 := by
  unfold tailWord_5156599
  simp only [CollatzResearch.WordTrace]
  refine ⟨188076616645529974840032851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125384411097019983226688567 188076616645529974840032851)
  ·
    refine ⟨282114924968294962260049277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188076616645529974840032851 282114924968294962260049277)
    ·
      refine ⟨105793096863110610847518479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 282114924968294962260049277 105793096863110610847518479)
      ·
        refine ⟨158689645294665916271277719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105793096863110610847518479 158689645294665916271277719)
        ·
          refine ⟨238034467941998874406916579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158689645294665916271277719 238034467941998874406916579)
          ·
            refine ⟨357051701912998311610374869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 238034467941998874406916579 357051701912998311610374869)
            ·
              refine ⟨8368399263585897928368161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 357051701912998311610374869 8368399263585897928368161)
              ·
                refine ⟨6276299447689423446276121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8368399263585897928368161 6276299447689423446276121)
                ·
                  refine ⟨4707224585767067584707091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6276299447689423446276121 4707224585767067584707091)
                  ·
                    refine ⟨7060836878650601377060637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4707224585767067584707091 7060836878650601377060637)
                    ·
                      refine ⟨2647813829493975516397739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7060836878650601377060637 2647813829493975516397739)
                      ·
                        rfl

theorem cell23_5156599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 7, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 7, 2, 2, 1, 3].length) (baseStart_5156599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5156599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5156599 prefixEnd_5156599 := by exact prefixLift 5156599
  have htrace : WordTrace (prefixWord ++ tailWord_5156599) baseStart_5156599 baseEnd_5156599 := by
    simpa [prefixWord, tailWord_5156599, baseEnd_5156599] using wordTrace_append hprefix tailTrace_5156599
  have hstable : (prefixWord ++ tailWord_5156599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5156599).length < 2 ^ (prefixWord ++ tailWord_5156599).sum := by decide
  have hdescent : baseEnd_5156599 < baseStart_5156599 := by decide
  rcases family_descends (prefixWord ++ tailWord_5156599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5156605 : List Nat := [1, 4, 1, 1, 1, 1, 2, 3, 2, 3, 4]
def baseStart_5156605 : Nat := 118140960795 + 5156605 * 2 ^ 59
def prefixEnd_5156605 : Nat := 4983230072969 + 3 ^ 40 * 5156605 * 2
def baseEnd_5156605 : Nat := 2647816910377902492922711

theorem tailTrace_5156605 : CollatzResearch.WordTrace tailWord_5156605 prefixEnd_5156605 2647816910377902492922711 := by
  unfold tailWord_5156605
  simp only [CollatzResearch.WordTrace]
  refine ⟨188076835483508237864751269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125384556989005491909834179 188076835483508237864751269)
  ·
    refine ⟨35264406653157794599640863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 188076835483508237864751269 35264406653157794599640863)
    ·
      refine ⟨52896609979736691899461295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35264406653157794599640863 52896609979736691899461295)
      ·
        refine ⟨79344914969605037849191943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52896609979736691899461295 79344914969605037849191943)
        ·
          refine ⟨119017372454407556773787915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79344914969605037849191943 119017372454407556773787915)
          ·
            refine ⟨178526058681611335160681873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119017372454407556773787915 178526058681611335160681873)
            ·
              refine ⟨133894544011208501370511405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 178526058681611335160681873 133894544011208501370511405)
              ·
                refine ⟨50210454004203188013941777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 133894544011208501370511405 50210454004203188013941777)
                ·
                  refine ⟨37657840503152391010456333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50210454004203188013941777 37657840503152391010456333)
                  ·
                    refine ⟨14121690188682146628921125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37657840503152391010456333 14121690188682146628921125)
                    ·
                      refine ⟨2647816910377902492922711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14121690188682146628921125 2647816910377902492922711)
                      ·
                        rfl

theorem cell23_5156605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 3, 2, 3, 4].length) (baseStart_5156605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5156605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5156605 prefixEnd_5156605 := by exact prefixLift 5156605
  have htrace : WordTrace (prefixWord ++ tailWord_5156605) baseStart_5156605 baseEnd_5156605 := by
    simpa [prefixWord, tailWord_5156605, baseEnd_5156605] using wordTrace_append hprefix tailTrace_5156605
  have hstable : (prefixWord ++ tailWord_5156605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5156605).length < 2 ^ (prefixWord ++ tailWord_5156605).sum := by decide
  have hdescent : baseEnd_5156605 < baseStart_5156605 := by decide
  rcases family_descends (prefixWord ++ tailWord_5156605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5156616 : List Nat := [2, 1, 3, 2, 2, 1, 5, 1, 2, 1, 3]
def baseStart_5156616 : Nat := 118140960795 + 5156616 * 2 ^ 59
def prefixEnd_5156616 : Nat := 4983230072969 + 3 ^ 40 * 5156616 * 2
def baseEnd_5156616 : Nat := 2647822558665101949885161

theorem tailTrace_5156616 : CollatzResearch.WordTrace tailWord_5156616 prefixEnd_5156616 2647822558665101949885161 := by
  unfold tailWord_5156616
  simp only [CollatzResearch.WordTrace]
  refine ⟨94038618343234193371700851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125384824457645591162267801 94038618343234193371700851)
  ·
    refine ⟨141057927514851290057551277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94038618343234193371700851 141057927514851290057551277)
    ·
      refine ⟨52896722818069233771581729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141057927514851290057551277 52896722818069233771581729)
      ·
        refine ⟨39672542113551925328686297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52896722818069233771581729 39672542113551925328686297)
        ·
          refine ⟨29754406585163943996514723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39672542113551925328686297 29754406585163943996514723)
          ·
            refine ⟨44631609877745915994772085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29754406585163943996514723 44631609877745915994772085)
            ·
              refine ⟨4184213426038679624509883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44631609877745915994772085 4184213426038679624509883)
              ·
                refine ⟨6276320139058019436764825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4184213426038679624509883 6276320139058019436764825)
                ·
                  refine ⟨4707240104293514577573619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6276320139058019436764825 4707240104293514577573619)
                  ·
                    refine ⟨7060860156440271866360429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4707240104293514577573619 7060860156440271866360429)
                    ·
                      refine ⟨2647822558665101949885161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7060860156440271866360429 2647822558665101949885161)
                      ·
                        rfl

theorem cell23_5156616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 5, 1, 2, 1, 3].length) (baseStart_5156616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5156616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5156616 prefixEnd_5156616 := by exact prefixLift 5156616
  have htrace : WordTrace (prefixWord ++ tailWord_5156616) baseStart_5156616 baseEnd_5156616 := by
    simpa [prefixWord, tailWord_5156616, baseEnd_5156616] using wordTrace_append hprefix tailTrace_5156616
  have hstable : (prefixWord ++ tailWord_5156616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5156616).length < 2 ^ (prefixWord ++ tailWord_5156616).sum := by decide
  have hdescent : baseEnd_5156616 < baseStart_5156616 := by decide
  rcases family_descends (prefixWord ++ tailWord_5156616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5156625 : List Nat := [1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 5]
def baseStart_5156625 : Nat := 118140960795 + 5156625 * 2 ^ 59
def prefixEnd_5156625 : Nat := 4983230072969 + 3 ^ 40 * 5156625 * 2
def baseEnd_5156625 : Nat := 2647827179990992414672619

theorem tailTrace_5156625 : CollatzResearch.WordTrace tailWord_5156625 prefixEnd_5156625 2647827179990992414672619 := by
  unfold tailWord_5156625
  simp only [CollatzResearch.WordTrace]
  refine ⟨188077564943435781280479329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125385043295623854186986219 188077564943435781280479329)
  ·
    refine ⟨141058173707576835960359497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188077564943435781280479329 141058173707576835960359497)
    ·
      refine ⟨105793630280682626970269623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141058173707576835960359497 105793630280682626970269623)
      ·
        refine ⟨158690445421023940455404435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105793630280682626970269623 158690445421023940455404435)
        ·
          refine ⟨238035668131535910683106653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158690445421023940455404435 238035668131535910683106653)
          ·
            refine ⟨89263375549325966506164995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 238035668131535910683106653 89263375549325966506164995)
            ·
              refine ⟨133895063323988949759247493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89263375549325966506164995 133895063323988949759247493)
              ·
                refine ⟨25105324373247928079858905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 133895063323988949759247493 25105324373247928079858905)
                ·
                  refine ⟨18828993279935946059894179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25105324373247928079858905 18828993279935946059894179)
                  ·
                    refine ⟨28243489919903919089841269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18828993279935946059894179 28243489919903919089841269)
                    ·
                      refine ⟨2647827179990992414672619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28243489919903919089841269 2647827179990992414672619)
                      ·
                        rfl

theorem cell23_5156625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 5].length) (baseStart_5156625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5156625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5156625 prefixEnd_5156625 := by exact prefixLift 5156625
  have htrace : WordTrace (prefixWord ++ tailWord_5156625) baseStart_5156625 baseEnd_5156625 := by
    simpa [prefixWord, tailWord_5156625, baseEnd_5156625] using wordTrace_append hprefix tailTrace_5156625
  have hstable : (prefixWord ++ tailWord_5156625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5156625).length < 2 ^ (prefixWord ++ tailWord_5156625).sum := by decide
  have hdescent : baseEnd_5156625 < baseStart_5156625 := by decide
  rcases family_descends (prefixWord ++ tailWord_5156625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5156639 : List Nat := [1, 1, 2, 4, 2, 1, 1, 1, 6, 2, 2]
def baseStart_5156639 : Nat := 118140960795 + 5156639 * 2 ^ 59
def prefixEnd_5156639 : Nat := 4983230072969 + 3 ^ 40 * 5156639 * 2
def baseEnd_5156639 : Nat := 2647834368720155359897555

theorem tailTrace_5156639 : CollatzResearch.WordTrace tailWord_5156639 prefixEnd_5156639 2647834368720155359897555 := by
  unfold tailWord_5156639
  simp only [CollatzResearch.WordTrace]
  refine ⟨188078075565385061671488971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125385383710256707780992647 188078075565385061671488971)
  ·
    refine ⟨282117113348077592507233457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188078075565385061671488971 282117113348077592507233457)
    ·
      refine ⟨211587835011058194380425093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 282117113348077592507233457 211587835011058194380425093)
      ·
        refine ⟨39672719064573411446329705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 211587835011058194380425093 39672719064573411446329705)
        ·
          refine ⟨29754539298430058584747279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39672719064573411446329705 29754539298430058584747279)
          ·
            refine ⟨44631808947645087877120919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29754539298430058584747279 44631808947645087877120919)
            ·
              refine ⟨66947713421467631815681379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44631808947645087877120919 66947713421467631815681379)
              ·
                refine ⟨100421570132201447723522069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66947713421467631815681379 100421570132201447723522069)
                ·
                  refine ⟨4707261099946942862040097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 100421570132201447723522069 4707261099946942862040097)
                  ·
                    refine ⟨3530445824960207146530073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4707261099946942862040097 3530445824960207146530073)
                    ·
                      refine ⟨2647834368720155359897555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3530445824960207146530073 2647834368720155359897555)
                      ·
                        rfl

theorem cell23_5156639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 6, 2, 2].length) (baseStart_5156639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5156639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5156639 prefixEnd_5156639 := by exact prefixLift 5156639
  have htrace : WordTrace (prefixWord ++ tailWord_5156639) baseStart_5156639 baseEnd_5156639 := by
    simpa [prefixWord, tailWord_5156639, baseEnd_5156639] using wordTrace_append hprefix tailTrace_5156639
  have hstable : (prefixWord ++ tailWord_5156639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5156639).length < 2 ^ (prefixWord ++ tailWord_5156639).sum := by decide
  have hdescent : baseEnd_5156639 < baseStart_5156639 := by decide
  rcases family_descends (prefixWord ++ tailWord_5156639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5156642 : List Nat := [3, 3, 1, 1, 2, 1, 3, 1, 2, 1, 5]
def baseStart_5156642 : Nat := 118140960795 + 5156642 * 2 ^ 59
def prefixEnd_5156642 : Nat := 4983230072969 + 3 ^ 40 * 5156642 * 2
def baseEnd_5156642 : Nat := 2647835909162118848160041

theorem tailTrace_5156642 : CollatzResearch.WordTrace tailWord_5156642 prefixEnd_5156642 2647835909162118848160041 := by
  unfold tailWord_5156642
  simp only [CollatzResearch.WordTrace]
  refine ⟨47019546246093548295962045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125385456656249462122565453 47019546246093548295962045)
  ·
    refine ⟨17632329842285080610985767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47019546246093548295962045 17632329842285080610985767)
    ·
      refine ⟨26448494763427620916478651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17632329842285080610985767 26448494763427620916478651)
      ·
        refine ⟨39672742145141431374717977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26448494763427620916478651 39672742145141431374717977)
        ·
          refine ⟨29754556608856073531038483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39672742145141431374717977 29754556608856073531038483)
          ·
            refine ⟨44631834913284110296557725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29754556608856073531038483 44631834913284110296557725)
            ·
              refine ⟨16736938092481541361209147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44631834913284110296557725 16736938092481541361209147)
              ·
                refine ⟨25105407138722312041813721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16736938092481541361209147 25105407138722312041813721)
                ·
                  refine ⟨18829055354041734031360291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25105407138722312041813721 18829055354041734031360291)
                  ·
                    refine ⟨28243583031062601047040437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18829055354041734031360291 28243583031062601047040437)
                    ·
                      refine ⟨2647835909162118848160041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28243583031062601047040437 2647835909162118848160041)
                      ·
                        rfl

theorem cell23_5156642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 1, 2, 1, 5].length) (baseStart_5156642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5156642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5156642 prefixEnd_5156642 := by exact prefixLift 5156642
  have htrace : WordTrace (prefixWord ++ tailWord_5156642) baseStart_5156642 baseEnd_5156642 := by
    simpa [prefixWord, tailWord_5156642, baseEnd_5156642] using wordTrace_append hprefix tailTrace_5156642
  have hstable : (prefixWord ++ tailWord_5156642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5156642).length < 2 ^ (prefixWord ++ tailWord_5156642).sum := by decide
  have hdescent : baseEnd_5156642 < baseStart_5156642 := by decide
  rcases family_descends (prefixWord ++ tailWord_5156642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5156715 : List Nat := [1, 1, 1, 1, 2, 2, 3, 1, 1, 5, 5]
def baseStart_5156715 : Nat := 118140960795 + 5156715 * 2 ^ 59
def prefixEnd_5156715 : Nat := 4983230072969 + 3 ^ 40 * 5156715 * 2
def baseEnd_5156715 : Nat := 2647873393249897062547205

theorem tailTrace_5156715 : CollatzResearch.WordTrace tailWord_5156715 prefixEnd_5156715 2647873393249897062547205 := by
  unfold tailWord_5156715
  simp only [CollatzResearch.WordTrace]
  refine ⟨188080847513109726651255599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125387231675406484434170399 188080847513109726651255599)
  ·
    refine ⟨282121271269664589976883399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188080847513109726651255599 282121271269664589976883399)
    ·
      refine ⟨423181906904496884965325099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 282121271269664589976883399 423181906904496884965325099)
      ·
        refine ⟨634772860356745327447987649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 423181906904496884965325099 634772860356745327447987649)
        ·
          refine ⟨476079645267558995585990737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 634772860356745327447987649 476079645267558995585990737)
          ·
            refine ⟨357059733950669246689493053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 476079645267558995585990737 357059733950669246689493053)
            ·
              refine ⟨133897400231500967508559895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 357059733950669246689493053 133897400231500967508559895)
              ·
                refine ⟨200846100347251451262839843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 133897400231500967508559895 200846100347251451262839843)
                ·
                  refine ⟨301269150520877176894259765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 200846100347251451262839843 301269150520877176894259765)
                  ·
                    refine ⟨28243982861332235333836853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 301269150520877176894259765 28243982861332235333836853)
                    ·
                      refine ⟨2647873393249897062547205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28243982861332235333836853 2647873393249897062547205)
                      ·
                        rfl

theorem cell23_5156715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 5, 5].length) (baseStart_5156715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5156715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5156715 prefixEnd_5156715 := by exact prefixLift 5156715
  have htrace : WordTrace (prefixWord ++ tailWord_5156715) baseStart_5156715 baseEnd_5156715 := by
    simpa [prefixWord, tailWord_5156715, baseEnd_5156715] using wordTrace_append hprefix tailTrace_5156715
  have hstable : (prefixWord ++ tailWord_5156715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5156715).length < 2 ^ (prefixWord ++ tailWord_5156715).sum := by decide
  have hdescent : baseEnd_5156715 < baseStart_5156715 := by decide
  rcases family_descends (prefixWord ++ tailWord_5156715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5156729 : List Nat := [1, 2, 1, 3, 2, 2, 3, 1, 2, 4, 2]
def baseStart_5156729 : Nat := 118140960795 + 5156729 * 2 ^ 59
def prefixEnd_5156729 : Nat := 4983230072969 + 3 ^ 40 * 5156729 * 2
def baseEnd_5156729 : Nat := 2647880581979060007772141

theorem tailTrace_5156729 : CollatzResearch.WordTrace tailWord_5156729 prefixEnd_5156729 2647880581979060007772141 := by
  unfold tailWord_5156729
  simp only [CollatzResearch.WordTrace]
  refine ⟨188081358135059007042265241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125387572090039338028176827 188081358135059007042265241)
  ·
    refine ⟨141061018601294255281698931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188081358135059007042265241 141061018601294255281698931)
    ·
      refine ⟨211591527901941382922548397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141061018601294255281698931 211591527901941382922548397)
      ·
        refine ⟨79346822963228018595955649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 211591527901941382922548397 79346822963228018595955649)
        ·
          refine ⟨59510117222421013946966737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79346822963228018595955649 59510117222421013946966737)
          ·
            refine ⟨44632587916815760460225053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59510117222421013946966737 44632587916815760460225053)
            ·
              refine ⟨16737220468805910172584395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44632587916815760460225053 16737220468805910172584395)
              ·
                refine ⟨25105830703208865258876593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16737220468805910172584395 25105830703208865258876593)
                ·
                  refine ⟨18829373027406648944157445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25105830703208865258876593 18829373027406648944157445)
                  ·
                    refine ⟨3530507442638746677029521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18829373027406648944157445 3530507442638746677029521)
                    ·
                      refine ⟨2647880581979060007772141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3530507442638746677029521 2647880581979060007772141)
                      ·
                        rfl

theorem cell23_5156729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 1, 2, 4, 2].length) (baseStart_5156729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5156729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5156729 prefixEnd_5156729 := by exact prefixLift 5156729
  have htrace : WordTrace (prefixWord ++ tailWord_5156729) baseStart_5156729 baseEnd_5156729 := by
    simpa [prefixWord, tailWord_5156729, baseEnd_5156729] using wordTrace_append hprefix tailTrace_5156729
  have hstable : (prefixWord ++ tailWord_5156729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5156729).length < 2 ^ (prefixWord ++ tailWord_5156729).sum := by decide
  have hdescent : baseEnd_5156729 < baseStart_5156729 := by decide
  rcases family_descends (prefixWord ++ tailWord_5156729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5156735 : List Nat := [1, 1, 2, 2, 1, 1, 3, 2, 10]
def baseStart_5156735 : Nat := 118140960795 + 5156735 * 2 ^ 59
def prefixEnd_5156735 : Nat := 4983230072969 + 3 ^ 40 * 5156735 * 2
def baseEnd_5156735 : Nat := 294209295873665220477457

theorem tailTrace_5156735 : CollatzResearch.WordTrace tailWord_5156735 prefixEnd_5156735 294209295873665220477457 := by
  unfold tailWord_5156735
  simp only [CollatzResearch.WordTrace]
  refine ⟨188081576973037270066983659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125387717982024846711322439 188081576973037270066983659)
  ·
    refine ⟨282122365459555905100475489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188081576973037270066983659 282122365459555905100475489)
    ·
      refine ⟨211591774094666928825356617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 282122365459555905100475489 211591774094666928825356617)
      ·
        refine ⟨158693830571000196619017463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 211591774094666928825356617 158693830571000196619017463)
        ·
          refine ⟨238040745856500294928526195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158693830571000196619017463 238040745856500294928526195)
          ·
            refine ⟨357061118784750442392789293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 238040745856500294928526195 357061118784750442392789293)
            ·
              refine ⟨133897919544281415897295985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 357061118784750442392789293 133897919544281415897295985)
              ·
                refine ⟨100423439658211061922971989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 133897919544281415897295985 100423439658211061922971989)
                ·
                  refine ⟨294209295873665220477457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 100423439658211061922971989 294209295873665220477457)
                  ·
                    rfl

theorem cell23_5156735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 10].length) (baseStart_5156735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5156735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5156735 prefixEnd_5156735 := by exact prefixLift 5156735
  have htrace : WordTrace (prefixWord ++ tailWord_5156735) baseStart_5156735 baseEnd_5156735 := by
    simpa [prefixWord, tailWord_5156735, baseEnd_5156735] using wordTrace_append hprefix tailTrace_5156735
  have hstable : (prefixWord ++ tailWord_5156735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5156735).length < 2 ^ (prefixWord ++ tailWord_5156735).sum := by decide
  have hdescent : baseEnd_5156735 < baseStart_5156735 := by decide
  rcases family_descends (prefixWord ++ tailWord_5156735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5156739 : List Nat := [1, 1, 1, 3, 4, 3, 1, 2, 3, 4]
def baseStart_5156739 : Nat := 118140960795 + 5156739 * 2 ^ 59
def prefixEnd_5156739 : Nat := 4983230072969 + 3 ^ 40 * 5156739 * 2
def baseEnd_5156739 : Nat := 882628572261868322882365

theorem tailTrace_5156739 : CollatzResearch.WordTrace tailWord_5156739 prefixEnd_5156739 882628572261868322882365 := by
  unfold tailWord_5156739
  simp only [CollatzResearch.WordTrace]
  refine ⟨188081722865022778750129271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125387815243348519166752847 188081722865022778750129271)
  ·
    refine ⟨282122584297534168125193907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188081722865022778750129271 282122584297534168125193907)
    ·
      refine ⟨423183876446301252187790861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 282122584297534168125193907 423183876446301252187790861)
      ·
        refine ⟨158693953667362969570421573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 423183876446301252187790861 158693953667362969570421573)
        ·
          refine ⟨29755116312630556794454045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 158693953667362969570421573 29755116312630556794454045)
          ·
            refine ⟨11158168617236458797920267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29755116312630556794454045 11158168617236458797920267)
            ·
              refine ⟨16737252925854688196880401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11158168617236458797920267 16737252925854688196880401)
              ·
                refine ⟨12552939694391016147660301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16737252925854688196880401 12552939694391016147660301)
                ·
                  refine ⟨4707352385396631055372613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12552939694391016147660301 4707352385396631055372613)
                  ·
                    refine ⟨882628572261868322882365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4707352385396631055372613 882628572261868322882365)
                    ·
                      rfl

theorem cell23_5156739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 2, 3, 4].length) (baseStart_5156739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5156739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5156739 prefixEnd_5156739 := by exact prefixLift 5156739
  have htrace : WordTrace (prefixWord ++ tailWord_5156739) baseStart_5156739 baseEnd_5156739 := by
    simpa [prefixWord, tailWord_5156739, baseEnd_5156739] using wordTrace_append hprefix tailTrace_5156739
  have hstable : (prefixWord ++ tailWord_5156739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5156739).length < 2 ^ (prefixWord ++ tailWord_5156739).sum := by decide
  have hdescent : baseEnd_5156739 < baseStart_5156739 := by decide
  rcases family_descends (prefixWord ++ tailWord_5156739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5156769 : List Nat := [1, 2, 3, 4, 2, 1, 1, 1, 8]
def baseStart_5156769 : Nat := 118140960795 + 5156769 * 2 ^ 59
def prefixEnd_5156769 : Nat := 4983230072969 + 3 ^ 40 * 5156769 * 2
def baseEnd_5156769 : Nat := 294211235689471094585773

theorem tailTrace_5156769 : CollatzResearch.WordTrace tailWord_5156769 prefixEnd_5156769 294211235689471094585773 := by
  unfold tailWord_5156769
  simp only [CollatzResearch.WordTrace]
  refine ⟨188082817054914093873721361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125388544703276062582480907 188082817054914093873721361)
  ·
    refine ⟨141062112791185570405291021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188082817054914093873721361 141062112791185570405291021)
    ·
      refine ⟨52898292296694588901984133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141062112791185570405291021 52898292296694588901984133)
      ·
        refine ⟨9918429805630235419122025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52898292296694588901984133 9918429805630235419122025)
        ·
          refine ⟨7438822354222676564341519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9918429805630235419122025 7438822354222676564341519)
          ·
            refine ⟨11158233531334014846512279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7438822354222676564341519 11158233531334014846512279)
            ·
              refine ⟨16737350297001022269768419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11158233531334014846512279 16737350297001022269768419)
              ·
                refine ⟨25106025445501533404652629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16737350297001022269768419 25106025445501533404652629)
                ·
                  refine ⟨294211235689471094585773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25106025445501533404652629 294211235689471094585773)
                  ·
                    rfl

theorem cell23_5156769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 1, 8].length) (baseStart_5156769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5156769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5156769 prefixEnd_5156769 := by exact prefixLift 5156769
  have htrace : WordTrace (prefixWord ++ tailWord_5156769) baseStart_5156769 baseEnd_5156769 := by
    simpa [prefixWord, tailWord_5156769, baseEnd_5156769] using wordTrace_append hprefix tailTrace_5156769
  have hstable : (prefixWord ++ tailWord_5156769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5156769).length < 2 ^ (prefixWord ++ tailWord_5156769).sum := by decide
  have hdescent : baseEnd_5156769 < baseStart_5156769 := by decide
  rcases family_descends (prefixWord ++ tailWord_5156769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5156772 : List Nat := [2, 3, 1, 2, 1, 3, 1, 1, 1, 2, 6]
def baseStart_5156772 : Nat := 118140960795 + 5156772 * 2 ^ 59
def prefixEnd_5156772 : Nat := 4983230072969 + 3 ^ 40 * 5156772 * 2
def baseEnd_5156772 : Nat := 2647902661647203339534443

theorem tailTrace_5156772 : CollatzResearch.WordTrace tailWord_5156772 prefixEnd_5156772 2647902661647203339534443 := by
  unfold tailWord_5156772
  simp only [CollatzResearch.WordTrace]
  refine ⟨94041463236951612693040285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125388617649268816924053713 94041463236951612693040285)
  ·
    refine ⟨35265548713856854759890107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94041463236951612693040285 35265548713856854759890107)
    ·
      refine ⟨52898323070785282139835161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35265548713856854759890107 52898323070785282139835161)
      ·
        refine ⟨39673742303088961604876371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52898323070785282139835161 39673742303088961604876371)
        ·
          refine ⟨59510613454633442407314557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39673742303088961604876371 59510613454633442407314557)
          ·
            refine ⟨22316480045487540902742959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59510613454633442407314557 22316480045487540902742959)
            ·
              refine ⟨33474720068231311354114439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22316480045487540902742959 33474720068231311354114439)
              ·
                refine ⟨50212080102346967031171659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33474720068231311354114439 50212080102346967031171659)
                ·
                  refine ⟨75318120153520450546757489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50212080102346967031171659 75318120153520450546757489)
                  ·
                    refine ⟨56488590115140337910068117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 75318120153520450546757489 56488590115140337910068117)
                    ·
                      refine ⟨2647902661647203339534443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56488590115140337910068117 2647902661647203339534443)
                      ·
                        rfl

theorem cell23_5156772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 1, 1, 2, 6].length) (baseStart_5156772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5156772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5156772 prefixEnd_5156772 := by exact prefixLift 5156772
  have htrace : WordTrace (prefixWord ++ tailWord_5156772) baseStart_5156772 baseEnd_5156772 := by
    simpa [prefixWord, tailWord_5156772, baseEnd_5156772] using wordTrace_append hprefix tailTrace_5156772
  have hstable : (prefixWord ++ tailWord_5156772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5156772).length < 2 ^ (prefixWord ++ tailWord_5156772).sum := by decide
  have hdescent : baseEnd_5156772 < baseStart_5156772 := by decide
  rcases family_descends (prefixWord ++ tailWord_5156772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5156799 : List Nat := [1, 1, 2, 2, 2, 1, 6, 2, 1, 5]
def baseStart_5156799 : Nat := 118140960795 + 5156799 * 2 ^ 59
def prefixEnd_5156799 : Nat := 4983230072969 + 3 ^ 40 * 5156799 * 2
def baseEnd_5156799 : Nat := 882638841874958244632273

theorem tailTrace_5156799 : CollatzResearch.WordTrace tailWord_5156799 prefixEnd_5156799 882638841874958244632273 := by
  unfold tailWord_5156799
  simp only [CollatzResearch.WordTrace]
  refine ⟨188083911244805408997313451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125389274163203605998208967 188083911244805408997313451)
  ·
    refine ⟨282125866867208113495970177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188083911244805408997313451 282125866867208113495970177)
    ·
      refine ⟨211594400150406085121977633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 282125866867208113495970177 211594400150406085121977633)
      ·
        refine ⟨158695800112804563841483225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 211594400150406085121977633 158695800112804563841483225)
        ·
          refine ⟨119021850084603422881112419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 158695800112804563841483225 119021850084603422881112419)
          ·
            refine ⟨178532775126905134321668629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119021850084603422881112419 178532775126905134321668629)
            ·
              refine ⟨8368723834073678171328217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 178532775126905134321668629 8368723834073678171328217)
              ·
                refine ⟨6276542875555258628496163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8368723834073678171328217 6276542875555258628496163)
                ·
                  refine ⟨9414814313332887942744245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6276542875555258628496163 9414814313332887942744245)
                  ·
                    refine ⟨882638841874958244632273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9414814313332887942744245 882638841874958244632273)
                    ·
                      rfl

theorem cell23_5156799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 6, 2, 1, 5].length) (baseStart_5156799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5156799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5156799 prefixEnd_5156799 := by exact prefixLift 5156799
  have htrace : WordTrace (prefixWord ++ tailWord_5156799) baseStart_5156799 baseEnd_5156799 := by
    simpa [prefixWord, tailWord_5156799, baseEnd_5156799] using wordTrace_append hprefix tailTrace_5156799
  have hstable : (prefixWord ++ tailWord_5156799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5156799).length < 2 ^ (prefixWord ++ tailWord_5156799).sum := by decide
  have hdescent : baseEnd_5156799 < baseStart_5156799 := by decide
  rcases family_descends (prefixWord ++ tailWord_5156799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5156856 : List Nat := [2, 1, 2, 1, 1, 3, 5, 2, 1, 2, 3]
def baseStart_5156856 : Nat := 118140960795 + 5156856 * 2 ^ 59
def prefixEnd_5156856 : Nat := 4983230072969 + 3 ^ 40 * 5156856 * 2
def baseEnd_5156856 : Nat := 2647945794022181010884057

theorem tailTrace_5156856 : CollatzResearch.WordTrace tailWord_5156856 prefixEnd_5156856 2647945794022181010884057 := by
  unfold tailWord_5156856
  simp only [CollatzResearch.WordTrace]
  refine ⟨94042995102799453866069211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125390660137065938488092281 94042995102799453866069211)
  ·
    refine ⟨141064492654199180799103817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94042995102799453866069211 141064492654199180799103817)
    ·
      refine ⟨105798369490649385599327863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141064492654199180799103817 105798369490649385599327863)
      ·
        refine ⟨158697554235974078398991795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105798369490649385599327863 158697554235974078398991795)
        ·
          refine ⟨238046331353961117598487693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158697554235974078398991795 238046331353961117598487693)
          ·
            refine ⟨89267374257735419099432885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 238046331353961117598487693 89267374257735419099432885)
            ·
              refine ⟨8368816336662695540571833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 89267374257735419099432885 8368816336662695540571833)
              ·
                refine ⟨6276612252497021655428875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8368816336662695540571833 6276612252497021655428875)
                ·
                  refine ⟨9414918378745532483143313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6276612252497021655428875 9414918378745532483143313)
                  ·
                    refine ⟨7061188784059149362357485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9414918378745532483143313 7061188784059149362357485)
                    ·
                      refine ⟨2647945794022181010884057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7061188784059149362357485 2647945794022181010884057)
                      ·
                        rfl

theorem cell23_5156856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 5, 2, 1, 2, 3].length) (baseStart_5156856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5156856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5156856 prefixEnd_5156856 := by exact prefixLift 5156856
  have htrace : WordTrace (prefixWord ++ tailWord_5156856) baseStart_5156856 baseEnd_5156856 := by
    simpa [prefixWord, tailWord_5156856, baseEnd_5156856] using wordTrace_append hprefix tailTrace_5156856
  have hstable : (prefixWord ++ tailWord_5156856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5156856).length < 2 ^ (prefixWord ++ tailWord_5156856).sum := by decide
  have hdescent : baseEnd_5156856 < baseStart_5156856 := by decide
  rcases family_descends (prefixWord ++ tailWord_5156856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5156869 : List Nat := [1, 3, 1, 1, 2, 4, 1, 1, 3, 3, 3]
def baseStart_5156869 : Nat := 118140960795 + 5156869 * 2 ^ 59
def prefixEnd_5156869 : Nat := 4983230072969 + 3 ^ 40 * 5156869 * 2
def baseEnd_5156869 : Nat := 2647952469270689460021497

theorem tailTrace_5156869 : CollatzResearch.WordTrace tailWord_5156869 prefixEnd_5156869 2647952469270689460021497 := by
  unfold tailWord_5156869
  simp only [CollatzResearch.WordTrace]
  refine ⟨188086464354551810952361661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125390976236367873968241107 188086464354551810952361661)
  ·
    refine ⟨70532424132956929107135623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 188086464354551810952361661 70532424132956929107135623)
    ·
      refine ⟨105798636199435393660703435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70532424132956929107135623 105798636199435393660703435)
      ·
        refine ⟨158697954299153090491055153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105798636199435393660703435 158697954299153090491055153)
        ·
          refine ⟨119023465724364817868291365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 158697954299153090491055153 119023465724364817868291365)
          ·
            refine ⟨22316899823318403350304631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 119023465724364817868291365 22316899823318403350304631)
            ·
              refine ⟨33475349734977605025456947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22316899823318403350304631 33475349734977605025456947)
              ·
                refine ⟨50213024602466407538185421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33475349734977605025456947 50213024602466407538185421)
                ·
                  refine ⟨18829884225924902826819533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50213024602466407538185421 18829884225924902826819533)
                  ·
                    refine ⟨7061206584721838560057325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18829884225924902826819533 7061206584721838560057325)
                    ·
                      refine ⟨2647952469270689460021497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7061206584721838560057325 2647952469270689460021497)
                      ·
                        rfl

theorem cell23_5156869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 1, 3, 3, 3].length) (baseStart_5156869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5156869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5156869 prefixEnd_5156869 := by exact prefixLift 5156869
  have htrace : WordTrace (prefixWord ++ tailWord_5156869) baseStart_5156869 baseEnd_5156869 := by
    simpa [prefixWord, tailWord_5156869, baseEnd_5156869] using wordTrace_append hprefix tailTrace_5156869
  have hstable : (prefixWord ++ tailWord_5156869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5156869).length < 2 ^ (prefixWord ++ tailWord_5156869).sum := by decide
  have hdescent : baseEnd_5156869 < baseStart_5156869 := by decide
  rcases family_descends (prefixWord ++ tailWord_5156869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5156887 : List Nat := [1, 1, 3, 5, 2, 1, 1, 4, 1, 2, 2]
def baseStart_5156887 : Nat := 118140960795 + 5156887 * 2 ^ 59
def prefixEnd_5156887 : Nat := 4983230072969 + 3 ^ 40 * 5156887 * 2
def baseEnd_5156887 : Nat := 2647961711922470389596415

theorem tailTrace_5156887 : CollatzResearch.WordTrace tailWord_5156887 prefixEnd_5156887 2647961711922470389596415 := by
  unfold tailWord_5156887
  simp only [CollatzResearch.WordTrace]
  refine ⟨188087120868486600026516915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125391413912324400017677943 188087120868486600026516915)
  ·
    refine ⟨282130681302729900039775373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188087120868486600026516915 282130681302729900039775373)
    ·
      refine ⟨105799005488523712514915765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 282130681302729900039775373 105799005488523712514915765)
      ·
        refine ⟨9918656764549098048273353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 105799005488523712514915765 9918656764549098048273353)
        ·
          refine ⟨7438992573411823536205015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9918656764549098048273353 7438992573411823536205015)
          ·
            refine ⟨11158488860117735304307523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7438992573411823536205015 11158488860117735304307523)
            ·
              refine ⟨16737733290176602956461285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11158488860117735304307523 16737733290176602956461285)
              ·
                refine ⟨3138324991908113054336491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16737733290176602956461285 3138324991908113054336491)
                ·
                  refine ⟨4707487487862169581504737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3138324991908113054336491 4707487487862169581504737)
                  ·
                    refine ⟨3530615615896627186128553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4707487487862169581504737 3530615615896627186128553)
                    ·
                      refine ⟨2647961711922470389596415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3530615615896627186128553 2647961711922470389596415)
                      ·
                        rfl

theorem cell23_5156887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 4, 1, 2, 2].length) (baseStart_5156887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5156887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5156887 prefixEnd_5156887 := by exact prefixLift 5156887
  have htrace : WordTrace (prefixWord ++ tailWord_5156887) baseStart_5156887 baseEnd_5156887 := by
    simpa [prefixWord, tailWord_5156887, baseEnd_5156887] using wordTrace_append hprefix tailTrace_5156887
  have hstable : (prefixWord ++ tailWord_5156887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5156887).length < 2 ^ (prefixWord ++ tailWord_5156887).sum := by decide
  have hdescent : baseEnd_5156887 < baseStart_5156887 := by decide
  rcases family_descends (prefixWord ++ tailWord_5156887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5156949 : List Nat := [1, 3, 2, 2, 1, 3, 1, 3, 7]
def baseStart_5156949 : Nat := 118140960795 + 5156949 * 2 ^ 59
def prefixEnd_5156949 : Nat := 4983230072969 + 3 ^ 40 * 5156949 * 2
def baseEnd_5156949 : Nat := 294221505302561016335681

theorem tailTrace_5156949 : CollatzResearch.WordTrace tailWord_5156949 prefixEnd_5156949 294221505302561016335681 := by
  unfold tailWord_5156949
  simp only [CollatzResearch.WordTrace]
  refine ⟨188089382194261984615273901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125392921462841323076849267 188089382194261984615273901)
  ·
    refine ⟨70533518322848244230727713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 188089382194261984615273901 70533518322848244230727713)
    ·
      refine ⟨52900138742136183173045785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70533518322848244230727713 52900138742136183173045785)
      ·
        refine ⟨39675104056602137379784339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52900138742136183173045785 39675104056602137379784339)
        ·
          refine ⟨59512656084903206069676509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39675104056602137379784339 59512656084903206069676509)
          ·
            refine ⟨22317246031838702276128691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59512656084903206069676509 22317246031838702276128691)
            ·
              refine ⟨33475869047758053414193037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22317246031838702276128691 33475869047758053414193037)
              ·
                refine ⟨12553450892909270030322389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33475869047758053414193037 12553450892909270030322389)
                ·
                  refine ⟨294221505302561016335681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12553450892909270030322389 294221505302561016335681)
                  ·
                    rfl

theorem cell23_5156949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 3, 7].length) (baseStart_5156949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5156949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5156949 prefixEnd_5156949 := by exact prefixLift 5156949
  have htrace : WordTrace (prefixWord ++ tailWord_5156949) baseStart_5156949 baseEnd_5156949 := by
    simpa [prefixWord, tailWord_5156949, baseEnd_5156949] using wordTrace_append hprefix tailTrace_5156949
  have hstable : (prefixWord ++ tailWord_5156949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5156949).length < 2 ^ (prefixWord ++ tailWord_5156949).sum := by decide
  have hdescent : baseEnd_5156949 < baseStart_5156949 := by decide
  rcases family_descends (prefixWord ++ tailWord_5156949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5156956 : List Nat := [2, 2, 4, 1, 1, 2, 2, 1, 2, 2, 4]
def baseStart_5156956 : Nat := 118140960795 + 5156956 * 2 ^ 59
def prefixEnd_5156956 : Nat := 4983230072969 + 3 ^ 40 * 5156956 * 2
def baseEnd_5156956 : Nat := 2647997142087630619633597

theorem tailTrace_5156956 : CollatzResearch.WordTrace tailWord_5156956 prefixEnd_5156956 2647997142087630619633597 := by
  unfold tailWord_5156956
  simp only [CollatzResearch.WordTrace]
  refine ⟨94044818752618312405389361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125393091670157749873852481 94044818752618312405389361)
  ·
    refine ⟨70533614064463734304042021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94044818752618312405389361 70533614064463734304042021)
    ·
      refine ⟨13225052637086950182007879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70533614064463734304042021 13225052637086950182007879)
      ·
        refine ⟨19837578955630425273011819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13225052637086950182007879 19837578955630425273011819)
        ·
          refine ⟨29756368433445637909517729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19837578955630425273011819 29756368433445637909517729)
          ·
            refine ⟨22317276325084228432138297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29756368433445637909517729 22317276325084228432138297)
            ·
              refine ⟨16737957243813171324103723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22317276325084228432138297 16737957243813171324103723)
              ·
                refine ⟨25106935865719756986155585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16737957243813171324103723 25106935865719756986155585)
                ·
                  refine ⟨18830201899289817739616689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25106935865719756986155585 18830201899289817739616689)
                  ·
                    refine ⟨14122651424467363304712517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18830201899289817739616689 14122651424467363304712517)
                    ·
                      refine ⟨2647997142087630619633597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14122651424467363304712517 2647997142087630619633597)
                      ·
                        rfl

theorem cell23_5156956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_5156956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5156956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5156956 prefixEnd_5156956 := by exact prefixLift 5156956
  have htrace : WordTrace (prefixWord ++ tailWord_5156956) baseStart_5156956 baseEnd_5156956 := by
    simpa [prefixWord, tailWord_5156956, baseEnd_5156956] using wordTrace_append hprefix tailTrace_5156956
  have hstable : (prefixWord ++ tailWord_5156956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5156956).length < 2 ^ (prefixWord ++ tailWord_5156956).sum := by decide
  have hdescent : baseEnd_5156956 < baseStart_5156956 := by decide
  rcases family_descends (prefixWord ++ tailWord_5156956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5156959 : List Nat := [1, 1, 2, 3, 1, 1, 2, 3, 1, 5, 3]
def baseStart_5156959 : Nat := 118140960795 + 5156959 * 2 ^ 59
def prefixEnd_5156959 : Nat := 4983230072969 + 3 ^ 40 * 5156959 * 2
def baseEnd_5156959 : Nat := 2647998682529594107896083

theorem tailTrace_5156959 : CollatzResearch.WordTrace tailWord_5156959 prefixEnd_5156959 2647998682529594107896083 := by
  unfold tailWord_5156959
  simp only [CollatzResearch.WordTrace]
  refine ⟨188089746924225756323137931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125393164616150504215425287 188089746924225756323137931)
  ·
    refine ⟨282134620386338634484706897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188089746924225756323137931 282134620386338634484706897)
    ·
      refine ⟨211600965289753975863530173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 282134620386338634484706897 211600965289753975863530173)
      ·
        refine ⟨79350361983657740948823815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 211600965289753975863530173 79350361983657740948823815)
        ·
          refine ⟨119025542975486611423235723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79350361983657740948823815 119025542975486611423235723)
          ·
            refine ⟨178538314463229917134853585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119025542975486611423235723 178538314463229917134853585)
            ·
              refine ⟨133903735847422437851140189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 178538314463229917134853585 133903735847422437851140189)
              ·
                refine ⟨50213900942783414194177571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 133903735847422437851140189 50213900942783414194177571)
                ·
                  refine ⟨75320851414175121291266357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50213900942783414194177571 75320851414175121291266357)
                  ·
                    refine ⟨7061329820078917621056221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 75320851414175121291266357 7061329820078917621056221)
                    ·
                      refine ⟨2647998682529594107896083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7061329820078917621056221 2647998682529594107896083)
                      ·
                        rfl

theorem cell23_5156959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 3, 1, 5, 3].length) (baseStart_5156959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5156959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5156959 prefixEnd_5156959 := by exact prefixLift 5156959
  have htrace : WordTrace (prefixWord ++ tailWord_5156959) baseStart_5156959 baseEnd_5156959 := by
    simpa [prefixWord, tailWord_5156959, baseEnd_5156959] using wordTrace_append hprefix tailTrace_5156959
  have hstable : (prefixWord ++ tailWord_5156959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5156959).length < 2 ^ (prefixWord ++ tailWord_5156959).sum := by decide
  have hdescent : baseEnd_5156959 < baseStart_5156959 := by decide
  rcases family_descends (prefixWord ++ tailWord_5156959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5156983 : List Nat := [1, 1, 3, 1, 1, 7, 1, 3, 5]
def baseStart_5156983 : Nat := 118140960795 + 5156983 * 2 ^ 59
def prefixEnd_5156983 : Nat := 4983230072969 + 3 ^ 40 * 5156983 * 2
def baseEnd_5156983 : Nat := 294223445118366890443997

theorem tailTrace_5156983 : CollatzResearch.WordTrace tailWord_5156983 prefixEnd_5156983 294223445118366890443997 := by
  unfold tailWord_5156983
  simp only [CollatzResearch.WordTrace]
  refine ⟨188090622276138808422011603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125393748184092538948007735 188090622276138808422011603)
  ·
    refine ⟨282135933414208212633017405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188090622276138808422011603 282135933414208212633017405)
    ·
      refine ⟨105800975030328079737381527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 282135933414208212633017405 105800975030328079737381527)
      ·
        refine ⟨158701462545492119606072291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105800975030328079737381527 158701462545492119606072291)
        ·
          refine ⟨238052193818238179409108437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158701462545492119606072291 238052193818238179409108437)
          ·
            refine ⟨5579348292614957329900979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 238052193818238179409108437 5579348292614957329900979)
            ·
              refine ⟨8369022438922435994851469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5579348292614957329900979 8369022438922435994851469)
              ·
                refine ⟨3138383414595913498069301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8369022438922435994851469 3138383414595913498069301)
                ·
                  refine ⟨294223445118366890443997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3138383414595913498069301 294223445118366890443997)
                  ·
                    rfl

theorem cell23_5156983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 1, 3, 5].length) (baseStart_5156983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5156983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5156983 prefixEnd_5156983 := by exact prefixLift 5156983
  have htrace : WordTrace (prefixWord ++ tailWord_5156983) baseStart_5156983 baseEnd_5156983 := by
    simpa [prefixWord, tailWord_5156983, baseEnd_5156983] using wordTrace_append hprefix tailTrace_5156983
  have hstable : (prefixWord ++ tailWord_5156983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5156983).length < 2 ^ (prefixWord ++ tailWord_5156983).sum := by decide
  have hdescent : baseEnd_5156983 < baseStart_5156983 := by decide
  rcases family_descends (prefixWord ++ tailWord_5156983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5156996 : List Nat := [2, 3, 2, 1, 2, 1, 3, 2, 2, 5]
def baseStart_5156996 : Nat := 118140960795 + 5156996 * 2 ^ 59
def prefixEnd_5156996 : Nat := 4983230072969 + 3 ^ 40 * 5156996 * 2
def baseEnd_5156996 : Nat := 882672560437936821044471

theorem tailTrace_5156996 : CollatzResearch.WordTrace tailWord_5156996 prefixEnd_5156996 882672560437936821044471 := by
  unfold tailWord_5156996
  simp only [CollatzResearch.WordTrace]
  refine ⟨94045548212545855821117421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125394064283394474428156561 94045548212545855821117421)
  ·
    refine ⟨35267080579704695932919033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94045548212545855821117421 35267080579704695932919033)
    ·
      refine ⟨26450310434778521949689275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35267080579704695932919033 26450310434778521949689275)
      ·
        refine ⟨39675465652167782924533913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26450310434778521949689275 39675465652167782924533913)
        ·
          refine ⟨29756599239125837193400435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39675465652167782924533913 29756599239125837193400435)
          ·
            refine ⟨44634898858688755790100653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29756599239125837193400435 44634898858688755790100653)
            ·
              refine ⟨16738087072008283421287745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44634898858688755790100653 16738087072008283421287745)
              ·
                refine ⟨12553565304006212565965809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16738087072008283421287745 12553565304006212565965809)
                ·
                  refine ⟨9415173978004659424474357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12553565304006212565965809 9415173978004659424474357)
                  ·
                    refine ⟨882672560437936821044471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9415173978004659424474357 882672560437936821044471)
                    ·
                      rfl

theorem cell23_5156996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 2, 2, 5].length) (baseStart_5156996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5156996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5156996 prefixEnd_5156996 := by exact prefixLift 5156996
  have htrace : WordTrace (prefixWord ++ tailWord_5156996) baseStart_5156996 baseEnd_5156996 := by
    simpa [prefixWord, tailWord_5156996, baseEnd_5156996] using wordTrace_append hprefix tailTrace_5156996
  have hstable : (prefixWord ++ tailWord_5156996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5156996).length < 2 ^ (prefixWord ++ tailWord_5156996).sum := by decide
  have hdescent : baseEnd_5156996 < baseStart_5156996 := by decide
  rcases family_descends (prefixWord ++ tailWord_5156996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5157000 : List Nat := [2, 1, 3, 4, 1, 2, 3, 2, 5]
def baseStart_5157000 : Nat := 118140960795 + 5157000 * 2 ^ 59
def prefixEnd_5157000 : Nat := 4983230072969 + 3 ^ 40 * 5157000 * 2
def baseEnd_5157000 : Nat := 294224415026269827498155

theorem tailTrace_5157000 : CollatzResearch.WordTrace tailWord_5157000 prefixEnd_5157000 294224415026269827498155 := by
  unfold tailWord_5157000
  simp only [CollatzResearch.WordTrace]
  refine ⟨94045621158538610162690227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125394161544718146883586969 94045621158538610162690227)
  ·
    refine ⟨141068431737807915244035341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94045621158538610162690227 141068431737807915244035341)
    ·
      refine ⟨52900661901677968216513253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141068431737807915244035341 52900661901677968216513253)
      ·
        refine ⟨9918874106564619040596235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52900661901677968216513253 9918874106564619040596235)
        ·
          refine ⟨14878311159846928560894353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9918874106564619040596235 14878311159846928560894353)
          ·
            refine ⟨11158733369885196420670765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14878311159846928560894353 11158733369885196420670765)
            ·
              refine ⟨4184525013706948657751537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11158733369885196420670765 4184525013706948657751537)
              ·
                refine ⟨3138393760280211493313653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4184525013706948657751537 3138393760280211493313653)
                ·
                  refine ⟨294224415026269827498155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3138393760280211493313653 294224415026269827498155)
                  ·
                    rfl

theorem cell23_5157000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 3, 2, 5].length) (baseStart_5157000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5157000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5157000 prefixEnd_5157000 := by exact prefixLift 5157000
  have htrace : WordTrace (prefixWord ++ tailWord_5157000) baseStart_5157000 baseEnd_5157000 := by
    simpa [prefixWord, tailWord_5157000, baseEnd_5157000] using wordTrace_append hprefix tailTrace_5157000
  have hstable : (prefixWord ++ tailWord_5157000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5157000).length < 2 ^ (prefixWord ++ tailWord_5157000).sum := by decide
  have hdescent : baseEnd_5157000 < baseStart_5157000 := by decide
  rcases family_descends (prefixWord ++ tailWord_5157000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5157043 : List Nat := [1, 1, 1, 2, 3, 2, 1, 7, 1, 4]
def baseStart_5157043 : Nat := 118140960795 + 5157043 * 2 ^ 59
def prefixEnd_5157043 : Nat := 4983230072969 + 3 ^ 40 * 5157043 * 2
def baseEnd_5157043 : Nat := 882680604968190593081899

theorem tailTrace_5157043 : CollatzResearch.WordTrace tailWord_5157043 prefixEnd_5157043 882680604968190593081899 := by
  unfold tailWord_5157043
  simp only [CollatzResearch.WordTrace]
  refine ⟨188092810655921438669195783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125395207103947625779463855 188092810655921438669195783)
  ·
    refine ⟨282139215983882158003793675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188092810655921438669195783 282139215983882158003793675)
    ·
      refine ⟨423208823975823237005690513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 282139215983882158003793675 423208823975823237005690513)
      ·
        refine ⟨317406617981867427754267885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 423208823975823237005690513 317406617981867427754267885)
        ·
          refine ⟨119027481743200285407850457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 317406617981867427754267885 119027481743200285407850457)
          ·
            refine ⟨89270611307400214055887843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119027481743200285407850457 89270611307400214055887843)
            ·
              refine ⟨133905916961100321083831765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89270611307400214055887843 133905916961100321083831765)
              ·
                refine ⟨3138419928775788775402307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 133905916961100321083831765 3138419928775788775402307)
                ·
                  refine ⟨4707629893163683163103461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3138419928775788775402307 4707629893163683163103461)
                  ·
                    refine ⟨882680604968190593081899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4707629893163683163103461 882680604968190593081899)
                    ·
                      rfl

theorem cell23_5157043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 7, 1, 4].length) (baseStart_5157043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5157043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5157043 prefixEnd_5157043 := by exact prefixLift 5157043
  have htrace : WordTrace (prefixWord ++ tailWord_5157043) baseStart_5157043 baseEnd_5157043 := by
    simpa [prefixWord, tailWord_5157043, baseEnd_5157043] using wordTrace_append hprefix tailTrace_5157043
  have hstable : (prefixWord ++ tailWord_5157043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5157043).length < 2 ^ (prefixWord ++ tailWord_5157043).sum := by decide
  have hdescent : baseEnd_5157043 < baseStart_5157043 := by decide
  rcases family_descends (prefixWord ++ tailWord_5157043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5157056 : List Nat := [2, 1, 1, 2, 5, 1, 1, 4, 6]
def baseStart_5157056 : Nat := 118140960795 + 5157056 * 2 ^ 59
def prefixEnd_5157056 : Nat := 4983230072969 + 3 ^ 40 * 5157056 * 2
def baseEnd_5157056 : Nat := 294227610017008914264793

theorem tailTrace_5157056 : CollatzResearch.WordTrace tailWord_5157056 prefixEnd_5157056 294227610017008914264793 := by
  unfold tailWord_5157056
  simp only [CollatzResearch.WordTrace]
  refine ⟨94046642402437170944709511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125395523203249561259612681 94046642402437170944709511)
  ·
    refine ⟨141069963603655756417064267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94046642402437170944709511 141069963603655756417064267)
    ·
      refine ⟨211604945405483634625596401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141069963603655756417064267 211604945405483634625596401)
      ·
        refine ⟨158703709054112725969197301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 211604945405483634625596401 158703709054112725969197301)
        ·
          refine ⟨14878472723823068059612247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 158703709054112725969197301 14878472723823068059612247)
          ·
            refine ⟨22317709085734602089418371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14878472723823068059612247 22317709085734602089418371)
            ·
              refine ⟨33476563628601903134127557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22317709085734602089418371 33476563628601903134127557)
              ·
                refine ⟨6276855680362856837648917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33476563628601903134127557 6276855680362856837648917)
                ·
                  refine ⟨294227610017008914264793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6276855680362856837648917 294227610017008914264793)
                  ·
                    rfl

theorem cell23_5157056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 4, 6].length) (baseStart_5157056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5157056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5157056 prefixEnd_5157056 := by exact prefixLift 5157056
  have htrace : WordTrace (prefixWord ++ tailWord_5157056) baseStart_5157056 baseEnd_5157056 := by
    simpa [prefixWord, tailWord_5157056, baseEnd_5157056] using wordTrace_append hprefix tailTrace_5157056
  have hstable : (prefixWord ++ tailWord_5157056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5157056).length < 2 ^ (prefixWord ++ tailWord_5157056).sum := by decide
  have hdescent : baseEnd_5157056 < baseStart_5157056 := by decide
  rcases family_descends (prefixWord ++ tailWord_5157056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5157079 : List Nat := [1, 1, 3, 2, 1, 2, 1, 1, 1, 3, 7]
def baseStart_5157079 : Nat := 118140960795 + 5157079 * 2 ^ 59
def prefixEnd_5157079 : Nat := 4983230072969 + 3 ^ 40 * 5157079 * 2
def baseEnd_5157079 : Nat := 2648060300208133638395531

theorem tailTrace_5157079 : CollatzResearch.WordTrace tailWord_5157079 prefixEnd_5157079 2648060300208133638395531 := by
  unfold tailWord_5157079
  simp only [CollatzResearch.WordTrace]
  refine ⟨188094123683791016817506291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125396082455860677878337527 188094123683791016817506291)
  ·
    refine ⟨282141185525686525226259437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188094123683791016817506291 282141185525686525226259437)
    ·
      refine ⟨105802944572132446959847289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 282141185525686525226259437 105802944572132446959847289)
      ·
        refine ⟨79352208429099335219885467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105802944572132446959847289 79352208429099335219885467)
        ·
          refine ⟨119028312643649002829828201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79352208429099335219885467 119028312643649002829828201)
          ·
            refine ⟨89271234482736752122371151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119028312643649002829828201 89271234482736752122371151)
            ·
              refine ⟨133906851724105128183556727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89271234482736752122371151 133906851724105128183556727)
              ·
                refine ⟨200860277586157692275335091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 133906851724105128183556727 200860277586157692275335091)
                ·
                  refine ⟨301290416379236538413002637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 200860277586157692275335091 301290416379236538413002637)
                  ·
                    refine ⟨112983906142213701904875989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 301290416379236538413002637 112983906142213701904875989)
                    ·
                      refine ⟨2648060300208133638395531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 112983906142213701904875989 2648060300208133638395531)
                      ·
                        rfl

theorem cell23_5157079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 3, 7].length) (baseStart_5157079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5157079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5157079 prefixEnd_5157079 := by exact prefixLift 5157079
  have htrace : WordTrace (prefixWord ++ tailWord_5157079) baseStart_5157079 baseEnd_5157079 := by
    simpa [prefixWord, tailWord_5157079, baseEnd_5157079] using wordTrace_append hprefix tailTrace_5157079
  have hstable : (prefixWord ++ tailWord_5157079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5157079).length < 2 ^ (prefixWord ++ tailWord_5157079).sum := by decide
  have hdescent : baseEnd_5157079 < baseStart_5157079 := by decide
  rcases family_descends (prefixWord ++ tailWord_5157079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5157084 : List Nat := [2, 2, 5, 2, 2, 1, 1, 1, 2, 1, 4]
def baseStart_5157084 : Nat := 118140960795 + 5157084 * 2 ^ 59
def prefixEnd_5157084 : Nat := 4983230072969 + 3 ^ 40 * 5157084 * 2
def baseEnd_5157084 : Nat := 2648062867611406118833009

theorem tailTrace_5157084 : CollatzResearch.WordTrace tailWord_5157084 prefixEnd_5157084 2648062867611406118833009 := by
  unfold tailWord_5157084
  simp only [CollatzResearch.WordTrace]
  refine ⟨94047153024386451335719153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125396204032515268447625537 94047153024386451335719153)
  ·
    refine ⟨70535364768289838501789365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94047153024386451335719153 70535364768289838501789365)
    ·
      refine ⟨6612690447027172359542753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 70535364768289838501789365 6612690447027172359542753)
      ·
        refine ⟨4959517835270379269657065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6612690447027172359542753 4959517835270379269657065)
        ·
          refine ⟨3719638376452784452242799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4959517835270379269657065 3719638376452784452242799)
          ·
            refine ⟨5579457564679176678364199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3719638376452784452242799 5579457564679176678364199)
            ·
              refine ⟨8369186347018765017546299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5579457564679176678364199 8369186347018765017546299)
              ·
                refine ⟨12553779520528147526319449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8369186347018765017546299 12553779520528147526319449)
                ·
                  refine ⟨9415334640396110644739587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12553779520528147526319449 9415334640396110644739587)
                  ·
                    refine ⟨14123001960594165967109381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9415334640396110644739587 14123001960594165967109381)
                    ·
                      refine ⟨2648062867611406118833009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14123001960594165967109381 2648062867611406118833009)
                      ·
                        rfl

theorem cell23_5157084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_5157084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5157084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5157084 prefixEnd_5157084 := by exact prefixLift 5157084
  have htrace : WordTrace (prefixWord ++ tailWord_5157084) baseStart_5157084 baseEnd_5157084 := by
    simpa [prefixWord, tailWord_5157084, baseEnd_5157084] using wordTrace_append hprefix tailTrace_5157084
  have hstable : (prefixWord ++ tailWord_5157084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5157084).length < 2 ^ (prefixWord ++ tailWord_5157084).sum := by decide
  have hdescent : baseEnd_5157084 < baseStart_5157084 := by decide
  rcases family_descends (prefixWord ++ tailWord_5157084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5157103 : List Nat := [1, 1, 2, 1, 6, 2, 1, 3, 1, 5]
def baseStart_5157103 : Nat := 118140960795 + 5157103 * 2 ^ 59
def prefixEnd_5157103 : Nat := 4983230072969 + 3 ^ 40 * 5157103 * 2
def baseEnd_5157103 : Nat := 882690874581280514831807

theorem tailTrace_5157103 : CollatzResearch.WordTrace tailWord_5157103 prefixEnd_5157103 882690874581280514831807 := by
  unfold tailWord_5157103
  simp only [CollatzResearch.WordTrace]
  refine ⟨188094999035704068916379963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125396666023802712610919975 188094999035704068916379963)
  ·
    refine ⟨282142498553556103374569945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188094999035704068916379963 282142498553556103374569945)
    ·
      refine ⟨211606873915167077530927459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 282142498553556103374569945 211606873915167077530927459)
      ·
        refine ⟨317410310872750616296391189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211606873915167077530927459 317410310872750616296391189)
        ·
          refine ⟨14878608322160185138893337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 317410310872750616296391189 14878608322160185138893337)
          ·
            refine ⟨11158956241620138854170003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14878608322160185138893337 11158956241620138854170003)
            ·
              refine ⟨16738434362430208281255005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11158956241620138854170003 16738434362430208281255005)
              ·
                refine ⟨6276912885911328105470627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16738434362430208281255005 6276912885911328105470627)
                ·
                  refine ⟨9415369328866992158205941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6276912885911328105470627 9415369328866992158205941)
                  ·
                    refine ⟨882690874581280514831807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9415369328866992158205941 882690874581280514831807)
                    ·
                      rfl

theorem cell23_5157103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 3, 1, 5].length) (baseStart_5157103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5157103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5157103 prefixEnd_5157103 := by exact prefixLift 5157103
  have htrace : WordTrace (prefixWord ++ tailWord_5157103) baseStart_5157103 baseEnd_5157103 := by
    simpa [prefixWord, tailWord_5157103, baseEnd_5157103] using wordTrace_append hprefix tailTrace_5157103
  have hstable : (prefixWord ++ tailWord_5157103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5157103).length < 2 ^ (prefixWord ++ tailWord_5157103).sum := by decide
  have hdescent : baseEnd_5157103 < baseStart_5157103 := by decide
  rcases family_descends (prefixWord ++ tailWord_5157103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5157110 : List Nat := [5, 1, 1, 1, 1, 1, 2, 4, 2, 3, 2]
def baseStart_5157110 : Nat := 118140960795 + 5157110 * 2 ^ 59
def prefixEnd_5157110 : Nat := 4983230072969 + 3 ^ 40 * 5157110 * 2
def baseEnd_5157110 : Nat := 2648076218108423017107889

theorem tailTrace_5157110 : CollatzResearch.WordTrace tailWord_5157110 prefixEnd_5157110 2648076218108423017107889 := by
  unfold tailWord_5157110
  simp only [CollatzResearch.WordTrace]
  refine ⟨11755953396667419319492799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 125396836231119139407923189 11755953396667419319492799)
  ·
    refine ⟨17633930095001128979239199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11755953396667419319492799 17633930095001128979239199)
    ·
      refine ⟨26450895142501693468858799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17633930095001128979239199 26450895142501693468858799)
      ·
        refine ⟨39676342713752540203288199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26450895142501693468858799 39676342713752540203288199)
        ·
          refine ⟨59514514070628810304932299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39676342713752540203288199 59514514070628810304932299)
          ·
            refine ⟨89271771105943215457398449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59514514070628810304932299 89271771105943215457398449)
            ·
              refine ⟨66953828329457411593048837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89271771105943215457398449 66953828329457411593048837)
              ·
                refine ⟨12553842811773264673696657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 66953828329457411593048837 12553842811773264673696657)
                ·
                  refine ⟨9415382108829948505272493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12553842811773264673696657 9415382108829948505272493)
                  ·
                    refine ⟨3530768290811230689477185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9415382108829948505272493 3530768290811230689477185)
                    ·
                      refine ⟨2648076218108423017107889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3530768290811230689477185 2648076218108423017107889)
                      ·
                        rfl

theorem cell23_5157110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 4, 2, 3, 2].length) (baseStart_5157110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5157110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5157110 prefixEnd_5157110 := by exact prefixLift 5157110
  have htrace : WordTrace (prefixWord ++ tailWord_5157110) baseStart_5157110 baseEnd_5157110 := by
    simpa [prefixWord, tailWord_5157110, baseEnd_5157110] using wordTrace_append hprefix tailTrace_5157110
  have hstable : (prefixWord ++ tailWord_5157110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5157110).length < 2 ^ (prefixWord ++ tailWord_5157110).sum := by decide
  have hdescent : baseEnd_5157110 < baseStart_5157110 := by decide
  rcases family_descends (prefixWord ++ tailWord_5157110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5157160 : List Nat := [2, 1, 5, 1, 3, 1, 2, 1, 1, 1, 5]
def baseStart_5157160 : Nat := 118140960795 + 5157160 * 2 ^ 59
def prefixEnd_5157160 : Nat := 4983230072969 + 3 ^ 40 * 5157160 * 2
def baseEnd_5157160 : Nat := 2648101892141147821482659

theorem tailTrace_5157160 : CollatzResearch.WordTrace tailWord_5157160 prefixEnd_5157160 2648101892141147821482659 := by
  unfold tailWord_5157160
  simp only [CollatzResearch.WordTrace]
  refine ⟨94048538998248783825602467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125398051997665045100803289 94048538998248783825602467)
  ·
    refine ⟨141072808497373175738403701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94048538998248783825602467 141072808497373175738403701)
    ·
      refine ⟨13225575796628735225475347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 141072808497373175738403701 13225575796628735225475347)
      ·
        refine ⟨19838363694943102838213021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13225575796628735225475347 19838363694943102838213021)
        ·
          refine ⟨7439386385603663564329883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19838363694943102838213021 7439386385603663564329883)
          ·
            refine ⟨11159079578405495346494825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7439386385603663564329883 11159079578405495346494825)
            ·
              refine ⟨8369309683804121509871119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11159079578405495346494825 8369309683804121509871119)
              ·
                refine ⟨12553964525706182264806679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8369309683804121509871119 12553964525706182264806679)
                ·
                  refine ⟨18830946788559273397210019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12553964525706182264806679 18830946788559273397210019)
                  ·
                    refine ⟨28246420182838910095815029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18830946788559273397210019 28246420182838910095815029)
                    ·
                      refine ⟨2648101892141147821482659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28246420182838910095815029 2648101892141147821482659)
                      ·
                        rfl

theorem cell23_5157160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 2, 1, 1, 1, 5].length) (baseStart_5157160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5157160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5157160 prefixEnd_5157160 := by exact prefixLift 5157160
  have htrace : WordTrace (prefixWord ++ tailWord_5157160) baseStart_5157160 baseEnd_5157160 := by
    simpa [prefixWord, tailWord_5157160, baseEnd_5157160] using wordTrace_append hprefix tailTrace_5157160
  have hstable : (prefixWord ++ tailWord_5157160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5157160).length < 2 ^ (prefixWord ++ tailWord_5157160).sum := by decide
  have hdescent : baseEnd_5157160 < baseStart_5157160 := by decide
  rcases family_descends (prefixWord ++ tailWord_5157160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5157200 : List Nat := [2, 1, 1, 1, 1, 7, 1, 1, 3, 3, 2]
def baseStart_5157200 : Nat := 118140960795 + 5157200 * 2 ^ 59
def prefixEnd_5157200 : Nat := 4983230072969 + 3 ^ 40 * 5157200 * 2
def baseEnd_5157200 : Nat := 2648122431367327664982475

theorem tailTrace_5157200 : CollatzResearch.WordTrace tailWord_5157200 prefixEnd_5157200 2648122431367327664982475 := by
  unfold tailWord_5157200
  simp only [CollatzResearch.WordTrace]
  refine ⟨94049268458176327241330527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125399024610901769655107369 94049268458176327241330527)
  ·
    refine ⟨141073902687264490861995791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94049268458176327241330527 141073902687264490861995791)
    ·
      refine ⟨211610854030896736292993687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141073902687264490861995791 211610854030896736292993687)
      ·
        refine ⟨317416281046345104439490531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211610854030896736292993687 317416281046345104439490531)
        ·
          refine ⟨476124421569517656659235797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 317416281046345104439490531 476124421569517656659235797)
          ·
            refine ⟨11159166130535570077950839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 476124421569517656659235797 11159166130535570077950839)
            ·
              refine ⟨16738749195803355116926259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11159166130535570077950839 16738749195803355116926259)
              ·
                refine ⟨25108123793705032675389389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16738749195803355116926259 25108123793705032675389389)
                ·
                  refine ⟨9415546422639387253271021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25108123793705032675389389 9415546422639387253271021)
                  ·
                    refine ⟨3530829908489770219976633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9415546422639387253271021 3530829908489770219976633)
                    ·
                      refine ⟨2648122431367327664982475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3530829908489770219976633 2648122431367327664982475)
                      ·
                        rfl

theorem cell23_5157200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 1, 3, 3, 2].length) (baseStart_5157200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5157200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5157200 prefixEnd_5157200 := by exact prefixLift 5157200
  have htrace : WordTrace (prefixWord ++ tailWord_5157200) baseStart_5157200 baseEnd_5157200 := by
    simpa [prefixWord, tailWord_5157200, baseEnd_5157200] using wordTrace_append hprefix tailTrace_5157200
  have hstable : (prefixWord ++ tailWord_5157200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5157200).length < 2 ^ (prefixWord ++ tailWord_5157200).sum := by decide
  have hdescent : baseEnd_5157200 < baseStart_5157200 := by decide
  rcases family_descends (prefixWord ++ tailWord_5157200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5157214 : List Nat := [4, 4, 2, 1, 2, 10]
def baseStart_5157214 : Nat := 118140960795 + 5157214 * 2 ^ 59
def prefixEnd_5157214 : Nat := 4983230072969 + 3 ^ 40 * 5157214 * 2
def baseEnd_5157214 : Nat := 10897652757598726790977

theorem tailTrace_5157214 : CollatzResearch.WordTrace tailWord_5157214 prefixEnd_5157214 10897652757598726790977 := by
  unfold tailWord_5157214
  simp only [CollatzResearch.WordTrace]
  refine ⟨23512380942287741859208837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125399365025534623249113797 23512380942287741859208837)
  ·
    refine ⟨4408571426678951598601657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23512380942287741859208837 4408571426678951598601657)
    ·
      refine ⟨3306428570009213698951243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4408571426678951598601657 3306428570009213698951243)
      ·
        refine ⟨4959642855013820548426865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3306428570009213698951243 4959642855013820548426865)
        ·
          refine ⟨3719732141260365411320149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4959642855013820548426865 3719732141260365411320149)
          ·
            refine ⟨10897652757598726790977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3719732141260365411320149 10897652757598726790977)
            ·
              rfl

theorem cell23_5157214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 10].length) (baseStart_5157214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5157214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5157214 prefixEnd_5157214 := by exact prefixLift 5157214
  have htrace : WordTrace (prefixWord ++ tailWord_5157214) baseStart_5157214 baseEnd_5157214 := by
    simpa [prefixWord, tailWord_5157214, baseEnd_5157214] using wordTrace_append hprefix tailTrace_5157214
  have hstable : (prefixWord ++ tailWord_5157214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5157214).length < 2 ^ (prefixWord ++ tailWord_5157214).sum := by decide
  have hdescent : baseEnd_5157214 < baseStart_5157214 := by decide
  rcases family_descends (prefixWord ++ tailWord_5157214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5157243 : List Nat := [1, 1, 1, 1, 1, 8, 1, 1, 2, 2, 4]
def baseStart_5157243 : Nat := 118140960795 + 5157243 * 2 ^ 59
def prefixEnd_5157243 : Nat := 4983230072969 + 3 ^ 40 * 5157243 * 2
def baseEnd_5157243 : Nat := 2648144511035470996744777

theorem tailTrace_5157243 : CollatzResearch.WordTrace tailWord_5157243 prefixEnd_5157243 2648144511035470996744777 := by
  unfold tailWord_5157243
  simp only [CollatzResearch.WordTrace]
  refine ⟨188100105255196872826476383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125400070170131248550984255 188100105255196872826476383)
  ·
    refine ⟨282150157882795309239714575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188100105255196872826476383 282150157882795309239714575)
    ·
      refine ⟨423225236824192963859571863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 282150157882795309239714575 423225236824192963859571863)
      ·
        refine ⟨634837855236289445789357795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 423225236824192963859571863 634837855236289445789357795)
        ·
          refine ⟨952256782854434168684036693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 634837855236289445789357795 952256782854434168684036693)
          ·
            refine ⟨11159259174075400414266055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 952256782854434168684036693 11159259174075400414266055)
            ·
              refine ⟨16738888761113100621399083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11159259174075400414266055 16738888761113100621399083)
              ·
                refine ⟨25108333141669650932098625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16738888761113100621399083 25108333141669650932098625)
                ·
                  refine ⟨18831249856252238199073969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25108333141669650932098625 18831249856252238199073969)
                  ·
                    refine ⟨14123437392189178649305477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18831249856252238199073969 14123437392189178649305477)
                    ·
                      refine ⟨2648144511035470996744777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14123437392189178649305477 2648144511035470996744777)
                      ·
                        rfl

theorem cell23_5157243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 1, 2, 2, 4].length) (baseStart_5157243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5157243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5157243 prefixEnd_5157243 := by exact prefixLift 5157243
  have htrace : WordTrace (prefixWord ++ tailWord_5157243) baseStart_5157243 baseEnd_5157243 := by
    simpa [prefixWord, tailWord_5157243, baseEnd_5157243] using wordTrace_append hprefix tailTrace_5157243
  have hstable : (prefixWord ++ tailWord_5157243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5157243).length < 2 ^ (prefixWord ++ tailWord_5157243).sum := by decide
  have hdescent : baseEnd_5157243 < baseStart_5157243 := by decide
  rcases family_descends (prefixWord ++ tailWord_5157243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5157268 : List Nat := [2, 4, 2, 1, 4, 1, 2, 1, 1, 3, 2]
def baseStart_5157268 : Nat := 118140960795 + 5157268 * 2 ^ 59
def prefixEnd_5157268 : Nat := 4983230072969 + 3 ^ 40 * 5157268 * 2
def baseEnd_5157268 : Nat := 2648157348051833398932163

theorem tailTrace_5157268 : CollatzResearch.WordTrace tailWord_5157268 prefixEnd_5157268 2648157348051833398932163 := by
  unfold tailWord_5157268
  simp only [CollatzResearch.WordTrace]
  refine ⟨94050508540053151048068229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125400678053404201397424305 94050508540053151048068229)
  ·
    refine ⟨17634470351259965821512793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94050508540053151048068229 17634470351259965821512793)
    ·
      refine ⟨13225852763444974366134595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17634470351259965821512793 13225852763444974366134595)
      ·
        refine ⟨19838779145167461549201893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13225852763444974366134595 19838779145167461549201893)
        ·
          refine ⟨3719771089718899040475355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19838779145167461549201893 3719771089718899040475355)
          ·
            refine ⟨5579656634578348560713033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3719771089718899040475355 5579656634578348560713033)
            ·
              refine ⟨4184742475933761420534775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5579656634578348560713033 4184742475933761420534775)
              ·
                refine ⟨6277113713900642130802163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4184742475933761420534775 6277113713900642130802163)
                ·
                  refine ⟨9415670570850963196203245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6277113713900642130802163 9415670570850963196203245)
                  ·
                    refine ⟨3530876464069111198576217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9415670570850963196203245 3530876464069111198576217)
                    ·
                      refine ⟨2648157348051833398932163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3530876464069111198576217 2648157348051833398932163)
                      ·
                        rfl

theorem cell23_5157268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 2, 1, 1, 3, 2].length) (baseStart_5157268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5157268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5157268 prefixEnd_5157268 := by exact prefixLift 5157268
  have htrace : WordTrace (prefixWord ++ tailWord_5157268) baseStart_5157268 baseEnd_5157268 := by
    simpa [prefixWord, tailWord_5157268, baseEnd_5157268] using wordTrace_append hprefix tailTrace_5157268
  have hstable : (prefixWord ++ tailWord_5157268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5157268).length < 2 ^ (prefixWord ++ tailWord_5157268).sum := by decide
  have hdescent : baseEnd_5157268 < baseStart_5157268 := by decide
  rcases family_descends (prefixWord ++ tailWord_5157268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5157303 : List Nat := [1, 1, 3, 1, 3, 3, 1, 2, 1, 3, 4]
def baseStart_5157303 : Nat := 118140960795 + 5157303 * 2 ^ 59
def prefixEnd_5157303 : Nat := 4983230072969 + 3 ^ 40 * 5157303 * 2
def baseEnd_5157303 : Nat := 2648175319874740761994501

theorem tailTrace_5157303 : CollatzResearch.WordTrace tailWord_5157303 prefixEnd_5157303 2648175319874740761994501 := by
  unfold tailWord_5157303
  simp only [CollatzResearch.WordTrace]
  refine ⟨188102293634979503073660563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125401529089986335382440375 188102293634979503073660563)
  ·
    refine ⟨282153440452469254610490845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188102293634979503073660563 282153440452469254610490845)
    ·
      refine ⟨105807540169675970478934067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 282153440452469254610490845 105807540169675970478934067)
      ·
        refine ⟨158711310254513955718401101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105807540169675970478934067 158711310254513955718401101)
        ·
          refine ⟨59516741345442733394400413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 158711310254513955718401101 59516741345442733394400413)
          ·
            refine ⟨22318778004541025022900155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59516741345442733394400413 22318778004541025022900155)
            ·
              refine ⟨33478167006811537534350233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22318778004541025022900155 33478167006811537534350233)
              ·
                refine ⟨25108625255108653150762675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33478167006811537534350233 25108625255108653150762675)
                ·
                  refine ⟨37662937882662979726144013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25108625255108653150762675 37662937882662979726144013)
                  ·
                    refine ⟨14123601705998617397304005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37662937882662979726144013 14123601705998617397304005)
                    ·
                      refine ⟨2648175319874740761994501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14123601705998617397304005 2648175319874740761994501)
                      ·
                        rfl

theorem cell23_5157303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 2, 1, 3, 4].length) (baseStart_5157303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5157303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5157303 prefixEnd_5157303 := by exact prefixLift 5157303
  have htrace : WordTrace (prefixWord ++ tailWord_5157303) baseStart_5157303 baseEnd_5157303 := by
    simpa [prefixWord, tailWord_5157303, baseEnd_5157303] using wordTrace_append hprefix tailTrace_5157303
  have hstable : (prefixWord ++ tailWord_5157303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5157303).length < 2 ^ (prefixWord ++ tailWord_5157303).sum := by decide
  have hdescent : baseEnd_5157303 < baseStart_5157303 := by decide
  rcases family_descends (prefixWord ++ tailWord_5157303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5157343 : List Nat := [1, 1, 2, 3, 3, 2, 2, 1, 8]
def baseStart_5157343 : Nat := 118140960795 + 5157343 * 2 ^ 59
def prefixEnd_5157343 : Nat := 4983230072969 + 3 ^ 40 * 5157343 * 2
def baseEnd_5157343 : Nat := 294243984344546733943813

theorem tailTrace_5157343 : CollatzResearch.WordTrace tailWord_5157343 prefixEnd_5157343 294243984344546733943813 := by
  unfold tailWord_5157343
  simp only [CollatzResearch.WordTrace]
  refine ⟨188103752554834589905116683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125402501703223059936744455 188103752554834589905116683)
  ·
    refine ⟨282155628832251884857675025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188103752554834589905116683 282155628832251884857675025)
    ·
      refine ⟨211616721624188913643256269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 282155628832251884857675025 211616721624188913643256269)
      ·
        refine ⟨79356270609070842616221101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 211616721624188913643256269 79356270609070842616221101)
        ·
          refine ⟨29758601478401565981082913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79356270609070842616221101 29758601478401565981082913)
          ·
            refine ⟨22318951108801174485812185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29758601478401565981082913 22318951108801174485812185)
            ·
              refine ⟨16739213331600880864359139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22318951108801174485812185 16739213331600880864359139)
              ·
                refine ⟨25108819997401321296538709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16739213331600880864359139 25108819997401321296538709)
                ·
                  refine ⟨294243984344546733943813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25108819997401321296538709 294243984344546733943813)
                  ·
                    rfl

theorem cell23_5157343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 1, 8].length) (baseStart_5157343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5157343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5157343 prefixEnd_5157343 := by exact prefixLift 5157343
  have htrace : WordTrace (prefixWord ++ tailWord_5157343) baseStart_5157343 baseEnd_5157343 := by
    simpa [prefixWord, tailWord_5157343, baseEnd_5157343] using wordTrace_append hprefix tailTrace_5157343
  have hstable : (prefixWord ++ tailWord_5157343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5157343).length < 2 ^ (prefixWord ++ tailWord_5157343).sum := by decide
  have hdescent : baseEnd_5157343 < baseStart_5157343 := by decide
  rcases family_descends (prefixWord ++ tailWord_5157343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5157353 : List Nat := [1, 2, 1, 1, 1, 2, 1, 4, 2, 5, 3]
def baseStart_5157353 : Nat := 118140960795 + 5157353 * 2 ^ 59
def prefixEnd_5157353 : Nat := 4983230072969 + 3 ^ 40 * 5157353 * 2
def baseEnd_5157353 : Nat := 2648200993907465566369271

theorem tailTrace_5157353 : CollatzResearch.WordTrace tailWord_5157353 prefixEnd_5157353 2648200993907465566369271 := by
  unfold tailWord_5157353
  simp only [CollatzResearch.WordTrace]
  refine ⟨188104117284798361612980713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125402744856532241075320475 188104117284798361612980713)
  ·
    refine ⟨141078087963598771209735535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188104117284798361612980713 141078087963598771209735535)
    ·
      refine ⟨211617131945398156814603303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141078087963598771209735535 211617131945398156814603303)
      ·
        refine ⟨317425697918097235221904955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211617131945398156814603303 317425697918097235221904955)
        ·
          refine ⟨476138546877145852832857433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 317425697918097235221904955 476138546877145852832857433)
          ·
            refine ⟨357103910157859389624643075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 476138546877145852832857433 357103910157859389624643075)
            ·
              refine ⟨535655865236789084436964613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 357103910157859389624643075 535655865236789084436964613)
              ·
                refine ⟨100435474731897953331930865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 535655865236789084436964613 100435474731897953331930865)
                ·
                  refine ⟨75326606048923464998948149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 100435474731897953331930865 75326606048923464998948149)
                  ·
                    refine ⟨7061869317086574843651389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 75326606048923464998948149 7061869317086574843651389)
                    ·
                      refine ⟨2648200993907465566369271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7061869317086574843651389 2648200993907465566369271)
                      ·
                        rfl

theorem cell23_5157353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 2, 5, 3].length) (baseStart_5157353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5157353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5157353 prefixEnd_5157353 := by exact prefixLift 5157353
  have htrace : WordTrace (prefixWord ++ tailWord_5157353) baseStart_5157353 baseEnd_5157353 := by
    simpa [prefixWord, tailWord_5157353, baseEnd_5157353] using wordTrace_append hprefix tailTrace_5157353
  have hstable : (prefixWord ++ tailWord_5157353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5157353).length < 2 ^ (prefixWord ++ tailWord_5157353).sum := by decide
  have hdescent : baseEnd_5157353 < baseStart_5157353 := by decide
  rcases family_descends (prefixWord ++ tailWord_5157353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5157397 : List Nat := [1, 3, 2, 1, 3, 1, 1, 4, 2, 3, 2]
def baseStart_5157397 : Nat := 118140960795 + 5157397 * 2 ^ 59
def prefixEnd_5157397 : Nat := 4983230072969 + 3 ^ 40 * 5157397 * 2
def baseEnd_5157397 : Nat := 2648223587056263394219069

theorem tailTrace_5157397 : CollatzResearch.WordTrace tailWord_5157397 prefixEnd_5157397 2648223587056263394219069 := by
  unfold tailWord_5157397
  simp only [CollatzResearch.WordTrace]
  refine ⟨188105722096638957127582445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125403814731092638085054963 188105722096638957127582445)
  ·
    refine ⟨70539645786239608922843417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 188105722096638957127582445 70539645786239608922843417)
    ·
      refine ⟨52904734339679706692132563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70539645786239608922843417 52904734339679706692132563)
      ·
        refine ⟨79357101509519560038198845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52904734339679706692132563 79357101509519560038198845)
        ·
          refine ⟨29758913066069835014324567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79357101509519560038198845 29758913066069835014324567)
          ·
            refine ⟨44638369599104752521486851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29758913066069835014324567 44638369599104752521486851)
            ·
              refine ⟨66957554398657128782230277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44638369599104752521486851 66957554398657128782230277)
              ·
                refine ⟨12554541449748211646668177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 66957554398657128782230277 12554541449748211646668177)
                ·
                  refine ⟨9415906087311158735001133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12554541449748211646668177 9415906087311158735001133)
                  ·
                    refine ⟨3530964782741684525625425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9415906087311158735001133 3530964782741684525625425)
                    ·
                      refine ⟨2648223587056263394219069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3530964782741684525625425 2648223587056263394219069)
                      ·
                        rfl

theorem cell23_5157397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 4, 2, 3, 2].length) (baseStart_5157397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5157397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5157397 prefixEnd_5157397 := by exact prefixLift 5157397
  have htrace : WordTrace (prefixWord ++ tailWord_5157397) baseStart_5157397 baseEnd_5157397 := by
    simpa [prefixWord, tailWord_5157397, baseEnd_5157397] using wordTrace_append hprefix tailTrace_5157397
  have hstable : (prefixWord ++ tailWord_5157397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5157397).length < 2 ^ (prefixWord ++ tailWord_5157397).sum := by decide
  have hdescent : baseEnd_5157397 < baseStart_5157397 := by decide
  rcases family_descends (prefixWord ++ tailWord_5157397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5157440 : List Nat := [2, 1, 1, 2, 2, 2, 4, 2, 1, 2, 4]
def baseStart_5157440 : Nat := 118140960795 + 5157440 * 2 ^ 59
def prefixEnd_5157440 : Nat := 4983230072969 + 3 ^ 40 * 5157440 * 2
def baseEnd_5157440 : Nat := 2648245666724406725981371

theorem tailTrace_5157440 : CollatzResearch.WordTrace tailWord_5157440 prefixEnd_5157440 2648245666724406725981371 := by
  unfold tailWord_5157440
  simp only [CollatzResearch.WordTrace]
  refine ⟨94053645217741587735698887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125404860290322116980931849 94053645217741587735698887)
  ·
    refine ⟨141080467826612381603548331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94053645217741587735698887 141080467826612381603548331)
    ·
      refine ⟨211620701739918572405322497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141080467826612381603548331 211620701739918572405322497)
      ·
        refine ⟨158715526304938929303991873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 211620701739918572405322497 158715526304938929303991873)
        ·
          refine ⟨119036644728704196977993905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 158715526304938929303991873 119036644728704196977993905)
          ·
            refine ⟨89277483546528147733495429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119036644728704196977993905 89277483546528147733495429)
            ·
              refine ⟨16739528164974027700030393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 89277483546528147733495429 16739528164974027700030393)
              ·
                refine ⟨12554646123730520775022795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16739528164974027700030393 12554646123730520775022795)
                ·
                  refine ⟨18831969185595781162534193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12554646123730520775022795 18831969185595781162534193)
                  ·
                    refine ⟨14123976889196835871900645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18831969185595781162534193 14123976889196835871900645)
                    ·
                      refine ⟨2648245666724406725981371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14123976889196835871900645 2648245666724406725981371)
                      ·
                        rfl

theorem cell23_5157440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 2, 1, 2, 4].length) (baseStart_5157440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5157440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5157440 prefixEnd_5157440 := by exact prefixLift 5157440
  have htrace : WordTrace (prefixWord ++ tailWord_5157440) baseStart_5157440 baseEnd_5157440 := by
    simpa [prefixWord, tailWord_5157440, baseEnd_5157440] using wordTrace_append hprefix tailTrace_5157440
  have hstable : (prefixWord ++ tailWord_5157440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5157440).length < 2 ^ (prefixWord ++ tailWord_5157440).sum := by decide
  have hdescent : baseEnd_5157440 < baseStart_5157440 := by decide
  rcases family_descends (prefixWord ++ tailWord_5157440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5157461 : List Nat := [1, 3, 2, 2, 1, 1, 4, 4, 1, 2, 2]
def baseStart_5157461 : Nat := 118140960795 + 5157461 * 2 ^ 59
def prefixEnd_5157461 : Nat := 4983230072969 + 3 ^ 40 * 5157461 * 2
def baseEnd_5157461 : Nat := 2648256449818151143818775

theorem tailTrace_5157461 : CollatzResearch.WordTrace tailWord_5157461 prefixEnd_5157461 2648256449818151143818775 := by
  unfold tailWord_5157461
  simp only [CollatzResearch.WordTrace]
  refine ⟨188108056368407096057912237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125405370912271397371941491 188108056368407096057912237)
  ·
    refine ⟨70540521138152661021717089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 188108056368407096057912237 70540521138152661021717089)
    ·
      refine ⟨52905390853614495766287817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70540521138152661021717089 52905390853614495766287817)
      ·
        refine ⟨39679043140210871824715863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52905390853614495766287817 39679043140210871824715863)
        ·
          refine ⟨59518564710316307737073795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39679043140210871824715863 59518564710316307737073795)
          ·
            refine ⟨89277847065474461605610693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59518564710316307737073795 89277847065474461605610693)
            ·
              refine ⟨16739596324776461551052005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 89277847065474461605610693 16739596324776461551052005)
              ·
                refine ⟨3138674310895586540822251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16739596324776461551052005 3138674310895586540822251)
                ·
                  refine ⟨4708011466343379811233377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3138674310895586540822251 4708011466343379811233377)
                  ·
                    refine ⟨3531008599757534858425033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4708011466343379811233377 3531008599757534858425033)
                    ·
                      refine ⟨2648256449818151143818775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3531008599757534858425033 2648256449818151143818775)
                      ·
                        rfl

theorem cell23_5157461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 4, 1, 2, 2].length) (baseStart_5157461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5157461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5157461 prefixEnd_5157461 := by exact prefixLift 5157461
  have htrace : WordTrace (prefixWord ++ tailWord_5157461) baseStart_5157461 baseEnd_5157461 := by
    simpa [prefixWord, tailWord_5157461, baseEnd_5157461] using wordTrace_append hprefix tailTrace_5157461
  have hstable : (prefixWord ++ tailWord_5157461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5157461).length < 2 ^ (prefixWord ++ tailWord_5157461).sum := by decide
  have hdescent : baseEnd_5157461 < baseStart_5157461 := by decide
  rcases family_descends (prefixWord ++ tailWord_5157461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5157474 : List Nat := [3, 3, 2, 3, 1, 1, 1, 1, 1, 1, 6]
def baseStart_5157474 : Nat := 118140960795 + 5157474 * 2 ^ 59
def prefixEnd_5157474 : Nat := 4983230072969 + 3 ^ 40 * 5157474 * 2
def baseEnd_5157474 : Nat := 2648263125066659592956215

theorem tailTrace_5157474 : CollatzResearch.WordTrace tailWord_5157474 prefixEnd_5157474 2648263125066659592956215 := by
  unfold tailWord_5157474
  simp only [CollatzResearch.WordTrace]
  refine ⟨47027132629339999819533869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125405687011573332852090317 47027132629339999819533869)
  ·
    refine ⟨17635174736002499932325201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47027132629339999819533869 17635174736002499932325201)
    ·
      refine ⟨13226381052001874949243901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17635174736002499932325201 13226381052001874949243901)
      ·
        refine ⟨4959892894500703105966463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13226381052001874949243901 4959892894500703105966463)
        ·
          refine ⟨7439839341751054658949695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4959892894500703105966463 7439839341751054658949695)
          ·
            refine ⟨11159759012626581988424543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7439839341751054658949695 11159759012626581988424543)
            ·
              refine ⟨16739638518939872982636815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11159759012626581988424543 16739638518939872982636815)
              ·
                refine ⟨25109457778409809473955223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16739638518939872982636815 25109457778409809473955223)
                ·
                  refine ⟨37664186667614714210932835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25109457778409809473955223 37664186667614714210932835)
                  ·
                    refine ⟨56496280001422071316399253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37664186667614714210932835 56496280001422071316399253)
                    ·
                      refine ⟨2648263125066659592956215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56496280001422071316399253 2648263125066659592956215)
                      ·
                        rfl

theorem cell23_5157474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_5157474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5157474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5157474 prefixEnd_5157474 := by exact prefixLift 5157474
  have htrace : WordTrace (prefixWord ++ tailWord_5157474) baseStart_5157474 baseEnd_5157474 := by
    simpa [prefixWord, tailWord_5157474, baseEnd_5157474] using wordTrace_append hprefix tailTrace_5157474
  have hstable : (prefixWord ++ tailWord_5157474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5157474).length < 2 ^ (prefixWord ++ tailWord_5157474).sum := by decide
  have hdescent : baseEnd_5157474 < baseStart_5157474 := by decide
  rcases family_descends (prefixWord ++ tailWord_5157474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5157483 : List Nat := [1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 8]
def baseStart_5157483 : Nat := 118140960795 + 5157483 * 2 ^ 59
def prefixEnd_5157483 : Nat := 4983230072969 + 3 ^ 40 * 5157483 * 2
def baseEnd_5157483 : Nat := 2648267746392550057743673

theorem tailTrace_5157483 : CollatzResearch.WordTrace tailWord_5157483 prefixEnd_5157483 2648267746392550057743673 := by
  unfold tailWord_5157483
  simp only [CollatzResearch.WordTrace]
  refine ⟨188108858774327393815213103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125405905849551595876808735 188108858774327393815213103)
  ·
    refine ⟨282163288161491090722819655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188108858774327393815213103 282163288161491090722819655)
    ·
      refine ⟨423244932242236636084229483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 282163288161491090722819655 423244932242236636084229483)
      ·
        refine ⟨634867398363354954126344225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 423244932242236636084229483 634867398363354954126344225)
        ·
          refine ⟨476150548772516215594758169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 634867398363354954126344225 476150548772516215594758169)
          ·
            refine ⟨357112911579387161696068627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 476150548772516215594758169 357112911579387161696068627)
            ·
              refine ⟨535669367369080742544102941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 357112911579387161696068627 535669367369080742544102941)
              ·
                refine ⟨200876012763405278454038603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 535669367369080742544102941 200876012763405278454038603)
                ·
                  refine ⟨301314019145107917681057905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 200876012763405278454038603 301314019145107917681057905)
                  ·
                    refine ⟨225985514358830938260793429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 301314019145107917681057905 225985514358830938260793429)
                    ·
                      refine ⟨2648267746392550057743673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 225985514358830938260793429 2648267746392550057743673)
                      ·
                        rfl

theorem cell23_5157483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 8].length) (baseStart_5157483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5157483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5157483 prefixEnd_5157483 := by exact prefixLift 5157483
  have htrace : WordTrace (prefixWord ++ tailWord_5157483) baseStart_5157483 baseEnd_5157483 := by
    simpa [prefixWord, tailWord_5157483, baseEnd_5157483] using wordTrace_append hprefix tailTrace_5157483
  have hstable : (prefixWord ++ tailWord_5157483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5157483).length < 2 ^ (prefixWord ++ tailWord_5157483).sum := by decide
  have hdescent : baseEnd_5157483 < baseStart_5157483 := by decide
  rcases family_descends (prefixWord ++ tailWord_5157483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5157487 : List Nat := [1, 1, 2, 1, 3, 2, 2, 3, 3, 3, 2]
def baseStart_5157487 : Nat := 118140960795 + 5157487 * 2 ^ 59
def prefixEnd_5157487 : Nat := 4983230072969 + 3 ^ 40 * 5157487 * 2
def baseEnd_5157487 : Nat := 2648269800315168042093655

theorem tailTrace_5157487 : CollatzResearch.WordTrace tailWord_5157487 prefixEnd_5157487 2648269800315168042093655 := by
  unfold tailWord_5157487
  simp only [CollatzResearch.WordTrace]
  refine ⟨188109004666312902498358715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125406003110875268332239143 188109004666312902498358715)
  ·
    refine ⟨282163506999469353747538073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188109004666312902498358715 282163506999469353747538073)
    ·
      refine ⟨211622630249602015310653555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 282163506999469353747538073 211622630249602015310653555)
      ·
        refine ⟨317433945374403022965980333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211622630249602015310653555 317433945374403022965980333)
        ·
          refine ⟨119037729515401133612242625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 317433945374403022965980333 119037729515401133612242625)
          ·
            refine ⟨89278297136550850209181969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119037729515401133612242625 89278297136550850209181969)
            ·
              refine ⟨66958722852413137656886477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89278297136550850209181969 66958722852413137656886477)
              ·
                refine ⟨25109521069654926621332429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66958722852413137656886477 25109521069654926621332429)
                ·
                  refine ⟨9416070401120597482999661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25109521069654926621332429 9416070401120597482999661)
                  ·
                    refine ⟨3531026400420224056124873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9416070401120597482999661 3531026400420224056124873)
                    ·
                      refine ⟨2648269800315168042093655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3531026400420224056124873 2648269800315168042093655)
                      ·
                        rfl

theorem cell23_5157487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 3, 3, 3, 2].length) (baseStart_5157487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5157487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5157487 prefixEnd_5157487 := by exact prefixLift 5157487
  have htrace : WordTrace (prefixWord ++ tailWord_5157487) baseStart_5157487 baseEnd_5157487 := by
    simpa [prefixWord, tailWord_5157487, baseEnd_5157487] using wordTrace_append hprefix tailTrace_5157487
  have hstable : (prefixWord ++ tailWord_5157487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5157487).length < 2 ^ (prefixWord ++ tailWord_5157487).sum := by decide
  have hdescent : baseEnd_5157487 < baseStart_5157487 := by decide
  rcases family_descends (prefixWord ++ tailWord_5157487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5157504 : List Nat := [2, 1, 1, 2, 1, 5, 2, 3, 1, 3, 2]
def baseStart_5157504 : Nat := 118140960795 + 5157504 * 2 ^ 59
def prefixEnd_5157504 : Nat := 4983230072969 + 3 ^ 40 * 5157504 * 2
def baseEnd_5157504 : Nat := 2648278529486294475581077

theorem tailTrace_5157504 : CollatzResearch.WordTrace tailWord_5157504 prefixEnd_5157504 2648278529486294475581077 := by
  unfold tailWord_5157504
  simp only [CollatzResearch.WordTrace]
  refine ⟨94054812353625657200863783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125406416471500876267818377 94054812353625657200863783)
  ·
    refine ⟨141082218530438485801295675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94054812353625657200863783 141082218530438485801295675)
    ·
      refine ⟨211623327795657728701943513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141082218530438485801295675 211623327795657728701943513)
      ·
        refine ⟨158717495846743296526457635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 211623327795657728701943513 158717495846743296526457635)
        ·
          refine ⟨238076243770114944789686453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158717495846743296526457635 238076243770114944789686453)
          ·
            refine ⟨22319647853448276074033105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 238076243770114944789686453 22319647853448276074033105)
            ·
              refine ⟨16739735890086207055524829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22319647853448276074033105 16739735890086207055524829)
              ·
                refine ⟨6277400958782327645821811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16739735890086207055524829 6277400958782327645821811)
                ·
                  refine ⟨9416101438173491468732717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6277400958782327645821811 9416101438173491468732717)
                  ·
                    refine ⟨3531038039315059300774769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9416101438173491468732717 3531038039315059300774769)
                    ·
                      refine ⟨2648278529486294475581077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3531038039315059300774769 2648278529486294475581077)
                      ·
                        rfl

theorem cell23_5157504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 3, 1, 3, 2].length) (baseStart_5157504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5157504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5157504 prefixEnd_5157504 := by exact prefixLift 5157504
  have htrace : WordTrace (prefixWord ++ tailWord_5157504) baseStart_5157504 baseEnd_5157504 := by
    simpa [prefixWord, tailWord_5157504, baseEnd_5157504] using wordTrace_append hprefix tailTrace_5157504
  have hstable : (prefixWord ++ tailWord_5157504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5157504).length < 2 ^ (prefixWord ++ tailWord_5157504).sum := by decide
  have hdescent : baseEnd_5157504 < baseStart_5157504 := by decide
  rcases family_descends (prefixWord ++ tailWord_5157504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5157540 : List Nat := [2, 3, 1, 2, 2, 1, 2, 1, 9]
def baseStart_5157540 : Nat := 118140960795 + 5157540 * 2 ^ 59
def prefixEnd_5157540 : Nat := 4983230072969 + 3 ^ 40 * 5157540 * 2
def baseEnd_5157540 : Nat := 294255223865539592747879

theorem tailTrace_5157540 : CollatzResearch.WordTrace tailWord_5157540 prefixEnd_5157540 294255223865539592747879 := by
  unfold tailWord_5157540
  simp only [CollatzResearch.WordTrace]
  refine ⟨94055468867560446275019037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125407291823413928366692049 94055468867560446275019037)
  ·
    refine ⟨35270800825335167353132139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94055468867560446275019037 35270800825335167353132139)
    ·
      refine ⟨52906201238002751029698209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35270800825335167353132139 52906201238002751029698209)
      ·
        refine ⟨39679650928502063272273657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52906201238002751029698209 39679650928502063272273657)
        ·
          refine ⟨29759738196376547454205243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39679650928502063272273657 29759738196376547454205243)
          ·
            refine ⟨44639607294564821181307865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29759738196376547454205243 44639607294564821181307865)
            ·
              refine ⟨33479705470923615885980899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44639607294564821181307865 33479705470923615885980899)
              ·
                refine ⟨50219558206385423828971349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33479705470923615885980899 50219558206385423828971349)
                ·
                  refine ⟨294255223865539592747879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 50219558206385423828971349 294255223865539592747879)
                  ·
                    rfl

theorem cell23_5157540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 1, 9].length) (baseStart_5157540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5157540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5157540 prefixEnd_5157540 := by exact prefixLift 5157540
  have htrace : WordTrace (prefixWord ++ tailWord_5157540) baseStart_5157540 baseEnd_5157540 := by
    simpa [prefixWord, tailWord_5157540, baseEnd_5157540] using wordTrace_append hprefix tailTrace_5157540
  have hstable : (prefixWord ++ tailWord_5157540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5157540).length < 2 ^ (prefixWord ++ tailWord_5157540).sum := by decide
  have hdescent : baseEnd_5157540 < baseStart_5157540 := by decide
  rcases family_descends (prefixWord ++ tailWord_5157540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5157581 : List Nat := [1, 6, 2, 1, 2, 1, 1, 1, 2, 2, 4]
def baseStart_5157581 : Nat := 118140960795 + 5157581 * 2 ^ 59
def prefixEnd_5157581 : Nat := 4983230072969 + 3 ^ 40 * 5157581 * 2
def baseEnd_5157581 : Nat := 2648318067496690674318223

theorem tailTrace_5157581 : CollatzResearch.WordTrace tailWord_5157581 prefixEnd_5157581 2648318067496690674318223 := by
  unfold tailWord_5157581
  simp only [CollatzResearch.WordTrace]
  refine ⟨188112433127972356552280597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125408288751981571034853731 188112433127972356552280597)
  ·
    refine ⟨8817770302873704213388153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 188112433127972356552280597 8817770302873704213388153)
    ·
      refine ⟨6613327727155278160041115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8817770302873704213388153 6613327727155278160041115)
      ·
        refine ⟨9919991590732917240061673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6613327727155278160041115 9919991590732917240061673)
        ·
          refine ⟨7439993693049687930046255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9919991590732917240061673 7439993693049687930046255)
          ·
            refine ⟨11159990539574531895069383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7439993693049687930046255 11159990539574531895069383)
            ·
              refine ⟨16739985809361797842604075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11159990539574531895069383 16739985809361797842604075)
              ·
                refine ⟨25109978714042696763906113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16739985809361797842604075 25109978714042696763906113)
                ·
                  refine ⟨18832484035532022572929585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25109978714042696763906113 18832484035532022572929585)
                  ·
                    refine ⟨14124363026649016929697189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18832484035532022572929585 14124363026649016929697189)
                    ·
                      refine ⟨2648318067496690674318223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14124363026649016929697189 2648318067496690674318223)
                      ·
                        rfl

theorem cell23_5157581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_5157581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5157581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5157581 prefixEnd_5157581 := by exact prefixLift 5157581
  have htrace : WordTrace (prefixWord ++ tailWord_5157581) baseStart_5157581 baseEnd_5157581 := by
    simpa [prefixWord, tailWord_5157581, baseEnd_5157581] using wordTrace_append hprefix tailTrace_5157581
  have hstable : (prefixWord ++ tailWord_5157581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5157581).length < 2 ^ (prefixWord ++ tailWord_5157581).sum := by decide
  have hdescent : baseEnd_5157581 < baseStart_5157581 := by decide
  rcases family_descends (prefixWord ++ tailWord_5157581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5157604 : List Nat := [2, 3, 1, 1, 1, 6, 1, 1, 2, 5]
def baseStart_5157604 : Nat := 118140960795 + 5157604 * 2 ^ 59
def prefixEnd_5157604 : Nat := 4983230072969 + 3 ^ 40 * 5157604 * 2
def baseEnd_5157604 : Nat := 882776625850581361443539

theorem tailTrace_5157604 : CollatzResearch.WordTrace tailWord_5157604 prefixEnd_5157604 882776625850581361443539 := by
  unfold tailWord_5157604
  simp only [CollatzResearch.WordTrace]
  refine ⟨94056636003444515740183933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125408848004592687653578577 94056636003444515740183933)
  ·
    refine ⟨35271238501291693402568975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94056636003444515740183933 35271238501291693402568975)
    ·
      refine ⟨52906857751937540103853463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35271238501291693402568975 52906857751937540103853463)
      ·
        refine ⟨79360286627906310155780195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52906857751937540103853463 79360286627906310155780195)
        ·
          refine ⟨119040429941859465233670293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79360286627906310155780195 119040429941859465233670293)
          ·
            refine ⟨5580020153524662432828295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 119040429941859465233670293 5580020153524662432828295)
            ·
              refine ⟨8370030230286993649242443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5580020153524662432828295 8370030230286993649242443)
              ·
                refine ⟨12555045345430490473863665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8370030230286993649242443 12555045345430490473863665)
                ·
                  refine ⟨9416284009072867855397749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12555045345430490473863665 9416284009072867855397749)
                  ·
                    refine ⟨882776625850581361443539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9416284009072867855397749 882776625850581361443539)
                    ·
                      rfl

theorem cell23_5157604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 1, 1, 2, 5].length) (baseStart_5157604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5157604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5157604 prefixEnd_5157604 := by exact prefixLift 5157604
  have htrace : WordTrace (prefixWord ++ tailWord_5157604) baseStart_5157604 baseEnd_5157604 := by
    simpa [prefixWord, tailWord_5157604, baseEnd_5157604] using wordTrace_append hprefix tailTrace_5157604
  have hstable : (prefixWord ++ tailWord_5157604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5157604).length < 2 ^ (prefixWord ++ tailWord_5157604).sum := by decide
  have hdescent : baseEnd_5157604 < baseStart_5157604 := by decide
  rcases family_descends (prefixWord ++ tailWord_5157604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5157617 : List Nat := [1, 2, 2, 2, 2, 2, 1, 2, 5, 4]
def baseStart_5157617 : Nat := 118140960795 + 5157617 * 2 ^ 59
def prefixEnd_5157617 : Nat := 4983230072969 + 3 ^ 40 * 5157617 * 2
def baseEnd_5157617 : Nat := 882778850933417511156019

theorem tailTrace_5157617 : CollatzResearch.WordTrace tailWord_5157617 prefixEnd_5157617 882778850933417511156019 := by
  unfold tailWord_5157617
  simp only [CollatzResearch.WordTrace]
  refine ⟨188113746155841934700591105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125409164103894623133727403 188113746155841934700591105)
  ·
    refine ⟨141085309616881451025443329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188113746155841934700591105 141085309616881451025443329)
    ·
      refine ⟨105813982212661088269082497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141085309616881451025443329 105813982212661088269082497)
      ·
        refine ⟨79360486659495816201811873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105813982212661088269082497 79360486659495816201811873)
        ·
          refine ⟨59520364994621862151358905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79360486659495816201811873 59520364994621862151358905)
          ·
            refine ⟨44640273745966396613519179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59520364994621862151358905 44640273745966396613519179)
            ·
              refine ⟨66960410618949594920278769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44640273745966396613519179 66960410618949594920278769)
              ·
                refine ⟨50220307964212196190209077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66960410618949594920278769 50220307964212196190209077)
                ·
                  refine ⟨4708153871644893392832101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 50220307964212196190209077 4708153871644893392832101)
                  ·
                    refine ⟨882778850933417511156019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4708153871644893392832101 882778850933417511156019)
                    ·
                      rfl

theorem cell23_5157617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 2, 5, 4].length) (baseStart_5157617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5157617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5157617 prefixEnd_5157617 := by exact prefixLift 5157617
  have htrace : WordTrace (prefixWord ++ tailWord_5157617) baseStart_5157617 baseEnd_5157617 := by
    simpa [prefixWord, tailWord_5157617, baseEnd_5157617] using wordTrace_append hprefix tailTrace_5157617
  have hstable : (prefixWord ++ tailWord_5157617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5157617).length < 2 ^ (prefixWord ++ tailWord_5157617).sum := by decide
  have hdescent : baseEnd_5157617 < baseStart_5157617 := by decide
  rcases family_descends (prefixWord ++ tailWord_5157617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5157714 : List Nat := [3, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4]
def baseStart_5157714 : Nat := 118140960795 + 5157714 * 2 ^ 59
def prefixEnd_5157714 : Nat := 4983230072969 + 3 ^ 40 * 5157714 * 2
def baseEnd_5157714 : Nat := 2648386360423738653955111

theorem tailTrace_5157714 : CollatzResearch.WordTrace tailWord_5157714 prefixEnd_5157714 2648386360423738653955111 := by
  unfold tailWord_5157714
  simp only [CollatzResearch.WordTrace]
  refine ⟨47029321009122630066718049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125411522690993680177914797 47029321009122630066718049)
  ·
    refine ⟨35271990756841972550038537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47029321009122630066718049 35271990756841972550038537)
    ·
      refine ⟨26453993067631479412528903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35271990756841972550038537 26453993067631479412528903)
      ·
        refine ⟨39680989601447219118793355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26453993067631479412528903 39680989601447219118793355)
        ·
          refine ⟨59521484402170828678190033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39680989601447219118793355 59521484402170828678190033)
          ·
            refine ⟨44641113301628121508642525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59521484402170828678190033 44641113301628121508642525)
            ·
              refine ⟨16740417488110545565740947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44641113301628121508642525 16740417488110545565740947)
              ·
                refine ⟨25110626232165818348611421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16740417488110545565740947 25110626232165818348611421)
                ·
                  refine ⟨9416484837062181880729283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25110626232165818348611421 9416484837062181880729283)
                  ·
                    refine ⟨14124727255593272821093925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9416484837062181880729283 14124727255593272821093925)
                    ·
                      refine ⟨2648386360423738653955111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14124727255593272821093925 2648386360423738653955111)
                      ·
                        rfl

theorem cell23_5157714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4].length) (baseStart_5157714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5157714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5157714 prefixEnd_5157714 := by exact prefixLift 5157714
  have htrace : WordTrace (prefixWord ++ tailWord_5157714) baseStart_5157714 baseEnd_5157714 := by
    simpa [prefixWord, tailWord_5157714, baseEnd_5157714] using wordTrace_append hprefix tailTrace_5157714
  have hstable : (prefixWord ++ tailWord_5157714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5157714).length < 2 ^ (prefixWord ++ tailWord_5157714).sum := by decide
  have hdescent : baseEnd_5157714 < baseStart_5157714 := by decide
  rcases family_descends (prefixWord ++ tailWord_5157714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5157724 : List Nat := [2, 2, 4, 2, 1, 1, 1, 1, 3, 6]
def baseStart_5157724 : Nat := 118140960795 + 5157724 * 2 ^ 59
def prefixEnd_5157724 : Nat := 4983230072969 + 3 ^ 40 * 5157724 * 2
def baseEnd_5157724 : Nat := 882797165076761204943355

theorem tailTrace_5157724 : CollatzResearch.WordTrace tailWord_5157724 prefixEnd_5157724 882797165076761204943355 := by
  unfold tailWord_5157724
  simp only [CollatzResearch.WordTrace]
  refine ⟨94058824383227145987368113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125411765844302861316490817 94058824383227145987368113)
  ·
    refine ⟨70544118287420359490526085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94058824383227145987368113 70544118287420359490526085)
    ·
      refine ⟨13227022178891317404473641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70544118287420359490526085 13227022178891317404473641)
      ·
        refine ⟨9920266634168488053355231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13227022178891317404473641 9920266634168488053355231)
        ·
          refine ⟨14880399951252732080032847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9920266634168488053355231 14880399951252732080032847)
          ·
            refine ⟨22320599926879098120049271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14880399951252732080032847 22320599926879098120049271)
            ·
              refine ⟨33480899890318647180073907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22320599926879098120049271 33480899890318647180073907)
              ·
                refine ⟨50221349835477970770110861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33480899890318647180073907 50221349835477970770110861)
                ·
                  refine ⟨18833006188304239038791573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50221349835477970770110861 18833006188304239038791573)
                  ·
                    refine ⟨882797165076761204943355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18833006188304239038791573 882797165076761204943355)
                    ·
                      rfl

theorem cell23_5157724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 1, 3, 6].length) (baseStart_5157724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5157724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5157724 prefixEnd_5157724 := by exact prefixLift 5157724
  have htrace : WordTrace (prefixWord ++ tailWord_5157724) baseStart_5157724 baseEnd_5157724 := by
    simpa [prefixWord, tailWord_5157724, baseEnd_5157724] using wordTrace_append hprefix tailTrace_5157724
  have hstable : (prefixWord ++ tailWord_5157724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5157724).length < 2 ^ (prefixWord ++ tailWord_5157724).sum := by decide
  have hdescent : baseEnd_5157724 < baseStart_5157724 := by decide
  rcases family_descends (prefixWord ++ tailWord_5157724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5157757 : List Nat := [1, 4, 1, 1, 2, 1, 2, 1, 2, 2, 6]
def baseStart_5157757 : Nat := 118140960795 + 5157757 * 2 ^ 59
def prefixEnd_5157757 : Nat := 4983230072969 + 3 ^ 40 * 5157757 * 2
def baseEnd_5157757 : Nat := 2648408440091881985717413

theorem tailTrace_5157757 : CollatzResearch.WordTrace tailWord_5157757 prefixEnd_5157757 2648408440091881985717413 := by
  unfold tailWord_5157757
  simp only [CollatzResearch.WordTrace]
  refine ⟨188118852375334738610687525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125412568250223159073791683 188118852375334738610687525)
  ·
    refine ⟨35272284820375263489503911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 188118852375334738610687525 35272284820375263489503911)
    ·
      refine ⟨52908427230562895234255867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35272284820375263489503911 52908427230562895234255867)
      ·
        refine ⟨79362640845844342851383801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52908427230562895234255867 79362640845844342851383801)
        ·
          refine ⟨59521980634383257138537851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79362640845844342851383801 59521980634383257138537851)
          ·
            refine ⟨89282970951574885707806777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59521980634383257138537851 89282970951574885707806777)
            ·
              refine ⟨66962228213681164280855083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89282970951574885707806777 66962228213681164280855083)
              ·
                refine ⟨100443342320521746421282625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66962228213681164280855083 100443342320521746421282625)
                ·
                  refine ⟨75332506740391309815961969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 100443342320521746421282625 75332506740391309815961969)
                  ·
                    refine ⟨56499380055293482361971477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 75332506740391309815961969 56499380055293482361971477)
                    ·
                      refine ⟨2648408440091881985717413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56499380055293482361971477 2648408440091881985717413)
                      ·
                        rfl

theorem cell23_5157757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 2, 2, 6].length) (baseStart_5157757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5157757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5157757 prefixEnd_5157757 := by exact prefixLift 5157757
  have htrace : WordTrace (prefixWord ++ tailWord_5157757) baseStart_5157757 baseEnd_5157757 := by
    simpa [prefixWord, tailWord_5157757, baseEnd_5157757] using wordTrace_append hprefix tailTrace_5157757
  have hstable : (prefixWord ++ tailWord_5157757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5157757).length < 2 ^ (prefixWord ++ tailWord_5157757).sum := by decide
  have hdescent : baseEnd_5157757 < baseStart_5157757 := by decide
  rcases family_descends (prefixWord ++ tailWord_5157757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5157758 : List Nat := [4, 2, 3, 1, 2, 1, 2, 1, 1, 6]
def baseStart_5157758 : Nat := 118140960795 + 5157758 * 2 ^ 59
def prefixEnd_5157758 : Nat := 4983230072969 + 3 ^ 40 * 5157758 * 2
def baseEnd_5157758 : Nat := 882802984524178827268303

theorem tailTrace_5157758 : CollatzResearch.WordTrace tailWord_5157758 prefixEnd_5157758 882802984524178827268303 := by
  unfold tailWord_5157758
  simp only [CollatzResearch.WordTrace]
  refine ⟨23514861106041389472684241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125412592565554077187649285 23514861106041389472684241)
  ·
    refine ⟨17636145829531042104513181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23514861106041389472684241 17636145829531042104513181)
    ·
      refine ⟨6613554686074140789192443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17636145829531042104513181 6613554686074140789192443)
      ·
        refine ⟨9920332029111211183788665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6613554686074140789192443 9920332029111211183788665)
        ·
          refine ⟨7440249021833408387841499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9920332029111211183788665 7440249021833408387841499)
          ·
            refine ⟨11160373532750112581762249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7440249021833408387841499 11160373532750112581762249)
            ·
              refine ⟨8370280149562584436321687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11160373532750112581762249 8370280149562584436321687)
              ·
                refine ⟨12555420224343876654482531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8370280149562584436321687 12555420224343876654482531)
                ·
                  refine ⟨18833130336515814981723797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12555420224343876654482531 18833130336515814981723797)
                  ·
                    refine ⟨882802984524178827268303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18833130336515814981723797 882802984524178827268303)
                    ·
                      rfl

theorem cell23_5157758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_5157758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5157758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5157758 prefixEnd_5157758 := by exact prefixLift 5157758
  have htrace : WordTrace (prefixWord ++ tailWord_5157758) baseStart_5157758 baseEnd_5157758 := by
    simpa [prefixWord, tailWord_5157758, baseEnd_5157758] using wordTrace_append hprefix tailTrace_5157758
  have hstable : (prefixWord ++ tailWord_5157758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5157758).length < 2 ^ (prefixWord ++ tailWord_5157758).sum := by decide
  have hdescent : baseEnd_5157758 < baseStart_5157758 := by decide
  rcases family_descends (prefixWord ++ tailWord_5157758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5157777 : List Nat := [1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 5]
def baseStart_5157777 : Nat := 118140960795 + 5157777 * 2 ^ 59
def prefixEnd_5157777 : Nat := 4983230072969 + 3 ^ 40 * 5157777 * 2
def baseEnd_5157777 : Nat := 2648418709704971907467321

theorem tailTrace_5157777 : CollatzResearch.WordTrace tailWord_5157777 prefixEnd_5157777 2648418709704971907467321 := by
  unfold tailWord_5157777
  simp only [CollatzResearch.WordTrace]
  refine ⟨188119581835262282026415585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125413054556841521350943723 188119581835262282026415585)
  ·
    refine ⟨141089686376446711519811689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188119581835262282026415585 141089686376446711519811689)
    ·
      refine ⟨105817264782335033639858767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141089686376446711519811689 105817264782335033639858767)
      ·
        refine ⟨158725897173502550459788151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105817264782335033639858767 158725897173502550459788151)
        ·
          refine ⟨238088845760253825689682227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158725897173502550459788151 238088845760253825689682227)
          ·
            refine ⟨357133268640380738534523341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 238088845760253825689682227 357133268640380738534523341)
            ·
              refine ⟨133924975740142776950446253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 357133268640380738534523341 133924975740142776950446253)
              ·
                refine ⟨50221865902553541356417345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 133924975740142776950446253 50221865902553541356417345)
                ·
                  refine ⟨37666399426915156017313009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50221865902553541356417345 37666399426915156017313009)
                  ·
                    refine ⟨28249799570186367012984757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37666399426915156017313009 28249799570186367012984757)
                    ·
                      refine ⟨2648418709704971907467321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28249799570186367012984757 2648418709704971907467321)
                      ·
                        rfl

theorem cell23_5157777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 5].length) (baseStart_5157777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5157777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5157777 prefixEnd_5157777 := by exact prefixLift 5157777
  have htrace : WordTrace (prefixWord ++ tailWord_5157777) baseStart_5157777 baseEnd_5157777 := by
    simpa [prefixWord, tailWord_5157777, baseEnd_5157777] using wordTrace_append hprefix tailTrace_5157777
  have hstable : (prefixWord ++ tailWord_5157777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5157777).length < 2 ^ (prefixWord ++ tailWord_5157777).sum := by decide
  have hdescent : baseEnd_5157777 < baseStart_5157777 := by decide
  rcases family_descends (prefixWord ++ tailWord_5157777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5157782 : List Nat := [5, 3, 1, 1, 1, 1, 4, 1, 1, 1, 4]
def baseStart_5157782 : Nat := 118140960795 + 5157782 * 2 ^ 59
def prefixEnd_5157782 : Nat := 4983230072969 + 3 ^ 40 * 5157782 * 2
def baseEnd_5157782 : Nat := 2648421277108244387904799

theorem tailTrace_5157782 : CollatzResearch.WordTrace tailWord_5157782 prefixEnd_5157782 2648421277108244387904799 := by
  unfold tailWord_5157782
  simp only [CollatzResearch.WordTrace]
  refine ⟨11757485262515260492521725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 125413176133496111920231733 11757485262515260492521725)
  ·
    refine ⟨4409056973443222684695647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11757485262515260492521725 4409056973443222684695647)
    ·
      refine ⟨6613585460164834027043471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4409056973443222684695647 6613585460164834027043471)
      ·
        refine ⟨9920378190247251040565207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6613585460164834027043471 9920378190247251040565207)
        ·
          refine ⟨14880567285370876560847811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9920378190247251040565207 14880567285370876560847811)
          ·
            refine ⟨22320850928056314841271717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14880567285370876560847811 22320850928056314841271717)
            ·
              refine ⟨4185159549010559032738447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22320850928056314841271717 4185159549010559032738447)
              ·
                refine ⟨6277739323515838549107671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4185159549010559032738447 6277739323515838549107671)
                ·
                  refine ⟨9416608985273757823661507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6277739323515838549107671 9416608985273757823661507)
                  ·
                    refine ⟨14124913477910636735492261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9416608985273757823661507 14124913477910636735492261)
                    ·
                      refine ⟨2648421277108244387904799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14124913477910636735492261 2648421277108244387904799)
                      ·
                        rfl

theorem cell23_5157782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 4, 1, 1, 1, 4].length) (baseStart_5157782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5157782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5157782 prefixEnd_5157782 := by exact prefixLift 5157782
  have htrace : WordTrace (prefixWord ++ tailWord_5157782) baseStart_5157782 baseEnd_5157782 := by
    simpa [prefixWord, tailWord_5157782, baseEnd_5157782] using wordTrace_append hprefix tailTrace_5157782
  have hstable : (prefixWord ++ tailWord_5157782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5157782).length < 2 ^ (prefixWord ++ tailWord_5157782).sum := by decide
  have hdescent : baseEnd_5157782 < baseStart_5157782 := by decide
  rcases family_descends (prefixWord ++ tailWord_5157782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5157807 : List Nat := [1, 1, 2, 1, 2, 2, 2, 1, 3, 3, 5]
def baseStart_5157807 : Nat := 118140960795 + 5157807 * 2 ^ 59
def prefixEnd_5157807 : Nat := 4983230072969 + 3 ^ 40 * 5157807 * 2
def baseEnd_5157807 : Nat := 2648434114124606790092183

theorem tailTrace_5157807 : CollatzResearch.WordTrace tailWord_5157807 prefixEnd_5157807 2648434114124606790092183 := by
  unfold tailWord_5157807
  simp only [CollatzResearch.WordTrace]
  refine ⟨188120676025153597150007675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125413784016769064766671783 188120676025153597150007675)
  ·
    refine ⟨282181014037730395725011513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188120676025153597150007675 282181014037730395725011513)
    ·
      refine ⟨211635760528297796793758635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 282181014037730395725011513 211635760528297796793758635)
      ·
        refine ⟨317453640792446695190637953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211635760528297796793758635 317453640792446695190637953)
        ·
          refine ⟨238090230594335021392978465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 317453640792446695190637953 238090230594335021392978465)
          ·
            refine ⟨178567672945751266044733849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 238090230594335021392978465 178567672945751266044733849)
            ·
              refine ⟨133925754709313449533550387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 178567672945751266044733849 133925754709313449533550387)
              ·
                refine ⟨200888632063970174300325581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 133925754709313449533550387 200888632063970174300325581)
                ·
                  refine ⟨75333237023988815362622093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 200888632063970174300325581 75333237023988815362622093)
                  ·
                    refine ⟨28249963883995805760983285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 75333237023988815362622093 28249963883995805760983285)
                    ·
                      refine ⟨2648434114124606790092183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28249963883995805760983285 2648434114124606790092183)
                      ·
                        rfl

theorem cell23_5157807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 3, 3, 5].length) (baseStart_5157807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5157807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5157807 prefixEnd_5157807 := by exact prefixLift 5157807
  have htrace : WordTrace (prefixWord ++ tailWord_5157807) baseStart_5157807 baseEnd_5157807 := by
    simpa [prefixWord, tailWord_5157807, baseEnd_5157807] using wordTrace_append hprefix tailTrace_5157807
  have hstable : (prefixWord ++ tailWord_5157807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5157807).length < 2 ^ (prefixWord ++ tailWord_5157807).sum := by decide
  have hdescent : baseEnd_5157807 < baseStart_5157807 := by decide
  rcases family_descends (prefixWord ++ tailWord_5157807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5157838 : List Nat := [4, 1, 1, 1, 2, 3, 1, 2, 4, 2, 2]
def baseStart_5157838 : Nat := 118140960795 + 5157838 * 2 ^ 59
def prefixEnd_5157838 : Nat := 4983230072969 + 3 ^ 40 * 5157838 * 2
def baseEnd_5157838 : Nat := 2648450032024896168804541

theorem tailTrace_5157838 : CollatzResearch.WordTrace tailWord_5157838 prefixEnd_5157838 2648450032024896168804541 := by
  unfold tailWord_5157838
  simp only [CollatzResearch.WordTrace]
  refine ⟨23515225836005161180548271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125414537792027526296257445 23515225836005161180548271)
  ·
    refine ⟨35272838754007741770822407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23515225836005161180548271 35272838754007741770822407)
    ·
      refine ⟨52909258131011612656233611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35272838754007741770822407 52909258131011612656233611)
      ·
        refine ⟨79363887196517418984350417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52909258131011612656233611 79363887196517418984350417)
        ·
          refine ⟨59522915397388064238262813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79363887196517418984350417 59522915397388064238262813)
          ·
            refine ⟨22321093274020524089348555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59522915397388064238262813 22321093274020524089348555)
            ·
              refine ⟨33481639911030786134022833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22321093274020524089348555 33481639911030786134022833)
              ·
                refine ⟨25111229933273089600517125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33481639911030786134022833 25111229933273089600517125)
                ·
                  refine ⟨4708355612488704300096961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25111229933273089600517125 4708355612488704300096961)
                  ·
                    refine ⟨3531266709366528225072721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4708355612488704300096961 3531266709366528225072721)
                    ·
                      refine ⟨2648450032024896168804541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3531266709366528225072721 2648450032024896168804541)
                      ·
                        rfl

theorem cell23_5157838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 2, 4, 2, 2].length) (baseStart_5157838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5157838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5157838 prefixEnd_5157838 := by exact prefixLift 5157838
  have htrace : WordTrace (prefixWord ++ tailWord_5157838) baseStart_5157838 baseEnd_5157838 := by
    simpa [prefixWord, tailWord_5157838, baseEnd_5157838] using wordTrace_append hprefix tailTrace_5157838
  have hstable : (prefixWord ++ tailWord_5157838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5157838).length < 2 ^ (prefixWord ++ tailWord_5157838).sum := by decide
  have hdescent : baseEnd_5157838 < baseStart_5157838 := by decide
  rcases family_descends (prefixWord ++ tailWord_5157838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5157906 : List Nat := [3, 2, 5, 1, 1, 1, 2, 2, 2, 2, 2]
def baseStart_5157906 : Nat := 118140960795 + 5157906 * 2 ^ 59
def prefixEnd_5157906 : Nat := 4983230072969 + 3 ^ 40 * 5157906 * 2
def baseEnd_5157906 : Nat := 2648484948709401902754229

theorem tailTrace_5157906 : CollatzResearch.WordTrace tailWord_5157906 prefixEnd_5157906 2648484948709401902754229 := by
  unfold tailWord_5157906
  simp only [CollatzResearch.WordTrace]
  refine ⟨47031071712948734264465393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125416191234529958038574381 47031071712948734264465393)
  ·
    refine ⟨35273303784711550698349045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47031071712948734264465393 35273303784711550698349045)
    ·
      refine ⟨3306872229816707877970223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 35273303784711550698349045 3306872229816707877970223)
      ·
        refine ⟨4960308344725061816955335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3306872229816707877970223 4960308344725061816955335)
        ·
          refine ⟨7440462517087592725433003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4960308344725061816955335 7440462517087592725433003)
          ·
            refine ⟨11160693775631389088149505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7440462517087592725433003 11160693775631389088149505)
            ·
              refine ⟨8370520331723541816112129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11160693775631389088149505 8370520331723541816112129)
              ·
                refine ⟨6277890248792656362084097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8370520331723541816112129 6277890248792656362084097)
                ·
                  refine ⟨4708417686594492271563073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6277890248792656362084097 4708417686594492271563073)
                  ·
                    refine ⟨3531313264945869203672305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4708417686594492271563073 3531313264945869203672305)
                    ·
                      refine ⟨2648484948709401902754229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3531313264945869203672305 2648484948709401902754229)
                      ·
                        rfl

theorem cell23_5157906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_5157906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5157906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5157906 prefixEnd_5157906 := by exact prefixLift 5157906
  have htrace : WordTrace (prefixWord ++ tailWord_5157906) baseStart_5157906 baseEnd_5157906 := by
    simpa [prefixWord, tailWord_5157906, baseEnd_5157906] using wordTrace_append hprefix tailTrace_5157906
  have hstable : (prefixWord ++ tailWord_5157906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5157906).length < 2 ^ (prefixWord ++ tailWord_5157906).sum := by decide
  have hdescent : baseEnd_5157906 < baseStart_5157906 := by decide
  rcases family_descends (prefixWord ++ tailWord_5157906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5157914 : List Nat := [3, 1, 1, 3, 1, 2, 1, 1, 2, 3, 5]
def baseStart_5157914 : Nat := 118140960795 + 5157914 * 2 ^ 59
def prefixEnd_5157914 : Nat := 4983230072969 + 3 ^ 40 * 5157914 * 2
def baseEnd_5157914 : Nat := 2648489056554637871454191

theorem tailTrace_5157914 : CollatzResearch.WordTrace tailWord_5157914 prefixEnd_5157914 2648489056554637871454191 := by
  unfold tailWord_5157914
  simp only [CollatzResearch.WordTrace]
  refine ⟨47031144658941488606038199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125416385757177302949435197 47031144658941488606038199)
  ·
    refine ⟨70546716988412232909057299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47031144658941488606038199 70546716988412232909057299)
    ·
      refine ⟨105820075482618349363585949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70546716988412232909057299 105820075482618349363585949)
      ·
        refine ⟨39682528305981881011344731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105820075482618349363585949 39682528305981881011344731)
        ·
          refine ⟨59523792458972821517017097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39682528305981881011344731 59523792458972821517017097)
          ·
            refine ⟨44642844344229616137762823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59523792458972821517017097 44642844344229616137762823)
            ·
              refine ⟨66964266516344424206644235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44642844344229616137762823 66964266516344424206644235)
              ·
                refine ⟨100446399774516636309966353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66964266516344424206644235 100446399774516636309966353)
                ·
                  refine ⟨75334799830887477232474765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 100446399774516636309966353 75334799830887477232474765)
                  ·
                    refine ⟨28250549936582803962178037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 75334799830887477232474765 28250549936582803962178037)
                    ·
                      refine ⟨2648489056554637871454191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28250549936582803962178037 2648489056554637871454191)
                      ·
                        rfl

theorem cell23_5157914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 2, 3, 5].length) (baseStart_5157914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5157914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5157914 prefixEnd_5157914 := by exact prefixLift 5157914
  have htrace : WordTrace (prefixWord ++ tailWord_5157914) baseStart_5157914 baseEnd_5157914 := by
    simpa [prefixWord, tailWord_5157914, baseEnd_5157914] using wordTrace_append hprefix tailTrace_5157914
  have hstable : (prefixWord ++ tailWord_5157914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5157914).length < 2 ^ (prefixWord ++ tailWord_5157914).sum := by decide
  have hdescent : baseEnd_5157914 < baseStart_5157914 := by decide
  rcases family_descends (prefixWord ++ tailWord_5157914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5157948 : List Nat := [2, 2, 2, 2, 2, 2, 3, 1, 2, 2, 3]
def baseStart_5157948 : Nat := 118140960795 + 5157948 * 2 ^ 59
def prefixEnd_5157948 : Nat := 4983230072969 + 3 ^ 40 * 5157948 * 2
def baseEnd_5157948 : Nat := 2648506514896890738429035

theorem tailTrace_5157948 : CollatzResearch.WordTrace tailWord_5157948 prefixEnd_5157948 2648506514896890738429035 := by
  unfold tailWord_5157948
  simp only [CollatzResearch.WordTrace]
  refine ⟨94062909358821389115445249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125417212478428518820593665 94062909358821389115445249)
  ·
    refine ⟨70547182019116041836583937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94062909358821389115445249 70547182019116041836583937)
    ·
      refine ⟨52910386514337031377437953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70547182019116041836583937 52910386514337031377437953)
      ·
        refine ⟨39682789885752773533078465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52910386514337031377437953 39682789885752773533078465)
        ·
          refine ⟨29762092414314580149808849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39682789885752773533078465 29762092414314580149808849)
          ·
            refine ⟨22321569310735935112356637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29762092414314580149808849 22321569310735935112356637)
            ·
              refine ⟨8370588491525975667133739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22321569310735935112356637 8370588491525975667133739)
              ·
                refine ⟨12555882737288963500700609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8370588491525975667133739 12555882737288963500700609)
                ·
                  refine ⟨9416912052966722625525457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12555882737288963500700609 9416912052966722625525457)
                  ·
                    refine ⟨7062684039725041969144093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9416912052966722625525457 7062684039725041969144093)
                    ·
                      refine ⟨2648506514896890738429035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7062684039725041969144093 2648506514896890738429035)
                      ·
                        rfl

theorem cell23_5157948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 3, 1, 2, 2, 3].length) (baseStart_5157948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5157948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5157948 prefixEnd_5157948 := by exact prefixLift 5157948
  have htrace : WordTrace (prefixWord ++ tailWord_5157948) baseStart_5157948 baseEnd_5157948 := by
    simpa [prefixWord, tailWord_5157948, baseEnd_5157948] using wordTrace_append hprefix tailTrace_5157948
  have hstable : (prefixWord ++ tailWord_5157948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5157948).length < 2 ^ (prefixWord ++ tailWord_5157948).sum := by decide
  have hdescent : baseEnd_5157948 < baseStart_5157948 := by decide
  rcases family_descends (prefixWord ++ tailWord_5157948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5157958 : List Nat := [6, 1, 1, 1, 1, 2, 1, 1, 2, 1, 6]
def baseStart_5157958 : Nat := 118140960795 + 5157958 * 2 ^ 59
def prefixEnd_5157958 : Nat := 4983230072969 + 3 ^ 40 * 5157958 * 2
def baseEnd_5157958 : Nat := 2648511649703435699303989

theorem tailTrace_5157958 : CollatzResearch.WordTrace tailWord_5157958 prefixEnd_5157958 2648511649703435699303989 := by
  unfold tailWord_5157958
  simp only [CollatzResearch.WordTrace]
  refine ⟨5878943232737704685586079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 125417455631737699959169685 5878943232737704685586079)
  ·
    refine ⟨8818414849106557028379119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5878943232737704685586079 8818414849106557028379119)
    ·
      refine ⟨13227622273659835542568679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8818414849106557028379119 13227622273659835542568679)
      ·
        refine ⟨19841433410489753313853019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13227622273659835542568679 19841433410489753313853019)
        ·
          refine ⟨29762150115734629970779529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19841433410489753313853019 29762150115734629970779529)
          ·
            refine ⟨22321612586800972478084647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29762150115734629970779529 22321612586800972478084647)
            ·
              refine ⟨33482418880201458717126971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22321612586800972478084647 33482418880201458717126971)
              ·
                refine ⟨50223628320302188075690457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33482418880201458717126971 50223628320302188075690457)
                ·
                  refine ⟨37667721240226641056767843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50223628320302188075690457 37667721240226641056767843)
                  ·
                    refine ⟨56501581860339961585151765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37667721240226641056767843 56501581860339961585151765)
                    ·
                      refine ⟨2648511649703435699303989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56501581860339961585151765 2648511649703435699303989)
                      ·
                        rfl

theorem cell23_5157958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_5157958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5157958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5157958 prefixEnd_5157958 := by exact prefixLift 5157958
  have htrace : WordTrace (prefixWord ++ tailWord_5157958) baseStart_5157958 baseEnd_5157958 := by
    simpa [prefixWord, tailWord_5157958, baseEnd_5157958] using wordTrace_append hprefix tailTrace_5157958
  have hstable : (prefixWord ++ tailWord_5157958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5157958).length < 2 ^ (prefixWord ++ tailWord_5157958).sum := by decide
  have hdescent : baseEnd_5157958 < baseStart_5157958 := by decide
  rcases family_descends (prefixWord ++ tailWord_5157958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5157971 : List Nat := [1, 1, 1, 2, 1, 1, 2, 4, 3, 5, 2]
def baseStart_5157971 : Nat := 118140960795 + 5157971 * 2 ^ 59
def prefixEnd_5157971 : Nat := 4983230072969 + 3 ^ 40 * 5157971 * 2
def baseEnd_5157971 : Nat := 2648518324951944148441429

theorem tailTrace_5157971 : CollatzResearch.WordTrace tailWord_5157971 prefixEnd_5157971 2648518324951944148441429 := by
  unfold tailWord_5157971
  simp only [CollatzResearch.WordTrace]
  refine ⟨188126657596559453158977767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125417771731039635439318511 188126657596559453158977767)
  ·
    refine ⟨282189986394839179738466651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188126657596559453158977767 282189986394839179738466651)
    ·
      refine ⟨423284979592258769607699977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 282189986394839179738466651 423284979592258769607699977)
      ·
        refine ⟨317463734694194077205774983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 423284979592258769607699977 317463734694194077205774983)
        ·
          refine ⟨476195602041291115808662475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 317463734694194077205774983 476195602041291115808662475)
          ·
            refine ⟨714293403061936673712993713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 476195602041291115808662475 714293403061936673712993713)
            ·
              refine ⟨535720052296452505284745285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 714293403061936673712993713 535720052296452505284745285)
              ·
                refine ⟨100447509805584844740889741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 535720052296452505284745285 100447509805584844740889741)
                ·
                  refine ⟨37667816177094316777833653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 100447509805584844740889741 37667816177094316777833653)
                  ·
                    refine ⟨3531357766602592197921905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37667816177094316777833653 3531357766602592197921905)
                    ·
                      refine ⟨2648518324951944148441429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3531357766602592197921905 2648518324951944148441429)
                      ·
                        rfl

theorem cell23_5157971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 3, 5, 2].length) (baseStart_5157971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5157971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5157971 prefixEnd_5157971 := by exact prefixLift 5157971
  have htrace : WordTrace (prefixWord ++ tailWord_5157971) baseStart_5157971 baseEnd_5157971 := by
    simpa [prefixWord, tailWord_5157971, baseEnd_5157971] using wordTrace_append hprefix tailTrace_5157971
  have hstable : (prefixWord ++ tailWord_5157971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5157971).length < 2 ^ (prefixWord ++ tailWord_5157971).sum := by decide
  have hdescent : baseEnd_5157971 < baseStart_5157971 := by decide
  rcases family_descends (prefixWord ++ tailWord_5157971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5157998 : List Nat := [4, 1, 2, 2, 1, 2, 1, 4, 1, 5]
def baseStart_5157998 : Nat := 118140960795 + 5157998 * 2 ^ 59
def prefixEnd_5157998 : Nat := 4983230072969 + 3 ^ 40 * 5157998 * 2
def baseEnd_5157998 : Nat := 882844062976538514267935

theorem tailTrace_5157998 : CollatzResearch.WordTrace tailWord_5157998 prefixEnd_5157998 882844062976538514267935 := by
  unfold tailWord_5157998
  simp only [CollatzResearch.WordTrace]
  refine ⟨23515955295932704596276331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125418428244974424513473765 23515955295932704596276331)
  ·
    refine ⟨35273932943899056894414497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23515955295932704596276331 35273932943899056894414497)
    ·
      refine ⟨26455449707924292670810873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35273932943899056894414497 26455449707924292670810873)
      ·
        refine ⟨19841587280943219503108155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26455449707924292670810873 19841587280943219503108155)
        ·
          refine ⟨29762380921414829254662233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19841587280943219503108155 29762380921414829254662233)
          ·
            refine ⟨22321785691061121940996675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29762380921414829254662233 22321785691061121940996675)
            ·
              refine ⟨33482678536591682911495013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22321785691061121940996675 33482678536591682911495013)
              ·
                refine ⟨6278002225610940545905315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33482678536591682911495013 6278002225610940545905315)
                ·
                  refine ⟨9417003338416410818857973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6278002225610940545905315 9417003338416410818857973)
                  ·
                    refine ⟨882844062976538514267935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9417003338416410818857973 882844062976538514267935)
                    ·
                      rfl

theorem cell23_5157998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 4, 1, 5].length) (baseStart_5157998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5157998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5157998 prefixEnd_5157998 := by exact prefixLift 5157998
  have htrace : WordTrace (prefixWord ++ tailWord_5157998) baseStart_5157998 baseEnd_5157998 := by
    simpa [prefixWord, tailWord_5157998, baseEnd_5157998] using wordTrace_append hprefix tailTrace_5157998
  have hstable : (prefixWord ++ tailWord_5157998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5157998).length < 2 ^ (prefixWord ++ tailWord_5157998).sum := by decide
  have hdescent : baseEnd_5157998 < baseStart_5157998 := by decide
  rcases family_descends (prefixWord ++ tailWord_5157998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5158035 : List Nat := [1, 1, 1, 2, 1, 2, 7, 1, 3, 2, 2]
def baseStart_5158035 : Nat := 118140960795 + 5158035 * 2 ^ 59
def prefixEnd_5158035 : Nat := 4983230072969 + 3 ^ 40 * 5158035 * 2
def baseEnd_5158035 : Nat := 2648551187713831898041135

theorem tailTrace_5158035 : CollatzResearch.WordTrace tailWord_5158035 prefixEnd_5158035 2648551187713831898041135 := by
  unfold tailWord_5158035
  simp only [CollatzResearch.WordTrace]
  refine ⟨188128991868327592089307559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125419327912218394726205039 188128991868327592089307559)
  ·
    refine ⟨282193487802491388133961339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188128991868327592089307559 282193487802491388133961339)
    ·
      refine ⟨423290231703737082200942009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 282193487802491388133961339 423290231703737082200942009)
      ·
        refine ⟨317467673777802811650706507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 423290231703737082200942009 317467673777802811650706507)
        ·
          refine ⟨476201510666704217476059761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 317467673777802811650706507 476201510666704217476059761)
          ·
            refine ⟨357151133000028163107044821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 476201510666704217476059761 357151133000028163107044821)
            ·
              refine ⟨8370729679688160072821363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 357151133000028163107044821 8370729679688160072821363)
              ·
                refine ⟨12556094519532240109232045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8370729679688160072821363 12556094519532240109232045)
                ·
                  refine ⟨4708535444824590040962017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12556094519532240109232045 4708535444824590040962017)
                  ·
                    refine ⟨3531401583618442530721513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4708535444824590040962017 3531401583618442530721513)
                    ·
                      refine ⟨2648551187713831898041135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3531401583618442530721513 2648551187713831898041135)
                      ·
                        rfl

theorem cell23_5158035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 7, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 7, 1, 3, 2, 2].length) (baseStart_5158035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5158035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5158035 prefixEnd_5158035 := by exact prefixLift 5158035
  have htrace : WordTrace (prefixWord ++ tailWord_5158035) baseStart_5158035 baseEnd_5158035 := by
    simpa [prefixWord, tailWord_5158035, baseEnd_5158035] using wordTrace_append hprefix tailTrace_5158035
  have hstable : (prefixWord ++ tailWord_5158035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5158035).length < 2 ^ (prefixWord ++ tailWord_5158035).sum := by decide
  have hdescent : baseEnd_5158035 < baseStart_5158035 := by decide
  rcases family_descends (prefixWord ++ tailWord_5158035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5158051 : List Nat := [1, 1, 1, 4, 1, 1, 1, 2, 5, 3, 3]
def baseStart_5158051 : Nat := 118140960795 + 5158051 * 2 ^ 59
def prefixEnd_5158051 : Nat := 4983230072969 + 3 ^ 40 * 5158051 * 2
def baseEnd_5158051 : Nat := 2648559403404303835441061

theorem tailTrace_5158051 : CollatzResearch.WordTrace tailWord_5158051 prefixEnd_5158051 2648559403404303835441061 := by
  unfold tailWord_5158051
  simp only [CollatzResearch.WordTrace]
  refine ⟨188129575436269626821890007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125419716957513084547926671 188129575436269626821890007)
  ·
    refine ⟨282194363154404440232835011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188129575436269626821890007 282194363154404440232835011)
    ·
      refine ⟨423291544731606660349252517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 282194363154404440232835011 423291544731606660349252517)
      ·
        refine ⟨79367164637176248815484847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 423291544731606660349252517 79367164637176248815484847)
        ·
          refine ⟨119050746955764373223227271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79367164637176248815484847 119050746955764373223227271)
          ·
            refine ⟨178576120433646559834840907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119050746955764373223227271 178576120433646559834840907)
            ·
              refine ⟨267864180650469839752261361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 178576120433646559834840907 267864180650469839752261361)
              ·
                refine ⟨200898135487852379814196021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 267864180650469839752261361 200898135487852379814196021)
                ·
                  refine ⟨18834200201986160607580877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 200898135487852379814196021 18834200201986160607580877)
                  ·
                    refine ⟨7062825075744810227842829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18834200201986160607580877 7062825075744810227842829)
                    ·
                      refine ⟨2648559403404303835441061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7062825075744810227842829 2648559403404303835441061)
                      ·
                        rfl

theorem cell23_5158051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 5, 3, 3].length) (baseStart_5158051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5158051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5158051 prefixEnd_5158051 := by exact prefixLift 5158051
  have htrace : WordTrace (prefixWord ++ tailWord_5158051) baseStart_5158051 baseEnd_5158051 := by
    simpa [prefixWord, tailWord_5158051, baseEnd_5158051] using wordTrace_append hprefix tailTrace_5158051
  have hstable : (prefixWord ++ tailWord_5158051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5158051).length < 2 ^ (prefixWord ++ tailWord_5158051).sum := by decide
  have hdescent : baseEnd_5158051 < baseStart_5158051 := by decide
  rcases family_descends (prefixWord ++ tailWord_5158051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5158055 : List Nat := [1, 1, 6, 2, 1, 2, 1, 1, 3, 2, 3]
def baseStart_5158055 : Nat := 118140960795 + 5158055 * 2 ^ 59
def prefixEnd_5158055 : Nat := 4983230072969 + 3 ^ 40 * 5158055 * 2
def baseEnd_5158055 : Nat := 2648561457326921819791043

theorem tailTrace_5158055 : CollatzResearch.WordTrace tailWord_5158055 prefixEnd_5158055 2648561457326921819791043 := by
  unfold tailWord_5158055
  simp only [CollatzResearch.WordTrace]
  refine ⟨188129721328255135505035619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125419814218836757003357079 188129721328255135505035619)
  ·
    refine ⟨282194581992382703257553429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188129721328255135505035619 282194581992382703257553429)
    ·
      refine ⟨13227871030892939215197817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 282194581992382703257553429 13227871030892939215197817)
      ·
        refine ⟨9920903273169704411398363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13227871030892939215197817 9920903273169704411398363)
        ·
          refine ⟨14881354909754556617097545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9920903273169704411398363 14881354909754556617097545)
          ·
            refine ⟨11161016182315917462823159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14881354909754556617097545 11161016182315917462823159)
            ·
              refine ⟨16741524273473876194234739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11161016182315917462823159 16741524273473876194234739)
              ·
                refine ⟨25112286410210814291352109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16741524273473876194234739 25112286410210814291352109)
                ·
                  refine ⟨9417107403829055359257041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25112286410210814291352109 9417107403829055359257041)
                  ·
                    refine ⟨7062830552871791519442781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9417107403829055359257041 7062830552871791519442781)
                    ·
                      refine ⟨2648561457326921819791043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7062830552871791519442781 2648561457326921819791043)
                      ·
                        rfl

theorem cell23_5158055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_5158055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5158055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5158055 prefixEnd_5158055 := by exact prefixLift 5158055
  have htrace : WordTrace (prefixWord ++ tailWord_5158055) baseStart_5158055 baseEnd_5158055 := by
    simpa [prefixWord, tailWord_5158055, baseEnd_5158055] using wordTrace_append hprefix tailTrace_5158055
  have hstable : (prefixWord ++ tailWord_5158055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5158055).length < 2 ^ (prefixWord ++ tailWord_5158055).sum := by decide
  have hdescent : baseEnd_5158055 < baseStart_5158055 := by decide
  rcases family_descends (prefixWord ++ tailWord_5158055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5158058 : List Nat := [3, 1, 5, 1, 1, 1, 2, 9]
def baseStart_5158058 : Nat := 118140960795 + 5158058 * 2 ^ 59
def prefixEnd_5158058 : Nat := 4983230072969 + 3 ^ 40 * 5158058 * 2
def baseEnd_5158058 : Nat := 98094925843292048446427

theorem tailTrace_5158058 : CollatzResearch.WordTrace tailWord_5158058 prefixEnd_5158058 98094925843292048446427 := by
  unfold tailWord_5158058
  simp only [CollatzResearch.WordTrace]
  refine ⟨47032457686811066754348707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125419887164829511344929885 47032457686811066754348707)
  ·
    refine ⟨70548686530216600131523061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47032457686811066754348707 70548686530216600131523061)
    ·
      refine ⟨6613939362207806262330287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 70548686530216600131523061 6613939362207806262330287)
      ·
        refine ⟨9920909043311709393495431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6613939362207806262330287 9920909043311709393495431)
        ·
          refine ⟨14881363564967564090243147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9920909043311709393495431 14881363564967564090243147)
          ·
            refine ⟨22322045347451346135364721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14881363564967564090243147 22322045347451346135364721)
            ·
              refine ⟨16741534010588509601523541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22322045347451346135364721 16741534010588509601523541)
              ·
                refine ⟨98094925843292048446427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16741534010588509601523541 98094925843292048446427)
                ·
                  rfl

theorem cell23_5158058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 9].length) (baseStart_5158058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5158058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5158058 prefixEnd_5158058 := by exact prefixLift 5158058
  have htrace : WordTrace (prefixWord ++ tailWord_5158058) baseStart_5158058 baseEnd_5158058 := by
    simpa [prefixWord, tailWord_5158058, baseEnd_5158058] using wordTrace_append hprefix tailTrace_5158058
  have hstable : (prefixWord ++ tailWord_5158058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5158058).length < 2 ^ (prefixWord ++ tailWord_5158058).sum := by decide
  have hdescent : baseEnd_5158058 < baseStart_5158058 := by decide
  rcases family_descends (prefixWord ++ tailWord_5158058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5158111 : List Nat := [1, 1, 2, 3, 2, 1, 2, 1, 4, 1, 5]
def baseStart_5158111 : Nat := 118140960795 + 5158111 * 2 ^ 59
def prefixEnd_5158111 : Nat := 4983230072969 + 3 ^ 40 * 5158111 * 2
def baseEnd_5158111 : Nat := 2648590212243573600690785

theorem tailTrace_5158111 : CollatzResearch.WordTrace tailWord_5158111 prefixEnd_5158111 2648590212243573600690785 := by
  unfold tailWord_5158111
  simp only [CollatzResearch.WordTrace]
  refine ⟨188131763816052257069074187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125421175877368171379382791 188131763816052257069074187)
  ·
    refine ⟨282197645724078385603611281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188131763816052257069074187 282197645724078385603611281)
    ·
      refine ⟨211648234293058789202708461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 282197645724078385603611281 211648234293058789202708461)
      ·
        refine ⟨79368087859897045951015673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 211648234293058789202708461 79368087859897045951015673)
        ·
          refine ⟨59526065894922784463261755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79368087859897045951015673 59526065894922784463261755)
          ·
            refine ⟨89289098842384176694892633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59526065894922784463261755 89289098842384176694892633)
            ·
              refine ⟨66966824131788132521169475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89289098842384176694892633 66966824131788132521169475)
              ·
                refine ⟨100450236197682198781754213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66966824131788132521169475 100450236197682198781754213)
                ·
                  refine ⟨18834419287065412271578915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 100450236197682198781754213 18834419287065412271578915)
                  ·
                    refine ⟨28251628930598118407368373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18834419287065412271578915 28251628930598118407368373)
                    ·
                      refine ⟨2648590212243573600690785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28251628930598118407368373 2648590212243573600690785)
                      ·
                        rfl

theorem cell23_5158111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 4, 1, 5].length) (baseStart_5158111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5158111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5158111 prefixEnd_5158111 := by exact prefixLift 5158111
  have htrace : WordTrace (prefixWord ++ tailWord_5158111) baseStart_5158111 baseEnd_5158111 := by
    simpa [prefixWord, tailWord_5158111, baseEnd_5158111] using wordTrace_append hprefix tailTrace_5158111
  have hstable : (prefixWord ++ tailWord_5158111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5158111).length < 2 ^ (prefixWord ++ tailWord_5158111).sum := by decide
  have hdescent : baseEnd_5158111 < baseStart_5158111 := by decide
  rcases family_descends (prefixWord ++ tailWord_5158111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5158121 : List Nat := [1, 2, 1, 1, 1, 2, 2, 1, 6, 2, 4]
def baseStart_5158121 : Nat := 118140960795 + 5158121 * 2 ^ 59
def prefixEnd_5158121 : Nat := 4983230072969 + 3 ^ 40 * 5158121 * 2
def baseEnd_5158121 : Nat := 2648595347050118561565739

theorem tailTrace_5158121 : CollatzResearch.WordTrace tailWord_5158121 prefixEnd_5158121 2648595347050118561565739 := by
  unfold tailWord_5158121
  simp only [CollatzResearch.WordTrace]
  refine ⟨188132128546016028776938217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125421419030677352517958811 188132128546016028776938217)
  ·
    refine ⟨141099096409512021582703663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188132128546016028776938217 141099096409512021582703663)
    ·
      refine ⟨211648644614268032374055495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141099096409512021582703663 211648644614268032374055495)
      ·
        refine ⟨317472966921402048561083243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211648644614268032374055495 317472966921402048561083243)
        ·
          refine ⟨476209450382103072841624865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 317472966921402048561083243 476209450382103072841624865)
          ·
            refine ⟨357157087786577304631218649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 476209450382103072841624865 357157087786577304631218649)
            ·
              refine ⟨267867815839932978473413987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 357157087786577304631218649 267867815839932978473413987)
              ·
                refine ⟨401801723759899467710120981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 267867815839932978473413987 401801723759899467710120981)
                ·
                  refine ⟨18834455801245287548911921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 401801723759899467710120981 18834455801245287548911921)
                  ·
                    refine ⟨14125841850933965661683941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18834455801245287548911921 14125841850933965661683941)
                    ·
                      refine ⟨2648595347050118561565739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14125841850933965661683941 2648595347050118561565739)
                      ·
                        rfl

theorem cell23_5158121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 6, 2, 4].length) (baseStart_5158121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5158121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5158121 prefixEnd_5158121 := by exact prefixLift 5158121
  have htrace : WordTrace (prefixWord ++ tailWord_5158121) baseStart_5158121 baseEnd_5158121 := by
    simpa [prefixWord, tailWord_5158121, baseEnd_5158121] using wordTrace_append hprefix tailTrace_5158121
  have hstable : (prefixWord ++ tailWord_5158121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5158121).length < 2 ^ (prefixWord ++ tailWord_5158121).sum := by decide
  have hdescent : baseEnd_5158121 < baseStart_5158121 := by decide
  rcases family_descends (prefixWord ++ tailWord_5158121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5158148 : List Nat := [2, 3, 2, 2, 2, 1, 1, 3, 7]
def baseStart_5158148 : Nat := 118140960795 + 5158148 * 2 ^ 59
def prefixEnd_5158148 : Nat := 4983230072969 + 3 ^ 40 * 5158148 * 2
def baseEnd_5158148 : Nat := 294289912336421106214235

theorem tailTrace_5158148 : CollatzResearch.WordTrace tailWord_5158148 prefixEnd_5158148 294289912336421106214235 := by
  unfold tailWord_5158148
  simp only [CollatzResearch.WordTrace]
  refine ⟨94066556658459106194085549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125422075544612141592114065 94066556658459106194085549)
  ·
    refine ⟨35274958746922164822782081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94066556658459106194085549 35274958746922164822782081)
    ·
      refine ⟨26456219060191623617086561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35274958746922164822782081 26456219060191623617086561)
      ·
        refine ⟨19842164295143717712814921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26456219060191623617086561 19842164295143717712814921)
        ·
          refine ⟨14881623221357788284611191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19842164295143717712814921 14881623221357788284611191)
          ·
            refine ⟨22322434832036682426916787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14881623221357788284611191 22322434832036682426916787)
            ·
              refine ⟨33483652248055023640375181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22322434832036682426916787 33483652248055023640375181)
              ·
                refine ⟨12556369593020633865140693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33483652248055023640375181 12556369593020633865140693)
                ·
                  refine ⟨294289912336421106214235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12556369593020633865140693 294289912336421106214235)
                  ·
                    rfl

theorem cell23_5158148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 3, 7].length) (baseStart_5158148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5158148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5158148 prefixEnd_5158148 := by exact prefixLift 5158148
  have htrace : WordTrace (prefixWord ++ tailWord_5158148) baseStart_5158148 baseEnd_5158148 := by
    simpa [prefixWord, tailWord_5158148, baseEnd_5158148] using wordTrace_append hprefix tailTrace_5158148
  have hstable : (prefixWord ++ tailWord_5158148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5158148).length < 2 ^ (prefixWord ++ tailWord_5158148).sum := by decide
  have hdescent : baseEnd_5158148 < baseStart_5158148 := by decide
  rcases family_descends (prefixWord ++ tailWord_5158148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5158161 : List Nat := [1, 2, 2, 1, 1, 4, 1, 1, 3, 7]
def baseStart_5158161 : Nat := 118140960795 + 5158161 * 2 ^ 59
def prefixEnd_5158161 : Nat := 4983230072969 + 3 ^ 40 * 5158161 * 2
def baseEnd_5158161 : Nat := 882871962092099468355185

theorem tailTrace_5158161 : CollatzResearch.WordTrace tailWord_5158161 prefixEnd_5158161 882871962092099468355185 := by
  unfold tailWord_5158161
  simp only [CollatzResearch.WordTrace]
  refine ⟨188133587465871115608394337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125422391643914077072262891 188133587465871115608394337)
  ·
    refine ⟨141100190599403336706295753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188133587465871115608394337 141100190599403336706295753)
    ·
      refine ⟨105825142949552502529721815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141100190599403336706295753 105825142949552502529721815)
      ·
        refine ⟨158737714424328753794582723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105825142949552502529721815 158737714424328753794582723)
        ·
          refine ⟨238106571636493130691874085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158737714424328753794582723 238106571636493130691874085)
          ·
            refine ⟨44644982181842462004726391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 238106571636493130691874085 44644982181842462004726391)
            ·
              refine ⟨66967473272763693007089587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44644982181842462004726391 66967473272763693007089587)
              ·
                refine ⟨100451209909145539510634381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66967473272763693007089587 100451209909145539510634381)
                ·
                  refine ⟨37669203715929577316487893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 100451209909145539510634381 37669203715929577316487893)
                  ·
                    refine ⟨882871962092099468355185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37669203715929577316487893 882871962092099468355185)
                    ·
                      rfl

theorem cell23_5158161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 7].length) (baseStart_5158161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5158161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5158161 prefixEnd_5158161 := by exact prefixLift 5158161
  have htrace : WordTrace (prefixWord ++ tailWord_5158161) baseStart_5158161 baseEnd_5158161 := by
    simpa [prefixWord, tailWord_5158161, baseEnd_5158161] using wordTrace_append hprefix tailTrace_5158161
  have hstable : (prefixWord ++ tailWord_5158161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5158161).length < 2 ^ (prefixWord ++ tailWord_5158161).sum := by decide
  have hdescent : baseEnd_5158161 < baseStart_5158161 := by decide
  rcases family_descends (prefixWord ++ tailWord_5158161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5158171 : List Nat := [1, 1, 1, 1, 1, 1, 5, 2, 3, 2, 5]
def baseStart_5158171 : Nat := 118140960795 + 5158171 * 2 ^ 59
def prefixEnd_5158171 : Nat := 4983230072969 + 3 ^ 40 * 5158171 * 2
def baseEnd_5158171 : Nat := 2648621021082843365940509

theorem tailTrace_5158171 : CollatzResearch.WordTrace tailWord_5158171 prefixEnd_5158171 2648621021082843365940509 := by
  unfold tailWord_5158171
  simp only [CollatzResearch.WordTrace]
  refine ⟨188133952195834887316258367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125422634797223258210838911 188133952195834887316258367)
  ·
    refine ⟨282200928293752330974387551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188133952195834887316258367 282200928293752330974387551)
    ·
      refine ⟨423301392440628496461581327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 282200928293752330974387551 423301392440628496461581327)
      ·
        refine ⟨634952088660942744692371991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 423301392440628496461581327 634952088660942744692371991)
        ·
          refine ⟨952428132991414117038557987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 634952088660942744692371991 952428132991414117038557987)
          ·
            refine ⟨1428642199487121175557836981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 952428132991414117038557987 1428642199487121175557836981)
            ·
              refine ⟨133935206201917610208547217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1428642199487121175557836981 133935206201917610208547217)
              ·
                refine ⟨100451404651438207656410413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 133935206201917610208547217 100451404651438207656410413)
                ·
                  refine ⟨37669276744289327871153905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 100451404651438207656410413 37669276744289327871153905)
                  ·
                    refine ⟨28251957558216995903365429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37669276744289327871153905 28251957558216995903365429)
                    ·
                      refine ⟨2648621021082843365940509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28251957558216995903365429 2648621021082843365940509)
                      ·
                        rfl

theorem cell23_5158171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 3, 2, 5].length) (baseStart_5158171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5158171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5158171 prefixEnd_5158171 := by exact prefixLift 5158171
  have htrace : WordTrace (prefixWord ++ tailWord_5158171) baseStart_5158171 baseEnd_5158171 := by
    simpa [prefixWord, tailWord_5158171, baseEnd_5158171] using wordTrace_append hprefix tailTrace_5158171
  have hstable : (prefixWord ++ tailWord_5158171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5158171).length < 2 ^ (prefixWord ++ tailWord_5158171).sum := by decide
  have hdescent : baseEnd_5158171 < baseStart_5158171 := by decide
  rcases family_descends (prefixWord ++ tailWord_5158171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5158218 : List Nat := [3, 1, 2, 1, 1, 1, 1, 3, 3, 4, 3]
def baseStart_5158218 : Nat := 118140960795 + 5158218 * 2 ^ 59
def prefixEnd_5158218 : Nat := 4983230072969 + 3 ^ 40 * 5158218 * 2
def baseEnd_5158218 : Nat := 2648645154673604682052793

theorem tailTrace_5158218 : CollatzResearch.WordTrace tailWord_5158218 prefixEnd_5158218 2648645154673604682052793 := by
  unfold tailWord_5158218
  simp only [CollatzResearch.WordTrace]
  refine ⟨47033916606666153585804827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125423777617776409562146205 47033916606666153585804827)
  ·
    refine ⟨70550874909999230378707241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47033916606666153585804827 70550874909999230378707241)
    ·
      refine ⟨52913156182499422784030431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70550874909999230378707241 52913156182499422784030431)
      ·
        refine ⟨79369734273749134176045647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52913156182499422784030431 79369734273749134176045647)
        ·
          refine ⟨119054601410623701264068471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79369734273749134176045647 119054601410623701264068471)
          ·
            refine ⟨178581902115935551896102707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119054601410623701264068471 178581902115935551896102707)
            ·
              refine ⟨267872853173903327844154061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 178581902115935551896102707 267872853173903327844154061)
              ·
                refine ⟨100452319940213747941557773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 267872853173903327844154061 100452319940213747941557773)
                ·
                  refine ⟨37669619977580155478084165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 100452319940213747941557773 37669619977580155478084165)
                  ·
                    refine ⟨7063053745796279152140781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37669619977580155478084165 7063053745796279152140781)
                    ·
                      refine ⟨2648645154673604682052793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7063053745796279152140781 2648645154673604682052793)
                      ·
                        rfl

theorem cell23_5158218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 3, 4, 3].length) (baseStart_5158218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5158218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5158218 prefixEnd_5158218 := by exact prefixLift 5158218
  have htrace : WordTrace (prefixWord ++ tailWord_5158218) baseStart_5158218 baseEnd_5158218 := by
    simpa [prefixWord, tailWord_5158218, baseEnd_5158218] using wordTrace_append hprefix tailTrace_5158218
  have hstable : (prefixWord ++ tailWord_5158218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5158218).length < 2 ^ (prefixWord ++ tailWord_5158218).sum := by decide
  have hdescent : baseEnd_5158218 < baseStart_5158218 := by decide
  rcases family_descends (prefixWord ++ tailWord_5158218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5158258 : List Nat := [3, 2, 1, 2, 1, 2, 2, 1, 1, 2, 6]
def baseStart_5158258 : Nat := 118140960795 + 5158258 * 2 ^ 59
def prefixEnd_5158258 : Nat := 4983230072969 + 3 ^ 40 * 5158258 * 2
def baseEnd_5158258 : Nat := 2648665693899784525552609

theorem tailTrace_5158258 : CollatzResearch.WordTrace tailWord_5158258 prefixEnd_5158258 2648665693899784525552609 := by
  unfold tailWord_5158258
  simp only [CollatzResearch.WordTrace]
  refine ⟨47034281336629925293668857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125424750231013134116450285 47034281336629925293668857)
  ·
    refine ⟨35275711002472443970251643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47034281336629925293668857 35275711002472443970251643)
    ·
      refine ⟨52913566503708665955377465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35275711002472443970251643 52913566503708665955377465)
      ·
        refine ⟨39685174877781499466533099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52913566503708665955377465 39685174877781499466533099)
        ·
          refine ⟨59527762316672249199799649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39685174877781499466533099 59527762316672249199799649)
          ·
            refine ⟨44645821737504186899849737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59527762316672249199799649 44645821737504186899849737)
            ·
              refine ⟨33484366303128140174887303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44645821737504186899849737 33484366303128140174887303)
              ·
                refine ⟨50226549454692210262330955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33484366303128140174887303 50226549454692210262330955)
                ·
                  refine ⟨75339824182038315393496433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50226549454692210262330955 75339824182038315393496433)
                  ·
                    refine ⟨56504868136528736545122325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 75339824182038315393496433 56504868136528736545122325)
                    ·
                      refine ⟨2648665693899784525552609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56504868136528736545122325 2648665693899784525552609)
                      ·
                        rfl

theorem cell23_5158258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 1, 1, 2, 6].length) (baseStart_5158258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5158258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5158258 prefixEnd_5158258 := by exact prefixLift 5158258
  have htrace : WordTrace (prefixWord ++ tailWord_5158258) baseStart_5158258 baseEnd_5158258 := by
    simpa [prefixWord, tailWord_5158258, baseEnd_5158258] using wordTrace_append hprefix tailTrace_5158258
  have hstable : (prefixWord ++ tailWord_5158258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5158258).length < 2 ^ (prefixWord ++ tailWord_5158258).sum := by decide
  have hdescent : baseEnd_5158258 < baseStart_5158258 := by decide
  rcases family_descends (prefixWord ++ tailWord_5158258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5158268 : List Nat := [2, 2, 2, 1, 1, 1, 3, 1, 5, 5]
def baseStart_5158268 : Nat := 118140960795 + 5158268 * 2 ^ 59
def prefixEnd_5158268 : Nat := 4983230072969 + 3 ^ 40 * 5158268 * 2
def baseEnd_5158268 : Nat := 882890276235443162142521

theorem tailTrace_5158268 : CollatzResearch.WordTrace tailWord_5158268 prefixEnd_5158268 882890276235443162142521 := by
  unfold tailWord_5158268
  simp only [CollatzResearch.WordTrace]
  refine ⟨94068745038241736441269729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125424993384322315255026305 94068745038241736441269729)
  ·
    refine ⟨70551558778681302330952297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94068745038241736441269729 70551558778681302330952297)
    ·
      refine ⟨52913669084010976748214223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70551558778681302330952297 52913669084010976748214223)
      ·
        refine ⟨79370503626016465122321335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52913669084010976748214223 79370503626016465122321335)
        ·
          refine ⟨119055755439024697683482003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79370503626016465122321335 119055755439024697683482003)
          ·
            refine ⟨178583633158537046525223005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119055755439024697683482003 178583633158537046525223005)
            ·
              refine ⟨66968862434451392446958627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 178583633158537046525223005 66968862434451392446958627)
              ·
                refine ⟨100453293651677088670437941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66968862434451392446958627 100453293651677088670437941)
                ·
                  refine ⟨9417496279844727062853557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 100453293651677088670437941 9417496279844727062853557)
                  ·
                    refine ⟨882890276235443162142521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9417496279844727062853557 882890276235443162142521)
                    ·
                      rfl

theorem cell23_5158268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 5, 5].length) (baseStart_5158268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5158268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5158268 prefixEnd_5158268 := by exact prefixLift 5158268
  have htrace : WordTrace (prefixWord ++ tailWord_5158268) baseStart_5158268 baseEnd_5158268 := by
    simpa [prefixWord, tailWord_5158268, baseEnd_5158268] using wordTrace_append hprefix tailTrace_5158268
  have hstable : (prefixWord ++ tailWord_5158268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5158268).length < 2 ^ (prefixWord ++ tailWord_5158268).sum := by decide
  have hdescent : baseEnd_5158268 < baseStart_5158268 := by decide
  rcases family_descends (prefixWord ++ tailWord_5158268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5158286 : List Nat := [4, 1, 1, 4, 3, 1, 1, 1, 2, 2, 3]
def baseStart_5158286 : Nat := 118140960795 + 5158286 * 2 ^ 59
def prefixEnd_5158286 : Nat := 4983230072969 + 3 ^ 40 * 5158286 * 2
def baseEnd_5158286 : Nat := 2648680071358110416002481

theorem tailTrace_5158286 : CollatzResearch.WordTrace tailWord_5158286 prefixEnd_5158286 2648680071358110416002481 := by
  unfold tailWord_5158286
  simp only [CollatzResearch.WordTrace]
  refine ⟨23517268323802282744586839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125425431060278841304463141 23517268323802282744586839)
  ·
    refine ⟨35275902485703424116880259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23517268323802282744586839 35275902485703424116880259)
    ·
      refine ⟨52913853728555136175320389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35275902485703424116880259 52913853728555136175320389)
      ·
        refine ⟨9921347574104088032872573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52913853728555136175320389 9921347574104088032872573)
        ·
          refine ⟨3720505340289033012327215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9921347574104088032872573 3720505340289033012327215)
          ·
            refine ⟨5580758010433549518490823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3720505340289033012327215 5580758010433549518490823)
            ·
              refine ⟨8371137015650324277736235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5580758010433549518490823 8371137015650324277736235)
              ·
                refine ⟨12556705523475486416604353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8371137015650324277736235 12556705523475486416604353)
                ·
                  refine ⟨9417529142606614812453265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12556705523475486416604353 9417529142606614812453265)
                  ·
                    refine ⟨7063146856954961109339949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9417529142606614812453265 7063146856954961109339949)
                    ·
                      refine ⟨2648680071358110416002481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7063146856954961109339949 2648680071358110416002481)
                      ·
                        rfl

theorem cell23_5158286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 1, 1, 2, 2, 3].length) (baseStart_5158286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5158286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5158286 prefixEnd_5158286 := by exact prefixLift 5158286
  have htrace : WordTrace (prefixWord ++ tailWord_5158286) baseStart_5158286 baseEnd_5158286 := by
    simpa [prefixWord, tailWord_5158286, baseEnd_5158286] using wordTrace_append hprefix tailTrace_5158286
  have hstable : (prefixWord ++ tailWord_5158286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5158286).length < 2 ^ (prefixWord ++ tailWord_5158286).sum := by decide
  have hdescent : baseEnd_5158286 < baseStart_5158286 := by decide
  rcases family_descends (prefixWord ++ tailWord_5158286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5158325 : List Nat := [1, 3, 3, 2, 2, 1, 1, 1, 3, 1, 5]
def baseStart_5158325 : Nat := 118140960795 + 5158325 * 2 ^ 59
def prefixEnd_5158325 : Nat := 4983230072969 + 3 ^ 40 * 5158325 * 2
def baseEnd_5158325 : Nat := 2648700097103635763414801

theorem tailTrace_5158325 : CollatzResearch.WordTrace tailWord_5158325 prefixEnd_5158325 2648700097103635763414801 := by
  unfold tailWord_5158325
  simp only [CollatzResearch.WordTrace]
  refine ⟨188139569037276971617364429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125426379358184647744909619 188139569037276971617364429)
  ·
    refine ⟨70552338388978864356511661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 188139569037276971617364429 70552338388978864356511661)
    ·
      refine ⟨26457126895867074133691873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70552338388978864356511661 26457126895867074133691873)
      ·
        refine ⟨19842845171900305600268905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26457126895867074133691873 19842845171900305600268905)
        ·
          refine ⟨14882133878925229200201679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19842845171900305600268905 14882133878925229200201679)
          ·
            refine ⟨22323200818387843800302519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14882133878925229200201679 22323200818387843800302519)
            ·
              refine ⟨33484801227581765700453779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22323200818387843800302519 33484801227581765700453779)
              ·
                refine ⟨50227201841372648550680669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33484801227581765700453779 50227201841372648550680669)
                ·
                  refine ⟨18835200690514743206505251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50227201841372648550680669 18835200690514743206505251)
                  ·
                    refine ⟨28252801035772114809757877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18835200690514743206505251 28252801035772114809757877)
                    ·
                      refine ⟨2648700097103635763414801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28252801035772114809757877 2648700097103635763414801)
                      ·
                        rfl

theorem cell23_5158325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_5158325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5158325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5158325 prefixEnd_5158325 := by exact prefixLift 5158325
  have htrace : WordTrace (prefixWord ++ tailWord_5158325) baseStart_5158325 baseEnd_5158325 := by
    simpa [prefixWord, tailWord_5158325, baseEnd_5158325] using wordTrace_append hprefix tailTrace_5158325
  have hstable : (prefixWord ++ tailWord_5158325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5158325).length < 2 ^ (prefixWord ++ tailWord_5158325).sum := by decide
  have hdescent : baseEnd_5158325 < baseStart_5158325 := by decide
  rcases family_descends (prefixWord ++ tailWord_5158325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5158432 : List Nat := [2, 1, 1, 6, 1, 1, 1, 1, 2, 4, 3]
def baseStart_5158432 : Nat := 118140960795 + 5158432 * 2 ^ 59
def prefixEnd_5158432 : Nat := 4983230072969 + 3 ^ 40 * 5158432 * 2
def baseEnd_5158432 : Nat := 2648755039533666844776809

theorem tailTrace_5158432 : CollatzResearch.WordTrace tailWord_5158432 prefixEnd_5158432 2648755039533666844776809 := by
  unfold tailWord_5158432
  simp only [CollatzResearch.WordTrace]
  refine ⟨94071735823944664445754775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125428981098592885927673033 94071735823944664445754775)
  ·
    refine ⟨141107603735916996668632163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94071735823944664445754775 141107603735916996668632163)
    ·
      refine ⟨211661405603875495002948245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141107603735916996668632163 211661405603875495002948245)
      ·
        refine ⟨9921628387681663828263199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 211661405603875495002948245 9921628387681663828263199)
        ·
          refine ⟨14882442581522495742394799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9921628387681663828263199 14882442581522495742394799)
          ·
            refine ⟨22323663872283743613592199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14882442581522495742394799 22323663872283743613592199)
            ·
              refine ⟨33485495808425615420388299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22323663872283743613592199 33485495808425615420388299)
              ·
                refine ⟨50228243712638423130582449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33485495808425615420388299 50228243712638423130582449)
                ·
                  refine ⟨37671182784478817347936837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50228243712638423130582449 37671182784478817347936837)
                  ·
                    refine ⟨7063346772089778252738157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37671182784478817347936837 7063346772089778252738157)
                    ·
                      refine ⟨2648755039533666844776809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7063346772089778252738157 2648755039533666844776809)
                      ·
                        rfl

theorem cell23_5158432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_5158432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5158432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5158432 prefixEnd_5158432 := by exact prefixLift 5158432
  have htrace : WordTrace (prefixWord ++ tailWord_5158432) baseStart_5158432 baseEnd_5158432 := by
    simpa [prefixWord, tailWord_5158432, baseEnd_5158432] using wordTrace_append hprefix tailTrace_5158432
  have hstable : (prefixWord ++ tailWord_5158432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5158432).length < 2 ^ (prefixWord ++ tailWord_5158432).sum := by decide
  have hdescent : baseEnd_5158432 < baseStart_5158432 := by decide
  rcases family_descends (prefixWord ++ tailWord_5158432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5158442 : List Nat := [3, 1, 4, 1, 1, 1, 3, 1, 2, 2, 4]
def baseStart_5158442 : Nat := 118140960795 + 5158442 * 2 ^ 59
def prefixEnd_5158442 : Nat := 4983230072969 + 3 ^ 40 * 5158442 * 2
def baseEnd_5158442 : Nat := 2648760174340211805651763

theorem tailTrace_5158442 : CollatzResearch.WordTrace tailWord_5158442 prefixEnd_5158442 2648760174340211805651763 := by
  unfold tailWord_5158442
  simp only [CollatzResearch.WordTrace]
  refine ⟨47035959094463275149843395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125429224251902067066249053 47035959094463275149843395)
  ·
    refine ⟨70553938641694912724765093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47035959094463275149843395 70553938641694912724765093)
    ·
      refine ⟨13228863495317796135893455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70553938641694912724765093 13228863495317796135893455)
      ·
        refine ⟨19843295242976694203840183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13228863495317796135893455 19843295242976694203840183)
        ·
          refine ⟨29764942864465041305760275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19843295242976694203840183 29764942864465041305760275)
          ·
            refine ⟨44647414296697561958640413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29764942864465041305760275 44647414296697561958640413)
            ·
              refine ⟨16742780361261585734490155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44647414296697561958640413 16742780361261585734490155)
              ·
                refine ⟨25114170541892378601735233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16742780361261585734490155 25114170541892378601735233)
                ·
                  refine ⟨18835627906419283951301425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25114170541892378601735233 18835627906419283951301425)
                  ·
                    refine ⟨14126720929814462963476069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18835627906419283951301425 14126720929814462963476069)
                    ·
                      refine ⟨2648760174340211805651763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14126720929814462963476069 2648760174340211805651763)
                      ·
                        rfl

theorem cell23_5158442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_5158442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5158442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5158442 prefixEnd_5158442 := by exact prefixLift 5158442
  have htrace : WordTrace (prefixWord ++ tailWord_5158442) baseStart_5158442 baseEnd_5158442 := by
    simpa [prefixWord, tailWord_5158442, baseEnd_5158442] using wordTrace_append hprefix tailTrace_5158442
  have hstable : (prefixWord ++ tailWord_5158442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5158442).length < 2 ^ (prefixWord ++ tailWord_5158442).sum := by decide
  have hdescent : baseEnd_5158442 < baseStart_5158442 := by decide
  rcases family_descends (prefixWord ++ tailWord_5158442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5158446 : List Nat := [4, 1, 3, 1, 2, 2, 2, 1, 1, 4, 2]
def baseStart_5158446 : Nat := 118140960795 + 5158446 * 2 ^ 59
def prefixEnd_5158446 : Nat := 4983230072969 + 3 ^ 40 * 5158446 * 2
def baseEnd_5158446 : Nat := 2648762228262829790001745

theorem tailTrace_5158446 : CollatzResearch.WordTrace tailWord_5158446 prefixEnd_5158446 2648762228262829790001745 := by
  unfold tailWord_5158446
  simp only [CollatzResearch.WordTrace]
  refine ⟨23517997783729826160314899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125429321513225739521679461 23517997783729826160314899)
  ·
    refine ⟨35276996675594739240472349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23517997783729826160314899 35276996675594739240472349)
    ·
      refine ⟨13228873753348027215177131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35276996675594739240472349 13228873753348027215177131)
      ·
        refine ⟨19843310630022040822765697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13228873753348027215177131 19843310630022040822765697)
        ·
          refine ⟨14882482972516530617074273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19843310630022040822765697 14882482972516530617074273)
          ·
            refine ⟨11161862229387397962805705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14882482972516530617074273 11161862229387397962805705)
            ·
              refine ⟨8371396672040548472104279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11161862229387397962805705 8371396672040548472104279)
              ·
                refine ⟨12557095008060822708156419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8371396672040548472104279 12557095008060822708156419)
                ·
                  refine ⟨18835642512091234062234629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12557095008060822708156419 18835642512091234062234629)
                  ·
                    refine ⟨3531682971017106386668993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18835642512091234062234629 3531682971017106386668993)
                    ·
                      refine ⟨2648762228262829790001745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3531682971017106386668993 2648762228262829790001745)
                      ·
                        rfl

theorem cell23_5158446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 2, 1, 1, 4, 2].length) (baseStart_5158446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5158446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5158446 prefixEnd_5158446 := by exact prefixLift 5158446
  have htrace : WordTrace (prefixWord ++ tailWord_5158446) baseStart_5158446 baseEnd_5158446 := by
    simpa [prefixWord, tailWord_5158446, baseEnd_5158446] using wordTrace_append hprefix tailTrace_5158446
  have hstable : (prefixWord ++ tailWord_5158446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5158446).length < 2 ^ (prefixWord ++ tailWord_5158446).sum := by decide
  have hdescent : baseEnd_5158446 < baseStart_5158446 := by decide
  rcases family_descends (prefixWord ++ tailWord_5158446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5158536 : List Nat := [2, 1, 3, 5, 1, 1, 1, 2, 2, 1, 4]
def baseStart_5158536 : Nat := 118140960795 + 5158536 * 2 ^ 59
def prefixEnd_5158536 : Nat := 4983230072969 + 3 ^ 40 * 5158536 * 2
def baseEnd_5158536 : Nat := 2648808441521734437876331

theorem tailTrace_5158536 : CollatzResearch.WordTrace tailWord_5158536 prefixEnd_5158536 2648808441521734437876331 := by
  unfold tailWord_5158536
  simp only [CollatzResearch.WordTrace]
  refine ⟨94073632419756277326647731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125431509893008369768863641 94073632419756277326647731)
  ·
    refine ⟨141110448629634415989971597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94073632419756277326647731 141110448629634415989971597)
    ·
      refine ⟨52916418236112905996239349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141110448629634415989971597 52916418236112905996239349)
      ·
        refine ⟨4960914209635584937147439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 52916418236112905996239349 4960914209635584937147439)
        ·
          refine ⟨7441371314453377405721159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4960914209635584937147439 7441371314453377405721159)
          ·
            refine ⟨11162056971680066108581739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7441371314453377405721159 11162056971680066108581739)
            ·
              refine ⟨16743085457520099162872609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11162056971680066108581739 16743085457520099162872609)
              ·
                refine ⟨12557314093140074372154457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16743085457520099162872609 12557314093140074372154457)
                ·
                  refine ⟨9417985569855055779115843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12557314093140074372154457 9417985569855055779115843)
                  ·
                    refine ⟨14126978354782583668673765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9417985569855055779115843 14126978354782583668673765)
                    ·
                      refine ⟨2648808441521734437876331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14126978354782583668673765 2648808441521734437876331)
                      ·
                        rfl

theorem cell23_5158536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_5158536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5158536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5158536 prefixEnd_5158536 := by exact prefixLift 5158536
  have htrace : WordTrace (prefixWord ++ tailWord_5158536) baseStart_5158536 baseEnd_5158536 := by
    simpa [prefixWord, tailWord_5158536, baseEnd_5158536] using wordTrace_append hprefix tailTrace_5158536
  have hstable : (prefixWord ++ tailWord_5158536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5158536).length < 2 ^ (prefixWord ++ tailWord_5158536).sum := by decide
  have hdescent : baseEnd_5158536 < baseStart_5158536 := by decide
  rcases family_descends (prefixWord ++ tailWord_5158536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5158542 : List Nat := [4, 1, 1, 3, 1, 2, 2, 1, 8]
def baseStart_5158542 : Nat := 118140960795 + 5158542 * 2 ^ 59
def prefixEnd_5158542 : Nat := 4983230072969 + 3 ^ 40 * 5158542 * 2
def baseEnd_5158542 : Nat := 294312391378406823822367

theorem tailTrace_5158542 : CollatzResearch.WordTrace tailWord_5158542 prefixEnd_5158542 294312391378406823822367 := by
  unfold tailWord_5158542
  simp only [CollatzResearch.WordTrace]
  refine ⟨23518435459686352209751735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125431655784993878452009253 23518435459686352209751735)
  ·
    refine ⟨35277653189529528314627603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23518435459686352209751735 35277653189529528314627603)
    ·
      refine ⟨52916479784294292471941405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35277653189529528314627603 52916479784294292471941405)
      ·
        refine ⟨19843679919110359676978027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52916479784294292471941405 19843679919110359676978027)
        ·
          refine ⟨29765519878665539515467041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19843679919110359676978027 29765519878665539515467041)
          ·
            refine ⟨22324139908999154636600281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29765519878665539515467041 22324139908999154636600281)
            ·
              refine ⟨16743104931749365977450211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22324139908999154636600281 16743104931749365977450211)
              ·
                refine ⟨25114657397624048966175317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16743104931749365977450211 25114657397624048966175317)
                ·
                  refine ⟨294312391378406823822367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25114657397624048966175317 294312391378406823822367)
                  ·
                    rfl

theorem cell23_5158542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 1, 8].length) (baseStart_5158542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5158542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5158542 prefixEnd_5158542 := by exact prefixLift 5158542
  have htrace : WordTrace (prefixWord ++ tailWord_5158542) baseStart_5158542 baseEnd_5158542 := by
    simpa [prefixWord, tailWord_5158542, baseEnd_5158542] using wordTrace_append hprefix tailTrace_5158542
  have hstable : (prefixWord ++ tailWord_5158542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5158542).length < 2 ^ (prefixWord ++ tailWord_5158542).sum := by decide
  have hdescent : baseEnd_5158542 < baseStart_5158542 := by decide
  rcases family_descends (prefixWord ++ tailWord_5158542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5158545 : List Nat := [1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 6]
def baseStart_5158545 : Nat := 118140960795 + 5158545 * 2 ^ 59
def prefixEnd_5158545 : Nat := 4983230072969 + 3 ^ 40 * 5158545 * 2
def baseEnd_5158545 : Nat := 2648813062847624902663789

theorem tailTrace_5158545 : CollatzResearch.WordTrace tailWord_5158545 prefixEnd_5158545 2648813062847624902663789 := by
  unfold tailWord_5158545
  simp only [CollatzResearch.WordTrace]
  refine ⟨188147593096479949190373089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125431728730986632793582059 188147593096479949190373089)
  ·
    refine ⟨141110694822359961892779817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188147593096479949190373089 141110694822359961892779817)
    ·
      refine ⟨105833021116769971419584863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141110694822359961892779817 105833021116769971419584863)
      ·
        refine ⟨158749531675154957129377295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105833021116769971419584863 158749531675154957129377295)
        ·
          refine ⟨238124297512732435694065943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158749531675154957129377295 238124297512732435694065943)
          ·
            refine ⟨357186446269098653541098915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 238124297512732435694065943 357186446269098653541098915)
            ·
              refine ⟨535779669403647980311648373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 357186446269098653541098915 535779669403647980311648373)
              ·
                refine ⟨50229344006591998154217035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 535779669403647980311648373 50229344006591998154217035)
                ·
                  refine ⟨75344016009887997231325553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50229344006591998154217035 75344016009887997231325553)
                  ·
                    refine ⟨56508012007415997923494165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 75344016009887997231325553 56508012007415997923494165)
                    ·
                      refine ⟨2648813062847624902663789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56508012007415997923494165 2648813062847624902663789)
                      ·
                        rfl

theorem cell23_5158545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 6].length) (baseStart_5158545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5158545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5158545 prefixEnd_5158545 := by exact prefixLift 5158545
  have htrace : WordTrace (prefixWord ++ tailWord_5158545) baseStart_5158545 baseEnd_5158545 := by
    simpa [prefixWord, tailWord_5158545, baseEnd_5158545] using wordTrace_append hprefix tailTrace_5158545
  have hstable : (prefixWord ++ tailWord_5158545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5158545).length < 2 ^ (prefixWord ++ tailWord_5158545).sum := by decide
  have hdescent : baseEnd_5158545 < baseStart_5158545 := by decide
  rcases family_descends (prefixWord ++ tailWord_5158545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5158596 : List Nat := [2, 3, 3, 1, 1, 1, 1, 4, 2, 3, 2]
def baseStart_5158596 : Nat := 118140960795 + 5158596 * 2 ^ 59
def prefixEnd_5158596 : Nat := 4983230072969 + 3 ^ 40 * 5158596 * 2
def baseEnd_5158596 : Nat := 2648839250361004203126055

theorem tailTrace_5158596 : CollatzResearch.WordTrace tailWord_5158596 prefixEnd_5158596 2648839250361004203126055 := by
  unfold tailWord_5158596
  simp only [CollatzResearch.WordTrace]
  refine ⟨94074726609647592450239821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125432968812863456600319761 94074726609647592450239821)
  ·
    refine ⟨35278022478617847168839933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94074726609647592450239821 35278022478617847168839933)
    ·
      refine ⟨13229258429481692688314975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35278022478617847168839933 13229258429481692688314975)
      ·
        refine ⟨19843887644222539032472463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13229258429481692688314975 19843887644222539032472463)
        ·
          refine ⟨29765831466333808548708695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19843887644222539032472463 29765831466333808548708695)
          ·
            refine ⟨44648747199500712823063043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29765831466333808548708695 44648747199500712823063043)
            ·
              refine ⟨66973120799251069234594565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44648747199500712823063043 66973120799251069234594565)
              ·
                refine ⟨12557460149859575481486481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 66973120799251069234594565 12557460149859575481486481)
                ·
                  refine ⟨9418095112394681611114861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12557460149859575481486481 9418095112394681611114861)
                  ·
                    refine ⟨3531785667148005604168073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9418095112394681611114861 3531785667148005604168073)
                    ·
                      refine ⟨2648839250361004203126055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3531785667148005604168073 2648839250361004203126055)
                      ·
                        rfl

theorem cell23_5158596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 4, 2, 3, 2].length) (baseStart_5158596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5158596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5158596 prefixEnd_5158596 := by exact prefixLift 5158596
  have htrace : WordTrace (prefixWord ++ tailWord_5158596) baseStart_5158596 baseEnd_5158596 := by
    simpa [prefixWord, tailWord_5158596, baseEnd_5158596] using wordTrace_append hprefix tailTrace_5158596
  have hstable : (prefixWord ++ tailWord_5158596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5158596).length < 2 ^ (prefixWord ++ tailWord_5158596).sum := by decide
  have hdescent : baseEnd_5158596 < baseStart_5158596 := by decide
  rcases family_descends (prefixWord ++ tailWord_5158596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5158629 : List Nat := [1, 3, 1, 4, 1, 1, 1, 3, 3, 2, 3]
def baseStart_5158629 : Nat := 118140960795 + 5158629 * 2 ^ 59
def prefixEnd_5158629 : Nat := 4983230072969 + 3 ^ 40 * 5158629 * 2
def baseEnd_5158629 : Nat := 2648856195222602574013403

theorem tailTrace_5158629 : CollatzResearch.WordTrace tailWord_5158629 prefixEnd_5158629 2648856195222602574013403 := by
  unfold tailWord_5158629
  simp only [CollatzResearch.WordTrace]
  refine ⟨188150656828175631536430941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125433771218783754357620627 188150656828175631536430941)
  ·
    refine ⟨70556496310565861826161603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 188150656828175631536430941 70556496310565861826161603)
    ·
      refine ⟨105834744465848792739242405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70556496310565861826161603 105834744465848792739242405)
      ·
        refine ⟨19844014587346648638607951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 105834744465848792739242405 19844014587346648638607951)
        ·
          refine ⟨29766021881019972957911927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19844014587346648638607951 29766021881019972957911927)
          ·
            refine ⟨44649032821529959436867891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29766021881019972957911927 44649032821529959436867891)
            ·
              refine ⟨66973549232294939155301837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44649032821529959436867891 66973549232294939155301837)
              ·
                refine ⟨25115080962110602183238189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66973549232294939155301837 25115080962110602183238189)
                ·
                  refine ⟨9418155360791475818714321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25115080962110602183238189 9418155360791475818714321)
                  ·
                    refine ⟨7063616520593606864035741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9418155360791475818714321 7063616520593606864035741)
                    ·
                      refine ⟨2648856195222602574013403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7063616520593606864035741 2648856195222602574013403)
                      ·
                        rfl

theorem cell23_5158629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 3, 3, 2, 3].length) (baseStart_5158629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5158629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5158629 prefixEnd_5158629 := by exact prefixLift 5158629
  have htrace : WordTrace (prefixWord ++ tailWord_5158629) baseStart_5158629 baseEnd_5158629 := by
    simpa [prefixWord, tailWord_5158629, baseEnd_5158629] using wordTrace_append hprefix tailTrace_5158629
  have hstable : (prefixWord ++ tailWord_5158629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5158629).length < 2 ^ (prefixWord ++ tailWord_5158629).sum := by decide
  have hdescent : baseEnd_5158629 < baseStart_5158629 := by decide
  rcases family_descends (prefixWord ++ tailWord_5158629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5158643 : List Nat := [1, 1, 1, 2, 2, 3, 3, 5, 1, 2, 2]
def baseStart_5158643 : Nat := 118140960795 + 5158643 * 2 ^ 59
def prefixEnd_5158643 : Nat := 4983230072969 + 3 ^ 40 * 5158643 * 2
def baseEnd_5158643 : Nat := 2648863383951765519238339

theorem tailTrace_5158643 : CollatzResearch.WordTrace tailWord_5158643 prefixEnd_5158643 2648863383951765519238339 := by
  unfold tailWord_5158643
  simp only [CollatzResearch.WordTrace]
  refine ⟨188151167450124911927440583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125434111633416607951627055 188151167450124911927440583)
  ·
    refine ⟨282226751175187367891160875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188151167450124911927440583 282226751175187367891160875)
    ·
      refine ⟨423340126762781051836741313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 282226751175187367891160875 423340126762781051836741313)
      ·
        refine ⟨317505095072085788877555985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 423340126762781051836741313 317505095072085788877555985)
        ·
          refine ⟨238128821304064341658166989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 317505095072085788877555985 238128821304064341658166989)
          ·
            refine ⟨89298307989024128121812621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 238128821304064341658166989 89298307989024128121812621)
            ·
              refine ⟨33486865495884048045679733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89298307989024128121812621 33486865495884048045679733)
              ·
                refine ⟨3139393640239129504282475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33486865495884048045679733 3139393640239129504282475)
                ·
                  refine ⟨4709090460358694256423713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3139393640239129504282475 4709090460358694256423713)
                  ·
                    refine ⟨3531817845269020692317785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4709090460358694256423713 3531817845269020692317785)
                    ·
                      refine ⟨2648863383951765519238339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3531817845269020692317785 2648863383951765519238339)
                      ·
                        rfl

theorem cell23_5158643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 5, 1, 2, 2].length) (baseStart_5158643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5158643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5158643 prefixEnd_5158643 := by exact prefixLift 5158643
  have htrace : WordTrace (prefixWord ++ tailWord_5158643) baseStart_5158643 baseEnd_5158643 := by
    simpa [prefixWord, tailWord_5158643, baseEnd_5158643] using wordTrace_append hprefix tailTrace_5158643
  have hstable : (prefixWord ++ tailWord_5158643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5158643).length < 2 ^ (prefixWord ++ tailWord_5158643).sum := by decide
  have hdescent : baseEnd_5158643 < baseStart_5158643 := by decide
  rcases family_descends (prefixWord ++ tailWord_5158643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5158660 : List Nat := [2, 3, 2, 2, 1, 2, 2, 4, 1, 2, 2]
def baseStart_5158660 : Nat := 118140960795 + 5158660 * 2 ^ 59
def prefixEnd_5158660 : Nat := 4983230072969 + 3 ^ 40 * 5158660 * 2
def baseEnd_5158660 : Nat := 2648872113122891952725761

theorem tailTrace_5158660 : CollatzResearch.WordTrace tailWord_5158660 prefixEnd_5158660 2648872113122891952725761 := by
  unfold tailWord_5158660
  simp only [CollatzResearch.WordTrace]
  refine ⟨94075893745531661915404717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125434524994042215887206289 94075893745531661915404717)
  ·
    refine ⟨35278460154574373218276769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94075893745531661915404717 35278460154574373218276769)
    ·
      refine ⟨26458845115930779913707577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35278460154574373218276769 26458845115930779913707577)
      ·
        refine ⟨19844133836948084935280683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26458845115930779913707577 19844133836948084935280683)
        ·
          refine ⟨29766200755422127402921025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19844133836948084935280683 29766200755422127402921025)
          ·
            refine ⟨22324650566566595552190769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29766200755422127402921025 22324650566566595552190769)
            ·
              refine ⟨16743487924924946664143077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22324650566566595552190769 16743487924924946664143077)
              ·
                refine ⟨3139403985923427499526827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16743487924924946664143077 3139403985923427499526827)
                ·
                  refine ⟨4709105978885141249290241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3139403985923427499526827 4709105978885141249290241)
                  ·
                    refine ⟨3531829484163855936967681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4709105978885141249290241 3531829484163855936967681)
                    ·
                      refine ⟨2648872113122891952725761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3531829484163855936967681 2648872113122891952725761)
                      ·
                        rfl

theorem cell23_5158660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 4, 1, 2, 2].length) (baseStart_5158660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5158660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5158660 prefixEnd_5158660 := by exact prefixLift 5158660
  have htrace : WordTrace (prefixWord ++ tailWord_5158660) baseStart_5158660 baseEnd_5158660 := by
    simpa [prefixWord, tailWord_5158660, baseEnd_5158660] using wordTrace_append hprefix tailTrace_5158660
  have hstable : (prefixWord ++ tailWord_5158660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5158660).length < 2 ^ (prefixWord ++ tailWord_5158660).sum := by decide
  have hdescent : baseEnd_5158660 < baseStart_5158660 := by decide
  rcases family_descends (prefixWord ++ tailWord_5158660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5158769 : List Nat := [1, 2, 2, 2, 1, 3, 1, 4, 2, 5]
def baseStart_5158769 : Nat := 118140960795 + 5158769 * 2 ^ 59
def prefixEnd_5158769 : Nat := 4983230072969 + 3 ^ 40 * 5158769 * 2
def baseEnd_5158769 : Nat := 882976027504744008754253

theorem tailTrace_5158769 : CollatzResearch.WordTrace tailWord_5158769 prefixEnd_5158769 882976027504744008754253 := by
  unfold tailWord_5158769
  simp only [CollatzResearch.WordTrace]
  refine ⟨188155763047668435446527361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125437175365112290297684907 188155763047668435446527361)
  ·
    refine ⟨141116822285751326584895521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188155763047668435446527361 141116822285751326584895521)
    ·
      refine ⟨105837616714313494938671641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141116822285751326584895521 105837616714313494938671641)
      ·
        refine ⟨79378212535735121204003731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105837616714313494938671641 79378212535735121204003731)
        ·
          refine ⟨119067318803602681806005597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79378212535735121204003731 119067318803602681806005597)
          ·
            refine ⟨44650244551351005677252099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 119067318803602681806005597 44650244551351005677252099)
            ·
              refine ⟨66975366827026508515878149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44650244551351005677252099 66975366827026508515878149)
              ·
                refine ⟨12557881280067470346727153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 66975366827026508515878149 12557881280067470346727153)
                ·
                  refine ⟨9418410960050602760045365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12557881280067470346727153 9418410960050602760045365)
                  ·
                    refine ⟨882976027504744008754253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9418410960050602760045365 882976027504744008754253)
                    ·
                      rfl

theorem cell23_5158769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 4, 2, 5].length) (baseStart_5158769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5158769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5158769 prefixEnd_5158769 := by exact prefixLift 5158769
  have htrace : WordTrace (prefixWord ++ tailWord_5158769) baseStart_5158769 baseEnd_5158769 := by
    simpa [prefixWord, tailWord_5158769, baseEnd_5158769] using wordTrace_append hprefix tailTrace_5158769
  have hstable : (prefixWord ++ tailWord_5158769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5158769).length < 2 ^ (prefixWord ++ tailWord_5158769).sum := by decide
  have hdescent : baseEnd_5158769 < baseStart_5158769 := by decide
  rcases family_descends (prefixWord ++ tailWord_5158769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5158789 : List Nat := [1, 3, 1, 1, 3, 2, 2, 2, 1, 3, 4]
def baseStart_5158789 : Nat := 118140960795 + 5158789 * 2 ^ 59
def prefixEnd_5158789 : Nat := 4983230072969 + 3 ^ 40 * 5158789 * 2
def baseEnd_5158789 : Nat := 2648938352127321948012667

theorem tailTrace_5158789 : CollatzResearch.WordTrace tailWord_5158789 prefixEnd_5158789 2648938352127321948012667 := by
  unfold tailWord_5158789
  simp only [CollatzResearch.WordTrace]
  refine ⟨188156492507595978862255421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125437661671730652574836947 188156492507595978862255421)
  ·
    refine ⟨70558684690348492073345783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 188156492507595978862255421 70558684690348492073345783)
    ·
      refine ⟨105838027035522738110018675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70558684690348492073345783 105838027035522738110018675)
      ·
        refine ⟨158757040553284107165028013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105838027035522738110018675 158757040553284107165028013)
        ·
          refine ⟨59533890207481540186885505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 158757040553284107165028013 59533890207481540186885505)
          ·
            refine ⟨44650417655611155140164129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59533890207481540186885505 44650417655611155140164129)
            ·
              refine ⟨33487813241708366355123097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44650417655611155140164129 33487813241708366355123097)
              ·
                refine ⟨25115859931281274766342323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33487813241708366355123097 25115859931281274766342323)
                ·
                  refine ⟨37673789896921912149513485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25115859931281274766342323 37673789896921912149513485)
                  ·
                    refine ⟨14127671211345717056067557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37673789896921912149513485 14127671211345717056067557)
                    ·
                      refine ⟨2648938352127321948012667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14127671211345717056067557 2648938352127321948012667)
                      ·
                        rfl

theorem cell23_5158789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 2, 1, 3, 4].length) (baseStart_5158789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5158789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5158789 prefixEnd_5158789 := by exact prefixLift 5158789
  have htrace : WordTrace (prefixWord ++ tailWord_5158789) baseStart_5158789 baseEnd_5158789 := by
    simpa [prefixWord, tailWord_5158789, baseEnd_5158789] using wordTrace_append hprefix tailTrace_5158789
  have hstable : (prefixWord ++ tailWord_5158789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5158789).length < 2 ^ (prefixWord ++ tailWord_5158789).sum := by decide
  have hdescent : baseEnd_5158789 < baseStart_5158789 := by decide
  rcases family_descends (prefixWord ++ tailWord_5158789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5158823 : List Nat := [1, 1, 6, 1, 2, 1, 1, 2, 2, 4, 2]
def baseStart_5158823 : Nat := 118140960795 + 5158823 * 2 ^ 59
def prefixEnd_5158823 : Nat := 4983230072969 + 3 ^ 40 * 5158823 * 2
def baseEnd_5158823 : Nat := 2648955810469574814987511

theorem tailTrace_5158823 : CollatzResearch.WordTrace tailWord_5158823 prefixEnd_5158823 2648955810469574814987511 := by
  unfold tailWord_5158823
  simp only [CollatzResearch.WordTrace]
  refine ⟨188157732589472802668993123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125438488392981868445995415 188157732589472802668993123)
  ·
    refine ⟨282236598884209204003489685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188157732589472802668993123 282236598884209204003489685)
    ·
      refine ⟨13229840572697306437663579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 282236598884209204003489685 13229840572697306437663579)
      ·
        refine ⟨19844760859045959656495369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13229840572697306437663579 19844760859045959656495369)
        ·
          refine ⟨14883570644284469742371527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19844760859045959656495369 14883570644284469742371527)
          ·
            refine ⟨22325355966426704613557291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14883570644284469742371527 22325355966426704613557291)
            ·
              refine ⟨33488033949640056920335937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22325355966426704613557291 33488033949640056920335937)
              ·
                refine ⟨25116025462230042690251953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33488033949640056920335937 25116025462230042690251953)
                ·
                  refine ⟨18837019096672532017688965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25116025462230042690251953 18837019096672532017688965)
                  ·
                    refine ⟨3531941080626099753316681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18837019096672532017688965 3531941080626099753316681)
                    ·
                      refine ⟨2648955810469574814987511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3531941080626099753316681 2648955810469574814987511)
                      ·
                        rfl

theorem cell23_5158823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 2, 2, 4, 2].length) (baseStart_5158823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5158823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5158823 prefixEnd_5158823 := by exact prefixLift 5158823
  have htrace : WordTrace (prefixWord ++ tailWord_5158823) baseStart_5158823 baseEnd_5158823 := by
    simpa [prefixWord, tailWord_5158823, baseEnd_5158823] using wordTrace_append hprefix tailTrace_5158823
  have hstable : (prefixWord ++ tailWord_5158823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5158823).length < 2 ^ (prefixWord ++ tailWord_5158823).sum := by decide
  have hdescent : baseEnd_5158823 < baseStart_5158823 := by decide
  rcases family_descends (prefixWord ++ tailWord_5158823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5158833 : List Nat := [1, 2, 2, 4, 2, 2, 2, 1, 3, 4]
def baseStart_5158833 : Nat := 118140960795 + 5158833 * 2 ^ 59
def prefixEnd_5158833 : Nat := 4983230072969 + 3 ^ 40 * 5158833 * 2
def baseEnd_5158833 : Nat := 882986981758706591954155

theorem tailTrace_5158833 : CollatzResearch.WordTrace tailWord_5158833 prefixEnd_5158833 882986981758706591954155 := by
  unfold tailWord_5158833
  simp only [CollatzResearch.WordTrace]
  refine ⟨188158097319436574376857153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125438731546291049584571435 188158097319436574376857153)
  ·
    refine ⟨141118572989577430782642865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188158097319436574376857153 141118572989577430782642865)
    ·
      refine ⟨105838929742183073086982149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141118572989577430782642865 105838929742183073086982149)
      ·
        refine ⟨19844799326659326203809153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 105838929742183073086982149 19844799326659326203809153)
        ·
          refine ⟨14883599494994494652856865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19844799326659326203809153 14883599494994494652856865)
          ·
            refine ⟨11162699621245870989642649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14883599494994494652856865 11162699621245870989642649)
            ·
              refine ⟨8372024715934403242231987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11162699621245870989642649 8372024715934403242231987)
              ·
                refine ⟨12558037073901604863347981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8372024715934403242231987 12558037073901604863347981)
                ·
                  refine ⟨4709263902713101823755493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12558037073901604863347981 4709263902713101823755493)
                  ·
                    refine ⟨882986981758706591954155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4709263902713101823755493 882986981758706591954155)
                    ·
                      rfl

theorem cell23_5158833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 2, 1, 3, 4].length) (baseStart_5158833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5158833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5158833 prefixEnd_5158833 := by exact prefixLift 5158833
  have htrace : WordTrace (prefixWord ++ tailWord_5158833) baseStart_5158833 baseEnd_5158833 := by
    simpa [prefixWord, tailWord_5158833, baseEnd_5158833] using wordTrace_append hprefix tailTrace_5158833
  have hstable : (prefixWord ++ tailWord_5158833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5158833).length < 2 ^ (prefixWord ++ tailWord_5158833).sum := by decide
  have hdescent : baseEnd_5158833 < baseStart_5158833 := by decide
  rcases family_descends (prefixWord ++ tailWord_5158833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5158883 : List Nat := [1, 1, 1, 6, 1, 2, 1, 1, 4, 3, 2]
def baseStart_5158883 : Nat := 118140960795 + 5158883 * 2 ^ 59
def prefixEnd_5158883 : Nat := 4983230072969 + 3 ^ 40 * 5158883 * 2
def baseEnd_5158883 : Nat := 2648986619308844580237235

theorem tailTrace_5158883 : CollatzResearch.WordTrace tailWord_5158883 prefixEnd_5158883 2648986619308844580237235 := by
  unfold tailWord_5158883
  simp only [CollatzResearch.WordTrace]
  refine ⟨188159920969255432916177303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125439947312836955277451535 188159920969255432916177303)
  ·
    refine ⟨282239881453883149374265955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188159920969255432916177303 282239881453883149374265955)
    ·
      refine ⟨423359822180824724061398933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 282239881453883149374265955 423359822180824724061398933)
      ·
        refine ⟨19844991664726158940378075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 423359822180824724061398933 19844991664726158940378075)
        ·
          refine ⟨29767487497089238410567113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19844991664726158940378075 29767487497089238410567113)
          ·
            refine ⟨22325615622816928807925335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29767487497089238410567113 22325615622816928807925335)
            ·
              refine ⟨33488423434225393211888003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22325615622816928807925335 33488423434225393211888003)
              ·
                refine ⟨50232635151338089817832005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33488423434225393211888003 50232635151338089817832005)
                ·
                  refine ⟨9418619090875891840843501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50232635151338089817832005 9418619090875891840843501)
                  ·
                    refine ⟨3531982159078459440316313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9418619090875891840843501 3531982159078459440316313)
                    ·
                      refine ⟨2648986619308844580237235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3531982159078459440316313 2648986619308844580237235)
                      ·
                        rfl

theorem cell23_5158883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 1, 4, 3, 2].length) (baseStart_5158883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5158883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5158883 prefixEnd_5158883 := by exact prefixLift 5158883
  have htrace : WordTrace (prefixWord ++ tailWord_5158883) baseStart_5158883 baseEnd_5158883 := by
    simpa [prefixWord, tailWord_5158883, baseEnd_5158883] using wordTrace_append hprefix tailTrace_5158883
  have hstable : (prefixWord ++ tailWord_5158883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5158883).length < 2 ^ (prefixWord ++ tailWord_5158883).sum := by decide
  have hdescent : baseEnd_5158883 < baseStart_5158883 := by decide
  rcases family_descends (prefixWord ++ tailWord_5158883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5158910 : List Nat := [4, 2, 2, 2, 1, 1, 3, 2, 1, 5]
def baseStart_5158910 : Nat := 118140960795 + 5158910 * 2 ^ 59
def prefixEnd_5158910 : Nat := 4983230072969 + 3 ^ 40 * 5158910 * 2
def baseEnd_5158910 : Nat := 883000161095505324866537

theorem tailTrace_5158910 : CollatzResearch.WordTrace tailWord_5158910 prefixEnd_5158910 883000161095505324866537 := by
  unfold tailWord_5158910
  simp only [CollatzResearch.WordTrace]
  refine ⟨23520113217519702065926273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125440603826771744351606789 23520113217519702065926273)
  ·
    refine ⟨17640084913139776549444705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23520113217519702065926273 17640084913139776549444705)
    ·
      refine ⟨13230063684854832412083529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17640084913139776549444705 13230063684854832412083529)
      ·
        refine ⟨9922547763641124309062647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13230063684854832412083529 9922547763641124309062647)
        ·
          refine ⟨14883821645461686463593971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9922547763641124309062647 14883821645461686463593971)
          ·
            refine ⟨22325732468192529695390957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14883821645461686463593971 22325732468192529695390957)
            ·
              refine ⟨8372149675572198635771609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22325732468192529695390957 8372149675572198635771609)
              ·
                refine ⟨6279112256679148976828707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8372149675572198635771609 6279112256679148976828707)
                ·
                  refine ⟨9418668385018723465243061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6279112256679148976828707 9418668385018723465243061)
                  ·
                    refine ⟨883000161095505324866537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9418668385018723465243061 883000161095505324866537)
                    ·
                      rfl

theorem cell23_5158910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 3, 2, 1, 5].length) (baseStart_5158910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5158910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5158910 prefixEnd_5158910 := by exact prefixLift 5158910
  have htrace : WordTrace (prefixWord ++ tailWord_5158910) baseStart_5158910 baseEnd_5158910 := by
    simpa [prefixWord, tailWord_5158910, baseEnd_5158910] using wordTrace_append hprefix tailTrace_5158910
  have hstable : (prefixWord ++ tailWord_5158910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5158910).length < 2 ^ (prefixWord ++ tailWord_5158910).sum := by decide
  have hdescent : baseEnd_5158910 < baseStart_5158910 := by decide
  rcases family_descends (prefixWord ++ tailWord_5158910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5158939 : List Nat := [1, 1, 1, 1, 1, 1, 3, 4, 2, 2, 6]
def baseStart_5158939 : Nat := 118140960795 + 5158939 * 2 ^ 59
def prefixEnd_5158939 : Nat := 4983230072969 + 3 ^ 40 * 5158939 * 2
def baseEnd_5158939 : Nat := 2649015374225496361136977

theorem tailTrace_5158939 : CollatzResearch.WordTrace tailWord_5158939 prefixEnd_5158939 2649015374225496361136977 := by
  unfold tailWord_5158939
  simp only [CollatzResearch.WordTrace]
  refine ⟨188161963457052554480215871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125441308971368369653477247 188161963457052554480215871)
  ·
    refine ⟨282242945185578831720323807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188161963457052554480215871 282242945185578831720323807)
    ·
      refine ⟨423364417778368247580485711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 282242945185578831720323807 423364417778368247580485711)
      ·
        refine ⟨635046626667552371370728567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 423364417778368247580485711 635046626667552371370728567)
        ·
          refine ⟨952569940001328557056092851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 635046626667552371370728567 952569940001328557056092851)
          ·
            refine ⟨1428854910001992835584139277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 952569940001328557056092851 1428854910001992835584139277)
            ·
              refine ⟨535820591250747313344052229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1428854910001992835584139277 535820591250747313344052229)
              ·
                refine ⟨100466360859515121252009793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 535820591250747313344052229 100466360859515121252009793)
                ·
                  refine ⟨75349770644636340939007345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 100466360859515121252009793 75349770644636340939007345)
                  ·
                    refine ⟨56512327983477255704255509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 75349770644636340939007345 56512327983477255704255509)
                    ·
                      refine ⟨2649015374225496361136977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56512327983477255704255509 2649015374225496361136977)
                      ·
                        rfl

theorem cell23_5158939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 2, 2, 6].length) (baseStart_5158939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5158939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5158939 prefixEnd_5158939 := by exact prefixLift 5158939
  have htrace : WordTrace (prefixWord ++ tailWord_5158939) baseStart_5158939 baseEnd_5158939 := by
    simpa [prefixWord, tailWord_5158939, baseEnd_5158939] using wordTrace_append hprefix tailTrace_5158939
  have hstable : (prefixWord ++ tailWord_5158939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5158939).length < 2 ^ (prefixWord ++ tailWord_5158939).sum := by decide
  have hdescent : baseEnd_5158939 < baseStart_5158939 := by decide
  rcases family_descends (prefixWord ++ tailWord_5158939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5158940 : List Nat := [2, 2, 3, 1, 3, 2, 2, 2, 2, 4]
def baseStart_5158940 : Nat := 118140960795 + 5158940 * 2 ^ 59
def prefixEnd_5158940 : Nat := 4983230072969 + 3 ^ 40 * 5158940 * 2
def baseEnd_5158940 : Nat := 883005295902050285741491

theorem tailTrace_5158940 : CollatzResearch.WordTrace tailWord_5158940 prefixEnd_5158940 883005295902050285741491 := by
  unfold tailWord_5158940
  simp only [CollatzResearch.WordTrace]
  refine ⟨94080999965024465825501137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125441333286699287767334849 94080999965024465825501137)
  ·
    refine ⟨70560749973768349369125853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94080999965024465825501137 70560749973768349369125853)
    ·
      refine ⟨26460281240163131013422195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70560749973768349369125853 26460281240163131013422195)
      ·
        refine ⟨39690421860244696520133293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26460281240163131013422195 39690421860244696520133293)
        ·
          refine ⟨14883908197591761195049985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39690421860244696520133293 14883908197591761195049985)
          ·
            refine ⟨11162931148193820896287489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14883908197591761195049985 11162931148193820896287489)
            ·
              refine ⟨8372198361145365672215617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11162931148193820896287489 8372198361145365672215617)
              ·
                refine ⟨6279148770859024254161713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8372198361145365672215617 6279148770859024254161713)
                ·
                  refine ⟨4709361578144268190621285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6279148770859024254161713 4709361578144268190621285)
                  ·
                    refine ⟨883005295902050285741491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4709361578144268190621285 883005295902050285741491)
                    ·
                      rfl

theorem cell23_5158940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 2, 2, 2, 4].length) (baseStart_5158940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5158940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5158940 prefixEnd_5158940 := by exact prefixLift 5158940
  have htrace : WordTrace (prefixWord ++ tailWord_5158940) baseStart_5158940 baseEnd_5158940 := by
    simpa [prefixWord, tailWord_5158940, baseEnd_5158940] using wordTrace_append hprefix tailTrace_5158940
  have hstable : (prefixWord ++ tailWord_5158940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5158940).length < 2 ^ (prefixWord ++ tailWord_5158940).sum := by decide
  have hdescent : baseEnd_5158940 < baseStart_5158940 := by decide
  rcases family_descends (prefixWord ++ tailWord_5158940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5158947 : List Nat := [1, 1, 1, 4, 3, 1, 3, 4, 1, 2, 2]
def baseStart_5158947 : Nat := 118140960795 + 5158947 * 2 ^ 59
def prefixEnd_5158947 : Nat := 4983230072969 + 3 ^ 40 * 5158947 * 2
def baseEnd_5158947 : Nat := 2649019482070732329836941

theorem tailTrace_5158947 : CollatzResearch.WordTrace tailWord_5158947 prefixEnd_5158947 2649019482070732329836941 := by
  unfold tailWord_5158947
  simp only [CollatzResearch.WordTrace]
  refine ⟨188162255241023571846507095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125441503494015714564338063 188162255241023571846507095)
  ·
    refine ⟨282243382861535357769760643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188162255241023571846507095 282243382861535357769760643)
    ·
      refine ⟨423365074292303036654640965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 282243382861535357769760643 423365074292303036654640965)
      ·
        refine ⟨79380951429806819372745181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 423365074292303036654640965 79380951429806819372745181)
        ·
          refine ⟨29767856786177557264779443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79380951429806819372745181 29767856786177557264779443)
          ·
            refine ⟨44651785179266335897169165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29767856786177557264779443 44651785179266335897169165)
            ·
              refine ⟨16744419442224875961438437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44651785179266335897169165 16744419442224875961438437)
              ·
                refine ⟨3139578645417164242769707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16744419442224875961438437 3139578645417164242769707)
                ·
                  refine ⟨4709367968125746364154561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3139578645417164242769707 4709367968125746364154561)
                  ·
                    refine ⟨3532025976094309773115921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4709367968125746364154561 3532025976094309773115921)
                    ·
                      refine ⟨2649019482070732329836941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3532025976094309773115921 2649019482070732329836941)
                      ·
                        rfl

theorem cell23_5158947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 4, 1, 2, 2].length) (baseStart_5158947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5158947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5158947 prefixEnd_5158947 := by exact prefixLift 5158947
  have htrace : WordTrace (prefixWord ++ tailWord_5158947) baseStart_5158947 baseEnd_5158947 := by
    simpa [prefixWord, tailWord_5158947, baseEnd_5158947] using wordTrace_append hprefix tailTrace_5158947
  have hstable : (prefixWord ++ tailWord_5158947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5158947).length < 2 ^ (prefixWord ++ tailWord_5158947).sum := by decide
  have hdescent : baseEnd_5158947 < baseStart_5158947 := by decide
  rcases family_descends (prefixWord ++ tailWord_5158947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5158964 : List Nat := [2, 5, 1, 2, 2, 1, 1, 2, 3, 2, 2]
def baseStart_5158964 : Nat := 118140960795 + 5158964 * 2 ^ 59
def prefixEnd_5158964 : Nat := 4983230072969 + 3 ^ 40 * 5158964 * 2
def baseEnd_5158964 : Nat := 2649028211241858763324363

theorem tailTrace_5158964 : CollatzResearch.WordTrace tailWord_5158964 prefixEnd_5158964 2649028211241858763324363 := by
  unfold tailWord_5158964
  simp only [CollatzResearch.WordTrace]
  refine ⟨94081437640980991874937973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125441916854641322499917297 94081437640980991874937973)
  ·
    refine ⟨8820134778841967988275435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 94081437640980991874937973 8820134778841967988275435)
    ·
      refine ⟨13230202168262951982413153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8820134778841967988275435 13230202168262951982413153)
      ·
        refine ⟨9922651626197213986809865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13230202168262951982413153 9922651626197213986809865)
        ·
          refine ⟨7441988719647910490107399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9922651626197213986809865 7441988719647910490107399)
          ·
            refine ⟨11162983079471865735161099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7441988719647910490107399 11162983079471865735161099)
            ·
              refine ⟨16744474619207798602741649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11162983079471865735161099 16744474619207798602741649)
              ·
                refine ⟨12558355964405848952056237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16744474619207798602741649 12558355964405848952056237)
                ·
                  refine ⟨4709383486652193357021089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12558355964405848952056237 4709383486652193357021089)
                  ·
                    refine ⟨3532037614989145017765817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4709383486652193357021089 3532037614989145017765817)
                    ·
                      refine ⟨2649028211241858763324363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3532037614989145017765817 2649028211241858763324363)
                      ·
                        rfl

theorem cell23_5158964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 2, 3, 2, 2].length) (baseStart_5158964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5158964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5158964 prefixEnd_5158964 := by exact prefixLift 5158964
  have htrace : WordTrace (prefixWord ++ tailWord_5158964) baseStart_5158964 baseEnd_5158964 := by
    simpa [prefixWord, tailWord_5158964, baseEnd_5158964] using wordTrace_append hprefix tailTrace_5158964
  have hstable : (prefixWord ++ tailWord_5158964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5158964).length < 2 ^ (prefixWord ++ tailWord_5158964).sum := by decide
  have hdescent : baseEnd_5158964 < baseStart_5158964 := by decide
  rcases family_descends (prefixWord ++ tailWord_5158964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5158997 : List Nat := [1, 3, 2, 2, 1, 5, 1, 2, 2, 1, 3]
def baseStart_5158997 : Nat := 118140960795 + 5158997 * 2 ^ 59
def prefixEnd_5158997 : Nat := 4983230072969 + 3 ^ 40 * 5158997 * 2
def baseEnd_5158997 : Nat := 2649045156103457134211711

theorem tailTrace_5158997 : CollatzResearch.WordTrace tailWord_5158997 prefixEnd_5158997 2649045156103457134211711 := by
  unfold tailWord_5158997
  simp only [CollatzResearch.WordTrace]
  refine ⟨188164078890842430385827245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125442719260561620257218163 188164078890842430385827245)
  ·
    refine ⟨70561529584065911394685217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 188164078890842430385827245 70561529584065911394685217)
    ·
      refine ⟨52921147188049433546013913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70561529584065911394685217 52921147188049433546013913)
      ·
        refine ⟨39690860391037075159510435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52921147188049433546013913 39690860391037075159510435)
        ·
          refine ⟨59536290586555612739265653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39690860391037075159510435 59536290586555612739265653)
          ·
            refine ⟨5581527242489588694306155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 59536290586555612739265653 5581527242489588694306155)
            ·
              refine ⟨8372290863734383041459233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5581527242489588694306155 8372290863734383041459233)
              ·
                refine ⟨6279218147800787281094425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8372290863734383041459233 6279218147800787281094425)
                ·
                  refine ⟨4709413610850590460820819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6279218147800787281094425 4709413610850590460820819)
                  ·
                    refine ⟨7064120416275885691231229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4709413610850590460820819 7064120416275885691231229)
                    ·
                      refine ⟨2649045156103457134211711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7064120416275885691231229 2649045156103457134211711)
                      ·
                        rfl

theorem cell23_5158997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 1, 2, 2, 1, 3].length) (baseStart_5158997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5158997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5158997 prefixEnd_5158997 := by exact prefixLift 5158997
  have htrace : WordTrace (prefixWord ++ tailWord_5158997) baseStart_5158997 baseEnd_5158997 := by
    simpa [prefixWord, tailWord_5158997, baseEnd_5158997] using wordTrace_append hprefix tailTrace_5158997
  have hstable : (prefixWord ++ tailWord_5158997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5158997).length < 2 ^ (prefixWord ++ tailWord_5158997).sum := by decide
  have hdescent : baseEnd_5158997 < baseStart_5158997 := by decide
  rcases family_descends (prefixWord ++ tailWord_5158997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5159020 : List Nat := [2, 2, 1, 1, 3, 3, 3, 1, 1, 4, 2]
def baseStart_5159020 : Nat := 118140960795 + 5159020 * 2 ^ 59
def prefixEnd_5159020 : Nat := 4983230072969 + 3 ^ 40 * 5159020 * 2
def baseEnd_5159020 : Nat := 2649056966158510544224105

theorem tailTrace_5159020 : CollatzResearch.WordTrace tailWord_5159020 prefixEnd_5159020 2649056966158510544224105 := by
  unfold tailWord_5159020
  simp only [CollatzResearch.WordTrace]
  refine ⟨94082458884879552656957257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125443278513172736875943009 94082458884879552656957257)
  ·
    refine ⟨70561844163659664492717943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94082458884879552656957257 70561844163659664492717943)
    ·
      refine ⟨105842766245489496739076915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70561844163659664492717943 105842766245489496739076915)
      ·
        refine ⟨158764149368234245108615373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105842766245489496739076915 158764149368234245108615373)
        ·
          refine ⟨59536556013087841915730765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 158764149368234245108615373 59536556013087841915730765)
          ·
            refine ⟨22326208504907940718399037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59536556013087841915730765 22326208504907940718399037)
            ·
              refine ⟨8372328189340477769399639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22326208504907940718399037 8372328189340477769399639)
              ·
                refine ⟨12558492284010716654099459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8372328189340477769399639 12558492284010716654099459)
                ·
                  refine ⟨18837738426016074981149189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12558492284010716654099459 18837738426016074981149189)
                  ·
                    refine ⟨3532075954878014058965473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18837738426016074981149189 3532075954878014058965473)
                    ·
                      refine ⟨2649056966158510544224105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3532075954878014058965473 2649056966158510544224105)
                      ·
                        rfl

theorem cell23_5159020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 4, 2].length) (baseStart_5159020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5159020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5159020 prefixEnd_5159020 := by exact prefixLift 5159020
  have htrace : WordTrace (prefixWord ++ tailWord_5159020) baseStart_5159020 baseEnd_5159020 := by
    simpa [prefixWord, tailWord_5159020, baseEnd_5159020] using wordTrace_append hprefix tailTrace_5159020
  have hstable : (prefixWord ++ tailWord_5159020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5159020).length < 2 ^ (prefixWord ++ tailWord_5159020).sum := by decide
  have hdescent : baseEnd_5159020 < baseStart_5159020 := by decide
  rcases family_descends (prefixWord ++ tailWord_5159020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5159071 : List Nat := [1, 1, 2, 6, 1, 3, 2, 1, 2, 2, 2]
def baseStart_5159071 : Nat := 118140960795 + 5159071 * 2 ^ 59
def prefixEnd_5159071 : Nat := 4983230072969 + 3 ^ 40 * 5159071 * 2
def baseEnd_5159071 : Nat := 2649083153671889844686371

theorem tailTrace_5159071 : CollatzResearch.WordTrace tailWord_5159071 prefixEnd_5159071 2649083153671889844686371 := by
  unfold tailWord_5159071
  simp only [CollatzResearch.WordTrace]
  refine ⟨188166777892574341024021067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125444518595049560682680711 188166777892574341024021067)
  ·
    refine ⟨282250166838861511536031601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188166777892574341024021067 282250166838861511536031601)
    ·
      refine ⟨211687625129146133652023701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 282250166838861511536031601 211687625129146133652023701)
      ·
        refine ⟨9922857427928725014938611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 211687625129146133652023701 9922857427928725014938611)
        ·
          refine ⟨14884286141893087522407917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9922857427928725014938611 14884286141893087522407917)
          ·
            refine ⟨5581607303209907820902969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14884286141893087522407917 5581607303209907820902969)
            ·
              refine ⟨4186205477407430865677227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5581607303209907820902969 4186205477407430865677227)
              ·
                refine ⟨6279308216111146298515841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4186205477407430865677227 6279308216111146298515841)
                ·
                  refine ⟨4709481162083359723886881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6279308216111146298515841 4709481162083359723886881)
                  ·
                    refine ⟨3532110871562519792915161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4709481162083359723886881 3532110871562519792915161)
                    ·
                      refine ⟨2649083153671889844686371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3532110871562519792915161 2649083153671889844686371)
                      ·
                        rfl

theorem cell23_5159071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 2, 1, 2, 2, 2].length) (baseStart_5159071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5159071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5159071 prefixEnd_5159071 := by exact prefixLift 5159071
  have htrace : WordTrace (prefixWord ++ tailWord_5159071) baseStart_5159071 baseEnd_5159071 := by
    simpa [prefixWord, tailWord_5159071, baseEnd_5159071] using wordTrace_append hprefix tailTrace_5159071
  have hstable : (prefixWord ++ tailWord_5159071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5159071).length < 2 ^ (prefixWord ++ tailWord_5159071).sum := by decide
  have hdescent : baseEnd_5159071 < baseStart_5159071 := by decide
  rcases family_descends (prefixWord ++ tailWord_5159071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5159113 : List Nat := [1, 2, 1, 1, 2, 1, 1, 5, 4, 2, 3]
def baseStart_5159113 : Nat := 118140960795 + 5159113 * 2 ^ 59
def prefixEnd_5159113 : Nat := 4983230072969 + 3 ^ 40 * 5159113 * 2
def baseEnd_5159113 : Nat := 2649104719859378680361177

theorem tailTrace_5159113 : CollatzResearch.WordTrace tailWord_5159113 prefixEnd_5159113 2649104719859378680361177 := by
  unfold tailWord_5159113
  simp only [CollatzResearch.WordTrace]
  refine ⟨188168309758422182197049993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125445539838948121464699995 188168309758422182197049993)
  ·
    refine ⟨141126232318816636647787495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188168309758422182197049993 141126232318816636647787495)
    ·
      refine ⟨211689348478224954971681243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141126232318816636647787495 211689348478224954971681243)
      ·
        refine ⟨317534022717337432457521865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211689348478224954971681243 317534022717337432457521865)
        ·
          refine ⟨238150517038003074343141399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 317534022717337432457521865 238150517038003074343141399)
          ·
            refine ⟨357225775557004611514712099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 238150517038003074343141399 357225775557004611514712099)
            ·
              refine ⟨535838663335506917272068149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 357225775557004611514712099 535838663335506917272068149)
              ·
                refine ⟨50234874687703773494256389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 535838663335506917272068149 50234874687703773494256389)
                ·
                  refine ⟨9419039003944457530173073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50234874687703773494256389 9419039003944457530173073)
                  ·
                    refine ⟨7064279252958343147629805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9419039003944457530173073 7064279252958343147629805)
                    ·
                      refine ⟨2649104719859378680361177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7064279252958343147629805 2649104719859378680361177)
                      ·
                        rfl

theorem cell23_5159113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 5, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 5, 4, 2, 3].length) (baseStart_5159113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5159113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5159113 prefixEnd_5159113 := by exact prefixLift 5159113
  have htrace : WordTrace (prefixWord ++ tailWord_5159113) baseStart_5159113 baseEnd_5159113 := by
    simpa [prefixWord, tailWord_5159113, baseEnd_5159113] using wordTrace_append hprefix tailTrace_5159113
  have hstable : (prefixWord ++ tailWord_5159113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5159113).length < 2 ^ (prefixWord ++ tailWord_5159113).sum := by decide
  have hdescent : baseEnd_5159113 < baseStart_5159113 := by decide
  rcases family_descends (prefixWord ++ tailWord_5159113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5159154 : List Nat := [3, 2, 1, 3, 2, 2, 2, 3, 1, 4]
def baseStart_5159154 : Nat := 118140960795 + 5159154 * 2 ^ 59
def prefixEnd_5159154 : Nat := 4983230072969 + 3 ^ 40 * 5159154 * 2
def baseEnd_5159154 : Nat := 883041924188737673316163

theorem tailTrace_5159154 : CollatzResearch.WordTrace tailWord_5159154 prefixEnd_5159154 883041924188737673316163 := by
  unfold tailWord_5159154
  simp only [CollatzResearch.WordTrace]
  refine ⟨47042451287818411549823129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125446536767515764132861677 47042451287818411549823129)
  ·
    refine ⟨35281838465863808662367347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47042451287818411549823129 35281838465863808662367347)
    ·
      refine ⟨52922757698795712993551021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35281838465863808662367347 52922757698795712993551021)
      ·
        refine ⟨19846034137048392372581633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52922757698795712993551021 19846034137048392372581633)
        ·
          refine ⟨14884525602786294279436225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19846034137048392372581633 14884525602786294279436225)
          ·
            refine ⟨11163394202089720709577169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14884525602786294279436225 11163394202089720709577169)
            ·
              refine ⟨8372545651567290532182877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11163394202089720709577169 8372545651567290532182877)
              ·
                refine ⟨3139704619337733949568579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8372545651567290532182877 3139704619337733949568579)
                ·
                  refine ⟨4709556929006600924352869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3139704619337733949568579 4709556929006600924352869)
                  ·
                    refine ⟨883041924188737673316163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4709556929006600924352869 883041924188737673316163)
                    ·
                      rfl

theorem cell23_5159154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 2, 3, 1, 4].length) (baseStart_5159154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5159154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5159154 prefixEnd_5159154 := by exact prefixLift 5159154
  have htrace : WordTrace (prefixWord ++ tailWord_5159154) baseStart_5159154 baseEnd_5159154 := by
    simpa [prefixWord, tailWord_5159154, baseEnd_5159154] using wordTrace_append hprefix tailTrace_5159154
  have hstable : (prefixWord ++ tailWord_5159154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5159154).length < 2 ^ (prefixWord ++ tailWord_5159154).sum := by decide
  have hdescent : baseEnd_5159154 < baseStart_5159154 := by decide
  rcases family_descends (prefixWord ++ tailWord_5159154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5159170 : List Nat := [3, 4, 1, 1, 2, 1, 1, 1, 1, 2, 6]
def baseStart_5159170 : Nat := 118140960795 + 5159170 * 2 ^ 59
def prefixEnd_5159170 : Nat := 4983230072969 + 3 ^ 40 * 5159170 * 2
def baseEnd_5159170 : Nat := 2649133988256684957348415

theorem tailTrace_5159170 : CollatzResearch.WordTrace tailWord_5159170 prefixEnd_5159170 2649133988256684957348415 := by
  unfold tailWord_5159170
  simp only [CollatzResearch.WordTrace]
  refine ⟨47042597179803920232968741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125446925812810453954583309 47042597179803920232968741)
  ·
    refine ⟨8820486971213235043681639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47042597179803920232968741 8820486971213235043681639)
    ·
      refine ⟨13230730456819852565522459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8820486971213235043681639 13230730456819852565522459)
      ·
        refine ⟨19846095685229778848283689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13230730456819852565522459 19846095685229778848283689)
        ·
          refine ⟨14884571763922334136212767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19846095685229778848283689 14884571763922334136212767)
          ·
            refine ⟨22326857645883501204319151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14884571763922334136212767 22326857645883501204319151)
            ·
              refine ⟨33490286468825251806478727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22326857645883501204319151 33490286468825251806478727)
              ·
                refine ⟨50235429703237877709718091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33490286468825251806478727 50235429703237877709718091)
                ·
                  refine ⟨75353144554856816564577137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50235429703237877709718091 75353144554856816564577137)
                  ·
                    refine ⟨56514858416142612423432853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 75353144554856816564577137 56514858416142612423432853)
                    ·
                      refine ⟨2649133988256684957348415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56514858416142612423432853 2649133988256684957348415)
                      ·
                        rfl

theorem cell23_5159170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_5159170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5159170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5159170 prefixEnd_5159170 := by exact prefixLift 5159170
  have htrace : WordTrace (prefixWord ++ tailWord_5159170) baseStart_5159170 baseEnd_5159170 := by
    simpa [prefixWord, tailWord_5159170, baseEnd_5159170] using wordTrace_append hprefix tailTrace_5159170
  have hstable : (prefixWord ++ tailWord_5159170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5159170).length < 2 ^ (prefixWord ++ tailWord_5159170).sum := by decide
  have hdescent : baseEnd_5159170 < baseStart_5159170 := by decide
  rcases family_descends (prefixWord ++ tailWord_5159170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5159177 : List Nat := [1, 2, 1, 1, 3, 5, 2, 1, 3, 1, 3]
def baseStart_5159177 : Nat := 118140960795 + 5159177 * 2 ^ 59
def prefixEnd_5159177 : Nat := 4983230072969 + 3 ^ 40 * 5159177 * 2
def baseEnd_5159177 : Nat := 2649137582621266429960883

theorem tailTrace_5159177 : CollatzResearch.WordTrace tailWord_5159177 prefixEnd_5159177 2649137582621266429960883 := by
  unfold tailWord_5159177
  simp only [CollatzResearch.WordTrace]
  refine ⟨188170644030190321127379785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125447096020126880751586523 188170644030190321127379785)
  ·
    refine ⟨141127983022642740845534839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188170644030190321127379785 141127983022642740845534839)
    ·
      refine ⟨211691974533964111268302259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141127983022642740845534839 211691974533964111268302259)
      ·
        refine ⟨317537961800946166902453389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211691974533964111268302259 317537961800946166902453389)
        ·
          refine ⟨119076735675354812588420021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 317537961800946166902453389 119076735675354812588420021)
          ·
            refine ⟨11163443969564513680164377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 119076735675354812588420021 11163443969564513680164377)
            ·
              refine ⟨8372582977173385260123283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11163443969564513680164377 8372582977173385260123283)
              ·
                refine ⟨12558874465760077890184925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8372582977173385260123283 12558874465760077890184925)
                ·
                  refine ⟨4709577924660029208819347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12558874465760077890184925 4709577924660029208819347)
                  ·
                    refine ⟨7064366886990043813229021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4709577924660029208819347 7064366886990043813229021)
                    ·
                      refine ⟨2649137582621266429960883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7064366886990043813229021 2649137582621266429960883)
                      ·
                        rfl

theorem cell23_5159177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 2, 1, 3, 1, 3].length) (baseStart_5159177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5159177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5159177 prefixEnd_5159177 := by exact prefixLift 5159177
  have htrace : WordTrace (prefixWord ++ tailWord_5159177) baseStart_5159177 baseEnd_5159177 := by
    simpa [prefixWord, tailWord_5159177, baseEnd_5159177] using wordTrace_append hprefix tailTrace_5159177
  have hstable : (prefixWord ++ tailWord_5159177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5159177).length < 2 ^ (prefixWord ++ tailWord_5159177).sum := by decide
  have hdescent : baseEnd_5159177 < baseStart_5159177 := by decide
  rcases family_descends (prefixWord ++ tailWord_5159177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5159183 : List Nat := [1, 1, 2, 1, 1, 1, 3, 3, 5, 1, 4]
def baseStart_5159183 : Nat := 118140960795 + 5159183 * 2 ^ 59
def prefixEnd_5159183 : Nat := 4983230072969 + 3 ^ 40 * 5159183 * 2
def baseEnd_5159183 : Nat := 2649140663505193406485855

theorem tailTrace_5159183 : CollatzResearch.WordTrace tailWord_5159183 prefixEnd_5159183 2649140663505193406485855 := by
  unfold tailWord_5159183
  simp only [CollatzResearch.WordTrace]
  refine ⟨188170862868168584152098203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125447241912112389434732135 188170862868168584152098203)
  ·
    refine ⟨282256294302252876228147305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188170862868168584152098203 282256294302252876228147305)
    ·
      refine ⟨211692220726689657171110479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 282256294302252876228147305 211692220726689657171110479)
      ·
        refine ⟨317538331090034485756665719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211692220726689657171110479 317538331090034485756665719)
        ·
          refine ⟨476307496635051728634998579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 317538331090034485756665719 476307496635051728634998579)
          ·
            refine ⟨714461244952577592952497869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 476307496635051728634998579 714461244952577592952497869)
            ·
              refine ⟨267922966857216597357186701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 714461244952577592952497869 267922966857216597357186701)
              ·
                refine ⟨100471112571456224008945013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 267922966857216597357186701 100471112571456224008945013)
                ·
                  refine ⟨9419166803574021000838595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 100471112571456224008945013 9419166803574021000838595)
                  ·
                    refine ⟨14128750205361031501257893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9419166803574021000838595 14128750205361031501257893)
                    ·
                      refine ⟨2649140663505193406485855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14128750205361031501257893 2649140663505193406485855)
                      ·
                        rfl

theorem cell23_5159183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 5, 1, 4].length) (baseStart_5159183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5159183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5159183 prefixEnd_5159183 := by exact prefixLift 5159183
  have htrace : WordTrace (prefixWord ++ tailWord_5159183) baseStart_5159183 baseEnd_5159183 := by
    simpa [prefixWord, tailWord_5159183, baseEnd_5159183] using wordTrace_append hprefix tailTrace_5159183
  have hstable : (prefixWord ++ tailWord_5159183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5159183).length < 2 ^ (prefixWord ++ tailWord_5159183).sum := by decide
  have hdescent : baseEnd_5159183 < baseStart_5159183 := by decide
  rcases family_descends (prefixWord ++ tailWord_5159183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5159203 : List Nat := [1, 1, 1, 4, 2, 2, 1, 2, 3, 1, 5]
def baseStart_5159203 : Nat := 118140960795 + 5159203 * 2 ^ 59
def prefixEnd_5159203 : Nat := 4983230072969 + 3 ^ 40 * 5159203 * 2
def baseEnd_5159203 : Nat := 2649150933118283328235763

theorem tailTrace_5159203 : CollatzResearch.WordTrace tailWord_5159203 prefixEnd_5159203 2649150933118283328235763 := by
  unfold tailWord_5159203
  simp only [CollatzResearch.WordTrace]
  refine ⟨188171592328096127567826263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125447728218730751711884175 188171592328096127567826263)
  ·
    refine ⟨282257388492144191351739395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188171592328096127567826263 282257388492144191351739395)
    ·
      refine ⟨423386082738216287027609093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 282257388492144191351739395 423386082738216287027609093)
      ·
        refine ⟨79384890513415553817676705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 423386082738216287027609093 79384890513415553817676705)
        ·
          refine ⟨59538667885061665363257529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79384890513415553817676705 59538667885061665363257529)
          ·
            refine ⟨44654000913796249022443147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59538667885061665363257529 44654000913796249022443147)
            ·
              refine ⟨66981001370694373533664721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44654000913796249022443147 66981001370694373533664721)
              ·
                refine ⟨50235751028020780150248541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66981001370694373533664721 50235751028020780150248541)
                ·
                  refine ⟨18838406635507792556343203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50235751028020780150248541 18838406635507792556343203)
                  ·
                    refine ⟨28257609953261688834514805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18838406635507792556343203 28257609953261688834514805)
                    ·
                      refine ⟨2649150933118283328235763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28257609953261688834514805 2649150933118283328235763)
                      ·
                        rfl

theorem cell23_5159203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 2, 3, 1, 5].length) (baseStart_5159203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5159203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5159203 prefixEnd_5159203 := by exact prefixLift 5159203
  have htrace : WordTrace (prefixWord ++ tailWord_5159203) baseStart_5159203 baseEnd_5159203 := by
    simpa [prefixWord, tailWord_5159203, baseEnd_5159203] using wordTrace_append hprefix tailTrace_5159203
  have hstable : (prefixWord ++ tailWord_5159203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5159203).length < 2 ^ (prefixWord ++ tailWord_5159203).sum := by decide
  have hdescent : baseEnd_5159203 < baseStart_5159203 := by decide
  rcases family_descends (prefixWord ++ tailWord_5159203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5159230 : List Nat := [4, 2, 1, 2, 1, 2, 1, 2, 1, 1, 6]
def baseStart_5159230 : Nat := 118140960795 + 5159230 * 2 ^ 59
def prefixEnd_5159230 : Nat := 4983230072969 + 3 ^ 40 * 5159230 * 2
def baseEnd_5159230 : Nat := 2649164797095954722598139

theorem tailTrace_5159230 : CollatzResearch.WordTrace tailWord_5159230 prefixEnd_5159230 2649164797095954722598139 := by
  unfold tailWord_5159230
  simp only [CollatzResearch.WordTrace]
  refine ⟨23521572137374788897382393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125448384732665540786039429 23521572137374788897382393)
  ·
    refine ⟨17641179103031091673036795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23521572137374788897382393 17641179103031091673036795)
    ·
      refine ⟨26461768654546637509555193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17641179103031091673036795 26461768654546637509555193)
      ·
        refine ⟨19846326490909978132166395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26461768654546637509555193 19846326490909978132166395)
        ·
          refine ⟨29769489736364967198249593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19846326490909978132166395 29769489736364967198249593)
          ·
            refine ⟨22327117302273725398687195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29769489736364967198249593 22327117302273725398687195)
            ·
              refine ⟨33490675953410588098030793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22327117302273725398687195 33490675953410588098030793)
              ·
                refine ⟨25118006965057941073523095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33490675953410588098030793 25118006965057941073523095)
                ·
                  refine ⟨37677010447586911610284643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25118006965057941073523095 37677010447586911610284643)
                  ·
                    refine ⟨56515515671380367415426965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37677010447586911610284643 56515515671380367415426965)
                    ·
                      refine ⟨2649164797095954722598139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56515515671380367415426965 2649164797095954722598139)
                      ·
                        rfl

theorem cell23_5159230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_5159230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5159230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5159230 prefixEnd_5159230 := by exact prefixLift 5159230
  have htrace : WordTrace (prefixWord ++ tailWord_5159230) baseStart_5159230 baseEnd_5159230 := by
    simpa [prefixWord, tailWord_5159230, baseEnd_5159230] using wordTrace_append hprefix tailTrace_5159230
  have hstable : (prefixWord ++ tailWord_5159230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5159230).length < 2 ^ (prefixWord ++ tailWord_5159230).sum := by decide
  have hdescent : baseEnd_5159230 < baseStart_5159230 := by decide
  rcases family_descends (prefixWord ++ tailWord_5159230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5159263 : List Nat := [1, 1, 2, 3, 1, 2, 2, 1, 1, 4, 5]
def baseStart_5159263 : Nat := 118140960795 + 5159263 * 2 ^ 59
def prefixEnd_5159263 : Nat := 4983230072969 + 3 ^ 40 * 5159263 * 2
def baseEnd_5159263 : Nat := 2649181741957553093485487

theorem tailTrace_5159263 : CollatzResearch.WordTrace tailWord_5159263 prefixEnd_5159263 2649181741957553093485487 := by
  unfold tailWord_5159263
  simp only [CollatzResearch.WordTrace]
  refine ⟨188173780707878757815010443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125449187138585838543340295 188173780707878757815010443)
  ·
    refine ⟨282260671061818136722515665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188173780707878757815010443 282260671061818136722515665)
    ·
      refine ⟨211695503296363602541886749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 282260671061818136722515665 211695503296363602541886749)
      ·
        refine ⟨79385813736136350953207531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 211695503296363602541886749 79385813736136350953207531)
        ·
          refine ⟨119078720604204526429811297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79385813736136350953207531 119078720604204526429811297)
          ·
            refine ⟨89309040453153394822358473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119078720604204526429811297 89309040453153394822358473)
            ·
              refine ⟨66981780339865046116768855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89309040453153394822358473 66981780339865046116768855)
              ·
                refine ⟨100472670509797569175153283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66981780339865046116768855 100472670509797569175153283)
                ·
                  refine ⟨150709005764696353762729925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 100472670509797569175153283 150709005764696353762729925)
                  ·
                    refine ⟨28257938580880566330511861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 150709005764696353762729925 28257938580880566330511861)
                    ·
                      refine ⟨2649181741957553093485487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28257938580880566330511861 2649181741957553093485487)
                      ·
                        rfl

theorem cell23_5159263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 4, 5].length) (baseStart_5159263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5159263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5159263 prefixEnd_5159263 := by exact prefixLift 5159263
  have htrace : WordTrace (prefixWord ++ tailWord_5159263) baseStart_5159263 baseEnd_5159263 := by
    simpa [prefixWord, tailWord_5159263, baseEnd_5159263] using wordTrace_append hprefix tailTrace_5159263
  have hstable : (prefixWord ++ tailWord_5159263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5159263).length < 2 ^ (prefixWord ++ tailWord_5159263).sum := by decide
  have hdescent : baseEnd_5159263 < baseStart_5159263 := by decide
  rcases family_descends (prefixWord ++ tailWord_5159263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5159283 : List Nat := [1, 1, 1, 2, 2, 1, 2, 3, 4, 6]
def baseStart_5159283 : Nat := 118140960795 + 5159283 * 2 ^ 59
def prefixEnd_5159283 : Nat := 4983230072969 + 3 ^ 40 * 5159283 * 2
def baseEnd_5159283 : Nat := 883064003856881005078465

theorem tailTrace_5159283 : CollatzResearch.WordTrace tailWord_5159283 prefixEnd_5159283 883064003856881005078465 := by
  unfold tailWord_5159283
  simp only [CollatzResearch.WordTrace]
  refine ⟨188174510167806301230738503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125449673445204200820492335 188174510167806301230738503)
  ·
    refine ⟨282261765251709451846107755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188174510167806301230738503 282261765251709451846107755)
    ·
      refine ⟨423392647877564177769161633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 282261765251709451846107755 423392647877564177769161633)
      ·
        refine ⟨317544485908173133326871225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 423392647877564177769161633 317544485908173133326871225)
        ·
          refine ⟨238158364431129849995153419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 317544485908173133326871225 238158364431129849995153419)
          ·
            refine ⟨357237546646694774992730129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 238158364431129849995153419 357237546646694774992730129)
            ·
              refine ⟨267928159985021081244547597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 357237546646694774992730129 267928159985021081244547597)
              ·
                refine ⟨100473059994382905466705349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 267928159985021081244547597 100473059994382905466705349)
                ·
                  refine ⟨18838698748946794775007253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 100473059994382905466705349 18838698748946794775007253)
                  ·
                    refine ⟨883064003856881005078465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18838698748946794775007253 883064003856881005078465)
                    ·
                      rfl

theorem cell23_5159283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 4, 6].length) (baseStart_5159283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5159283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5159283 prefixEnd_5159283 := by exact prefixLift 5159283
  have htrace : WordTrace (prefixWord ++ tailWord_5159283) baseStart_5159283 baseEnd_5159283 := by
    simpa [prefixWord, tailWord_5159283, baseEnd_5159283] using wordTrace_append hprefix tailTrace_5159283
  have hstable : (prefixWord ++ tailWord_5159283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5159283).length < 2 ^ (prefixWord ++ tailWord_5159283).sum := by decide
  have hdescent : baseEnd_5159283 < baseStart_5159283 := by decide
  rcases family_descends (prefixWord ++ tailWord_5159283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5159285 : List Nat := [1, 3, 4, 1, 2, 3, 2, 2, 1, 2, 2]
def baseStart_5159285 : Nat := 118140960795 + 5159285 * 2 ^ 59
def prefixEnd_5159285 : Nat := 4983230072969 + 3 ^ 40 * 5159285 * 2
def baseEnd_5159285 : Nat := 2649193038531952007410387

theorem tailTrace_5159285 : CollatzResearch.WordTrace tailWord_5159285 prefixEnd_5159285 2649193038531952007410387 := by
  unfold tailWord_5159285
  simp only [CollatzResearch.WordTrace]
  refine ⟨188174583113799055572311309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125449722075866037048207539 188174583113799055572311309)
  ·
    refine ⟨70565468667674645839616741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 188174583113799055572311309 70565468667674645839616741)
    ·
      refine ⟨13231025375188996094928139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70565468667674645839616741 13231025375188996094928139)
      ·
        refine ⟨19846538062783494142392209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13231025375188996094928139 19846538062783494142392209)
        ·
          refine ⟨14884903547087620606794157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19846538062783494142392209 14884903547087620606794157)
          ·
            refine ⟨5581838830157857727547809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14884903547087620606794157 5581838830157857727547809)
            ·
              refine ⟨4186379122618393295660857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5581838830157857727547809 4186379122618393295660857)
              ·
                refine ⟨3139784341963794971745643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4186379122618393295660857 3139784341963794971745643)
                ·
                  refine ⟨4709676512945692457618465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3139784341963794971745643 4709676512945692457618465)
                  ·
                    refine ⟨3532257384709269343213849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4709676512945692457618465 3532257384709269343213849)
                    ·
                      refine ⟨2649193038531952007410387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3532257384709269343213849 2649193038531952007410387)
                      ·
                        rfl

theorem cell23_5159285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 2, 2, 1, 2, 2].length) (baseStart_5159285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5159285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5159285 prefixEnd_5159285 := by exact prefixLift 5159285
  have htrace : WordTrace (prefixWord ++ tailWord_5159285) baseStart_5159285 baseEnd_5159285 := by
    simpa [prefixWord, tailWord_5159285, baseEnd_5159285] using wordTrace_append hprefix tailTrace_5159285
  have hstable : (prefixWord ++ tailWord_5159285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5159285).length < 2 ^ (prefixWord ++ tailWord_5159285).sum := by decide
  have hdescent : baseEnd_5159285 < baseStart_5159285 := by decide
  rcases family_descends (prefixWord ++ tailWord_5159285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5159300 : List Nat := [2, 3, 2, 1, 1, 2, 3, 1, 2, 6]
def baseStart_5159300 : Nat := 118140960795 + 5159300 * 2 ^ 59
def prefixEnd_5159300 : Nat := 4983230072969 + 3 ^ 40 * 5159300 * 2
def baseEnd_5159300 : Nat := 883066913580589816240939

theorem tailTrace_5159300 : CollatzResearch.WordTrace tailWord_5159300 prefixEnd_5159300 883066913580589816240939 := by
  unfold tailWord_5159300
  simp only [CollatzResearch.WordTrace]
  refine ⟨94087565104372356567053677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125450086805829808756071569 94087565104372356567053677)
  ·
    refine ⟨35282836914139633712645129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94087565104372356567053677 35282836914139633712645129)
    ·
      refine ⟨26462127685604725284483847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35282836914139633712645129 26462127685604725284483847)
      ·
        refine ⟨39693191528407087926725771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26462127685604725284483847 39693191528407087926725771)
        ·
          refine ⟨59539787292610631890088657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39693191528407087926725771 59539787292610631890088657)
          ·
            refine ⟨44654840469457973917566493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59539787292610631890088657 44654840469457973917566493)
            ·
              refine ⟨16745565176046740219087435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44654840469457973917566493 16745565176046740219087435)
              ·
                refine ⟨25118347764070110328631153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16745565176046740219087435 25118347764070110328631153)
                ·
                  refine ⟨18838760823052582746473365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25118347764070110328631153 18838760823052582746473365)
                  ·
                    refine ⟨883066913580589816240939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18838760823052582746473365 883066913580589816240939)
                    ·
                      rfl

theorem cell23_5159300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 1, 2, 6].length) (baseStart_5159300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5159300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5159300 prefixEnd_5159300 := by exact prefixLift 5159300
  have htrace : WordTrace (prefixWord ++ tailWord_5159300) baseStart_5159300 baseEnd_5159300 := by
    simpa [prefixWord, tailWord_5159300, baseEnd_5159300] using wordTrace_append hprefix tailTrace_5159300
  have hstable : (prefixWord ++ tailWord_5159300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5159300).length < 2 ^ (prefixWord ++ tailWord_5159300).sum := by decide
  have hdescent : baseEnd_5159300 < baseStart_5159300 := by decide
  rcases family_descends (prefixWord ++ tailWord_5159300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5159307 : List Nat := [1, 1, 1, 1, 4, 4, 1, 3, 1, 4, 2]
def baseStart_5159307 : Nat := 118140960795 + 5159307 * 2 ^ 59
def prefixEnd_5159307 : Nat := 4983230072969 + 3 ^ 40 * 5159307 * 2
def baseEnd_5159307 : Nat := 2649204335106350921335285

theorem tailTrace_5159307 : CollatzResearch.WordTrace tailWord_5159307 prefixEnd_5159307 2649204335106350921335285 := by
  unfold tailWord_5159307
  simp only [CollatzResearch.WordTrace]
  refine ⟨188175385519719353329612175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125450257013146235553074783 188175385519719353329612175)
  ·
    refine ⟨282263078279579029994418263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188175385519719353329612175 282263078279579029994418263)
    ·
      refine ⟨423394617419368544991627395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 282263078279579029994418263 423394617419368544991627395)
      ·
        refine ⟨635091926129052817487441093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 423394617419368544991627395 635091926129052817487441093)
        ·
          refine ⟨119079736149197403278895205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 635091926129052817487441093 119079736149197403278895205)
          ·
            refine ⟨22327450527974513114792851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 119079736149197403278895205 22327450527974513114792851)
            ·
              refine ⟨33491175791961769672189277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22327450527974513114792851 33491175791961769672189277)
              ·
                refine ⟨12559190921985663627070979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33491175791961769672189277 12559190921985663627070979)
                ·
                  refine ⟨18838786382978495440606469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12559190921985663627070979 18838786382978495440606469)
                  ·
                    refine ⟨3532272446808467895113713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18838786382978495440606469 3532272446808467895113713)
                    ·
                      refine ⟨2649204335106350921335285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3532272446808467895113713 2649204335106350921335285)
                      ·
                        rfl

theorem cell23_5159307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 3, 1, 4, 2].length) (baseStart_5159307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5159307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5159307 prefixEnd_5159307 := by exact prefixLift 5159307
  have htrace : WordTrace (prefixWord ++ tailWord_5159307) baseStart_5159307 baseEnd_5159307 := by
    simpa [prefixWord, tailWord_5159307, baseEnd_5159307] using wordTrace_append hprefix tailTrace_5159307
  have hstable : (prefixWord ++ tailWord_5159307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5159307).length < 2 ^ (prefixWord ++ tailWord_5159307).sum := by decide
  have hdescent : baseEnd_5159307 < baseStart_5159307 := by decide
  rcases family_descends (prefixWord ++ tailWord_5159307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5159330 : List Nat := [3, 3, 1, 2, 1, 1, 1, 2, 9]
def baseStart_5159330 : Nat := 118140960795 + 5159330 * 2 ^ 59
def prefixEnd_5159330 : Nat := 4983230072969 + 3 ^ 40 * 5159330 * 2
def baseEnd_5159330 : Nat := 294357349462378259038631

theorem tailTrace_5159330 : CollatzResearch.WordTrace tailWord_5159330 prefixEnd_5159330 294357349462378259038631 := by
  unfold tailWord_5159330
  simp only [CollatzResearch.WordTrace]
  refine ⟨47044056099659007064424861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125450816265757352171799629 47044056099659007064424861)
  ·
    refine ⟨17641521037372127649159323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47044056099659007064424861 17641521037372127649159323)
    ·
      refine ⟨26462281556058191473738985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17641521037372127649159323 26462281556058191473738985)
      ·
        refine ⟨19846711167043643605304239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26462281556058191473738985 19846711167043643605304239)
        ·
          refine ⟨29770066750565465407956359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19846711167043643605304239 29770066750565465407956359)
          ·
            refine ⟨44655100125848198111934539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29770066750565465407956359 44655100125848198111934539)
            ·
              refine ⟨66982650188772297167901809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44655100125848198111934539 66982650188772297167901809)
              ·
                refine ⟨50236987641579222875926357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66982650188772297167901809 50236987641579222875926357)
                ·
                  refine ⟨294357349462378259038631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 50236987641579222875926357 294357349462378259038631)
                  ·
                    rfl

theorem cell23_5159330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 2, 9].length) (baseStart_5159330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5159330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5159330 prefixEnd_5159330 := by exact prefixLift 5159330
  have htrace : WordTrace (prefixWord ++ tailWord_5159330) baseStart_5159330 baseEnd_5159330 := by
    simpa [prefixWord, tailWord_5159330, baseEnd_5159330] using wordTrace_append hprefix tailTrace_5159330
  have hstable : (prefixWord ++ tailWord_5159330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5159330).length < 2 ^ (prefixWord ++ tailWord_5159330).sum := by decide
  have hdescent : baseEnd_5159330 < baseStart_5159330 := by decide
  rcases family_descends (prefixWord ++ tailWord_5159330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5159357 : List Nat := [1, 4, 1, 2, 2, 2, 2, 1, 2, 3, 3]
def baseStart_5159357 : Nat := 118140960795 + 5159357 * 2 ^ 59
def prefixEnd_5159357 : Nat := 4983230072969 + 3 ^ 40 * 5159357 * 2
def baseEnd_5159357 : Nat := 2649230009139075725710055

theorem tailTrace_5159357 : CollatzResearch.WordTrace tailWord_5159357 prefixEnd_5159357 2649230009139075725710055 := by
  unfold tailWord_5159357
  simp only [CollatzResearch.WordTrace]
  refine ⟨188177209169538211868932325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125451472779692141245954883 188177209169538211868932325)
  ·
    refine ⟨35283226719288414725424811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 188177209169538211868932325 35283226719288414725424811)
    ·
      refine ⟨52924840078932622088137217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35283226719288414725424811 52924840078932622088137217)
      ·
        refine ⟨39693630059199466566102913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52924840078932622088137217 39693630059199466566102913)
        ·
          refine ⟨29770222544399599924577185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39693630059199466566102913 29770222544399599924577185)
          ·
            refine ⟨22327666908299699943432889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29770222544399599924577185 22327666908299699943432889)
            ·
              refine ⟨16745750181224774957574667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22327666908299699943432889 16745750181224774957574667)
              ·
                refine ⟨25118625271837162436362001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16745750181224774957574667 25118625271837162436362001)
                ·
                  refine ⟨18838968953877871827271501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25118625271837162436362001 18838968953877871827271501)
                  ·
                    refine ⟨7064613357704201935226813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18838968953877871827271501 7064613357704201935226813)
                    ·
                      refine ⟨2649230009139075725710055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7064613357704201935226813 2649230009139075725710055)
                      ·
                        rfl

theorem cell23_5159357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 1, 2, 3, 3].length) (baseStart_5159357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5159357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5159357 prefixEnd_5159357 := by exact prefixLift 5159357
  have htrace : WordTrace (prefixWord ++ tailWord_5159357) baseStart_5159357 baseEnd_5159357 := by
    simpa [prefixWord, tailWord_5159357, baseEnd_5159357] using wordTrace_append hprefix tailTrace_5159357
  have hstable : (prefixWord ++ tailWord_5159357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5159357).length < 2 ^ (prefixWord ++ tailWord_5159357).sum := by decide
  have hdescent : baseEnd_5159357 < baseStart_5159357 := by decide
  rcases family_descends (prefixWord ++ tailWord_5159357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5159414 : List Nat := [5, 1, 1, 1, 2, 1, 2, 1, 1, 6, 2]
def baseStart_5159414 : Nat := 118140960795 + 5159414 * 2 ^ 59
def prefixEnd_5159414 : Nat := 4983230072969 + 3 ^ 40 * 5159414 * 2
def baseEnd_5159414 : Nat := 2649259277536382002697293

theorem tailTrace_5159414 : CollatzResearch.WordTrace tailWord_5159414 prefixEnd_5159414 2649259277536382002697293 := by
  unfold tailWord_5159414
  simp only [CollatzResearch.WordTrace]
  refine ⟨11761205508145731912734831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 125452858753554473735838197 11761205508145731912734831)
  ·
    refine ⟨17641808262218597869102247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11761205508145731912734831 17641808262218597869102247)
    ·
      refine ⟨26462712393327896803653371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17641808262218597869102247 26462712393327896803653371)
      ·
        refine ⟨39694068589991845205480057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26462712393327896803653371 39694068589991845205480057)
        ·
          refine ⟨29770551442493883904110043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39694068589991845205480057 29770551442493883904110043)
          ·
            refine ⟨44655827163740825856165065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29770551442493883904110043 44655827163740825856165065)
            ·
              refine ⟨33491870372805619392123799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44655827163740825856165065 33491870372805619392123799)
              ·
                refine ⟨50237805559208429088185699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33491870372805619392123799 50237805559208429088185699)
                ·
                  refine ⟨75356708338812643632278549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50237805559208429088185699 75356708338812643632278549)
                  ·
                    refine ⟨3532345703381842670263057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 75356708338812643632278549 3532345703381842670263057)
                    ·
                      refine ⟨2649259277536382002697293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3532345703381842670263057 2649259277536382002697293)
                      ·
                        rfl

theorem cell23_5159414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 1, 1, 6, 2].length) (baseStart_5159414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5159414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5159414 prefixEnd_5159414 := by exact prefixLift 5159414
  have htrace : WordTrace (prefixWord ++ tailWord_5159414) baseStart_5159414 baseEnd_5159414 := by
    simpa [prefixWord, tailWord_5159414, baseEnd_5159414] using wordTrace_append hprefix tailTrace_5159414
  have hstable : (prefixWord ++ tailWord_5159414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5159414).length < 2 ^ (prefixWord ++ tailWord_5159414).sum := by decide
  have hdescent : baseEnd_5159414 < baseStart_5159414 := by decide
  rcases family_descends (prefixWord ++ tailWord_5159414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5159434 : List Nat := [3, 1, 2, 2, 2, 1, 4, 1, 2, 2, 3]
def baseStart_5159434 : Nat := 118140960795 + 5159434 * 2 ^ 59
def prefixEnd_5159434 : Nat := 4983230072969 + 3 ^ 40 * 5159434 * 2
def baseEnd_5159434 : Nat := 2649269547149471924447201

theorem tailTrace_5159434 : CollatzResearch.WordTrace tailWord_5159434 prefixEnd_5159434 2649269547149471924447201 := by
  unfold tailWord_5159434
  simp only [CollatzResearch.WordTrace]
  refine ⟨47045004397564813504871339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125453345060172836012990237 47045004397564813504871339)
  ·
    refine ⟨70567506596347220257307009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47045004397564813504871339 70567506596347220257307009)
    ·
      refine ⟨52925629947260415192980257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70567506596347220257307009 52925629947260415192980257)
      ·
        refine ⟨39694222460445311394735193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52925629947260415192980257 39694222460445311394735193)
        ·
          refine ⟨29770666845333983546051395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39694222460445311394735193 29770666845333983546051395)
          ·
            refine ⟨44656000268000975319077093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29770666845333983546051395 44656000268000975319077093)
            ·
              refine ⟨8373000050250182872326955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44656000268000975319077093 8373000050250182872326955)
              ·
                refine ⟨12559500075375274308490433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8373000050250182872326955 12559500075375274308490433)
                ·
                  refine ⟨9419625056531455731367825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12559500075375274308490433 9419625056531455731367825)
                  ·
                    refine ⟨7064718792398591798525869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9419625056531455731367825 7064718792398591798525869)
                    ·
                      refine ⟨2649269547149471924447201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7064718792398591798525869 2649269547149471924447201)
                      ·
                        rfl

theorem cell23_5159434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 4, 1, 2, 2, 3].length) (baseStart_5159434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5159434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5159434 prefixEnd_5159434 := by exact prefixLift 5159434
  have htrace : WordTrace (prefixWord ++ tailWord_5159434) baseStart_5159434 baseEnd_5159434 := by
    simpa [prefixWord, tailWord_5159434, baseEnd_5159434] using wordTrace_append hprefix tailTrace_5159434
  have hstable : (prefixWord ++ tailWord_5159434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5159434).length < 2 ^ (prefixWord ++ tailWord_5159434).sum := by decide
  have hdescent : baseEnd_5159434 < baseStart_5159434 := by decide
  rcases family_descends (prefixWord ++ tailWord_5159434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5159474 : List Nat := [3, 2, 1, 1, 2, 1, 2, 2, 4, 3, 2]
def baseStart_5159474 : Nat := 118140960795 + 5159474 * 2 ^ 59
def prefixEnd_5159474 : Nat := 4983230072969 + 3 ^ 40 * 5159474 * 2
def baseEnd_5159474 : Nat := 2649290086375651767947017

theorem tailTrace_5159474 : CollatzResearch.WordTrace tailWord_5159474 prefixEnd_5159474 2649290086375651767947017 := by
  unfold tailWord_5159474
  simp only [CollatzResearch.WordTrace]
  refine ⟨47045369127528585212735369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125454317673409560567294317 47045369127528585212735369)
  ·
    refine ⟨35284026845646438909551527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47045369127528585212735369 35284026845646438909551527)
    ·
      refine ⟨52926040268469658364327291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35284026845646438909551527 52926040268469658364327291)
      ·
        refine ⟨79389060402704487546490937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52926040268469658364327291 79389060402704487546490937)
        ·
          refine ⟨59541795302028365659868203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79389060402704487546490937 59541795302028365659868203)
          ·
            refine ⟨89312692953042548489802305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59541795302028365659868203 89312692953042548489802305)
            ·
              refine ⟨66984519714781911367351729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89312692953042548489802305 66984519714781911367351729)
              ·
                refine ⟨50238389786086433525513797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66984519714781911367351729 50238389786086433525513797)
                ·
                  refine ⟨9419698084891206286033837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50238389786086433525513797 9419698084891206286033837)
                  ·
                    refine ⟨3532386781834202357262689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9419698084891206286033837 3532386781834202357262689)
                    ·
                      refine ⟨2649290086375651767947017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3532386781834202357262689 2649290086375651767947017)
                      ·
                        rfl

theorem cell23_5159474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 2, 4, 3, 2].length) (baseStart_5159474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5159474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5159474 prefixEnd_5159474 := by exact prefixLift 5159474
  have htrace : WordTrace (prefixWord ++ tailWord_5159474) baseStart_5159474 baseEnd_5159474 := by
    simpa [prefixWord, tailWord_5159474, baseEnd_5159474] using wordTrace_append hprefix tailTrace_5159474
  have hstable : (prefixWord ++ tailWord_5159474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5159474).length < 2 ^ (prefixWord ++ tailWord_5159474).sum := by decide
  have hdescent : baseEnd_5159474 < baseStart_5159474 := by decide
  rcases family_descends (prefixWord ++ tailWord_5159474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5159487 : List Nat := [1, 1, 2, 2, 3, 2, 1, 3, 3, 1, 4]
def baseStart_5159487 : Nat := 118140960795 + 5159487 * 2 ^ 59
def prefixEnd_5159487 : Nat := 4983230072969 + 3 ^ 40 * 5159487 * 2
def baseEnd_5159487 : Nat := 2649296761624160217084457

theorem tailTrace_5159487 : CollatzResearch.WordTrace tailWord_5159487 prefixEnd_5159487 2649296761624160217084457 := by
  unfold tailWord_5159487
  simp only [CollatzResearch.WordTrace]
  refine ⟨188181950659067244071164715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125454633772711496047443143 188181950659067244071164715)
  ·
    refine ⟨282272925988600866106747073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188181950659067244071164715 282272925988600866106747073)
    ·
      refine ⟨211704694491450649580060305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 282272925988600866106747073 211704694491450649580060305)
      ·
        refine ⟨158778520868587987185045229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 211704694491450649580060305 158778520868587987185045229)
        ·
          refine ⟨59541945325720495194391961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 158778520868587987185045229 59541945325720495194391961)
          ·
            refine ⟨44656458994290371395793971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59541945325720495194391961 44656458994290371395793971)
            ·
              refine ⟨66984688491435557093690957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44656458994290371395793971 66984688491435557093690957)
              ·
                refine ⟨25119258184288333910134109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66984688491435557093690957 25119258184288333910134109)
                ·
                  refine ⟨9419721819108125216300291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25119258184288333910134109 9419721819108125216300291)
                  ·
                    refine ⟨14129582728662187824450437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9419721819108125216300291 14129582728662187824450437)
                    ·
                      refine ⟨2649296761624160217084457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14129582728662187824450437 2649296761624160217084457)
                      ·
                        rfl

theorem cell23_5159487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 3, 3, 1, 4].length) (baseStart_5159487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5159487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5159487 prefixEnd_5159487 := by exact prefixLift 5159487
  have htrace : WordTrace (prefixWord ++ tailWord_5159487) baseStart_5159487 baseEnd_5159487 := by
    simpa [prefixWord, tailWord_5159487, baseEnd_5159487] using wordTrace_append hprefix tailTrace_5159487
  have hstable : (prefixWord ++ tailWord_5159487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5159487).length < 2 ^ (prefixWord ++ tailWord_5159487).sum := by decide
  have hdescent : baseEnd_5159487 < baseStart_5159487 := by decide
  rcases family_descends (prefixWord ++ tailWord_5159487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5159492 : List Nat := [2, 3, 5, 1, 1, 1, 2, 3, 1, 4]
def baseStart_5159492 : Nat := 118140960795 + 5159492 * 2 ^ 59
def prefixEnd_5159492 : Nat := 4983230072969 + 3 ^ 40 * 5159492 * 2
def baseEnd_5159492 : Nat := 883099776342477565840645

theorem tailTrace_5159492 : CollatzResearch.WordTrace tailWord_5159492 prefixEnd_5159492 883099776342477565840645 := by
  unfold tailWord_5159492
  simp only [CollatzResearch.WordTrace]
  refine ⟨94091066512024564962548365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125454755349366086616731153 94091066512024564962548365)
  ·
    refine ⟨35284149942009211860955637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94091066512024564962548365 35284149942009211860955637)
    ·
      refine ⟨3307889057063363611964591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 35284149942009211860955637 3307889057063363611964591)
      ·
        refine ⟨4961833585595045417946887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3307889057063363611964591 4961833585595045417946887)
        ·
          refine ⟨7442750378392568126920331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4961833585595045417946887 7442750378392568126920331)
          ·
            refine ⟨11164125567588852190380497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7442750378392568126920331 11164125567588852190380497)
            ·
              refine ⟨8373094175691639142785373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11164125567588852190380497 8373094175691639142785373)
              ·
                refine ⟨3139910315884364678544515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8373094175691639142785373 3139910315884364678544515)
                ·
                  refine ⟨4709865473826547017816773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3139910315884364678544515 4709865473826547017816773)
                  ·
                    refine ⟨883099776342477565840645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4709865473826547017816773 883099776342477565840645)
                    ·
                      rfl

theorem cell23_5159492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_5159492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5159492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5159492 prefixEnd_5159492 := by exact prefixLift 5159492
  have htrace : WordTrace (prefixWord ++ tailWord_5159492) baseStart_5159492 baseEnd_5159492 := by
    simpa [prefixWord, tailWord_5159492, baseEnd_5159492] using wordTrace_append hprefix tailTrace_5159492
  have hstable : (prefixWord ++ tailWord_5159492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5159492).length < 2 ^ (prefixWord ++ tailWord_5159492).sum := by decide
  have hdescent : baseEnd_5159492 < baseStart_5159492 := by decide
  rcases family_descends (prefixWord ++ tailWord_5159492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5159498 : List Nat := [3, 1, 2, 1, 1, 5, 2, 3, 1, 1, 3]
def baseStart_5159498 : Nat := 118140960795 + 5159498 * 2 ^ 59
def prefixEnd_5159498 : Nat := 4983230072969 + 3 ^ 40 * 5159498 * 2
def baseEnd_5159498 : Nat := 2649302409911359674046907

theorem tailTrace_5159498 : CollatzResearch.WordTrace tailWord_5159498 prefixEnd_5159498 2649302409911359674046907 := by
  unfold tailWord_5159498
  simp only [CollatzResearch.WordTrace]
  refine ⟨47045587965506848237453787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125454901241351595299876765 47045587965506848237453787)
  ·
    refine ⟨70568381948260272356180681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47045587965506848237453787 70568381948260272356180681)
    ·
      refine ⟨52926286461195204267135511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70568381948260272356180681 52926286461195204267135511)
      ·
        refine ⟨79389429691792806400703267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52926286461195204267135511 79389429691792806400703267)
        ·
          refine ⟨119084144537689209601054901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79389429691792806400703267 119084144537689209601054901)
          ·
            refine ⟨11164138550408363400098897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 119084144537689209601054901 11164138550408363400098897)
            ·
              refine ⟨8373103912806272550074173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11164138550408363400098897 8373103912806272550074173)
              ·
                refine ⟨3139913967302352206277815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8373103912806272550074173 3139913967302352206277815)
                ·
                  refine ⟨4709870950953528309416723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3139913967302352206277815 4709870950953528309416723)
                  ·
                    refine ⟨7064806426430292464125085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4709870950953528309416723 7064806426430292464125085)
                    ·
                      refine ⟨2649302409911359674046907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7064806426430292464125085 2649302409911359674046907)
                      ·
                        rfl

theorem cell23_5159498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 2, 3, 1, 1, 3].length) (baseStart_5159498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5159498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5159498 prefixEnd_5159498 := by exact prefixLift 5159498
  have htrace : WordTrace (prefixWord ++ tailWord_5159498) baseStart_5159498 baseEnd_5159498 := by
    simpa [prefixWord, tailWord_5159498, baseEnd_5159498] using wordTrace_append hprefix tailTrace_5159498
  have hstable : (prefixWord ++ tailWord_5159498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5159498).length < 2 ^ (prefixWord ++ tailWord_5159498).sum := by decide
  have hdescent : baseEnd_5159498 < baseStart_5159498 := by decide
  rcases family_descends (prefixWord ++ tailWord_5159498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5159501 : List Nat := [1, 6, 1, 1, 2, 2, 1, 3, 1, 5]
def baseStart_5159501 : Nat := 118140960795 + 5159501 * 2 ^ 59
def prefixEnd_5159501 : Nat := 4983230072969 + 3 ^ 40 * 5159501 * 2
def baseEnd_5159501 : Nat := 883101316784441054103131

theorem tailTrace_5159501 : CollatzResearch.WordTrace tailWord_5159501 prefixEnd_5159501 883101316784441054103131 := by
  unfold tailWord_5159501
  simp only [CollatzResearch.WordTrace]
  refine ⟨188182461281016524462174357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125454974187344349641449571 188182461281016524462174357)
  ·
    refine ⟨8821052872547649584164423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 188182461281016524462174357 8821052872547649584164423)
    ·
      refine ⟨13231579308821474376246635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8821052872547649584164423 13231579308821474376246635)
      ·
        refine ⟨19847368963232211564369953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13231579308821474376246635 19847368963232211564369953)
        ·
          refine ⟨14885526722424158673277465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19847368963232211564369953 14885526722424158673277465)
          ·
            refine ⟨11164145041818119004958099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14885526722424158673277465 11164145041818119004958099)
            ·
              refine ⟨16746217562727178507437149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11164145041818119004958099 16746217562727178507437149)
              ·
                refine ⟨6279831586022691940288931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16746217562727178507437149 6279831586022691940288931)
                ·
                  refine ⟨9419747379034037910433397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6279831586022691940288931 9419747379034037910433397)
                  ·
                    refine ⟨883101316784441054103131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9419747379034037910433397 883101316784441054103131)
                    ·
                      rfl

theorem cell23_5159501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 3, 1, 5].length) (baseStart_5159501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5159501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5159501 prefixEnd_5159501 := by exact prefixLift 5159501
  have htrace : WordTrace (prefixWord ++ tailWord_5159501) baseStart_5159501 baseEnd_5159501 := by
    simpa [prefixWord, tailWord_5159501, baseEnd_5159501] using wordTrace_append hprefix tailTrace_5159501
  have hstable : (prefixWord ++ tailWord_5159501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5159501).length < 2 ^ (prefixWord ++ tailWord_5159501).sum := by decide
  have hdescent : baseEnd_5159501 < baseStart_5159501 := by decide
  rcases family_descends (prefixWord ++ tailWord_5159501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5159521 : List Nat := [1, 2, 3, 1, 1, 4, 1, 3, 3, 2, 2]
def baseStart_5159521 : Nat := 118140960795 + 5159521 * 2 ^ 59
def prefixEnd_5159521 : Nat := 4983230072969 + 3 ^ 40 * 5159521 * 2
def baseEnd_5159521 : Nat := 2649314219966413084059301

theorem tailTrace_5159521 : CollatzResearch.WordTrace tailWord_5159521 prefixEnd_5159521 2649314219966413084059301 := by
  unfold tailWord_5159521
  simp only [CollatzResearch.WordTrace]
  refine ⟨188183190740944067877902417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125455460493962711918601611 188183190740944067877902417)
  ·
    refine ⟨141137393055708050908426813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188183190740944067877902417 141137393055708050908426813)
    ·
      refine ⟨52926522395890519090660055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141137393055708050908426813 52926522395890519090660055)
      ·
        refine ⟨79389783593835778635990083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52926522395890519090660055 79389783593835778635990083)
        ·
          refine ⟨119084675390753667953985125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79389783593835778635990083 119084675390753667953985125)
          ·
            refine ⟨22328376635766312741372211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 119084675390753667953985125 22328376635766312741372211)
            ·
              refine ⟨33492564953649469112058317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22328376635766312741372211 33492564953649469112058317)
              ·
                refine ⟨12559711857618550917021869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33492564953649469112058317 12559711857618550917021869)
                ·
                  refine ⟨4709891946606956593883201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12559711857618550917021869 4709891946606956593883201)
                  ·
                    refine ⟨3532418959955217445412401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4709891946606956593883201 3532418959955217445412401)
                    ·
                      refine ⟨2649314219966413084059301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3532418959955217445412401 2649314219966413084059301)
                      ·
                        rfl

theorem cell23_5159521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 3, 3, 2, 2].length) (baseStart_5159521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5159521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5159521 prefixEnd_5159521 := by exact prefixLift 5159521
  have htrace : WordTrace (prefixWord ++ tailWord_5159521) baseStart_5159521 baseEnd_5159521 := by
    simpa [prefixWord, tailWord_5159521, baseEnd_5159521] using wordTrace_append hprefix tailTrace_5159521
  have hstable : (prefixWord ++ tailWord_5159521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5159521).length < 2 ^ (prefixWord ++ tailWord_5159521).sum := by decide
  have hdescent : baseEnd_5159521 < baseStart_5159521 := by decide
  rcases family_descends (prefixWord ++ tailWord_5159521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5159534 : List Nat := [4, 1, 2, 2, 2, 2, 1, 1, 1, 1, 6]
def baseStart_5159534 : Nat := 118140960795 + 5159534 * 2 ^ 59
def prefixEnd_5159534 : Nat := 4983230072969 + 3 ^ 40 * 5159534 * 2
def baseEnd_5159534 : Nat := 2649320895214921533196741

theorem tailTrace_5159534 : CollatzResearch.WordTrace tailWord_5159534 prefixEnd_5159534 2649320895214921533196741 := by
  unfold tailWord_5159534
  simp only [CollatzResearch.WordTrace]
  refine ⟨23522958111237121387265707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125455776593264647398750437 23522958111237121387265707)
  ·
    refine ⟨35284437166855682080898561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23522958111237121387265707 35284437166855682080898561)
    ·
      refine ⟨26463327875141761560673921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35284437166855682080898561 26463327875141761560673921)
      ·
        refine ⟨19847495906356321170505441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26463327875141761560673921 19847495906356321170505441)
        ·
          refine ⟨14885621929767240877879081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19847495906356321170505441 14885621929767240877879081)
          ·
            refine ⟨11164216447325430658409311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14885621929767240877879081 11164216447325430658409311)
            ·
              refine ⟨16746324670988145987613967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11164216447325430658409311 16746324670988145987613967)
              ·
                refine ⟨25119487006482218981420951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16746324670988145987613967 25119487006482218981420951)
                ·
                  refine ⟨37679230509723328472131427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25119487006482218981420951 37679230509723328472131427)
                  ·
                    refine ⟨56518845764584992708197141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37679230509723328472131427 56518845764584992708197141)
                    ·
                      refine ⟨2649320895214921533196741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56518845764584992708197141 2649320895214921533196741)
                      ·
                        rfl

theorem cell23_5159534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_5159534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5159534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5159534 prefixEnd_5159534 := by exact prefixLift 5159534
  have htrace : WordTrace (prefixWord ++ tailWord_5159534) baseStart_5159534 baseEnd_5159534 := by
    simpa [prefixWord, tailWord_5159534, baseEnd_5159534] using wordTrace_append hprefix tailTrace_5159534
  have hstable : (prefixWord ++ tailWord_5159534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5159534).length < 2 ^ (prefixWord ++ tailWord_5159534).sum := by decide
  have hdescent : baseEnd_5159534 < baseStart_5159534 := by decide
  rcases family_descends (prefixWord ++ tailWord_5159534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5159577 : List Nat := [1, 2, 1, 2, 1, 2, 4, 1, 2, 3, 4]
def baseStart_5159577 : Nat := 118140960795 + 5159577 * 2 ^ 59
def prefixEnd_5159577 : Nat := 4983230072969 + 3 ^ 40 * 5159577 * 2
def baseEnd_5159577 : Nat := 2649342974883064864959043

theorem tailTrace_5159577 : CollatzResearch.WordTrace tailWord_5159577 prefixEnd_5159577 2649342974883064864959043 := by
  unfold tailWord_5159577
  simp only [CollatzResearch.WordTrace]
  refine ⟨188185233228741189441940985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125456822152494126294627323 188185233228741189441940985)
  ·
    refine ⟨141138924921555892081455739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188185233228741189441940985 141138924921555892081455739)
    ·
      refine ⟨211708387382333838122183609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141138924921555892081455739 211708387382333838122183609)
      ·
        refine ⟨158781290536750378591637707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 211708387382333838122183609 158781290536750378591637707)
        ·
          refine ⟨238171935805125567887456561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158781290536750378591637707 238171935805125567887456561)
          ·
            refine ⟨178628951853844175915592421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 238171935805125567887456561 178628951853844175915592421)
            ·
              refine ⟨33492928472595782984173579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 178628951853844175915592421 33492928472595782984173579)
              ·
                refine ⟨50239392708893674476260369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33492928472595782984173579 50239392708893674476260369)
                ·
                  refine ⟨37679544531670255857195277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50239392708893674476260369 37679544531670255857195277)
                  ·
                    refine ⟨14129829199376345946448229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37679544531670255857195277 14129829199376345946448229)
                    ·
                      refine ⟨2649342974883064864959043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14129829199376345946448229 2649342974883064864959043)
                      ·
                        rfl

theorem cell23_5159577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 1, 2, 3, 4].length) (baseStart_5159577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5159577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5159577 prefixEnd_5159577 := by exact prefixLift 5159577
  have htrace : WordTrace (prefixWord ++ tailWord_5159577) baseStart_5159577 baseEnd_5159577 := by
    simpa [prefixWord, tailWord_5159577, baseEnd_5159577] using wordTrace_append hprefix tailTrace_5159577
  have hstable : (prefixWord ++ tailWord_5159577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5159577).length < 2 ^ (prefixWord ++ tailWord_5159577).sum := by decide
  have hdescent : baseEnd_5159577 < baseStart_5159577 := by decide
  rcases family_descends (prefixWord ++ tailWord_5159577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5159614 : List Nat := [4, 2, 1, 1, 2, 1, 1, 3, 2, 1, 5]
def baseStart_5159614 : Nat := 118140960795 + 5159614 * 2 ^ 59
def prefixEnd_5159614 : Nat := 4983230072969 + 3 ^ 40 * 5159614 * 2
def baseEnd_5159614 : Nat := 2649361973667281220196373

theorem tailTrace_5159614 : CollatzResearch.WordTrace tailWord_5159614 prefixEnd_5159614 2649361973667281220196373 := by
  unfold tailWord_5159614
  simp only [CollatzResearch.WordTrace]
  refine ⟨23523322841200893095129737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125457721819738096507358597 23523322841200893095129737)
  ·
    refine ⟨17642492130900669821347303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23523322841200893095129737 17642492130900669821347303)
    ·
      refine ⟨26463738196351004732020955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17642492130900669821347303 26463738196351004732020955)
      ·
        refine ⟨39695607294526507098031433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26463738196351004732020955 39695607294526507098031433)
        ·
          refine ⟨29771705470894880323523575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39695607294526507098031433 29771705470894880323523575)
          ·
            refine ⟨44657558206342320485285363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29771705470894880323523575 44657558206342320485285363)
            ·
              refine ⟨66986337309513480727928045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44657558206342320485285363 66986337309513480727928045)
              ·
                refine ⟨25119876491067555272973017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66986337309513480727928045 25119876491067555272973017)
                ·
                  refine ⟨18839907368300666454729763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25119876491067555272973017 18839907368300666454729763)
                  ·
                    refine ⟨28259861052450999682094645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18839907368300666454729763 28259861052450999682094645)
                    ·
                      refine ⟨2649361973667281220196373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28259861052450999682094645 2649361973667281220196373)
                      ·
                        rfl

theorem cell23_5159614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 3, 2, 1, 5].length) (baseStart_5159614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5159614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5159614 prefixEnd_5159614 := by exact prefixLift 5159614
  have htrace : WordTrace (prefixWord ++ tailWord_5159614) baseStart_5159614 baseEnd_5159614 := by
    simpa [prefixWord, tailWord_5159614, baseEnd_5159614] using wordTrace_append hprefix tailTrace_5159614
  have hstable : (prefixWord ++ tailWord_5159614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5159614).length < 2 ^ (prefixWord ++ tailWord_5159614).sum := by decide
  have hdescent : baseEnd_5159614 < baseStart_5159614 := by decide
  rcases family_descends (prefixWord ++ tailWord_5159614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5159657 : List Nat := [1, 2, 1, 1, 1, 2, 4, 2, 1, 1, 7]
def baseStart_5159657 : Nat := 118140960795 + 5159657 * 2 ^ 59
def prefixEnd_5159657 : Nat := 4983230072969 + 3 ^ 40 * 5159657 * 2
def baseEnd_5159657 : Nat := 2649384053335424551958675

theorem tailTrace_5159657 : CollatzResearch.WordTrace tailWord_5159657 prefixEnd_5159657 2649384053335424551958675 := by
  unfold tailWord_5159657
  simp only [CollatzResearch.WordTrace]
  refine ⟨188188151068451363104853225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125458767378967575403235483 188188151068451363104853225)
  ·
    refine ⟨141141113301338522328639919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188188151068451363104853225 141141113301338522328639919)
    ·
      refine ⟨211711669952007783492959879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141141113301338522328639919 211711669952007783492959879)
      ·
        refine ⟨317567504928011675239439819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211711669952007783492959879 317567504928011675239439819)
        ·
          refine ⟨476351257392017512859159729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 317567504928011675239439819 476351257392017512859159729)
          ·
            refine ⟨357263443044013134644369797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 476351257392017512859159729 357263443044013134644369797)
            ·
              refine ⟨66986895570752462745819337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 357263443044013134644369797 66986895570752462745819337)
              ·
                refine ⟨50240171678064347059364503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66986895570752462745819337 50240171678064347059364503)
                ·
                  refine ⟨75360257517096520589046755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50240171678064347059364503 75360257517096520589046755)
                  ·
                    refine ⟨113040386275644780883570133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 75360257517096520589046755 113040386275644780883570133)
                    ·
                      refine ⟨2649384053335424551958675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 113040386275644780883570133 2649384053335424551958675)
                      ·
                        rfl

theorem cell23_5159657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 2, 1, 1, 7].length) (baseStart_5159657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5159657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5159657 prefixEnd_5159657 := by exact prefixLift 5159657
  have htrace : WordTrace (prefixWord ++ tailWord_5159657) baseStart_5159657 baseEnd_5159657 := by
    simpa [prefixWord, tailWord_5159657, baseEnd_5159657] using wordTrace_append hprefix tailTrace_5159657
  have hstable : (prefixWord ++ tailWord_5159657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5159657).length < 2 ^ (prefixWord ++ tailWord_5159657).sum := by decide
  have hdescent : baseEnd_5159657 < baseStart_5159657 := by decide
  rcases family_descends (prefixWord ++ tailWord_5159657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5159701 : List Nat := [1, 3, 2, 1, 2, 2, 1, 3, 2, 4, 2]
def baseStart_5159701 : Nat := 118140960795 + 5159701 * 2 ^ 59
def prefixEnd_5159701 : Nat := 4983230072969 + 3 ^ 40 * 5159701 * 2
def baseEnd_5159701 : Nat := 2649406646484222379808473

theorem tailTrace_5159701 : CollatzResearch.WordTrace tailWord_5159701 prefixEnd_5159701 2649406646484222379808473 := by
  unfold tailWord_5159701
  simp only [CollatzResearch.WordTrace]
  refine ⟨188189755880291958619454957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125459837253527972412969971 188189755880291958619454957)
  ·
    refine ⟨70571158455109484482295609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 188189755880291958619454957 70571158455109484482295609)
    ·
      refine ⟨52928368841332113361721707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70571158455109484482295609 52928368841332113361721707)
      ·
        refine ⟨79392553261998170042582561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52928368841332113361721707 79392553261998170042582561)
        ·
          refine ⟨59544414946498627531936921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79392553261998170042582561 59544414946498627531936921)
          ·
            refine ⟨44658311209873970648952691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59544414946498627531936921 44658311209873970648952691)
            ·
              refine ⟨66987466814810955973429037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44658311209873970648952691 66987466814810955973429037)
              ·
                refine ⟨25120300055554108490035889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66987466814810955973429037 25120300055554108490035889)
                ·
                  refine ⟨18840225041665581367526917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25120300055554108490035889 18840225041665581367526917)
                  ·
                    refine ⟨3532542195312296506411297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18840225041665581367526917 3532542195312296506411297)
                    ·
                      refine ⟨2649406646484222379808473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3532542195312296506411297 2649406646484222379808473)
                      ·
                        rfl

theorem cell23_5159701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 3, 2, 4, 2].length) (baseStart_5159701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5159701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5159701 prefixEnd_5159701 := by exact prefixLift 5159701
  have htrace : WordTrace (prefixWord ++ tailWord_5159701) baseStart_5159701 baseEnd_5159701 := by
    simpa [prefixWord, tailWord_5159701, baseEnd_5159701] using wordTrace_append hprefix tailTrace_5159701
  have hstable : (prefixWord ++ tailWord_5159701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5159701).length < 2 ^ (prefixWord ++ tailWord_5159701).sum := by decide
  have hdescent : baseEnd_5159701 < baseStart_5159701 := by decide
  rcases family_descends (prefixWord ++ tailWord_5159701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5159707 : List Nat := [1, 1, 1, 1, 1, 1, 4, 1, 12]
def baseStart_5159707 : Nat := 118140960795 + 5159707 * 2 ^ 59
def prefixEnd_5159707 : Nat := 4983230072969 + 3 ^ 40 * 5159707 * 2
def baseEnd_5159707 : Nat := 294378858596461039592605

theorem tailTrace_5159707 : CollatzResearch.WordTrace tailWord_5159707 prefixEnd_5159707 294378858596461039592605 := by
  unfold tailWord_5159707
  simp only [CollatzResearch.WordTrace]
  refine ⟨188189974718270221644173375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125459983145513481096115583 188189974718270221644173375)
  ·
    refine ⟨282284962077405332466260063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188189974718270221644173375 282284962077405332466260063)
    ·
      refine ⟨423427443116107998699390095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 282284962077405332466260063 423427443116107998699390095)
      ·
        refine ⟨635141164674161998049085143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 423427443116107998699390095 635141164674161998049085143)
        ·
          refine ⟨952711747011242997073627715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 635141164674161998049085143 952711747011242997073627715)
          ·
            refine ⟨1429067620516864495610441573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 952711747011242997073627715 1429067620516864495610441573)
            ·
              refine ⟨267950178846912092926957795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1429067620516864495610441573 267950178846912092926957795)
              ·
                refine ⟨401925268270368139390436693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 267950178846912092926957795 401925268270368139390436693)
                ·
                  refine ⟨294378858596461039592605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 401925268270368139390436693 294378858596461039592605)
                  ·
                    rfl

theorem cell23_5159707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 12].length) (baseStart_5159707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5159707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5159707 prefixEnd_5159707 := by exact prefixLift 5159707
  have htrace : WordTrace (prefixWord ++ tailWord_5159707) baseStart_5159707 baseEnd_5159707 := by
    simpa [prefixWord, tailWord_5159707, baseEnd_5159707] using wordTrace_append hprefix tailTrace_5159707
  have hstable : (prefixWord ++ tailWord_5159707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5159707).length < 2 ^ (prefixWord ++ tailWord_5159707).sum := by decide
  have hdescent : baseEnd_5159707 < baseStart_5159707 := by decide
  rcases family_descends (prefixWord ++ tailWord_5159707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5159711 : List Nat := [1, 1, 2, 4, 2, 2, 2, 2, 3, 4]
def baseStart_5159711 : Nat := 118140960795 + 5159711 * 2 ^ 59
def prefixEnd_5159711 : Nat := 4983230072969 + 3 ^ 40 * 5159711 * 2
def baseEnd_5159711 : Nat := 883137260430255780227809

theorem tailTrace_5159711 : CollatzResearch.WordTrace tailWord_5159711 prefixEnd_5159711 883137260430255780227809 := by
  unfold tailWord_5159711
  simp only [CollatzResearch.WordTrace]
  refine ⟨188190120610255730327318987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125460080406837153551545991 188190120610255730327318987)
  ·
    refine ⟨282285180915383595490978481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188190120610255730327318987 282285180915383595490978481)
    ·
      refine ⟨211713885686537696618233861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 282285180915383595490978481 211713885686537696618233861)
      ·
        refine ⟨39696353566225818115918849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 211713885686537696618233861 39696353566225818115918849)
        ·
          refine ⟨29772265174669363586939137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39696353566225818115918849 29772265174669363586939137)
          ·
            refine ⟨22329198881002022690204353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29772265174669363586939137 22329198881002022690204353)
            ·
              refine ⟨16746899160751517017653265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22329198881002022690204353 16746899160751517017653265)
              ·
                refine ⟨12560174370563637763239949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16746899160751517017653265 12560174370563637763239949)
                ·
                  refine ⟨4710065388961364161214981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12560174370563637763239949 4710065388961364161214981)
                  ·
                    refine ⟨883137260430255780227809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4710065388961364161214981 883137260430255780227809)
                    ·
                      rfl

theorem cell23_5159711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 2, 3, 4].length) (baseStart_5159711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5159711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5159711 prefixEnd_5159711 := by exact prefixLift 5159711
  have htrace : WordTrace (prefixWord ++ tailWord_5159711) baseStart_5159711 baseEnd_5159711 := by
    simpa [prefixWord, tailWord_5159711, baseEnd_5159711] using wordTrace_append hprefix tailTrace_5159711
  have hstable : (prefixWord ++ tailWord_5159711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5159711).length < 2 ^ (prefixWord ++ tailWord_5159711).sum := by decide
  have hdescent : baseEnd_5159711 < baseStart_5159711 := by decide
  rcases family_descends (prefixWord ++ tailWord_5159711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5159738 : List Nat := [3, 1, 1, 1, 6, 1, 1, 2, 2, 2, 3]
def baseStart_5159738 : Nat := 118140960795 + 5159738 * 2 ^ 59
def prefixEnd_5159738 : Nat := 4983230072969 + 3 ^ 40 * 5159738 * 2
def baseEnd_5159738 : Nat := 2649425645268438735045803

theorem tailTrace_5159738 : CollatzResearch.WordTrace tailWord_5159738 prefixEnd_5159738 2649425645268438735045803 := by
  unfold tailWord_5159738
  simp only [CollatzResearch.WordTrace]
  refine ⟨47047776345289478484637967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125460736920771942625701245 47047776345289478484637967)
  ·
    refine ⟨70571664517934217726956951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47047776345289478484637967 70571664517934217726956951)
    ·
      refine ⟨105857496776901326590435427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70571664517934217726956951 105857496776901326590435427)
      ·
        refine ⟨158786245165351989885653141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105857496776901326590435427 158786245165351989885653141)
        ·
          refine ⟨7443105242125874525889991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 158786245165351989885653141 7443105242125874525889991)
          ·
            refine ⟨11164657863188811788834987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7443105242125874525889991 11164657863188811788834987)
            ·
              refine ⟨16746986794783217683252481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11164657863188811788834987 16746986794783217683252481)
              ·
                refine ⟨12560240096087413262439361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16746986794783217683252481 12560240096087413262439361)
                ·
                  refine ⟨9420180072065559946829521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12560240096087413262439361 9420180072065559946829521)
                  ·
                    refine ⟨7065135054049169960122141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9420180072065559946829521 7065135054049169960122141)
                    ·
                      refine ⟨2649425645268438735045803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7065135054049169960122141 2649425645268438735045803)
                      ·
                        rfl

theorem cell23_5159738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 2, 2, 2, 3].length) (baseStart_5159738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5159738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5159738 prefixEnd_5159738 := by exact prefixLift 5159738
  have htrace : WordTrace (prefixWord ++ tailWord_5159738) baseStart_5159738 baseEnd_5159738 := by
    simpa [prefixWord, tailWord_5159738, baseEnd_5159738] using wordTrace_append hprefix tailTrace_5159738
  have hstable : (prefixWord ++ tailWord_5159738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5159738).length < 2 ^ (prefixWord ++ tailWord_5159738).sum := by decide
  have hdescent : baseEnd_5159738 < baseStart_5159738 := by decide
  rcases family_descends (prefixWord ++ tailWord_5159738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5159788 : List Nat := [2, 2, 1, 1, 4, 1, 5, 1, 1, 5]
def baseStart_5159788 : Nat := 118140960795 + 5159788 * 2 ^ 59
def prefixEnd_5159788 : Nat := 4983230072969 + 3 ^ 40 * 5159788 * 2
def baseEnd_5159788 : Nat := 883150439767054513140191

theorem tailTrace_5159788 : CollatzResearch.WordTrace tailWord_5159788 prefixEnd_5159788 883150439767054513140191 := by
  unfold tailWord_5159788
  simp only [CollatzResearch.WordTrace]
  refine ⟨94096464515488386238936009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125461952687317848318581345 94096464515488386238936009)
  ·
    refine ⟨70572348386616289679202007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94096464515488386238936009 70572348386616289679202007)
    ·
      refine ⟨105858522579924434518803011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70572348386616289679202007 105858522579924434518803011)
      ·
        refine ⟨158787783869886651778204517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105858522579924434518803011 158787783869886651778204517)
        ·
          refine ⟨29772709475603747208413347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 158787783869886651778204517 29772709475603747208413347)
          ·
            refine ⟨44659064213405620812620021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29772709475603747208413347 44659064213405620812620021)
            ·
              refine ⟨4186787270006776951183127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44659064213405620812620021 4186787270006776951183127)
              ·
                refine ⟨6280180905010165426774691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4186787270006776951183127 6280180905010165426774691)
                ·
                  refine ⟨9420271357515248140162037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6280180905010165426774691 9420271357515248140162037)
                  ·
                    refine ⟨883150439767054513140191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9420271357515248140162037 883150439767054513140191)
                    ·
                      rfl

theorem cell23_5159788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 5].length) (baseStart_5159788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5159788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5159788 prefixEnd_5159788 := by exact prefixLift 5159788
  have htrace : WordTrace (prefixWord ++ tailWord_5159788) baseStart_5159788 baseEnd_5159788 := by
    simpa [prefixWord, tailWord_5159788, baseEnd_5159788] using wordTrace_append hprefix tailTrace_5159788
  have hstable : (prefixWord ++ tailWord_5159788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5159788).length < 2 ^ (prefixWord ++ tailWord_5159788).sum := by decide
  have hdescent : baseEnd_5159788 < baseStart_5159788 := by decide
  rcases family_descends (prefixWord ++ tailWord_5159788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5159791 : List Nat := [1, 1, 2, 1, 3, 1, 1, 7, 1, 1, 4]
def baseStart_5159791 : Nat := 118140960795 + 5159791 * 2 ^ 59
def prefixEnd_5159791 : Nat := 4983230072969 + 3 ^ 40 * 5159791 * 2
def baseEnd_5159791 : Nat := 2649452859743127027683059

theorem tailTrace_5159791 : CollatzResearch.WordTrace tailWord_5159791 prefixEnd_5159791 2649452859743127027683059 := by
  unfold tailWord_5159791
  simp only [CollatzResearch.WordTrace]
  refine ⟨188193038449965903990231227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125462025633310602660154151 188193038449965903990231227)
  ·
    refine ⟨282289557674948855985346841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188193038449965903990231227 282289557674948855985346841)
    ·
      refine ⟨211717168256211641989010131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 282289557674948855985346841 211717168256211641989010131)
      ·
        refine ⟨317575752384317462983515197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211717168256211641989010131 317575752384317462983515197)
        ·
          refine ⟨119090907144119048618818199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 317575752384317462983515197 119090907144119048618818199)
          ·
            refine ⟨178636360716178572928227299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119090907144119048618818199 178636360716178572928227299)
            ·
              refine ⟨267954541074267859392340949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 178636360716178572928227299 267954541074267859392340949)
              ·
                refine ⟨6280184556428152954507991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 267954541074267859392340949 6280184556428152954507991)
                ·
                  refine ⟨9420276834642229431761987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6280184556428152954507991 9420276834642229431761987)
                  ·
                    refine ⟨14130415251963344147642981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9420276834642229431761987 14130415251963344147642981)
                    ·
                      refine ⟨2649452859743127027683059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14130415251963344147642981 2649452859743127027683059)
                      ·
                        rfl

theorem cell23_5159791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 7, 1, 1, 4].length) (baseStart_5159791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5159791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5159791 prefixEnd_5159791 := by exact prefixLift 5159791
  have htrace : WordTrace (prefixWord ++ tailWord_5159791) baseStart_5159791 baseEnd_5159791 := by
    simpa [prefixWord, tailWord_5159791, baseEnd_5159791] using wordTrace_append hprefix tailTrace_5159791
  have hstable : (prefixWord ++ tailWord_5159791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5159791).length < 2 ^ (prefixWord ++ tailWord_5159791).sum := by decide
  have hdescent : baseEnd_5159791 < baseStart_5159791 := by decide
  rcases family_descends (prefixWord ++ tailWord_5159791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5159804 : List Nat := [2, 2, 2, 1, 1, 1, 1, 3, 3, 1, 6]
def baseStart_5159804 : Nat := 118140960795 + 5159804 * 2 ^ 59
def prefixEnd_5159804 : Nat := 4983230072969 + 3 ^ 40 * 5159804 * 2
def baseEnd_5159804 : Nat := 2649459534991635476820499

theorem tailTrace_5159804 : CollatzResearch.WordTrace tailWord_5159804 prefixEnd_5159804 2649459534991635476820499 := by
  unfold tailWord_5159804
  simp only [CollatzResearch.WordTrace]
  refine ⟨94096756299459403605227233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125462341732612538140302977 94096756299459403605227233)
  ·
    refine ⟨70572567224594552703920425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94096756299459403605227233 70572567224594552703920425)
    ·
      refine ⟨52929425418445914527940319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70572567224594552703920425 52929425418445914527940319)
      ·
        refine ⟨79394138127668871791910479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52929425418445914527940319 79394138127668871791910479)
        ·
          refine ⟨119091207191503307687865719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79394138127668871791910479 119091207191503307687865719)
          ·
            refine ⟨178636810787254961531798579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119091207191503307687865719 178636810787254961531798579)
            ·
              refine ⟨267955216180882442297697869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 178636810787254961531798579 267955216180882442297697869)
              ·
                refine ⟨100483206067830915861636701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 267955216180882442297697869 100483206067830915861636701)
                ·
                  refine ⟨37681202275436593448113763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 100483206067830915861636701 37681202275436593448113763)
                  ·
                    refine ⟨56521803413154890172170645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37681202275436593448113763 56521803413154890172170645)
                    ·
                      refine ⟨2649459534991635476820499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56521803413154890172170645 2649459534991635476820499)
                      ·
                        rfl

theorem cell23_5159804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 3, 1, 6].length) (baseStart_5159804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5159804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5159804 prefixEnd_5159804 := by exact prefixLift 5159804
  have htrace : WordTrace (prefixWord ++ tailWord_5159804) baseStart_5159804 baseEnd_5159804 := by
    simpa [prefixWord, tailWord_5159804, baseEnd_5159804] using wordTrace_append hprefix tailTrace_5159804
  have hstable : (prefixWord ++ tailWord_5159804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5159804).length < 2 ^ (prefixWord ++ tailWord_5159804).sum := by decide
  have hdescent : baseEnd_5159804 < baseStart_5159804 := by decide
  rcases family_descends (prefixWord ++ tailWord_5159804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5159811 : List Nat := [1, 1, 1, 3, 4, 1, 1, 1, 5, 2, 3]
def baseStart_5159811 : Nat := 118140960795 + 5159811 * 2 ^ 59
def prefixEnd_5159811 : Nat := 4983230072969 + 3 ^ 40 * 5159811 * 2
def baseEnd_5159811 : Nat := 2649463129356216949432967

theorem tailTrace_5159811 : CollatzResearch.WordTrace tailWord_5159811 prefixEnd_5159811 2649463129356216949432967 := by
  unfold tailWord_5159811
  simp only [CollatzResearch.WordTrace]
  refine ⟨188193767909893447405959287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125462511939928964937306191 188193767909893447405959287)
  ·
    refine ⟨282290651864840171108938931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188193767909893447405959287 282290651864840171108938931)
    ·
      refine ⟨423435977797260256663408397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 282290651864840171108938931 423435977797260256663408397)
      ·
        refine ⟨158788491673972596248778149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 423435977797260256663408397 158788491673972596248778149)
        ·
          refine ⟨29772842188869861796645903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 158788491673972596248778149 29772842188869861796645903)
          ·
            refine ⟨44659263283304792694968855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29772842188869861796645903 44659263283304792694968855)
            ·
              refine ⟨66988894924957189042453283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44659263283304792694968855 66988894924957189042453283)
              ·
                refine ⟨100483342387435783563679925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66988894924957189042453283 100483342387435783563679925)
                ·
                  refine ⟨9420313348822104709094993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 100483342387435783563679925 9420313348822104709094993)
                  ·
                    refine ⟨7065235011616578531821245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9420313348822104709094993 7065235011616578531821245)
                    ·
                      refine ⟨2649463129356216949432967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7065235011616578531821245 2649463129356216949432967)
                      ·
                        rfl

theorem cell23_5159811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 5, 2, 3].length) (baseStart_5159811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5159811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5159811 prefixEnd_5159811 := by exact prefixLift 5159811
  have htrace : WordTrace (prefixWord ++ tailWord_5159811) baseStart_5159811 baseEnd_5159811 := by
    simpa [prefixWord, tailWord_5159811, baseEnd_5159811] using wordTrace_append hprefix tailTrace_5159811
  have hstable : (prefixWord ++ tailWord_5159811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5159811).length < 2 ^ (prefixWord ++ tailWord_5159811).sum := by decide
  have hdescent : baseEnd_5159811 < baseStart_5159811 := by decide
  rcases family_descends (prefixWord ++ tailWord_5159811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5159818 : List Nat := [3, 1, 2, 4, 1, 2, 2, 1, 1, 6]
def baseStart_5159818 : Nat := 118140960795 + 5159818 * 2 ^ 59
def prefixEnd_5159818 : Nat := 4983230072969 + 3 ^ 40 * 5159818 * 2
def baseEnd_5159818 : Nat := 883155574573599474015145

theorem tailTrace_5159818 : CollatzResearch.WordTrace tailWord_5159818 prefixEnd_5159818 883155574573599474015145 := by
  unfold tailWord_5159818
  simp only [CollatzResearch.WordTrace]
  refine ⟨47048505805217021900366027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125462682147245391734309405 47048505805217021900366027)
  ·
    refine ⟨70572758707825532850549041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47048505805217021900366027 70572758707825532850549041)
    ·
      refine ⟨52929569030869149637911781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70572758707825532850549041 52929569030869149637911781)
      ·
        refine ⟨9924294193287965557108459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52929569030869149637911781 9924294193287965557108459)
        ·
          refine ⟨14886441289931948335662689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9924294193287965557108459 14886441289931948335662689)
          ·
            refine ⟨11164830967448961251747017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14886441289931948335662689 11164830967448961251747017)
            ·
              refine ⟨8373623225586720938810263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11164830967448961251747017 8373623225586720938810263)
              ·
                refine ⟨12560434838380081408215395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8373623225586720938810263 12560434838380081408215395)
                ·
                  refine ⟨18840652257570122112323093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12560434838380081408215395 18840652257570122112323093)
                  ·
                    refine ⟨883155574573599474015145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18840652257570122112323093 883155574573599474015145)
                    ·
                      rfl

theorem cell23_5159818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 2, 1, 1, 6].length) (baseStart_5159818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5159818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5159818 prefixEnd_5159818 := by exact prefixLift 5159818
  have htrace : WordTrace (prefixWord ++ tailWord_5159818) baseStart_5159818 baseEnd_5159818 := by
    simpa [prefixWord, tailWord_5159818, baseEnd_5159818] using wordTrace_append hprefix tailTrace_5159818
  have hstable : (prefixWord ++ tailWord_5159818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5159818).length < 2 ^ (prefixWord ++ tailWord_5159818).sum := by decide
  have hdescent : baseEnd_5159818 < baseStart_5159818 := by decide
  rcases family_descends (prefixWord ++ tailWord_5159818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5159828 : List Nat := [2, 4, 2, 1, 1, 1, 1, 3, 3, 2, 3]
def baseStart_5159828 : Nat := 118140960795 + 5159828 * 2 ^ 59
def prefixEnd_5159828 : Nat := 4983230072969 + 3 ^ 40 * 5159828 * 2
def baseEnd_5159828 : Nat := 2649471858527343382920389

theorem tailTrace_5159828 : CollatzResearch.WordTrace tailWord_5159828 prefixEnd_5159828 2649471858527343382920389 := by
  unfold tailWord_5159828
  simp only [CollatzResearch.WordTrace]
  refine ⟨94097193975415929654664069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125462925300554572872885425 94097193975415929654664069)
  ·
    refine ⟨17643223870390486810249513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94097193975415929654664069 17643223870390486810249513)
    ·
      refine ⟨13232417902792865107687135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17643223870390486810249513 13232417902792865107687135)
      ·
        refine ⟨19848626854189297661530703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13232417902792865107687135 19848626854189297661530703)
        ·
          refine ⟨29772940281283946492296055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19848626854189297661530703 29772940281283946492296055)
          ·
            refine ⟨44659410421925919738444083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29772940281283946492296055 44659410421925919738444083)
            ·
              refine ⟨66989115632888879607666125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44659410421925919738444083 66989115632888879607666125)
              ·
                refine ⟨25120918362333329852874797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66989115632888879607666125 25120918362333329852874797)
                ·
                  refine ⟨9420344385874998694828049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25120918362333329852874797 9420344385874998694828049)
                  ·
                    refine ⟨7065258289406249021121037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9420344385874998694828049 7065258289406249021121037)
                    ·
                      refine ⟨2649471858527343382920389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7065258289406249021121037 2649471858527343382920389)
                      ·
                        rfl

theorem cell23_5159828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 3, 3, 2, 3].length) (baseStart_5159828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5159828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5159828 prefixEnd_5159828 := by exact prefixLift 5159828
  have htrace : WordTrace (prefixWord ++ tailWord_5159828) baseStart_5159828 baseEnd_5159828 := by
    simpa [prefixWord, tailWord_5159828, baseEnd_5159828] using wordTrace_append hprefix tailTrace_5159828
  have hstable : (prefixWord ++ tailWord_5159828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5159828).length < 2 ^ (prefixWord ++ tailWord_5159828).sum := by decide
  have hdescent : baseEnd_5159828 < baseStart_5159828 := by decide
  rcases family_descends (prefixWord ++ tailWord_5159828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5159831 : List Nat := [1, 1, 3, 3, 1, 2, 5, 7]
def baseStart_5159831 : Nat := 118140960795 + 5159831 * 2 ^ 59
def prefixEnd_5159831 : Nat := 4983230072969 + 3 ^ 40 * 5159831 * 2
def baseEnd_5159831 : Nat := 98128644406270624858625

theorem tailTrace_5159831 : CollatzResearch.WordTrace tailWord_5159831 prefixEnd_5159831 98128644406270624858625 := by
  unfold tailWord_5159831
  simp only [CollatzResearch.WordTrace]
  refine ⟨188194497369820990821687347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125462998246547327214458231 188194497369820990821687347)
  ·
    refine ⟨282291746054731486232531021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188194497369820990821687347 282291746054731486232531021)
    ·
      refine ⟨105859404770524307337199133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 282291746054731486232531021 105859404770524307337199133)
      ·
        refine ⟨39697276788946615251449675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105859404770524307337199133 39697276788946615251449675)
        ·
          refine ⟨59545915183419922877174513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39697276788946615251449675 59545915183419922877174513)
          ·
            refine ⟨44659436387564942157880885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59545915183419922877174513 44659436387564942157880885)
            ·
              refine ⟨4186822161334213327301333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44659436387564942157880885 4186822161334213327301333)
              ·
                refine ⟨98128644406270624858625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4186822161334213327301333 98128644406270624858625)
                ·
                  rfl

theorem cell23_5159831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 5, 7].length) (baseStart_5159831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5159831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5159831 prefixEnd_5159831 := by exact prefixLift 5159831
  have htrace : WordTrace (prefixWord ++ tailWord_5159831) baseStart_5159831 baseEnd_5159831 := by
    simpa [prefixWord, tailWord_5159831, baseEnd_5159831] using wordTrace_append hprefix tailTrace_5159831
  have hstable : (prefixWord ++ tailWord_5159831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5159831).length < 2 ^ (prefixWord ++ tailWord_5159831).sum := by decide
  have hdescent : baseEnd_5159831 < baseStart_5159831 := by decide
  rcases family_descends (prefixWord ++ tailWord_5159831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5159842 : List Nat := [3, 3, 1, 2, 2, 3, 2, 1, 1, 1, 4]
def baseStart_5159842 : Nat := 118140960795 + 5159842 * 2 ^ 59
def prefixEnd_5159842 : Nat := 4983230072969 + 3 ^ 40 * 5159842 * 2
def baseEnd_5159842 : Nat := 2649479047256506328145325

theorem tailTrace_5159842 : CollatzResearch.WordTrace tailWord_5159842 prefixEnd_5159842 2649479047256506328145325 := by
  unfold tailWord_5159842
  simp only [CollatzResearch.WordTrace]
  refine ⟨47048724643195284925084445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125463265715187426466891853 47048724643195284925084445)
  ·
    refine ⟨17643271741198231846906667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47048724643195284925084445 17643271741198231846906667)
    ·
      refine ⟨26464907611797347770360001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17643271741198231846906667 26464907611797347770360001)
      ·
        refine ⟨19848680708848010827770001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26464907611797347770360001 19848680708848010827770001)
        ·
          refine ⟨14886510531636008120827501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19848680708848010827770001 14886510531636008120827501)
          ·
            refine ⟨5582441449363503045310313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14886510531636008120827501 5582441449363503045310313)
            ·
              refine ⟨4186831087022627283982735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5582441449363503045310313 4186831087022627283982735)
              ·
                refine ⟨6280246630533940925974103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4186831087022627283982735 6280246630533940925974103)
                ·
                  refine ⟨9420369945800911388961155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6280246630533940925974103 9420369945800911388961155)
                  ·
                    refine ⟨14130554918701367083441733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9420369945800911388961155 14130554918701367083441733)
                    ·
                      refine ⟨2649479047256506328145325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14130554918701367083441733 2649479047256506328145325)
                      ·
                        rfl

theorem cell23_5159842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 2, 1, 1, 1, 4].length) (baseStart_5159842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5159842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5159842 prefixEnd_5159842 := by exact prefixLift 5159842
  have htrace : WordTrace (prefixWord ++ tailWord_5159842) baseStart_5159842 baseEnd_5159842 := by
    simpa [prefixWord, tailWord_5159842, baseEnd_5159842] using wordTrace_append hprefix tailTrace_5159842
  have hstable : (prefixWord ++ tailWord_5159842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5159842).length < 2 ^ (prefixWord ++ tailWord_5159842).sum := by decide
  have hdescent : baseEnd_5159842 < baseStart_5159842 := by decide
  rcases family_descends (prefixWord ++ tailWord_5159842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5159931 : List Nat := [1, 1, 1, 1, 1, 3, 3, 3, 1, 5, 3]
def baseStart_5159931 : Nat := 118140960795 + 5159931 * 2 ^ 59
def prefixEnd_5159931 : Nat := 4983230072969 + 3 ^ 40 * 5159931 * 2
def baseEnd_5159931 : Nat := 2649524747034756479932415

theorem tailTrace_5159931 : CollatzResearch.WordTrace tailWord_5159931 prefixEnd_5159931 2649524747034756479932415 := by
  unfold tailWord_5159931
  simp only [CollatzResearch.WordTrace]
  refine ⟨188198144669458707900327647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125465429779639138600218431 188198144669458707900327647)
  ·
    refine ⟨282297217004188061850491471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188198144669458707900327647 282297217004188061850491471)
    ·
      refine ⟨423445825506282092775737207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 282297217004188061850491471 423445825506282092775737207)
      ·
        refine ⟨635168738259423139163605811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 423445825506282092775737207 635168738259423139163605811)
        ·
          refine ⟨952753107389134708745408717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 635168738259423139163605811 952753107389134708745408717)
          ·
            refine ⟨357282415270925515779528269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 952753107389134708745408717 357282415270925515779528269)
            ·
              refine ⟨133980905726597068417323101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 357282415270925515779528269 133980905726597068417323101)
              ·
                refine ⟨50242839647473900656496163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 133980905726597068417323101 50242839647473900656496163)
                ·
                  refine ⟨75364259471210850984744245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50242839647473900656496163 75364259471210850984744245)
                  ·
                    refine ⟨7065399325426017279819773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 75364259471210850984744245 7065399325426017279819773)
                    ·
                      refine ⟨2649524747034756479932415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7065399325426017279819773 2649524747034756479932415)
                      ·
                        rfl

theorem cell23_5159931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 1, 5, 3].length) (baseStart_5159931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5159931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5159931 prefixEnd_5159931 := by exact prefixLift 5159931
  have htrace : WordTrace (prefixWord ++ tailWord_5159931) baseStart_5159931 baseEnd_5159931 := by
    simpa [prefixWord, tailWord_5159931, baseEnd_5159931] using wordTrace_append hprefix tailTrace_5159931
  have hstable : (prefixWord ++ tailWord_5159931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5159931).length < 2 ^ (prefixWord ++ tailWord_5159931).sum := by decide
  have hdescent : baseEnd_5159931 < baseStart_5159931 := by decide
  rcases family_descends (prefixWord ++ tailWord_5159931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5159932 : List Nat := [2, 2, 2, 1, 2, 4, 1, 3, 2, 2, 2]
def baseStart_5159932 : Nat := 118140960795 + 5159932 * 2 ^ 59
def prefixEnd_5159932 : Nat := 4983230072969 + 3 ^ 40 * 5159932 * 2
def baseEnd_5159932 : Nat := 2649525260515410976019911

theorem tailTrace_5159932 : CollatzResearch.WordTrace tailWord_5159932 prefixEnd_5159932 2649525260515410976019911 := by
  unfold tailWord_5159932
  simp only [CollatzResearch.WordTrace]
  refine ⟨94099090571227542535557025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125465454094970056714076033 94099090571227542535557025)
  ·
    refine ⟨70574317928420656901667769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94099090571227542535557025 70574317928420656901667769)
    ·
      refine ⟨52930738446315492676250827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70574317928420656901667769 52930738446315492676250827)
      ·
        refine ⟨79396107669473239014376241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52930738446315492676250827 79396107669473239014376241)
        ·
          refine ⟨59547080752104929260782181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79396107669473239014376241 59547080752104929260782181)
          ·
            refine ⟨11165077641019674236396659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59547080752104929260782181 11165077641019674236396659)
            ·
              refine ⟨16747616461529511354594989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11165077641019674236396659 16747616461529511354594989)
              ·
                refine ⟨6280356173073566757973121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16747616461529511354594989 6280356173073566757973121)
                ·
                  refine ⟨4710267129805175068479841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6280356173073566757973121 4710267129805175068479841)
                  ·
                    refine ⟨3532700347353881301359881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4710267129805175068479841 3532700347353881301359881)
                    ·
                      refine ⟨2649525260515410976019911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3532700347353881301359881 2649525260515410976019911)
                      ·
                        rfl

theorem cell23_5159932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 3, 2, 2, 2].length) (baseStart_5159932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5159932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5159932 prefixEnd_5159932 := by exact prefixLift 5159932
  have htrace : WordTrace (prefixWord ++ tailWord_5159932) baseStart_5159932 baseEnd_5159932 := by
    simpa [prefixWord, tailWord_5159932, baseEnd_5159932] using wordTrace_append hprefix tailTrace_5159932
  have hstable : (prefixWord ++ tailWord_5159932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5159932).length < 2 ^ (prefixWord ++ tailWord_5159932).sum := by decide
  have hdescent : baseEnd_5159932 < baseStart_5159932 := by decide
  rcases family_descends (prefixWord ++ tailWord_5159932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5159961 : List Nat := [1, 2, 1, 2, 1, 1, 5, 2, 1, 2, 5]
def baseStart_5159961 : Nat := 118140960795 + 5159961 * 2 ^ 59
def prefixEnd_5159961 : Nat := 4983230072969 + 3 ^ 40 * 5159961 * 2
def baseEnd_5159961 : Nat := 2649540151454391362557277

theorem tailTrace_5159961 : CollatzResearch.WordTrace tailWord_5159961 prefixEnd_5159961 2649540151454391362557277 := by
  unfold tailWord_5159961
  simp only [CollatzResearch.WordTrace]
  refine ⟨188199238859350023023919737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125466159239566682015946491 188199238859350023023919737)
  ·
    refine ⟨141149429144512517267939803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188199238859350023023919737 141149429144512517267939803)
    ·
      refine ⟨211724143716768775901909705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141149429144512517267939803 211724143716768775901909705)
      ·
        refine ⟨158793107787576581926432279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 211724143716768775901909705 158793107787576581926432279)
        ·
          refine ⟨238189661681364872889648419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158793107787576581926432279 238189661681364872889648419)
          ·
            refine ⟨357284492522047309334472629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 238189661681364872889648419 357284492522047309334472629)
            ·
              refine ⟨33495421173941935250106809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 357284492522047309334472629 33495421173941935250106809)
              ·
                refine ⟨25121565880456451437580107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33495421173941935250106809 25121565880456451437580107)
                ·
                  refine ⟨37682348820684677156370161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25121565880456451437580107 37682348820684677156370161)
                  ·
                    refine ⟨28261761615513507867277621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37682348820684677156370161 28261761615513507867277621)
                    ·
                      refine ⟨2649540151454391362557277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28261761615513507867277621 2649540151454391362557277)
                      ·
                        rfl

theorem cell23_5159961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 2, 1, 2, 5].length) (baseStart_5159961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5159961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5159961 prefixEnd_5159961 := by exact prefixLift 5159961
  have htrace : WordTrace (prefixWord ++ tailWord_5159961) baseStart_5159961 baseEnd_5159961 := by
    simpa [prefixWord, tailWord_5159961, baseEnd_5159961] using wordTrace_append hprefix tailTrace_5159961
  have hstable : (prefixWord ++ tailWord_5159961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5159961).length < 2 ^ (prefixWord ++ tailWord_5159961).sum := by decide
  have hdescent : baseEnd_5159961 < baseStart_5159961 := by decide
  rcases family_descends (prefixWord ++ tailWord_5159961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5159972 : List Nat := [2, 3, 1, 4, 1, 1, 4, 2, 5]
def baseStart_5159972 : Nat := 118140960795 + 5159972 * 2 ^ 59
def prefixEnd_5159972 : Nat := 4983230072969 + 3 ^ 40 * 5159972 * 2
def baseEnd_5159972 : Nat := 294393977749065646613303

theorem tailTrace_5159972 : CollatzResearch.WordTrace tailWord_5159972 prefixEnd_5159972 294393977749065646613303 := by
  unfold tailWord_5159972
  simp only [CollatzResearch.WordTrace]
  refine ⟨94099820031155085951285085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125466426708206781268380113 94099820031155085951285085)
  ·
    refine ⟨35287432511683157231731907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94099820031155085951285085 35287432511683157231731907)
    ·
      refine ⟨52931148767524735847597861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35287432511683157231731907 52931148767524735847597861)
      ·
        refine ⟨9924590393910887971424599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52931148767524735847597861 9924590393910887971424599)
        ·
          refine ⟨14886885590866331957136899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9924590393910887971424599 14886885590866331957136899)
          ·
            refine ⟨22330328386299497935705349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14886885590866331957136899 22330328386299497935705349)
            ·
              refine ⟨4186936572431155862944753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22330328386299497935705349 4186936572431155862944753)
              ·
                refine ⟨3140202429323366897208565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4186936572431155862944753 3140202429323366897208565)
                ·
                  refine ⟨294393977749065646613303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3140202429323366897208565 294393977749065646613303)
                  ·
                    rfl

theorem cell23_5159972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 4, 2, 5].length) (baseStart_5159972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5159972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5159972 prefixEnd_5159972 := by exact prefixLift 5159972
  have htrace : WordTrace (prefixWord ++ tailWord_5159972) baseStart_5159972 baseEnd_5159972 := by
    simpa [prefixWord, tailWord_5159972, baseEnd_5159972] using wordTrace_append hprefix tailTrace_5159972
  have hstable : (prefixWord ++ tailWord_5159972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5159972).length < 2 ^ (prefixWord ++ tailWord_5159972).sum := by decide
  have hdescent : baseEnd_5159972 < baseStart_5159972 := by decide
  rcases family_descends (prefixWord ++ tailWord_5159972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5160008 : List Nat := [2, 1, 3, 1, 1, 1, 5, 1, 1, 4, 3]
def baseStart_5160008 : Nat := 118140960795 + 5160008 * 2 ^ 59
def prefixEnd_5160008 : Nat := 4983230072969 + 3 ^ 40 * 5160008 * 2
def baseEnd_5160008 : Nat := 2649564285045152678669561

theorem tailTrace_5160008 : CollatzResearch.WordTrace tailWord_5160008 prefixEnd_5160008 2649564285045152678669561 := by
  unfold tailWord_5160008
  simp only [CollatzResearch.WordTrace]
  refine ⟨94100476545089875025440339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125467302060119833367253785 94100476545089875025440339)
  ·
    refine ⟨141150714817634812538160509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94100476545089875025440339 141150714817634812538160509)
    ·
      refine ⟨52931518056613054701810191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141150714817634812538160509 52931518056613054701810191)
      ·
        refine ⟨79397277084919582052715287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52931518056613054701810191 79397277084919582052715287)
        ·
          refine ⟨119095915627379373079072931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79397277084919582052715287 119095915627379373079072931)
          ·
            refine ⟨178643873441069059618609397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119095915627379373079072931 178643873441069059618609397)
            ·
              refine ⟨16747863135100224339244631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 178643873441069059618609397 16747863135100224339244631)
              ·
                refine ⟨25121794702650336508866947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16747863135100224339244631 25121794702650336508866947)
                ·
                  refine ⟨37682692053975504763300421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25121794702650336508866947 37682692053975504763300421)
                  ·
                    refine ⟨7065504760120407143118829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37682692053975504763300421 7065504760120407143118829)
                    ·
                      refine ⟨2649564285045152678669561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7065504760120407143118829 2649564285045152678669561)
                      ·
                        rfl

theorem cell23_5160008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 1, 1, 4, 3].length) (baseStart_5160008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5160008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5160008 prefixEnd_5160008 := by exact prefixLift 5160008
  have htrace : WordTrace (prefixWord ++ tailWord_5160008) baseStart_5160008 baseEnd_5160008 := by
    simpa [prefixWord, tailWord_5160008, baseEnd_5160008] using wordTrace_append hprefix tailTrace_5160008
  have hstable : (prefixWord ++ tailWord_5160008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5160008).length < 2 ^ (prefixWord ++ tailWord_5160008).sum := by decide
  have hdescent : baseEnd_5160008 < baseStart_5160008 := by decide
  rcases family_descends (prefixWord ++ tailWord_5160008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5160018 : List Nat := [3, 2, 2, 1, 3, 1, 1, 1, 2, 1, 6]
def baseStart_5160018 : Nat := 118140960795 + 5160018 * 2 ^ 59
def prefixEnd_5160018 : Nat := 4983230072969 + 3 ^ 40 * 5160018 * 2
def baseEnd_5160018 : Nat := 2649569419851697639544515

theorem tailTrace_5160018 : CollatzResearch.WordTrace tailWord_5160018 prefixEnd_5160018 2649569419851697639544515 := by
  unfold tailWord_5160018
  simp only [CollatzResearch.WordTrace]
  refine ⟨47050329455035880439686177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125467545213429014505829805 47050329455035880439686177)
  ·
    refine ⟨35287747091276910329764633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47050329455035880439686177 35287747091276910329764633)
    ·
      refine ⟨26465810318457682747323475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35287747091276910329764633 26465810318457682747323475)
      ·
        refine ⟨39698715477686524120985213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26465810318457682747323475 39698715477686524120985213)
        ·
          refine ⟨14887018304132446545369455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39698715477686524120985213 14887018304132446545369455)
          ·
            refine ⟨22330527456198669818054183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14887018304132446545369455 22330527456198669818054183)
            ·
              refine ⟨33495791184298004727081275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22330527456198669818054183 33495791184298004727081275)
              ·
                refine ⟨50243686776447007090621913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33495791184298004727081275 50243686776447007090621913)
                ·
                  refine ⟨37682765082335255317966435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50243686776447007090621913 37682765082335255317966435)
                  ·
                    refine ⟨56524147623502882976949653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37682765082335255317966435 56524147623502882976949653)
                    ·
                      refine ⟨2649569419851697639544515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56524147623502882976949653 2649569419851697639544515)
                      ·
                        rfl

theorem cell23_5160018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 1, 2, 1, 6].length) (baseStart_5160018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5160018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5160018 prefixEnd_5160018 := by exact prefixLift 5160018
  have htrace : WordTrace (prefixWord ++ tailWord_5160018) baseStart_5160018 baseEnd_5160018 := by
    simpa [prefixWord, tailWord_5160018, baseEnd_5160018] using wordTrace_append hprefix tailTrace_5160018
  have hstable : (prefixWord ++ tailWord_5160018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5160018).length < 2 ^ (prefixWord ++ tailWord_5160018).sum := by decide
  have hdescent : baseEnd_5160018 < baseStart_5160018 := by decide
  rcases family_descends (prefixWord ++ tailWord_5160018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5160028 : List Nat := [2, 2, 4, 1, 1, 1, 3, 1, 8]
def baseStart_5160028 : Nat := 118140960795 + 5160028 * 2 ^ 59
def prefixEnd_5160028 : Nat := 4983230072969 + 3 ^ 40 * 5160028 * 2
def baseEnd_5160028 : Nat := 294397172739804733379941

theorem tailTrace_5160028 : CollatzResearch.WordTrace tailWord_5160028 prefixEnd_5160028 294397172739804733379941 := by
  unfold tailWord_5160028
  simp only [CollatzResearch.WordTrace]
  refine ⟨94100841275053646733304369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125467788366738195644405825 94100841275053646733304369)
  ·
    refine ⟨70575630956290235049978277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94100841275053646733304369 70575630956290235049978277)
    ·
      refine ⟨13232930804304419071870927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70575630956290235049978277 13232930804304419071870927)
      ·
        refine ⟨19849396206456628607806391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13232930804304419071870927 19849396206456628607806391)
        ·
          refine ⟨29774094309684942911709587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19849396206456628607806391 29774094309684942911709587)
          ·
            refine ⟨44661141464527414367564381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29774094309684942911709587 44661141464527414367564381)
            ·
              refine ⟨16747928049197780387836643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44661141464527414367564381 16747928049197780387836643)
              ·
                refine ⟨25121892073796670581754965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16747928049197780387836643 25121892073796670581754965)
                ·
                  refine ⟨294397172739804733379941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25121892073796670581754965 294397172739804733379941)
                  ·
                    rfl

theorem cell23_5160028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 1, 8].length) (baseStart_5160028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5160028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5160028 prefixEnd_5160028 := by exact prefixLift 5160028
  have htrace : WordTrace (prefixWord ++ tailWord_5160028) baseStart_5160028 baseEnd_5160028 := by
    simpa [prefixWord, tailWord_5160028, baseEnd_5160028] using wordTrace_append hprefix tailTrace_5160028
  have hstable : (prefixWord ++ tailWord_5160028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5160028).length < 2 ^ (prefixWord ++ tailWord_5160028).sum := by decide
  have hdescent : baseEnd_5160028 < baseStart_5160028 := by decide
  rcases family_descends (prefixWord ++ tailWord_5160028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5160031 : List Nat := [1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 8]
def baseStart_5160031 : Nat := 118140960795 + 5160031 * 2 ^ 59
def prefixEnd_5160031 : Nat := 4983230072969 + 3 ^ 40 * 5160031 * 2
def baseEnd_5160031 : Nat := 2649576095100206088681955

theorem tailTrace_5160031 : CollatzResearch.WordTrace tailWord_5160031 prefixEnd_5160031 2649576095100206088681955 := by
  unfold tailWord_5160031
  simp only [CollatzResearch.WordTrace]
  refine ⟨188201791969096424978967947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125467861312730949985978631 188201791969096424978967947)
  ·
    refine ⟨282302687953644637468451921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188201791969096424978967947 282302687953644637468451921)
    ·
      refine ⟨211727015965233478101338941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 282302687953644637468451921 211727015965233478101338941)
      ·
        refine ⟨79397630986962554288002103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 211727015965233478101338941 79397630986962554288002103)
        ·
          refine ⟨119096446480443831432003155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79397630986962554288002103 119096446480443831432003155)
          ·
            refine ⟨178644669720665747148004733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119096446480443831432003155 178644669720665747148004733)
            ·
              refine ⟨66991751145249655180501775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 178644669720665747148004733 66991751145249655180501775)
              ·
                refine ⟨100487626717874482770752663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66991751145249655180501775 100487626717874482770752663)
                ·
                  refine ⟨150731440076811724156128995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 100487626717874482770752663 150731440076811724156128995)
                  ·
                    refine ⟨226097160115217586234193493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 150731440076811724156128995 226097160115217586234193493)
                    ·
                      refine ⟨2649576095100206088681955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 226097160115217586234193493 2649576095100206088681955)
                      ·
                        rfl

theorem cell23_5160031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 8].length) (baseStart_5160031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5160031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5160031 prefixEnd_5160031 := by exact prefixLift 5160031
  have htrace : WordTrace (prefixWord ++ tailWord_5160031) baseStart_5160031 baseEnd_5160031 := by
    simpa [prefixWord, tailWord_5160031, baseEnd_5160031] using wordTrace_append hprefix tailTrace_5160031
  have hstable : (prefixWord ++ tailWord_5160031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5160031).length < 2 ^ (prefixWord ++ tailWord_5160031).sum := by decide
  have hdescent : baseEnd_5160031 < baseStart_5160031 := by decide
  rcases family_descends (prefixWord ++ tailWord_5160031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5160055 : List Nat := [1, 1, 3, 1, 1, 4, 1, 4, 3, 1, 3]
def baseStart_5160055 : Nat := 118140960795 + 5160055 * 2 ^ 59
def prefixEnd_5160055 : Nat := 4983230072969 + 3 ^ 40 * 5160055 * 2
def baseEnd_5160055 : Nat := 2649588418635913994781845

theorem tailTrace_5160055 : CollatzResearch.WordTrace tailWord_5160055 prefixEnd_5160055 2649588418635913994781845 := by
  unfold tailWord_5160055
  simp only [CollatzResearch.WordTrace]
  refine ⟨188202667321009477077841619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125468444880672984718561079 188202667321009477077841619)
  ·
    refine ⟨282304000981514215616762429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188202667321009477077841619 282304000981514215616762429)
    ·
      refine ⟨105864000368067830856285911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 282304000981514215616762429 105864000368067830856285911)
      ·
        refine ⟨158796000552101746284428867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105864000368067830856285911 158796000552101746284428867)
        ·
          refine ⟨238194000828152619426643301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158796000552101746284428867 238194000828152619426643301)
          ·
            refine ⟨44661375155278616142495619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 238194000828152619426643301 44661375155278616142495619)
            ·
              refine ⟨66992062732917924213743429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44661375155278616142495619 66992062732917924213743429)
              ·
                refine ⟨12561011762422110790076893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 66992062732917924213743429 12561011762422110790076893)
                ·
                  refine ⟨4710379410908291546278835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12561011762422110790076893 4710379410908291546278835)
                  ·
                    refine ⟨7065569116362437319418253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4710379410908291546278835 7065569116362437319418253)
                    ·
                      refine ⟨2649588418635913994781845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7065569116362437319418253 2649588418635913994781845)
                      ·
                        rfl

theorem cell23_5160055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 4, 3, 1, 3].length) (baseStart_5160055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5160055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5160055 prefixEnd_5160055 := by exact prefixLift 5160055
  have htrace : WordTrace (prefixWord ++ tailWord_5160055) baseStart_5160055 baseEnd_5160055 := by
    simpa [prefixWord, tailWord_5160055, baseEnd_5160055] using wordTrace_append hprefix tailTrace_5160055
  have hstable : (prefixWord ++ tailWord_5160055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5160055).length < 2 ^ (prefixWord ++ tailWord_5160055).sum := by decide
  have hdescent : baseEnd_5160055 < baseStart_5160055 := by decide
  rcases family_descends (prefixWord ++ tailWord_5160055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5160082 : List Nat := [3, 2, 3, 1, 1, 2, 1, 1, 4, 3, 2]
def baseStart_5160082 : Nat := 118140960795 + 5160082 * 2 ^ 59
def prefixEnd_5160082 : Nat := 4983230072969 + 3 ^ 40 * 5160082 * 2
def baseEnd_5160082 : Nat := 2649602282613585389144221

theorem tailTrace_5160082 : CollatzResearch.WordTrace tailWord_5160082 prefixEnd_5160082 2649602282613585389144221 := by
  unfold tailWord_5160082
  simp only [CollatzResearch.WordTrace]
  refine ⟨47050913022977915172268625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125469101394607773792716333 47050913022977915172268625)
  ·
    refine ⟨35288184767233436379201469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47050913022977915172268625 35288184767233436379201469)
    ·
      refine ⟨13233069287712538642200551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35288184767233436379201469 13233069287712538642200551)
      ·
        refine ⟨19849603931568807963300827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13233069287712538642200551 19849603931568807963300827)
        ·
          refine ⟨29774405897353211944951241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19849603931568807963300827 29774405897353211944951241)
          ·
            refine ⟨22330804423014908958713431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29774405897353211944951241 22330804423014908958713431)
            ·
              refine ⟨33496206634522363438070147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22330804423014908958713431 33496206634522363438070147)
              ·
                refine ⟨50244309951783545157105221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33496206634522363438070147 50244309951783545157105221)
                ·
                  refine ⟨9420808115959414716957229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50244309951783545157105221 9420808115959414716957229)
                  ·
                    refine ⟨3532803043484780518858961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9420808115959414716957229 3532803043484780518858961)
                    ·
                      refine ⟨2649602282613585389144221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3532803043484780518858961 2649602282613585389144221)
                      ·
                        rfl

theorem cell23_5160082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 1, 4, 3, 2].length) (baseStart_5160082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5160082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5160082 prefixEnd_5160082 := by exact prefixLift 5160082
  have htrace : WordTrace (prefixWord ++ tailWord_5160082) baseStart_5160082 baseEnd_5160082 := by
    simpa [prefixWord, tailWord_5160082, baseEnd_5160082] using wordTrace_append hprefix tailTrace_5160082
  have hstable : (prefixWord ++ tailWord_5160082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5160082).length < 2 ^ (prefixWord ++ tailWord_5160082).sum := by decide
  have hdescent : baseEnd_5160082 < baseStart_5160082 := by decide
  rcases family_descends (prefixWord ++ tailWord_5160082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5160109 : List Nat := [1, 5, 2, 1, 3, 2, 1, 2, 1, 5]
def baseStart_5160109 : Nat := 118140960795 + 5160109 * 2 ^ 59
def prefixEnd_5160109 : Nat := 4983230072969 + 3 ^ 40 * 5160109 * 2
def baseEnd_5160109 : Nat := 883205382197085594502199

theorem tailTrace_5160109 : CollatzResearch.WordTrace tailWord_5160109 prefixEnd_5160109 883205382197085594502199 := by
  unfold tailWord_5160109
  simp only [CollatzResearch.WordTrace]
  refine ⟨188204636862813844300307381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125469757908542562866871587 188204636862813844300307381)
  ·
    refine ⟨17644184705888797903153817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 188204636862813844300307381 17644184705888797903153817)
    ·
      refine ⟨13233138529416598427365363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17644184705888797903153817 13233138529416598427365363)
      ·
        refine ⟨19849707794124897641048045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13233138529416598427365363 19849707794124897641048045)
        ·
          refine ⟨7443640422796836615393017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19849707794124897641048045 7443640422796836615393017)
          ·
            refine ⟨5582730317097627461544763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7443640422796836615393017 5582730317097627461544763)
            ·
              refine ⟨8374095475646441192317145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5582730317097627461544763 8374095475646441192317145)
              ·
                refine ⟨6280571606734830894237859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8374095475646441192317145 6280571606734830894237859)
                ·
                  refine ⟨9420857410102246341356789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6280571606734830894237859 9420857410102246341356789)
                  ·
                    refine ⟨883205382197085594502199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9420857410102246341356789 883205382197085594502199)
                    ·
                      rfl

theorem cell23_5160109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 1, 2, 1, 5].length) (baseStart_5160109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5160109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5160109 prefixEnd_5160109 := by exact prefixLift 5160109
  have htrace : WordTrace (prefixWord ++ tailWord_5160109) baseStart_5160109 baseEnd_5160109 := by
    simpa [prefixWord, tailWord_5160109, baseEnd_5160109] using wordTrace_append hprefix tailTrace_5160109
  have hstable : (prefixWord ++ tailWord_5160109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5160109).length < 2 ^ (prefixWord ++ tailWord_5160109).sum := by decide
  have hdescent : baseEnd_5160109 < baseStart_5160109 := by decide
  rcases family_descends (prefixWord ++ tailWord_5160109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5160146 : List Nat := [3, 2, 2, 2, 1, 1, 3, 4, 1, 2, 2]
def baseStart_5160146 : Nat := 118140960795 + 5160146 * 2 ^ 59
def prefixEnd_5160146 : Nat := 4983230072969 + 3 ^ 40 * 5160146 * 2
def baseEnd_5160146 : Nat := 2649635145375473138743927

theorem tailTrace_5160146 : CollatzResearch.WordTrace tailWord_5160146 prefixEnd_5160146 2649635145375473138743927 := by
  unfold tailWord_5160146
  simp only [CollatzResearch.WordTrace]
  refine ⟨47051496590919949904851073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125470657575786533079602861 47051496590919949904851073)
  ·
    refine ⟨35288622443189962428638305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47051496590919949904851073 35288622443189962428638305)
    ·
      refine ⟨26466466832392471821478729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35288622443189962428638305 26466466832392471821478729)
      ·
        refine ⟨19849850124294353866109047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26466466832392471821478729 19849850124294353866109047)
        ·
          refine ⟨29774775186441530799163571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19849850124294353866109047 29774775186441530799163571)
          ·
            refine ⟨44662162779662296198745357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29774775186441530799163571 44662162779662296198745357)
            ·
              refine ⟨16748311042373361074529509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44662162779662296198745357 16748311042373361074529509)
              ·
                refine ⟨3140308320445005201474283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16748311042373361074529509 3140308320445005201474283)
                ·
                  refine ⟨4710462480667507802211425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3140308320445005201474283 4710462480667507802211425)
                  ·
                    refine ⟨3532846860500630851658569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4710462480667507802211425 3532846860500630851658569)
                    ·
                      refine ⟨2649635145375473138743927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3532846860500630851658569 2649635145375473138743927)
                      ·
                        rfl

theorem cell23_5160146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 4, 1, 2, 2].length) (baseStart_5160146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5160146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5160146 prefixEnd_5160146 := by exact prefixLift 5160146
  have htrace : WordTrace (prefixWord ++ tailWord_5160146) baseStart_5160146 baseEnd_5160146 := by
    simpa [prefixWord, tailWord_5160146, baseEnd_5160146] using wordTrace_append hprefix tailTrace_5160146
  have hstable : (prefixWord ++ tailWord_5160146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5160146).length < 2 ^ (prefixWord ++ tailWord_5160146).sum := by decide
  have hdescent : baseEnd_5160146 < baseStart_5160146 := by decide
  rcases family_descends (prefixWord ++ tailWord_5160146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5160152 : List Nat := [2, 1, 2, 2, 6, 1, 1, 8]
def baseStart_5160152 : Nat := 118140960795 + 5160152 * 2 ^ 59
def prefixEnd_5160152 : Nat := 4983230072969 + 3 ^ 40 * 5160152 * 2
def baseEnd_5160152 : Nat := 98134749120718522787737

theorem tailTrace_5160152 : CollatzResearch.WordTrace tailWord_5160152 prefixEnd_5160152 98134749120718522787737 := by
  unfold tailWord_5160152
  simp only [CollatzResearch.WordTrace]
  refine ⟨94103102600829031322061355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125470803467772041762748473 94103102600829031322061355)
  ·
    refine ⟨141154653901243546983092033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94103102600829031322061355 141154653901243546983092033)
    ·
      refine ⟨105865990425932660237319025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141154653901243546983092033 105865990425932660237319025)
      ·
        refine ⟨79399492819449495177989269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105865990425932660237319025 79399492819449495177989269)
        ·
          refine ⟨3721851225911695086468247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 79399492819449495177989269 3721851225911695086468247)
          ·
            refine ⟨5582776838867542629702371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3721851225911695086468247 5582776838867542629702371)
            ·
              refine ⟨8374165258301313944553557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5582776838867542629702371 8374165258301313944553557)
              ·
                refine ⟨98134749120718522787737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8374165258301313944553557 98134749120718522787737)
                ·
                  rfl

theorem cell23_5160152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 1, 8].length) (baseStart_5160152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5160152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5160152 prefixEnd_5160152 := by exact prefixLift 5160152
  have htrace : WordTrace (prefixWord ++ tailWord_5160152) baseStart_5160152 baseEnd_5160152 := by
    simpa [prefixWord, tailWord_5160152, baseEnd_5160152] using wordTrace_append hprefix tailTrace_5160152
  have hstable : (prefixWord ++ tailWord_5160152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5160152).length < 2 ^ (prefixWord ++ tailWord_5160152).sum := by decide
  have hdescent : baseEnd_5160152 < baseStart_5160152 := by decide
  rcases family_descends (prefixWord ++ tailWord_5160152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5160172 : List Nat := [2, 2, 1, 1, 2, 4, 2, 1, 3, 3, 2]
def baseStart_5160172 : Nat := 118140960795 + 5160172 * 2 ^ 59
def prefixEnd_5160172 : Nat := 4983230072969 + 3 ^ 40 * 5160172 * 2
def baseEnd_5160172 : Nat := 2649648495872490037018807

theorem tailTrace_5160172 : CollatzResearch.WordTrace tailWord_5160172 prefixEnd_5160172 2649648495872490037018807 := by
  unfold tailWord_5160172
  simp only [CollatzResearch.WordTrace]
  refine ⟨94103467330792803029925385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125471289774390404039900513 94103467330792803029925385)
  ·
    refine ⟨70577600498094602272444039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94103467330792803029925385 70577600498094602272444039)
    ·
      refine ⟨105866400747141903408666059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70577600498094602272444039 105866400747141903408666059)
      ·
        refine ⟨158799601120712855112999089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105866400747141903408666059 158799601120712855112999089)
        ·
          refine ⟨119099700840534641334749317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 158799601120712855112999089 119099700840534641334749317)
          ·
            refine ⟨22331193907600245250265497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 119099700840534641334749317 22331193907600245250265497)
            ·
              refine ⟨16748395430700183937699123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22331193907600245250265497 16748395430700183937699123)
              ·
                refine ⟨25122593146050275906548685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16748395430700183937699123 25122593146050275906548685)
                ·
                  refine ⟨9420972429768853464955757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25122593146050275906548685 9420972429768853464955757)
                  ·
                    refine ⟨3532864661163320049358409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9420972429768853464955757 3532864661163320049358409)
                    ·
                      refine ⟨2649648495872490037018807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3532864661163320049358409 2649648495872490037018807)
                      ·
                        rfl

theorem cell23_5160172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 3, 2].length) (baseStart_5160172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5160172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5160172 prefixEnd_5160172 := by exact prefixLift 5160172
  have htrace : WordTrace (prefixWord ++ tailWord_5160172) baseStart_5160172 baseEnd_5160172 := by
    simpa [prefixWord, tailWord_5160172, baseEnd_5160172] using wordTrace_append hprefix tailTrace_5160172
  have hstable : (prefixWord ++ tailWord_5160172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5160172).length < 2 ^ (prefixWord ++ tailWord_5160172).sum := by decide
  have hdescent : baseEnd_5160172 < baseStart_5160172 := by decide
  rcases family_descends (prefixWord ++ tailWord_5160172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5160180 : List Nat := [2, 6, 1, 2, 1, 2, 2, 1, 1, 1, 4]
def baseStart_5160180 : Nat := 118140960795 + 5160180 * 2 ^ 59
def prefixEnd_5160180 : Nat := 4983230072969 + 3 ^ 40 * 5160180 * 2
def baseEnd_5160180 : Nat := 2649652603717726005718771

theorem tailTrace_5160180 : CollatzResearch.WordTrace tailWord_5160180 prefixEnd_5160180 2649652603717726005718771 := by
  unfold tailWord_5160180
  simp only [CollatzResearch.WordTrace]
  refine ⟨94103613222778311713070997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125471484297037748950761329 94103613222778311713070997)
  ·
    refine ⟨4411106869817733361550203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 94103613222778311713070997 4411106869817733361550203)
    ·
      refine ⟨6616660304726600042325305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4411106869817733361550203 6616660304726600042325305)
      ·
        refine ⟨4962495228544950031743979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6616660304726600042325305 4962495228544950031743979)
        ·
          refine ⟨7443742842817425047615969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4962495228544950031743979 7443742842817425047615969)
          ·
            refine ⟨5582807132113068785711977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7443742842817425047615969 5582807132113068785711977)
            ·
              refine ⟨4187105349084801589283983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5582807132113068785711977 4187105349084801589283983)
              ·
                refine ⟨6280658023627202383925975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4187105349084801589283983 6280658023627202383925975)
                ·
                  refine ⟨9420987035440803575888963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6280658023627202383925975 9420987035440803575888963)
                  ·
                    refine ⟨14131480553161205363833445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9420987035440803575888963 14131480553161205363833445)
                    ·
                      refine ⟨2649652603717726005718771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14131480553161205363833445 2649652603717726005718771)
                      ·
                        rfl

theorem cell23_5160180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_5160180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5160180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5160180 prefixEnd_5160180 := by exact prefixLift 5160180
  have htrace : WordTrace (prefixWord ++ tailWord_5160180) baseStart_5160180 baseEnd_5160180 := by
    simpa [prefixWord, tailWord_5160180, baseEnd_5160180] using wordTrace_append hprefix tailTrace_5160180
  have hstable : (prefixWord ++ tailWord_5160180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5160180).length < 2 ^ (prefixWord ++ tailWord_5160180).sum := by decide
  have hdescent : baseEnd_5160180 < baseStart_5160180 := by decide
  rcases family_descends (prefixWord ++ tailWord_5160180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5160196 : List Nat := [2, 3, 2, 2, 2, 3, 1, 2, 2, 1, 3]
def baseStart_5160196 : Nat := 118140960795 + 5160196 * 2 ^ 59
def prefixEnd_5160196 : Nat := 4983230072969 + 3 ^ 40 * 5160196 * 2
def baseEnd_5160196 : Nat := 2649660819408197943118697

theorem tailTrace_5160196 : CollatzResearch.WordTrace tailWord_5160196 prefixEnd_5160196 2649660819408197943118697 := by
  unfold tailWord_5160196
  simp only [CollatzResearch.WordTrace]
  refine ⟨94103905006749329079362221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125471873342332438772482961 94103905006749329079362221)
  ·
    refine ⟨35288964377530998404760833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94103905006749329079362221 35288964377530998404760833)
    ·
      refine ⟨26466723283148248803570625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35288964377530998404760833 26466723283148248803570625)
      ·
        refine ⟨19850042462361186602677969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26466723283148248803570625 19850042462361186602677969)
        ·
          refine ⟨14887531846770889952008477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19850042462361186602677969 14887531846770889952008477)
          ·
            refine ⟨5582824442539083732003179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14887531846770889952008477 5582824442539083732003179)
            ·
              refine ⟨8374236663808625598004769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5582824442539083732003179 8374236663808625598004769)
              ·
                refine ⟨6280677497856469198503577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8374236663808625598004769 6280677497856469198503577)
                ·
                  refine ⟨4710508123392351898877683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6280677497856469198503577 4710508123392351898877683)
                  ·
                    refine ⟨7065762185088527848316525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4710508123392351898877683 7065762185088527848316525)
                    ·
                      refine ⟨2649660819408197943118697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7065762185088527848316525 2649660819408197943118697)
                      ·
                        rfl

theorem cell23_5160196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 1, 2, 2, 1, 3].length) (baseStart_5160196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5160196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5160196 prefixEnd_5160196 := by exact prefixLift 5160196
  have htrace : WordTrace (prefixWord ++ tailWord_5160196) baseStart_5160196 baseEnd_5160196 := by
    simpa [prefixWord, tailWord_5160196, baseEnd_5160196] using wordTrace_append hprefix tailTrace_5160196
  have hstable : (prefixWord ++ tailWord_5160196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5160196).length < 2 ^ (prefixWord ++ tailWord_5160196).sum := by decide
  have hdescent : baseEnd_5160196 < baseStart_5160196 := by decide
  rcases family_descends (prefixWord ++ tailWord_5160196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5160215 : List Nat := [1, 1, 3, 4, 1, 1, 1, 3, 2, 2, 4]
def baseStart_5160215 : Nat := 118140960795 + 5160215 * 2 ^ 59
def prefixEnd_5160215 : Nat := 4983230072969 + 3 ^ 40 * 5160215 * 2
def baseEnd_5160215 : Nat := 2649670575540633368781109

theorem tailTrace_5160215 : CollatzResearch.WordTrace tailWord_5160215 prefixEnd_5160215 2649670575540633368781109 := by
  unfold tailWord_5160215
  simp only [CollatzResearch.WordTrace]
  refine ⟨188208503000429824403666099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125472335333619882935777399 188208503000429824403666099)
  ·
    refine ⟨282312754500644736605499149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188208503000429824403666099 282312754500644736605499149)
    ·
      refine ⟨105867282937741776227062181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 282312754500644736605499149 105867282937741776227062181)
      ·
        refine ⟨19850115550826583042574159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 105867282937741776227062181 19850115550826583042574159)
        ·
          refine ⟨29775173326239874563861239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19850115550826583042574159 29775173326239874563861239)
          ·
            refine ⟨44662759989359811845791859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29775173326239874563861239 44662759989359811845791859)
            ·
              refine ⟨66994139984039717768687789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44662759989359811845791859 66994139984039717768687789)
              ·
                refine ⟨25122802494014894163257921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66994139984039717768687789 25122802494014894163257921)
                ·
                  refine ⟨18842101870511170622443441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25122802494014894163257921 18842101870511170622443441)
                  ·
                    refine ⟨14131576402883377966832581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18842101870511170622443441 14131576402883377966832581)
                    ·
                      refine ⟨2649670575540633368781109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14131576402883377966832581 2649670575540633368781109)
                      ·
                        rfl

theorem cell23_5160215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_5160215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5160215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5160215 prefixEnd_5160215 := by exact prefixLift 5160215
  have htrace : WordTrace (prefixWord ++ tailWord_5160215) baseStart_5160215 baseEnd_5160215 := by
    simpa [prefixWord, tailWord_5160215, baseEnd_5160215] using wordTrace_append hprefix tailTrace_5160215
  have hstable : (prefixWord ++ tailWord_5160215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5160215).length < 2 ^ (prefixWord ++ tailWord_5160215).sum := by decide
  have hdescent : baseEnd_5160215 < baseStart_5160215 := by decide
  rcases family_descends (prefixWord ++ tailWord_5160215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5160255 : List Nat := [1, 1, 2, 2, 4, 2, 1, 1, 4, 5]
def baseStart_5160255 : Nat := 118140960795 + 5160255 * 2 ^ 59
def prefixEnd_5160255 : Nat := 4983230072969 + 3 ^ 40 * 5160255 * 2
def baseEnd_5160255 : Nat := 883230371588937737426975

theorem tailTrace_5160255 : CollatzResearch.WordTrace tailWord_5160255 prefixEnd_5160255 883230371588937737426975 := by
  unfold tailWord_5160255
  simp only [CollatzResearch.WordTrace]
  refine ⟨188209961920284911235122219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125473307946856607490081479 188209961920284911235122219)
  ·
    refine ⟨282314942880427366852683329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188209961920284911235122219 282314942880427366852683329)
    ·
      refine ⟨211736207160320525139512497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 282314942880427366852683329 211736207160320525139512497)
      ·
        refine ⟨158802155370240393854634373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 211736207160320525139512497 158802155370240393854634373)
        ·
          refine ⟨29775404131920073847743945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 158802155370240393854634373 29775404131920073847743945)
          ·
            refine ⟨22331553098940055385807959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29775404131920073847743945 22331553098940055385807959)
            ·
              refine ⟨33497329648410083078711939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22331553098940055385807959 33497329648410083078711939)
              ·
                refine ⟨50245994472615124618067909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33497329648410083078711939 50245994472615124618067909)
                ·
                  refine ⟨9421123963615335865887733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50245994472615124618067909 9421123963615335865887733)
                  ·
                    refine ⟨883230371588937737426975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9421123963615335865887733 883230371588937737426975)
                    ·
                      rfl

theorem cell23_5160255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 1, 4, 5].length) (baseStart_5160255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5160255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5160255 prefixEnd_5160255 := by exact prefixLift 5160255
  have htrace : WordTrace (prefixWord ++ tailWord_5160255) baseStart_5160255 baseEnd_5160255 := by
    simpa [prefixWord, tailWord_5160255, baseEnd_5160255] using wordTrace_append hprefix tailTrace_5160255
  have hstable : (prefixWord ++ tailWord_5160255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5160255).length < 2 ^ (prefixWord ++ tailWord_5160255).sum := by decide
  have hdescent : baseEnd_5160255 < baseStart_5160255 := by decide
  rcases family_descends (prefixWord ++ tailWord_5160255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5160275 : List Nat := [1, 1, 1, 2, 1, 1, 5, 2, 4, 1, 4]
def baseStart_5160275 : Nat := 118140960795 + 5160275 * 2 ^ 59
def prefixEnd_5160275 : Nat := 4983230072969 + 3 ^ 40 * 5160275 * 2
def baseEnd_5160275 : Nat := 2649701384379903134030833

theorem tailTrace_5160275 : CollatzResearch.WordTrace tailWord_5160275 prefixEnd_5160275 2649701384379903134030833 := by
  unfold tailWord_5160275
  simp only [CollatzResearch.WordTrace]
  refine ⟨188210691380212454650850279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125473794253474969767233519 188210691380212454650850279)
  ·
    refine ⟨282316037070318681976275419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188210691380212454650850279 282316037070318681976275419)
    ·
      refine ⟨423474055605478022964413129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 282316037070318681976275419 423474055605478022964413129)
      ·
        refine ⟨317605541704108517223309847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 423474055605478022964413129 317605541704108517223309847)
        ·
          refine ⟨476408312556162775834964771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 317605541704108517223309847 476408312556162775834964771)
          ·
            refine ⟨714612468834244163752447157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 476408312556162775834964771 714612468834244163752447157)
            ·
              refine ⟨66994918953210390351791921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 714612468834244163752447157 66994918953210390351791921)
              ·
                refine ⟨50246189214907792763843941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66994918953210390351791921 50246189214907792763843941)
                ·
                  refine ⟨9421160477795211143220739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50246189214907792763843941 9421160477795211143220739)
                  ·
                    refine ⟨14131740716692816714831109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9421160477795211143220739 14131740716692816714831109)
                    ·
                      refine ⟨2649701384379903134030833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14131740716692816714831109 2649701384379903134030833)
                      ·
                        rfl

theorem cell23_5160275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 2, 4, 1, 4].length) (baseStart_5160275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5160275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5160275 prefixEnd_5160275 := by exact prefixLift 5160275
  have htrace : WordTrace (prefixWord ++ tailWord_5160275) baseStart_5160275 baseEnd_5160275 := by
    simpa [prefixWord, tailWord_5160275, baseEnd_5160275] using wordTrace_append hprefix tailTrace_5160275
  have hstable : (prefixWord ++ tailWord_5160275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5160275).length < 2 ^ (prefixWord ++ tailWord_5160275).sum := by decide
  have hdescent : baseEnd_5160275 < baseStart_5160275 := by decide
  rcases family_descends (prefixWord ++ tailWord_5160275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5160292 : List Nat := [2, 3, 1, 1, 3, 2, 1, 3, 2, 1, 4]
def baseStart_5160292 : Nat := 118140960795 + 5160292 * 2 ^ 59
def prefixEnd_5160292 : Nat := 4983230072969 + 3 ^ 40 * 5160292 * 2
def baseEnd_5160292 : Nat := 2649710113551029567518255

theorem tailTrace_5160292 : CollatzResearch.WordTrace tailWord_5160292 prefixEnd_5160292 2649710113551029567518255 := by
  unfold tailWord_5160292
  simp only [CollatzResearch.WordTrace]
  refine ⟨94105655710575433277109565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125474207614100577702812753 94105655710575433277109565)
  ·
    refine ⟨35289620891465787478916087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94105655710575433277109565 35289620891465787478916087)
    ·
      refine ⟨52934431337198681218374131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35289620891465787478916087 52934431337198681218374131)
      ·
        refine ⟨79401647005798021827561197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52934431337198681218374131 79401647005798021827561197)
        ·
          refine ⟨29775617627174258185335449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79401647005798021827561197 29775617627174258185335449)
          ·
            refine ⟨22331713220380693639001587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29775617627174258185335449 22331713220380693639001587)
            ·
              refine ⟨33497569830571040458502381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22331713220380693639001587 33497569830571040458502381)
              ·
                refine ⟨12561588686464140171938393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33497569830571040458502381 12561588686464140171938393)
                ·
                  refine ⟨9421191514848105128953795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12561588686464140171938393 9421191514848105128953795)
                  ·
                    refine ⟨14131787272272157693430693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9421191514848105128953795 14131787272272157693430693)
                    ·
                      refine ⟨2649710113551029567518255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14131787272272157693430693 2649710113551029567518255)
                      ·
                        rfl

theorem cell23_5160292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 3, 2, 1, 4].length) (baseStart_5160292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5160292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5160292 prefixEnd_5160292 := by exact prefixLift 5160292
  have htrace : WordTrace (prefixWord ++ tailWord_5160292) baseStart_5160292 baseEnd_5160292 := by
    simpa [prefixWord, tailWord_5160292, baseEnd_5160292] using wordTrace_append hprefix tailTrace_5160292
  have hstable : (prefixWord ++ tailWord_5160292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5160292).length < 2 ^ (prefixWord ++ tailWord_5160292).sum := by decide
  have hdescent : baseEnd_5160292 < baseStart_5160292 := by decide
  rcases family_descends (prefixWord ++ tailWord_5160292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5160359 : List Nat := [1, 1, 6, 1, 1, 1, 1, 2, 5, 1, 3]
def baseStart_5160359 : Nat := 118140960795 + 5160359 * 2 ^ 59
def prefixEnd_5160359 : Nat := 4983230072969 + 3 ^ 40 * 5160359 * 2
def baseEnd_5160359 : Nat := 2649744516754880805380447

theorem tailTrace_5160359 : CollatzResearch.WordTrace tailWord_5160359 prefixEnd_5160359 2649744516754880805380447 := by
  unfold tailWord_5160359
  simp only [CollatzResearch.WordTrace]
  refine ⟨188213755111908136996908131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125475836741272091331272087 188213755111908136996908131)
  ·
    refine ⟨282320632667862205495362197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188213755111908136996908131 282320632667862205495362197)
    ·
      refine ⟨13233779656306040882595103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 282320632667862205495362197 13233779656306040882595103)
      ·
        refine ⟨19850669484459061323892655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13233779656306040882595103 19850669484459061323892655)
        ·
          refine ⟨29776004226688591985838983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19850669484459061323892655 29776004226688591985838983)
          ·
            refine ⟨44664006340032887978758475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29776004226688591985838983 44664006340032887978758475)
            ·
              refine ⟨66996009510049331968137713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44664006340032887978758475 66996009510049331968137713)
              ·
                refine ⟨50247007132536998976103285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66996009510049331968137713 50247007132536998976103285)
                ·
                  refine ⟨4710656918675343654009683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 50247007132536998976103285 4710656918675343654009683)
                  ·
                    refine ⟨7065985378013015481014525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4710656918675343654009683 7065985378013015481014525)
                    ·
                      refine ⟨2649744516754880805380447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7065985378013015481014525 2649744516754880805380447)
                      ·
                        rfl

theorem cell23_5160359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 2, 5, 1, 3].length) (baseStart_5160359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5160359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5160359 prefixEnd_5160359 := by exact prefixLift 5160359
  have htrace : WordTrace (prefixWord ++ tailWord_5160359) baseStart_5160359 baseEnd_5160359 := by
    simpa [prefixWord, tailWord_5160359, baseEnd_5160359] using wordTrace_append hprefix tailTrace_5160359
  have hstable : (prefixWord ++ tailWord_5160359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5160359).length < 2 ^ (prefixWord ++ tailWord_5160359).sum := by decide
  have hdescent : baseEnd_5160359 < baseStart_5160359 := by decide
  rcases family_descends (prefixWord ++ tailWord_5160359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5160369 : List Nat := [1, 2, 2, 4, 1, 1, 2, 1, 4, 3, 2]
def baseStart_5160369 : Nat := 118140960795 + 5160369 * 2 ^ 59
def prefixEnd_5160369 : Nat := 4983230072969 + 3 ^ 40 * 5160369 * 2
def baseEnd_5160369 : Nat := 2649749651561425766255401

theorem tailTrace_5160369 : CollatzResearch.WordTrace tailWord_5160369 prefixEnd_5160369 2649749651561425766255401 := by
  unfold tailWord_5160369
  simp only [CollatzResearch.WordTrace]
  refine ⟨188214119841871908704772161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125476079894581272469848107 188214119841871908704772161)
  ·
    refine ⟨141160589881403931528579121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188214119841871908704772161 141160589881403931528579121)
    ·
      refine ⟨105870442411052948646434341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141160589881403931528579121 105870442411052948646434341)
      ·
        refine ⟨19850707952072427871206439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 105870442411052948646434341 19850707952072427871206439)
        ·
          refine ⟨29776061928108641806809659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19850707952072427871206439 29776061928108641806809659)
          ·
            refine ⟨44664092892162962710214489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29776061928108641806809659 44664092892162962710214489)
            ·
              refine ⟨33498069669122222032660867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44664092892162962710214489 33498069669122222032660867)
              ·
                refine ⟨50247104503683333048991301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33498069669122222032660867 50247104503683333048991301)
                ·
                  refine ⟨9421332094440624946685869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50247104503683333048991301 9421332094440624946685869)
                  ·
                    refine ⟨3532999535415234355007201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9421332094440624946685869 3532999535415234355007201)
                    ·
                      refine ⟨2649749651561425766255401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3532999535415234355007201 2649749651561425766255401)
                      ·
                        rfl

theorem cell23_5160369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 1, 4, 3, 2].length) (baseStart_5160369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5160369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5160369 prefixEnd_5160369 := by exact prefixLift 5160369
  have htrace : WordTrace (prefixWord ++ tailWord_5160369) baseStart_5160369 baseEnd_5160369 := by
    simpa [prefixWord, tailWord_5160369, baseEnd_5160369] using wordTrace_append hprefix tailTrace_5160369
  have hstable : (prefixWord ++ tailWord_5160369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5160369).length < 2 ^ (prefixWord ++ tailWord_5160369).sum := by decide
  have hdescent : baseEnd_5160369 < baseStart_5160369 := by decide
  rcases family_descends (prefixWord ++ tailWord_5160369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5160376 : List Nat := [2, 1, 2, 1, 2, 2, 4, 4, 1, 1, 3]
def baseStart_5160376 : Nat := 118140960795 + 5160376 * 2 ^ 59
def prefixEnd_5160376 : Nat := 4983230072969 + 3 ^ 40 * 5160376 * 2
def baseEnd_5160376 : Nat := 2649753245926007238867869

theorem tailTrace_5160376 : CollatzResearch.WordTrace tailWord_5160376 prefixEnd_5160376 2649753245926007238867869 := by
  unfold tailWord_5160376
  simp only [CollatzResearch.WordTrace]
  refine ⟨94107187576423274450138491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125476250101897699266851321 94107187576423274450138491)
  ·
    refine ⟨141160781364634911675207737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94107187576423274450138491 141160781364634911675207737)
    ·
      refine ⟨105870586023476183756405803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141160781364634911675207737 105870586023476183756405803)
      ·
        refine ⟨158805879035214275634608705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105870586023476183756405803 158805879035214275634608705)
        ·
          refine ⟨119104409276410706725956529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 158805879035214275634608705 119104409276410706725956529)
          ·
            refine ⟨89328306957308030044467397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119104409276410706725956529 89328306957308030044467397)
            ·
              refine ⟨16749057554495255633337637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 89328306957308030044467397 16749057554495255633337637)
              ·
                refine ⟨3140448291467860431250807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16749057554495255633337637 3140448291467860431250807)
                ·
                  refine ⟨4710672437201790646876211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3140448291467860431250807 4710672437201790646876211)
                  ·
                    refine ⟨7066008655802685970314317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4710672437201790646876211 7066008655802685970314317)
                    ·
                      refine ⟨2649753245926007238867869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7066008655802685970314317 2649753245926007238867869)
                      ·
                        rfl

theorem cell23_5160376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 4, 1, 1, 3].length) (baseStart_5160376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5160376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5160376 prefixEnd_5160376 := by exact prefixLift 5160376
  have htrace : WordTrace (prefixWord ++ tailWord_5160376) baseStart_5160376 baseEnd_5160376 := by
    simpa [prefixWord, tailWord_5160376, baseEnd_5160376] using wordTrace_append hprefix tailTrace_5160376
  have hstable : (prefixWord ++ tailWord_5160376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5160376).length < 2 ^ (prefixWord ++ tailWord_5160376).sum := by decide
  have hdescent : baseEnd_5160376 < baseStart_5160376 := by decide
  rcases family_descends (prefixWord ++ tailWord_5160376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5160419 : List Nat := [1, 1, 1, 6, 2, 2, 2, 1, 1, 1, 5]
def baseStart_5160419 : Nat := 118140960795 + 5160419 * 2 ^ 59
def prefixEnd_5160419 : Nat := 4983230072969 + 3 ^ 40 * 5160419 * 2
def baseEnd_5160419 : Nat := 2649775325594150570630171

theorem tailTrace_5160419 : CollatzResearch.WordTrace tailWord_5160419 prefixEnd_5160419 2649775325594150570630171 := by
  unfold tailWord_5160419
  simp only [CollatzResearch.WordTrace]
  refine ⟨188215943491690767244092311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125477295661127178162728207 188215943491690767244092311)
  ·
    refine ⟨282323915237536150866138467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188215943491690767244092311 282323915237536150866138467)
    ·
      refine ⟨423485872856304226299207701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 282323915237536150866138467 423485872856304226299207701)
      ·
        refine ⟨19850900290139260607775361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 423485872856304226299207701 19850900290139260607775361)
        ·
          refine ⟨14888175217604445455831521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19850900290139260607775361 14888175217604445455831521)
          ·
            refine ⟨11166131413203334091873641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14888175217604445455831521 11166131413203334091873641)
            ·
              refine ⟨8374598559902500568905231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11166131413203334091873641 8374598559902500568905231)
              ·
                refine ⟨12561897839853750853357847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8374598559902500568905231 12561897839853750853357847)
                ·
                  refine ⟨18842846759780626280036771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12561897839853750853357847 18842846759780626280036771)
                  ·
                    refine ⟨28264270139670939420055157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18842846759780626280036771 28264270139670939420055157)
                    ·
                      refine ⟨2649775325594150570630171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28264270139670939420055157 2649775325594150570630171)
                      ·
                        rfl

theorem cell23_5160419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 2, 1, 1, 1, 5].length) (baseStart_5160419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5160419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5160419 prefixEnd_5160419 := by exact prefixLift 5160419
  have htrace : WordTrace (prefixWord ++ tailWord_5160419) baseStart_5160419 baseEnd_5160419 := by
    simpa [prefixWord, tailWord_5160419, baseEnd_5160419] using wordTrace_append hprefix tailTrace_5160419
  have hstable : (prefixWord ++ tailWord_5160419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5160419).length < 2 ^ (prefixWord ++ tailWord_5160419).sum := by decide
  have hdescent : baseEnd_5160419 < baseStart_5160419 := by decide
  rcases family_descends (prefixWord ++ tailWord_5160419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5160433 : List Nat := [1, 2, 2, 2, 3, 4, 1, 1, 3, 2, 2]
def baseStart_5160433 : Nat := 118140960795 + 5160433 * 2 ^ 59
def prefixEnd_5160433 : Nat := 4983230072969 + 3 ^ 40 * 5160433 * 2
def baseEnd_5160433 : Nat := 2649782514323313515855107

theorem tailTrace_5160433 : CollatzResearch.WordTrace tailWord_5160433 prefixEnd_5160433 2649782514323313515855107 := by
  unfold tailWord_5160433
  simp only [CollatzResearch.WordTrace]
  refine ⟨188216454113640047635101953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125477636075760031756734635 188216454113640047635101953)
  ·
    refine ⟨141162340585230035726326465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188216454113640047635101953 141162340585230035726326465)
    ·
      refine ⟨105871755438922526794744849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141162340585230035726326465 105871755438922526794744849)
      ·
        refine ⟨79403816579191895096058637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105871755438922526794744849 79403816579191895096058637)
        ·
          refine ⟨29776431217196960661021989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79403816579191895096058637 29776431217196960661021989)
          ·
            refine ⟨5583080853224430123941623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29776431217196960661021989 5583080853224430123941623)
            ·
              refine ⟨8374621279836645185912435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5583080853224430123941623 8374621279836645185912435)
              ·
                refine ⟨12561931919754967778868653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8374621279836645185912435 12561931919754967778868653)
                ·
                  refine ⟨4710724469908112917075745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12561931919754967778868653 4710724469908112917075745)
                  ·
                    refine ⟨3533043352431084687806809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4710724469908112917075745 3533043352431084687806809)
                    ·
                      refine ⟨2649782514323313515855107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3533043352431084687806809 2649782514323313515855107)
                      ·
                        rfl

theorem cell23_5160433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 1, 1, 3, 2, 2].length) (baseStart_5160433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5160433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5160433 prefixEnd_5160433 := by exact prefixLift 5160433
  have htrace : WordTrace (prefixWord ++ tailWord_5160433) baseStart_5160433 baseEnd_5160433 := by
    simpa [prefixWord, tailWord_5160433, baseEnd_5160433] using wordTrace_append hprefix tailTrace_5160433
  have hstable : (prefixWord ++ tailWord_5160433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5160433).length < 2 ^ (prefixWord ++ tailWord_5160433).sum := by decide
  have hdescent : baseEnd_5160433 < baseStart_5160433 := by decide
  rcases family_descends (prefixWord ++ tailWord_5160433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5160478 : List Nat := [4, 3, 3, 1, 2, 1, 2, 2, 1, 1, 3]
def baseStart_5160478 : Nat := 118140960795 + 5160478 * 2 ^ 59
def prefixEnd_5160478 : Nat := 4983230072969 + 3 ^ 40 * 5160478 * 2
def baseEnd_5160478 : Nat := 2649805620952765839792401

theorem tailTrace_5160478 : CollatzResearch.WordTrace tailWord_5160478 prefixEnd_5160478 2649805620952765839792401 := by
  unfold tailWord_5160478
  simp only [CollatzResearch.WordTrace]
  refine ⟨23527261924809627540061261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125478730265651346880326725 23527261924809627540061261)
  ·
    refine ⟨8822723221803610327522973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23527261924809627540061261 8822723221803610327522973)
    ·
      refine ⟨3308521208176353872821115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8822723221803610327522973 3308521208176353872821115)
      ·
        refine ⟨4962781812264530809231673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3308521208176353872821115 4962781812264530809231673)
        ·
          refine ⟨3722086359198398106923755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4962781812264530809231673 3722086359198398106923755)
          ·
            refine ⟨5583129538797597160385633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3722086359198398106923755 5583129538797597160385633)
            ·
              refine ⟨4187347154098197870289225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5583129538797597160385633 4187347154098197870289225)
              ·
                refine ⟨3140510365573648402716919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4187347154098197870289225 3140510365573648402716919)
                ·
                  refine ⟨4710765548360472604075379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3140510365573648402716919 4710765548360472604075379)
                  ·
                    refine ⟨7066148322540708906113069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4710765548360472604075379 7066148322540708906113069)
                    ·
                      refine ⟨2649805620952765839792401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7066148322540708906113069 2649805620952765839792401)
                      ·
                        rfl

theorem cell23_5160478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_5160478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5160478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5160478 prefixEnd_5160478 := by exact prefixLift 5160478
  have htrace : WordTrace (prefixWord ++ tailWord_5160478) baseStart_5160478 baseEnd_5160478 := by
    simpa [prefixWord, tailWord_5160478, baseEnd_5160478] using wordTrace_append hprefix tailTrace_5160478
  have hstable : (prefixWord ++ tailWord_5160478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5160478).length < 2 ^ (prefixWord ++ tailWord_5160478).sum := by decide
  have hdescent : baseEnd_5160478 < baseStart_5160478 := by decide
  rcases family_descends (prefixWord ++ tailWord_5160478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5160483 : List Nat := [1, 1, 1, 4, 5, 1, 2, 2, 2, 1, 3]
def baseStart_5160483 : Nat := 118140960795 + 5160483 * 2 ^ 59
def prefixEnd_5160483 : Nat := 4983230072969 + 3 ^ 40 * 5160483 * 2
def baseEnd_5160483 : Nat := 2649808188356038320229877

theorem tailTrace_5160483 : CollatzResearch.WordTrace tailWord_5160483 prefixEnd_5160483 2649808188356038320229877 := by
  unfold tailWord_5160483
  simp only [CollatzResearch.WordTrace]
  refine ⟨188218277763458906174422103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125478851842305937449614735 188218277763458906174422103)
  ·
    refine ⟨282327416645188359261633155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188218277763458906174422103 282327416645188359261633155)
    ·
      refine ⟨423491124967782538892449733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 282327416645188359261633155 423491124967782538892449733)
      ·
        refine ⟨79404585931459226042334325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 423491124967782538892449733 79404585931459226042334325)
        ·
          refine ⟨7444179931074302441468843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 79404585931459226042334325 7444179931074302441468843)
          ·
            refine ⟨11166269896611453662203265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7444179931074302441468843 11166269896611453662203265)
            ·
              refine ⟨8374702422458590246652449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11166269896611453662203265 8374702422458590246652449)
              ·
                refine ⟨6281026816843942684989337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8374702422458590246652449 6281026816843942684989337)
                ·
                  refine ⟨4710770112632957013742003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6281026816843942684989337 4710770112632957013742003)
                  ·
                    refine ⟨7066155168949435520613005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4710770112632957013742003 7066155168949435520613005)
                    ·
                      refine ⟨2649808188356038320229877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7066155168949435520613005 2649808188356038320229877)
                      ·
                        rfl

theorem cell23_5160483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 2, 2, 2, 1, 3].length) (baseStart_5160483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5160483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5160483 prefixEnd_5160483 := by exact prefixLift 5160483
  have htrace : WordTrace (prefixWord ++ tailWord_5160483) baseStart_5160483 baseEnd_5160483 := by
    simpa [prefixWord, tailWord_5160483, baseEnd_5160483] using wordTrace_append hprefix tailTrace_5160483
  have hstable : (prefixWord ++ tailWord_5160483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5160483).length < 2 ^ (prefixWord ++ tailWord_5160483).sum := by decide
  have hdescent : baseEnd_5160483 < baseStart_5160483 := by decide
  rcases family_descends (prefixWord ++ tailWord_5160483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5160506 : List Nat := [3, 1, 1, 1, 3, 2, 4, 1, 1, 4, 2]
def baseStart_5160506 : Nat := 118140960795 + 5160506 * 2 ^ 59
def prefixEnd_5160506 : Nat := 4983230072969 + 3 ^ 40 * 5160506 * 2
def baseEnd_5160506 : Nat := 2649819998411091730242271

theorem tailTrace_5160506 : CollatzResearch.WordTrace tailWord_5160506 prefixEnd_5160506 2649819998411091730242271 := by
  unfold tailWord_5160506
  simp only [CollatzResearch.WordTrace]
  refine ⟨47054779160593895275627343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125479411094917054068339581 47054779160593895275627343)
  ·
    refine ⟨70582168740890842913441015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47054779160593895275627343 70582168740890842913441015)
    ·
      refine ⟨105873253111336264370161523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70582168740890842913441015 105873253111336264370161523)
      ·
        refine ⟨158809879667004396555242285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105873253111336264370161523 158809879667004396555242285)
        ·
          refine ⟨59553704875126648708215857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 158809879667004396555242285 59553704875126648708215857)
          ·
            refine ⟨44665278656344986531161893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59553704875126648708215857 44665278656344986531161893)
            ·
              refine ⟨8374739748064684974592855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44665278656344986531161893 8374739748064684974592855)
              ·
                refine ⟨12562109622097027461889283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8374739748064684974592855 12562109622097027461889283)
                ·
                  refine ⟨18843164433145541192833925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12562109622097027461889283 18843164433145541192833925)
                  ·
                    refine ⟨3533093331214788973656361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18843164433145541192833925 3533093331214788973656361)
                    ·
                      refine ⟨2649819998411091730242271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3533093331214788973656361 2649819998411091730242271)
                      ·
                        rfl

theorem cell23_5160506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 4, 1, 1, 4, 2].length) (baseStart_5160506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5160506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5160506 prefixEnd_5160506 := by exact prefixLift 5160506
  have htrace : WordTrace (prefixWord ++ tailWord_5160506) baseStart_5160506 baseEnd_5160506 := by
    simpa [prefixWord, tailWord_5160506, baseEnd_5160506] using wordTrace_append hprefix tailTrace_5160506
  have hstable : (prefixWord ++ tailWord_5160506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5160506).length < 2 ^ (prefixWord ++ tailWord_5160506).sum := by decide
  have hdescent : baseEnd_5160506 < baseStart_5160506 := by decide
  rcases family_descends (prefixWord ++ tailWord_5160506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
