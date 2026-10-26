import V185TrunkScan23Chunk0634

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3754440 : List Nat := [2, 1, 3, 1, 3, 2, 1, 4, 2, 2, 2]
def baseStart_3754440 : Nat := 118140960795 + 3754440 * 2 ^ 59
def prefixEnd_3754440 : Nat := 4983230072969 + 3 ^ 40 * 3754440 * 2
def baseEnd_3754440 : Nat := 1927832308466395969933651

theorem tailTrace_3754440 : CollatzResearch.WordTrace tailWord_3754440 prefixEnd_3754440 1927832308466395969933651 := by
  unfold tailWord_3754440
  simp only [CollatzResearch.WordTrace]
  refine ⟨68467838259156281073994387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91290451012208374765325849 68467838259156281073994387)
  ·
    refine ⟨102701757388734421610991581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68467838259156281073994387 102701757388734421610991581)
    ·
      refine ⟨38513159020775408104121843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102701757388734421610991581 38513159020775408104121843)
      ·
        refine ⟨57769738531163112156182765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38513159020775408104121843 57769738531163112156182765)
        ·
          refine ⟨21663651949186167058568537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57769738531163112156182765 21663651949186167058568537)
          ·
            refine ⟨16247738961889625293926403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21663651949186167058568537 16247738961889625293926403)
            ·
              refine ⟨24371608442834437940889605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16247738961889625293926403 24371608442834437940889605)
              ·
                refine ⟨4569676583031457113916801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24371608442834437940889605 4569676583031457113916801)
                ·
                  refine ⟨3427257437273592835437601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4569676583031457113916801 3427257437273592835437601)
                  ·
                    refine ⟨2570443077955194626578201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3427257437273592835437601 2570443077955194626578201)
                    ·
                      refine ⟨1927832308466395969933651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2570443077955194626578201 1927832308466395969933651)
                      ·
                        rfl

theorem cell23_3754440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 4, 2, 2, 2].length) (baseStart_3754440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3754440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3754440 prefixEnd_3754440 := by exact prefixLift 3754440
  have htrace : WordTrace (prefixWord ++ tailWord_3754440) baseStart_3754440 baseEnd_3754440 := by
    simpa [prefixWord, tailWord_3754440, baseEnd_3754440] using wordTrace_append hprefix tailTrace_3754440
  have hstable : (prefixWord ++ tailWord_3754440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3754440).length < 2 ^ (prefixWord ++ tailWord_3754440).sum := by decide
  have hdescent : baseEnd_3754440 < baseStart_3754440 := by decide
  rcases family_descends (prefixWord ++ tailWord_3754440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3754550 : List Nat := [5, 1, 2, 1, 2, 1, 1, 1, 4, 2, 3]
def baseStart_3754550 : Nat := 118140960795 + 3754550 * 2 ^ 59
def prefixEnd_3754550 : Nat := 4983230072969 + 3 ^ 40 * 3754550 * 2
def baseEnd_3754550 : Nat := 1927888791338390539558145

theorem tailTrace_3754550 : CollatzResearch.WordTrace tailWord_3754550 prefixEnd_3754550 1927888791338390539558145 := by
  unfold tailWord_3754550
  simp only [CollatzResearch.WordTrace]
  refine ⟨8558730534244628183405819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 91293125698609367289662069 8558730534244628183405819)
  ·
    refine ⟨12838095801366942275108729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8558730534244628183405819 12838095801366942275108729)
    ·
      refine ⟨9628571851025206706331547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12838095801366942275108729 9628571851025206706331547)
      ·
        refine ⟨14442857776537810059497321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9628571851025206706331547 14442857776537810059497321)
        ·
          refine ⟨10832143332403357544622991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14442857776537810059497321 10832143332403357544622991)
          ·
            refine ⟨16248214998605036316934487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10832143332403357544622991 16248214998605036316934487)
            ·
              refine ⟨24372322497907554475401731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16248214998605036316934487 24372322497907554475401731)
              ·
                refine ⟨36558483746861331713102597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24372322497907554475401731 36558483746861331713102597)
                ·
                  refine ⟨6854715702536499696206737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36558483746861331713102597 6854715702536499696206737)
                  ·
                    refine ⟨5141036776902374772155053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6854715702536499696206737 5141036776902374772155053)
                    ·
                      refine ⟨1927888791338390539558145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5141036776902374772155053 1927888791338390539558145)
                      ·
                        rfl

theorem cell23_3754550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 1, 4, 2, 3].length) (baseStart_3754550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3754550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3754550 prefixEnd_3754550 := by exact prefixLift 3754550
  have htrace : WordTrace (prefixWord ++ tailWord_3754550) baseStart_3754550 baseEnd_3754550 := by
    simpa [prefixWord, tailWord_3754550, baseEnd_3754550] using wordTrace_append hprefix tailTrace_3754550
  have hstable : (prefixWord ++ tailWord_3754550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3754550).length < 2 ^ (prefixWord ++ tailWord_3754550).sum := by decide
  have hdescent : baseEnd_3754550 < baseStart_3754550 := by decide
  rcases family_descends (prefixWord ++ tailWord_3754550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3754570 : List Nat := [3, 1, 2, 1, 1, 6, 2, 1, 6]
def baseStart_3754570 : Nat := 118140960795 + 3754570 * 2 ^ 59
def prefixEnd_3754570 : Nat := 4983230072969 + 3 ^ 40 * 3754570 * 2
def baseEnd_3754570 : Nat := 214211006772386717923117

theorem tailTrace_3754570 : CollatzResearch.WordTrace tailWord_3754570 prefixEnd_3754570 214211006772386717923117 := by
  unfold tailWord_3754570
  simp only [CollatzResearch.WordTrace]
  refine ⟨34235104501960398587555291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91293612005227729566814109 34235104501960398587555291)
  ·
    refine ⟨51352656752940597881332937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34235104501960398587555291 51352656752940597881332937)
    ·
      refine ⟨38514492564705448410999703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51352656752940597881332937 38514492564705448410999703)
      ·
        refine ⟨57771738847058172616499555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38514492564705448410999703 57771738847058172616499555)
        ·
          refine ⟨86657608270587258924749333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57771738847058172616499555 86657608270587258924749333)
          ·
            refine ⟨4062075387683777762097625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 86657608270587258924749333 4062075387683777762097625)
            ·
              refine ⟨3046556540762833321573219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4062075387683777762097625 3046556540762833321573219)
              ·
                refine ⟨4569834811144249982359829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3046556540762833321573219 4569834811144249982359829)
                ·
                  refine ⟨214211006772386717923117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4569834811144249982359829 214211006772386717923117)
                  ·
                    rfl

theorem cell23_3754570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 2, 1, 6].length) (baseStart_3754570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3754570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3754570 prefixEnd_3754570 := by exact prefixLift 3754570
  have htrace : WordTrace (prefixWord ++ tailWord_3754570) baseStart_3754570 baseEnd_3754570 := by
    simpa [prefixWord, tailWord_3754570, baseEnd_3754570] using wordTrace_append hprefix tailTrace_3754570
  have hstable : (prefixWord ++ tailWord_3754570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3754570).length < 2 ^ (prefixWord ++ tailWord_3754570).sum := by decide
  have hdescent : baseEnd_3754570 < baseStart_3754570 := by decide
  rcases family_descends (prefixWord ++ tailWord_3754570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3754657 : List Nat := [1, 2, 3, 3, 3, 1, 1, 3, 1, 2, 3]
def baseStart_3754657 : Nat := 118140960795 + 3754657 * 2 ^ 59
def prefixEnd_3754657 : Nat := 4983230072969 + 3 ^ 40 * 3754657 * 2
def baseEnd_3754657 : Nat := 1927943733768421620920153

theorem tailTrace_3754657 : CollatzResearch.WordTrace tailWord_3754657 prefixEnd_3754657 1927943733768421620920153 := by
  unfold tailWord_3754657
  simp only [CollatzResearch.WordTrace]
  refine ⟨136943591158526408208638225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91295727439017605472425483 136943591158526408208638225)
  ·
    refine ⟨102707693368894806156478669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136943591158526408208638225 102707693368894806156478669)
    ·
      refine ⟨38515385013335552308679501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102707693368894806156478669 38515385013335552308679501)
      ·
        refine ⟨14443269380000832115754813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38515385013335552308679501 14443269380000832115754813)
        ·
          refine ⟨5416226017500312043408055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14443269380000832115754813 5416226017500312043408055)
          ·
            refine ⟨8124339026250468065112083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5416226017500312043408055 8124339026250468065112083)
            ·
              refine ⟨12186508539375702097668125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8124339026250468065112083 12186508539375702097668125)
              ·
                refine ⟨4569940702265888286625547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12186508539375702097668125 4569940702265888286625547)
                ·
                  refine ⟨6854911053398832429938321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4569940702265888286625547 6854911053398832429938321)
                  ·
                    refine ⟨5141183290049124322453741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6854911053398832429938321 5141183290049124322453741)
                    ·
                      refine ⟨1927943733768421620920153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5141183290049124322453741 1927943733768421620920153)
                      ·
                        rfl

theorem cell23_3754657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 3, 1, 2, 3].length) (baseStart_3754657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3754657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3754657 prefixEnd_3754657 := by exact prefixLift 3754657
  have htrace : WordTrace (prefixWord ++ tailWord_3754657) baseStart_3754657 baseEnd_3754657 := by
    simpa [prefixWord, tailWord_3754657, baseEnd_3754657] using wordTrace_append hprefix tailTrace_3754657
  have hstable : (prefixWord ++ tailWord_3754657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3754657).length < 2 ^ (prefixWord ++ tailWord_3754657).sum := by decide
  have hdescent : baseEnd_3754657 < baseStart_3754657 := by decide
  rcases family_descends (prefixWord ++ tailWord_3754657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3754713 : List Nat := [1, 2, 1, 2, 3, 2, 3, 1, 2, 1, 5]
def baseStart_3754713 : Nat := 118140960795 + 3754713 * 2 ^ 59
def prefixEnd_3754713 : Nat := 4983230072969 + 3 ^ 40 * 3754713 * 2
def baseEnd_3754713 : Nat := 1927972488685073401819895

theorem tailTrace_3754713 : CollatzResearch.WordTrace tailWord_3754713 prefixEnd_3754713 1927972488685073401819895 := by
  unfold tailWord_3754713
  simp only [CollatzResearch.WordTrace]
  refine ⟨136945633646323529772676793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91297089097549019848451195 136945633646323529772676793)
  ·
    refine ⟨102709225234742647329507595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136945633646323529772676793 102709225234742647329507595)
    ·
      refine ⟨154063837852113970994261393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102709225234742647329507595 154063837852113970994261393)
      ·
        refine ⟨115547878389085478245696045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154063837852113970994261393 115547878389085478245696045)
        ·
          refine ⟨43330454395907054342136017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115547878389085478245696045 43330454395907054342136017)
          ·
            refine ⟨32497840796930290756602013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43330454395907054342136017 32497840796930290756602013)
            ·
              refine ⟨12186690298848859033725755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32497840796930290756602013 12186690298848859033725755)
              ·
                refine ⟨18280035448273288550588633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12186690298848859033725755 18280035448273288550588633)
                ·
                  refine ⟨13710026586204966412941475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18280035448273288550588633 13710026586204966412941475)
                  ·
                    refine ⟨20565039879307449619412213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13710026586204966412941475 20565039879307449619412213)
                    ·
                      refine ⟨1927972488685073401819895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20565039879307449619412213 1927972488685073401819895)
                      ·
                        rfl

theorem cell23_3754713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 1, 2, 1, 5].length) (baseStart_3754713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3754713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3754713 prefixEnd_3754713 := by exact prefixLift 3754713
  have htrace : WordTrace (prefixWord ++ tailWord_3754713) baseStart_3754713 baseEnd_3754713 := by
    simpa [prefixWord, tailWord_3754713, baseEnd_3754713] using wordTrace_append hprefix tailTrace_3754713
  have hstable : (prefixWord ++ tailWord_3754713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3754713).length < 2 ^ (prefixWord ++ tailWord_3754713).sum := by decide
  have hdescent : baseEnd_3754713 < baseStart_3754713 := by decide
  rcases family_descends (prefixWord ++ tailWord_3754713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3754743 : List Nat := [1, 1, 3, 1, 1, 1, 3, 3, 1, 5, 3]
def baseStart_3754743 : Nat := 118140960795 + 3754743 * 2 ^ 59
def prefixEnd_3754743 : Nat := 4983230072969 + 3 ^ 40 * 3754743 * 2
def baseEnd_3754743 : Nat := 1927987893104708284444757

theorem tailTrace_3754743 : CollatzResearch.WordTrace tailWord_3754743 prefixEnd_3754743 1927987893104708284444757 := by
  unfold tailWord_3754743
  simp only [CollatzResearch.WordTrace]
  refine ⟨136946727836214844896268883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91297818557476563264179255 136946727836214844896268883)
  ·
    refine ⟨205420091754322267344403325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136946727836214844896268883 205420091754322267344403325)
    ·
      refine ⟨77032534407870850254151247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205420091754322267344403325 77032534407870850254151247)
      ·
        refine ⟨115548801611806275381226871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77032534407870850254151247 115548801611806275381226871)
        ·
          refine ⟨173323202417709413071840307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115548801611806275381226871 173323202417709413071840307)
          ·
            refine ⟨259984803626564119607760461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173323202417709413071840307 259984803626564119607760461)
            ·
              refine ⟨97494301359961544852910173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 259984803626564119607760461 97494301359961544852910173)
              ·
                refine ⟨36560363009985579319841315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97494301359961544852910173 36560363009985579319841315)
                ·
                  refine ⟨54840544514978368979761973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36560363009985579319841315 54840544514978368979761973)
                  ·
                    refine ⟨5141301048279222091852685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54840544514978368979761973 5141301048279222091852685)
                    ·
                      refine ⟨1927987893104708284444757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5141301048279222091852685 1927987893104708284444757)
                      ·
                        rfl

theorem cell23_3754743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 3, 1, 5, 3].length) (baseStart_3754743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3754743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3754743 prefixEnd_3754743 := by exact prefixLift 3754743
  have htrace : WordTrace (prefixWord ++ tailWord_3754743) baseStart_3754743 baseEnd_3754743 := by
    simpa [prefixWord, tailWord_3754743, baseEnd_3754743] using wordTrace_append hprefix tailTrace_3754743
  have hstable : (prefixWord ++ tailWord_3754743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3754743).length < 2 ^ (prefixWord ++ tailWord_3754743).sum := by decide
  have hdescent : baseEnd_3754743 < baseStart_3754743 := by decide
  rcases family_descends (prefixWord ++ tailWord_3754743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3754773 : List Nat := [1, 3, 2, 1, 2, 2, 1, 1, 3, 2, 5]
def baseStart_3754773 : Nat := 118140960795 + 3754773 * 2 ^ 59
def prefixEnd_3754773 : Nat := 4983230072969 + 3 ^ 40 * 3754773 * 2
def baseEnd_3754773 : Nat := 1928003297524343167069619

theorem tailTrace_3754773 : CollatzResearch.WordTrace tailWord_3754773 prefixEnd_3754773 1928003297524343167069619 := by
  unfold tailWord_3754773
  simp only [CollatzResearch.WordTrace]
  refine ⟨136947822026106160019860973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91298548017404106679907315 136947822026106160019860973)
  ·
    refine ⟨51355433259789810007447865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136947822026106160019860973 51355433259789810007447865)
    ·
      refine ⟨38516574944842357505585899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51355433259789810007447865 38516574944842357505585899)
      ·
        refine ⟨57774862417263536258378849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38516574944842357505585899 57774862417263536258378849)
        ·
          refine ⟨43331146812947652193784137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57774862417263536258378849 43331146812947652193784137)
          ·
            refine ⟨32498360109710739145338103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43331146812947652193784137 32498360109710739145338103)
            ·
              refine ⟨48747540164566108718007155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32498360109710739145338103 48747540164566108718007155)
              ·
                refine ⟨73121310246849163077010733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48747540164566108718007155 73121310246849163077010733)
                ·
                  refine ⟨27420491342568436153879025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73121310246849163077010733 27420491342568436153879025)
                  ·
                    refine ⟨20565368506926327115409269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27420491342568436153879025 20565368506926327115409269)
                    ·
                      refine ⟨1928003297524343167069619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20565368506926327115409269 1928003297524343167069619)
                      ·
                        rfl

theorem cell23_3754773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 3, 2, 5].length) (baseStart_3754773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3754773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3754773 prefixEnd_3754773 := by exact prefixLift 3754773
  have htrace : WordTrace (prefixWord ++ tailWord_3754773) baseStart_3754773 baseEnd_3754773 := by
    simpa [prefixWord, tailWord_3754773, baseEnd_3754773] using wordTrace_append hprefix tailTrace_3754773
  have hstable : (prefixWord ++ tailWord_3754773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3754773).length < 2 ^ (prefixWord ++ tailWord_3754773).sum := by decide
  have hdescent : baseEnd_3754773 < baseStart_3754773 := by decide
  rcases family_descends (prefixWord ++ tailWord_3754773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3754780 : List Nat := [2, 2, 3, 1, 1, 3, 2, 2, 2, 5]
def baseStart_3754780 : Nat := 118140960795 + 3754780 * 2 ^ 59
def prefixEnd_3754780 : Nat := 4983230072969 + 3 ^ 40 * 3754780 * 2
def baseEnd_3754780 : Nat := 642668963962974879894029

theorem tailTrace_3754780 : CollatzResearch.WordTrace tailWord_3754780 prefixEnd_3754780 642668963962974879894029 := by
  unfold tailWord_3754780
  simp only [CollatzResearch.WordTrace]
  refine ⟨68474038668540400107682897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91298718224720533476910529 68474038668540400107682897)
  ·
    refine ⟨51355529001405300080762173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68474038668540400107682897 51355529001405300080762173)
    ·
      refine ⟨19258323375526987530285815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51355529001405300080762173 19258323375526987530285815)
      ·
        refine ⟨28887485063290481295428723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19258323375526987530285815 28887485063290481295428723)
        ·
          refine ⟨43331227594935721943143085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28887485063290481295428723 43331227594935721943143085)
          ·
            refine ⟨16249210348100895728678657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43331227594935721943143085 16249210348100895728678657)
            ·
              refine ⟨12186907761075671796508993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16249210348100895728678657 12186907761075671796508993)
              ·
                refine ⟨9140180820806753847381745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12186907761075671796508993 9140180820806753847381745)
                ·
                  refine ⟨6855135615605065385536309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9140180820806753847381745 6855135615605065385536309)
                  ·
                    refine ⟨642668963962974879894029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6855135615605065385536309 642668963962974879894029)
                    ·
                      rfl

theorem cell23_3754780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 2, 2, 5].length) (baseStart_3754780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3754780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3754780 prefixEnd_3754780 := by exact prefixLift 3754780
  have htrace : WordTrace (prefixWord ++ tailWord_3754780) baseStart_3754780 baseEnd_3754780 := by
    simpa [prefixWord, tailWord_3754780, baseEnd_3754780] using wordTrace_append hprefix tailTrace_3754780
  have hstable : (prefixWord ++ tailWord_3754780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3754780).length < 2 ^ (prefixWord ++ tailWord_3754780).sum := by decide
  have hdescent : baseEnd_3754780 < baseStart_3754780 := by decide
  rcases family_descends (prefixWord ++ tailWord_3754780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3754784 : List Nat := [2, 1, 1, 5, 1, 4, 2, 2, 5]
def baseStart_3754784 : Nat := 118140960795 + 3754784 * 2 ^ 59
def prefixEnd_3754784 : Nat := 4983230072969 + 3 ^ 40 * 3754784 * 2
def baseEnd_3754784 : Nat := 214223216201282513781341

theorem tailTrace_3754784 : CollatzResearch.WordTrace tailWord_3754784 prefixEnd_3754784 214223216201282513781341 := by
  unfold tailWord_3754784
  simp only [CollatzResearch.WordTrace]
  refine ⟨68474111614533154449255703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91298815486044205932340937 68474111614533154449255703)
  ·
    refine ⟨102711167421799731673883555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68474111614533154449255703 102711167421799731673883555)
    ·
      refine ⟨154066751132699597510825333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102711167421799731673883555 154066751132699597510825333)
      ·
        refine ⟨14443757918690587266639875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 154066751132699597510825333 14443757918690587266639875)
        ·
          refine ⟨21665636878035880899959813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14443757918690587266639875 21665636878035880899959813)
          ·
            refine ⟨4062306914631727668742465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21665636878035880899959813 4062306914631727668742465)
            ·
              refine ⟨3046730185973795751556849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4062306914631727668742465 3046730185973795751556849)
              ·
                refine ⟨2285047639480346813667637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3046730185973795751556849 2285047639480346813667637)
                ·
                  refine ⟨214223216201282513781341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2285047639480346813667637 214223216201282513781341)
                  ·
                    rfl

theorem cell23_3754784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 2, 2, 5].length) (baseStart_3754784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3754784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3754784 prefixEnd_3754784 := by exact prefixLift 3754784
  have htrace : WordTrace (prefixWord ++ tailWord_3754784) baseStart_3754784 baseEnd_3754784 := by
    simpa [prefixWord, tailWord_3754784, baseEnd_3754784] using wordTrace_append hprefix tailTrace_3754784
  have hstable : (prefixWord ++ tailWord_3754784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3754784).length < 2 ^ (prefixWord ++ tailWord_3754784).sum := by decide
  have hdescent : baseEnd_3754784 < baseStart_3754784 := by decide
  rcases family_descends (prefixWord ++ tailWord_3754784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3754794 : List Nat := [3, 1, 4, 3, 1, 1, 1, 1, 2, 3, 3]
def baseStart_3754794 : Nat := 118140960795 + 3754794 * 2 ^ 59
def prefixEnd_3754794 : Nat := 4983230072969 + 3 ^ 40 * 3754794 * 2
def baseEnd_3754794 : Nat := 1928014080618087584907023

theorem tailTrace_3754794 : CollatzResearch.WordTrace tailWord_3754794 prefixEnd_3754794 1928014080618087584907023 := by
  unfold tailWord_3754794
  simp only [CollatzResearch.WordTrace]
  refine ⟨34237146989757520151593859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91299058639353387070916957 34237146989757520151593859)
  ·
    refine ⟨51355720484636280227390789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34237146989757520151593859 51355720484636280227390789)
    ·
      refine ⟨9629197590869302542635773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51355720484636280227390789 9629197590869302542635773)
      ·
        refine ⟨3610949096575988453488415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9629197590869302542635773 3610949096575988453488415)
        ·
          refine ⟨5416423644863982680232623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3610949096575988453488415 5416423644863982680232623)
          ·
            refine ⟨8124635467295974020348935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5416423644863982680232623 8124635467295974020348935)
            ·
              refine ⟨12186953200943961030523403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8124635467295974020348935 12186953200943961030523403)
              ·
                refine ⟨18280429801415941545785105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12186953200943961030523403 18280429801415941545785105)
                ·
                  refine ⟨13710322351061956159338829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18280429801415941545785105 13710322351061956159338829)
                  ·
                    refine ⟨5141370881648233559752061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13710322351061956159338829 5141370881648233559752061)
                    ·
                      refine ⟨1928014080618087584907023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5141370881648233559752061 1928014080618087584907023)
                      ·
                        rfl

theorem cell23_3754794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_3754794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3754794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3754794 prefixEnd_3754794 := by exact prefixLift 3754794
  have htrace : WordTrace (prefixWord ++ tailWord_3754794) baseStart_3754794 baseEnd_3754794 := by
    simpa [prefixWord, tailWord_3754794, baseEnd_3754794] using wordTrace_append hprefix tailTrace_3754794
  have hstable : (prefixWord ++ tailWord_3754794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3754794).length < 2 ^ (prefixWord ++ tailWord_3754794).sum := by decide
  have hdescent : baseEnd_3754794 < baseStart_3754794 := by decide
  rcases family_descends (prefixWord ++ tailWord_3754794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3754814 : List Nat := [4, 2, 1, 2, 3, 2, 1, 1, 2, 5]
def baseStart_3754814 : Nat := 118140960795 + 3754814 * 2 ^ 59
def prefixEnd_3754814 : Nat := 4983230072969 + 3 ^ 40 * 3754814 * 2
def baseEnd_3754814 : Nat := 642674783410392502218977

theorem tailTrace_3754814 : CollatzResearch.WordTrace tailWord_3754814 prefixEnd_3754814 642674783410392502218977 := by
  unfold tailWord_3754814
  simp only [CollatzResearch.WordTrace]
  refine ⟨17118664677369703002762937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91299544945971749348068997 17118664677369703002762937)
  ·
    refine ⟨12838998508027277252072203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17118664677369703002762937 12838998508027277252072203)
    ·
      refine ⟨19258497762040915878108305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12838998508027277252072203 19258497762040915878108305)
      ·
        refine ⟨14443873321530686908581229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19258497762040915878108305 14443873321530686908581229)
        ·
          refine ⟨5416452495574007590717961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14443873321530686908581229 5416452495574007590717961)
          ·
            refine ⟨4062339371680505693038471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5416452495574007590717961 4062339371680505693038471)
            ·
              refine ⟨6093509057520758539557707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4062339371680505693038471 6093509057520758539557707)
              ·
                refine ⟨9140263586281137809336561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6093509057520758539557707 9140263586281137809336561)
                ·
                  refine ⟨6855197689710853357002421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9140263586281137809336561 6855197689710853357002421)
                  ·
                    refine ⟨642674783410392502218977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6855197689710853357002421 642674783410392502218977)
                    ·
                      rfl

theorem cell23_3754814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 1, 1, 2, 5].length) (baseStart_3754814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3754814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3754814 prefixEnd_3754814 := by exact prefixLift 3754814
  have htrace : WordTrace (prefixWord ++ tailWord_3754814) baseStart_3754814 baseEnd_3754814 := by
    simpa [prefixWord, tailWord_3754814, baseEnd_3754814] using wordTrace_append hprefix tailTrace_3754814
  have hstable : (prefixWord ++ tailWord_3754814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3754814).length < 2 ^ (prefixWord ++ tailWord_3754814).sum := by decide
  have hdescent : baseEnd_3754814 < baseStart_3754814 := by decide
  rcases family_descends (prefixWord ++ tailWord_3754814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3754823 : List Nat := [1, 1, 4, 1, 2, 1, 1, 4, 8]
def baseStart_3754823 : Nat := 118140960795 + 3754823 * 2 ^ 59
def prefixEnd_3754823 : Nat := 4983230072969 + 3 ^ 40 * 3754823 * 2
def baseEnd_3754823 : Nat := 214225441284118663493821

theorem tailTrace_3754823 : CollatzResearch.WordTrace tailWord_3754823 prefixEnd_3754823 214225441284118663493821 := by
  unfold tailWord_3754823
  simp only [CollatzResearch.WordTrace]
  refine ⟨136949645675925018559181123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91299763783950012372787415 136949645675925018559181123)
  ·
    refine ⟨205424468513887527838771685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136949645675925018559181123 205424468513887527838771685)
    ·
      refine ⟨38517087846353911469769691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 205424468513887527838771685 38517087846353911469769691)
      ·
        refine ⟨57775631769530867204654537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38517087846353911469769691 57775631769530867204654537)
        ·
          refine ⟨43331723827148150403490903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57775631769530867204654537 43331723827148150403490903)
          ·
            refine ⟨64997585740722225605236355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43331723827148150403490903 64997585740722225605236355)
            ·
              refine ⟨97496378611083338407854533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64997585740722225605236355 97496378611083338407854533)
              ·
                refine ⟨18280570989578125951472725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 97496378611083338407854533 18280570989578125951472725)
                ·
                  refine ⟨214225441284118663493821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18280570989578125951472725 214225441284118663493821)
                  ·
                    rfl

theorem cell23_3754823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 4, 8].length) (baseStart_3754823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3754823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3754823 prefixEnd_3754823 := by exact prefixLift 3754823
  have htrace : WordTrace (prefixWord ++ tailWord_3754823) baseStart_3754823 baseEnd_3754823 := by
    simpa [prefixWord, tailWord_3754823, baseEnd_3754823] using wordTrace_append hprefix tailTrace_3754823
  have hstable : (prefixWord ++ tailWord_3754823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3754823).length < 2 ^ (prefixWord ++ tailWord_3754823).sum := by decide
  have hdescent : baseEnd_3754823 < baseStart_3754823 := by decide
  rcases family_descends (prefixWord ++ tailWord_3754823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3754844 : List Nat := [2, 2, 4, 2, 1, 2, 2, 1, 3, 4]
def baseStart_3754844 : Nat := 118140960795 + 3754844 * 2 ^ 59
def prefixEnd_3754844 : Nat := 4983230072969 + 3 ^ 40 * 3754844 * 2
def baseEnd_3754844 : Nat := 642679918216937463093931

theorem tailTrace_3754844 : CollatzResearch.WordTrace tailWord_3754844 prefixEnd_3754844 642679918216937463093931 := by
  unfold tailWord_3754844
  simp only [CollatzResearch.WordTrace]
  refine ⟨68475205804424469572847793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91300274405899292763797057 68475205804424469572847793)
  ·
    refine ⟨51356404353318352179635845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68475205804424469572847793 51356404353318352179635845)
    ·
      refine ⟨9629325816247191033681721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51356404353318352179635845 9629325816247191033681721)
      ·
        refine ⟨7221994362185393275261291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9629325816247191033681721 7221994362185393275261291)
        ·
          refine ⟨10832991543278089912891937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7221994362185393275261291 10832991543278089912891937)
          ·
            refine ⟨8124743657458567434668953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10832991543278089912891937 8124743657458567434668953)
            ·
              refine ⟨6093557743093925576001715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8124743657458567434668953 6093557743093925576001715)
              ·
                refine ⟨9140336614640888364002573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6093557743093925576001715 9140336614640888364002573)
                ·
                  refine ⟨3427626230490333136500965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9140336614640888364002573 3427626230490333136500965)
                  ·
                    refine ⟨642679918216937463093931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3427626230490333136500965 642679918216937463093931)
                    ·
                      rfl

theorem cell23_3754844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 2, 1, 3, 4].length) (baseStart_3754844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3754844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3754844 prefixEnd_3754844 := by exact prefixLift 3754844
  have htrace : WordTrace (prefixWord ++ tailWord_3754844) baseStart_3754844 baseEnd_3754844 := by
    simpa [prefixWord, tailWord_3754844, baseEnd_3754844] using wordTrace_append hprefix tailTrace_3754844
  have hstable : (prefixWord ++ tailWord_3754844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3754844).length < 2 ^ (prefixWord ++ tailWord_3754844).sum := by decide
  have hdescent : baseEnd_3754844 < baseStart_3754844 := by decide
  rcases family_descends (prefixWord ++ tailWord_3754844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3754863 : List Nat := [1, 1, 2, 1, 3, 1, 1, 3, 2, 1, 7]
def baseStart_3754863 : Nat := 118140960795 + 3754863 * 2 ^ 59
def prefixEnd_3754863 : Nat := 4983230072969 + 3 ^ 40 * 3754863 * 2
def baseEnd_3754863 : Nat := 1928049510783247814944205

theorem tailTrace_3754863 : CollatzResearch.WordTrace tailWord_3754863 prefixEnd_3754863 1928049510783247814944205 := by
  unfold tailWord_3754863
  simp only [CollatzResearch.WordTrace]
  refine ⟨136951104595780105390637243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91300736397186736927091495 136951104595780105390637243)
  ·
    refine ⟨205426656893670158085955865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136951104595780105390637243 205426656893670158085955865)
    ·
      refine ⟨154069992670252618564466899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205426656893670158085955865 154069992670252618564466899)
      ·
        refine ⟨231104989005378927846700349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154069992670252618564466899 231104989005378927846700349)
        ·
          refine ⟨86664370877017097942512631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 231104989005378927846700349 86664370877017097942512631)
          ·
            refine ⟨129996556315525646913768947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86664370877017097942512631 129996556315525646913768947)
            ·
              refine ⟨194994834473288470370653421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129996556315525646913768947 194994834473288470370653421)
              ·
                refine ⟨73123062927483176388995033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 194994834473288470370653421 73123062927483176388995033)
                ·
                  refine ⟨54842297195612382291746275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73123062927483176388995033 54842297195612382291746275)
                  ·
                    refine ⟨82263445793418573437619413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54842297195612382291746275 82263445793418573437619413)
                    ·
                      refine ⟨1928049510783247814944205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 82263445793418573437619413 1928049510783247814944205)
                      ·
                        rfl

theorem cell23_3754863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 2, 1, 7].length) (baseStart_3754863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3754863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3754863 prefixEnd_3754863 := by exact prefixLift 3754863
  have htrace : WordTrace (prefixWord ++ tailWord_3754863) baseStart_3754863 baseEnd_3754863 := by
    simpa [prefixWord, tailWord_3754863, baseEnd_3754863] using wordTrace_append hprefix tailTrace_3754863
  have hstable : (prefixWord ++ tailWord_3754863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3754863).length < 2 ^ (prefixWord ++ tailWord_3754863).sum := by decide
  have hdescent : baseEnd_3754863 < baseStart_3754863 := by decide
  rcases family_descends (prefixWord ++ tailWord_3754863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3754867 : List Nat := [1, 1, 1, 2, 2, 1, 6, 2, 3, 1, 3]
def baseStart_3754867 : Nat := 118140960795 + 3754867 * 2 ^ 59
def prefixEnd_3754867 : Nat := 4983230072969 + 3 ^ 40 * 3754867 * 2
def baseEnd_3754867 : Nat := 1928051564705865799294187

theorem tailTrace_3754867 : CollatzResearch.WordTrace tailWord_3754867 prefixEnd_3754867 1928051564705865799294187 := by
  unfold tailWord_3754867
  simp only [CollatzResearch.WordTrace]
  refine ⟨136951250487765614073782855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91300833658510409382521903 136951250487765614073782855)
  ·
    refine ⟨205426875731648421110674283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136951250487765614073782855 205426875731648421110674283)
    ·
      refine ⟨308140313597472631666011425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205426875731648421110674283 308140313597472631666011425)
      ·
        refine ⟨231105235198104473749508569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 308140313597472631666011425 231105235198104473749508569)
        ·
          refine ⟨173328926398578355312131427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231105235198104473749508569 173328926398578355312131427)
          ·
            refine ⟨259993389597867532968197141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173328926398578355312131427 259993389597867532968197141)
            ·
              refine ⟨12187190137400040607884241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 259993389597867532968197141 12187190137400040607884241)
              ·
                refine ⟨9140392603050030455913181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12187190137400040607884241 9140392603050030455913181)
                ·
                  refine ⟨3427647226143761420967443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9140392603050030455913181 3427647226143761420967443)
                  ·
                    refine ⟨5141470839215642131451165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3427647226143761420967443 5141470839215642131451165)
                    ·
                      refine ⟨1928051564705865799294187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5141470839215642131451165 1928051564705865799294187)
                      ·
                        rfl

theorem cell23_3754867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 2, 3, 1, 3].length) (baseStart_3754867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3754867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3754867 prefixEnd_3754867 := by exact prefixLift 3754867
  have htrace : WordTrace (prefixWord ++ tailWord_3754867) baseStart_3754867 baseEnd_3754867 := by
    simpa [prefixWord, tailWord_3754867, baseEnd_3754867] using wordTrace_append hprefix tailTrace_3754867
  have hstable : (prefixWord ++ tailWord_3754867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3754867).length < 2 ^ (prefixWord ++ tailWord_3754867).sum := by decide
  have hdescent : baseEnd_3754867 < baseStart_3754867 := by decide
  rcases family_descends (prefixWord ++ tailWord_3754867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3754877 : List Nat := [1, 4, 1, 1, 2, 1, 4, 1, 1, 5, 2]
def baseStart_3754877 : Nat := 118140960795 + 3754877 * 2 ^ 59
def prefixEnd_3754877 : Nat := 4983230072969 + 3 ^ 40 * 3754877 * 2
def baseEnd_3754877 : Nat := 1928056699512410760169141

theorem tailTrace_3754877 : CollatzResearch.WordTrace tailWord_3754877 prefixEnd_3754877 1928056699512410760169141 := by
  unfold tailWord_3754877
  simp only [CollatzResearch.WordTrace]
  refine ⟨136951615217729385781646885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91301076811819590521097923 136951615217729385781646885)
  ·
    refine ⟨25678427853324259834058791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136951615217729385781646885 25678427853324259834058791)
    ·
      refine ⟨38517641779986389751088187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25678427853324259834058791 38517641779986389751088187)
      ·
        refine ⟨57776462669979584626632281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38517641779986389751088187 57776462669979584626632281)
        ·
          refine ⟨43332347002484688469974211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57776462669979584626632281 43332347002484688469974211)
          ·
            refine ⟨64998520503727032704961317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43332347002484688469974211 64998520503727032704961317)
            ·
              refine ⟨12187222594448818632180247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64998520503727032704961317 12187222594448818632180247)
              ·
                refine ⟨18280833891673227948270371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12187222594448818632180247 18280833891673227948270371)
                ·
                  refine ⟨27421250837509841922405557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18280833891673227948270371 27421250837509841922405557)
                  ·
                    refine ⟨2570742266016547680225521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27421250837509841922405557 2570742266016547680225521)
                    ·
                      refine ⟨1928056699512410760169141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2570742266016547680225521 1928056699512410760169141)
                      ·
                        rfl

theorem cell23_3754877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 1, 1, 5, 2].length) (baseStart_3754877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3754877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3754877 prefixEnd_3754877 := by exact prefixLift 3754877
  have htrace : WordTrace (prefixWord ++ tailWord_3754877) baseStart_3754877 baseEnd_3754877 := by
    simpa [prefixWord, tailWord_3754877, baseEnd_3754877] using wordTrace_append hprefix tailTrace_3754877
  have hstable : (prefixWord ++ tailWord_3754877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3754877).length < 2 ^ (prefixWord ++ tailWord_3754877).sum := by decide
  have hdescent : baseEnd_3754877 < baseStart_3754877 := by decide
  rcases family_descends (prefixWord ++ tailWord_3754877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3754887 : List Nat := [1, 1, 4, 2, 3, 1, 2, 3, 1, 5]
def baseStart_3754887 : Nat := 118140960795 + 3754887 * 2 ^ 59
def prefixEnd_3754887 : Nat := 4983230072969 + 3 ^ 40 * 3754887 * 2
def baseEnd_3754887 : Nat := 642687278106318573681365

theorem tailTrace_3754887 : CollatzResearch.WordTrace tailWord_3754887 prefixEnd_3754887 642687278106318573681365 := by
  unfold tailWord_3754887
  simp only [CollatzResearch.WordTrace]
  refine ⟨136951979947693157489510915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91301319965128771659673943 136951979947693157489510915)
  ·
    refine ⟨205427969921539736234266373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136951979947693157489510915 205427969921539736234266373)
    ·
      refine ⟨38517744360288700543924945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 205427969921539736234266373 38517744360288700543924945)
      ·
        refine ⟨28888308270216525407943709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38517744360288700543924945 28888308270216525407943709)
        ·
          refine ⟨10833115601331197027978891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28888308270216525407943709 10833115601331197027978891)
          ·
            refine ⟨16249673401996795541968337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10833115601331197027978891 16249673401996795541968337)
            ·
              refine ⟨12187255051497596656476253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16249673401996795541968337 12187255051497596656476253)
              ·
                refine ⟨4570220644311598746178595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12187255051497596656476253 4570220644311598746178595)
                ·
                  refine ⟨6855330966467398119267893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4570220644311598746178595 6855330966467398119267893)
                  ·
                    refine ⟨642687278106318573681365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6855330966467398119267893 642687278106318573681365)
                    ·
                      rfl

theorem cell23_3754887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 3, 1, 5].length) (baseStart_3754887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3754887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3754887 prefixEnd_3754887 := by exact prefixLift 3754887
  have htrace : WordTrace (prefixWord ++ tailWord_3754887) baseStart_3754887 baseEnd_3754887 := by
    simpa [prefixWord, tailWord_3754887, baseEnd_3754887] using wordTrace_append hprefix tailTrace_3754887
  have hstable : (prefixWord ++ tailWord_3754887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3754887).length < 2 ^ (prefixWord ++ tailWord_3754887).sum := by decide
  have hdescent : baseEnd_3754887 < baseStart_3754887 := by decide
  rcases family_descends (prefixWord ++ tailWord_3754887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3754927 : List Nat := [1, 1, 2, 1, 2, 2, 2, 6, 1, 2, 3]
def baseStart_3754927 : Nat := 118140960795 + 3754927 * 2 ^ 59
def prefixEnd_3754927 : Nat := 4983230072969 + 3 ^ 40 * 3754927 * 2
def baseEnd_3754927 : Nat := 1928082373545135564543911

theorem tailTrace_3754927 : CollatzResearch.WordTrace tailWord_3754927 prefixEnd_3754927 1928082373545135564543911 := by
  unfold tailWord_3754927
  simp only [CollatzResearch.WordTrace]
  refine ⟨136953438867548244320967035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91302292578365496213978023 136953438867548244320967035)
  ·
    refine ⟨205430158301322366481450553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136953438867548244320967035 205430158301322366481450553)
    ·
      refine ⟨154072618725991774861087915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205430158301322366481450553 154072618725991774861087915)
      ·
        refine ⟨231108928088987662291631873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154072618725991774861087915 231108928088987662291631873)
        ·
          refine ⟨173331696066740746718723905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231108928088987662291631873 173331696066740746718723905)
          ·
            refine ⟨129998772050055560039042929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173331696066740746718723905 129998772050055560039042929)
            ·
              refine ⟨97499079037541670029282197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129998772050055560039042929 97499079037541670029282197)
              ·
                refine ⟨4570269329884765782622603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 97499079037541670029282197 4570269329884765782622603)
                ·
                  refine ⟨6855403994827148673933905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4570269329884765782622603 6855403994827148673933905)
                  ·
                    refine ⟨5141552996120361505450429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6855403994827148673933905 5141552996120361505450429)
                    ·
                      refine ⟨1928082373545135564543911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5141552996120361505450429 1928082373545135564543911)
                      ·
                        rfl

theorem cell23_3754927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 6, 1, 2, 3].length) (baseStart_3754927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3754927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3754927 prefixEnd_3754927 := by exact prefixLift 3754927
  have htrace : WordTrace (prefixWord ++ tailWord_3754927) baseStart_3754927 baseEnd_3754927 := by
    simpa [prefixWord, tailWord_3754927, baseEnd_3754927] using wordTrace_append hprefix tailTrace_3754927
  have hstable : (prefixWord ++ tailWord_3754927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3754927).length < 2 ^ (prefixWord ++ tailWord_3754927).sum := by decide
  have hdescent : baseEnd_3754927 < baseStart_3754927 := by decide
  rcases family_descends (prefixWord ++ tailWord_3754927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3754937 : List Nat := [1, 2, 1, 4, 2, 3, 1, 2, 1, 2, 4]
def baseStart_3754937 : Nat := 118140960795 + 3754937 * 2 ^ 59
def prefixEnd_3754937 : Nat := 4983230072969 + 3 ^ 40 * 3754937 * 2
def baseEnd_3754937 : Nat := 1928087508351680525418865

theorem tailTrace_3754937 : CollatzResearch.WordTrace tailWord_3754937 prefixEnd_3754937 1928087508351680525418865 := by
  unfold tailWord_3754937
  simp only [CollatzResearch.WordTrace]
  refine ⟨136953803597512016028831065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91302535731674677352554043 136953803597512016028831065)
  ·
    refine ⟨102715352698134012021623299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136953803597512016028831065 102715352698134012021623299)
    ·
      refine ⟨154073029047201018032434949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102715352698134012021623299 154073029047201018032434949)
      ·
        refine ⟨28888692946350190881081553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 154073029047201018032434949 28888692946350190881081553)
        ·
          refine ⟨21666519709762643160811165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28888692946350190881081553 21666519709762643160811165)
          ·
            refine ⟨8124944891160991185304187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21666519709762643160811165 8124944891160991185304187)
            ·
              refine ⟨12187417336741486777956281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8124944891160991185304187 12187417336741486777956281)
              ·
                refine ⟨9140563002556115083467211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12187417336741486777956281 9140563002556115083467211)
                ·
                  refine ⟨13710844503834172625200817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9140563002556115083467211 13710844503834172625200817)
                  ·
                    refine ⟨10283133377875629468900613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13710844503834172625200817 10283133377875629468900613)
                    ·
                      refine ⟨1928087508351680525418865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10283133377875629468900613 1928087508351680525418865)
                      ·
                        rfl

theorem cell23_3754937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 2, 1, 2, 4].length) (baseStart_3754937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3754937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3754937 prefixEnd_3754937 := by exact prefixLift 3754937
  have htrace : WordTrace (prefixWord ++ tailWord_3754937) baseStart_3754937 baseEnd_3754937 := by
    simpa [prefixWord, tailWord_3754937, baseEnd_3754937] using wordTrace_append hprefix tailTrace_3754937
  have hstable : (prefixWord ++ tailWord_3754937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3754937).length < 2 ^ (prefixWord ++ tailWord_3754937).sum := by decide
  have hdescent : baseEnd_3754937 < baseStart_3754937 := by decide
  rcases family_descends (prefixWord ++ tailWord_3754937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3754941 : List Nat := [1, 4, 1, 2, 4, 1, 3, 1, 1, 1, 4]
def baseStart_3754941 : Nat := 118140960795 + 3754941 * 2 ^ 59
def prefixEnd_3754941 : Nat := 4983230072969 + 3 ^ 40 * 3754941 * 2
def baseEnd_3754941 : Nat := 1928089562274298509768847

theorem tailTrace_3754941 : CollatzResearch.WordTrace tailWord_3754941 prefixEnd_3754941 1928089562274298509768847 := by
  unfold tailWord_3754941
  simp only [CollatzResearch.WordTrace]
  refine ⟨136953949489497524711976677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91302632992998349807984451 136953949489497524711976677)
  ·
    refine ⟨25678865529280785883495627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136953949489497524711976677 25678865529280785883495627)
    ·
      refine ⟨38518298293921178825243441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25678865529280785883495627 38518298293921178825243441)
      ·
        refine ⟨28888723720440884118932581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38518298293921178825243441 28888723720440884118932581)
        ·
          refine ⟨5416635697582665772299859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28888723720440884118932581 5416635697582665772299859)
          ·
            refine ⟨8124953546373998658449789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5416635697582665772299859 8124953546373998658449789)
            ·
              refine ⟨3046857579890249496918671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8124953546373998658449789 3046857579890249496918671)
              ·
                refine ⟨4570286369835374245378007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3046857579890249496918671 4570286369835374245378007)
                ·
                  refine ⟨6855429554753061368067011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4570286369835374245378007 6855429554753061368067011)
                  ·
                    refine ⟨10283144332129592052100517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6855429554753061368067011 10283144332129592052100517)
                    ·
                      refine ⟨1928089562274298509768847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10283144332129592052100517 1928089562274298509768847)
                      ·
                        rfl

theorem cell23_3754941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 3, 1, 1, 1, 4].length) (baseStart_3754941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3754941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3754941 prefixEnd_3754941 := by exact prefixLift 3754941
  have htrace : WordTrace (prefixWord ++ tailWord_3754941) baseStart_3754941 baseEnd_3754941 := by
    simpa [prefixWord, tailWord_3754941, baseEnd_3754941] using wordTrace_append hprefix tailTrace_3754941
  have hstable : (prefixWord ++ tailWord_3754941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3754941).length < 2 ^ (prefixWord ++ tailWord_3754941).sum := by decide
  have hdescent : baseEnd_3754941 < baseStart_3754941 := by decide
  rcases family_descends (prefixWord ++ tailWord_3754941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3754958 : List Nat := [4, 1, 1, 1, 2, 4, 1, 4, 1, 2, 2]
def baseStart_3754958 : Nat := 118140960795 + 3754958 * 2 ^ 59
def prefixEnd_3754958 : Nat := 4983230072969 + 3 ^ 40 * 3754958 * 2
def baseEnd_3754958 : Nat := 1928098291445424943256269

theorem tailTrace_3754958 : CollatzResearch.WordTrace tailWord_3754958 prefixEnd_3754958 1928098291445424943256269 := by
  unfold tailWord_3754958
  simp only [CollatzResearch.WordTrace]
  refine ⟨17119321191304492076918191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91303046353623957743563685 17119321191304492076918191)
  ·
    refine ⟨25678981786956738115377287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17119321191304492076918191 25678981786956738115377287)
    ·
      refine ⟨38518472680435107173065931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25678981786956738115377287 38518472680435107173065931)
      ·
        refine ⟨57777709020652660759598897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38518472680435107173065931 57777709020652660759598897)
        ·
          refine ⟨43333281765489495569699173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57777709020652660759598897 43333281765489495569699173)
          ·
            refine ⟨8124990331029280419318595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43333281765489495569699173 8124990331029280419318595)
            ·
              refine ⟨12187485496543920628977893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8124990331029280419318595 12187485496543920628977893)
              ·
                refine ⟨2285153530601985117933355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12187485496543920628977893 2285153530601985117933355)
                ·
                  refine ⟨3427730295902977676900033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2285153530601985117933355 3427730295902977676900033)
                  ·
                    refine ⟨2570797721927233257675025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3427730295902977676900033 2570797721927233257675025)
                    ·
                      refine ⟨1928098291445424943256269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2570797721927233257675025 1928098291445424943256269)
                      ·
                        rfl

theorem cell23_3754958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 4, 1, 2, 2].length) (baseStart_3754958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3754958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3754958 prefixEnd_3754958 := by exact prefixLift 3754958
  have htrace : WordTrace (prefixWord ++ tailWord_3754958) baseStart_3754958 baseEnd_3754958 := by
    simpa [prefixWord, tailWord_3754958, baseEnd_3754958] using wordTrace_append hprefix tailTrace_3754958
  have hstable : (prefixWord ++ tailWord_3754958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3754958).length < 2 ^ (prefixWord ++ tailWord_3754958).sum := by decide
  have hdescent : baseEnd_3754958 < baseStart_3754958 := by decide
  rcases family_descends (prefixWord ++ tailWord_3754958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3754984 : List Nat := [2, 1, 4, 1, 1, 1, 4, 1, 3, 3, 2]
def baseStart_3754984 : Nat := 118140960795 + 3754984 * 2 ^ 59
def prefixEnd_3754984 : Nat := 4983230072969 + 3 ^ 40 * 3754984 * 2
def baseEnd_3754984 : Nat := 1928111641942441841531149

theorem tailTrace_3754984 : CollatzResearch.WordTrace tailWord_3754984 prefixEnd_3754984 1928111641942441841531149 := by
  unfold tailWord_3754984
  simp only [CollatzResearch.WordTrace]
  refine ⟨68477758914170871527896003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91303678552227828703861337 68477758914170871527896003)
  ·
    refine ⟨102716638371256307291844005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68477758914170871527896003 102716638371256307291844005)
    ·
      refine ⟨19259369694610557617220751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102716638371256307291844005 19259369694610557617220751)
      ·
        refine ⟨28889054541915836425831127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19259369694610557617220751 28889054541915836425831127)
        ·
          refine ⟨43333581812873754638746691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28889054541915836425831127 43333581812873754638746691)
          ·
            refine ⟨65000372719310631958120037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43333581812873754638746691 65000372719310631958120037)
            ·
              refine ⟨12187569884870743492147507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65000372719310631958120037 12187569884870743492147507)
              ·
                refine ⟨18281354827306115238221261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12187569884870743492147507 18281354827306115238221261)
                ·
                  refine ⟨6855508060239793214332973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18281354827306115238221261 6855508060239793214332973)
                  ·
                    refine ⟨2570815522589922455374865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6855508060239793214332973 2570815522589922455374865)
                    ·
                      refine ⟨1928111641942441841531149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2570815522589922455374865 1928111641942441841531149)
                      ·
                        rfl

theorem cell23_3754984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 1, 3, 3, 2].length) (baseStart_3754984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3754984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3754984 prefixEnd_3754984 := by exact prefixLift 3754984
  have htrace : WordTrace (prefixWord ++ tailWord_3754984) baseStart_3754984 baseEnd_3754984 := by
    simpa [prefixWord, tailWord_3754984, baseEnd_3754984] using wordTrace_append hprefix tailTrace_3754984
  have hstable : (prefixWord ++ tailWord_3754984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3754984).length < 2 ^ (prefixWord ++ tailWord_3754984).sum := by decide
  have hdescent : baseEnd_3754984 < baseStart_3754984 := by decide
  rcases family_descends (prefixWord ++ tailWord_3754984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3755000 : List Nat := [2, 1, 2, 1, 1, 3, 1, 3, 1, 3, 5]
def baseStart_3755000 : Nat := 118140960795 + 3755000 * 2 ^ 59
def prefixEnd_3755000 : Nat := 4983230072969 + 3 ^ 40 * 3755000 * 2
def baseEnd_3755000 : Nat := 1928119857632913778931075

theorem tailTrace_3755000 : CollatzResearch.WordTrace tailWord_3755000 prefixEnd_3755000 1928119857632913778931075 := by
  unfold tailWord_3755000
  simp only [CollatzResearch.WordTrace]
  refine ⟨68478050698141888894187227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91304067597522518525582969 68478050698141888894187227)
  ·
    refine ⟨102717076047212833341280841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68478050698141888894187227 102717076047212833341280841)
    ·
      refine ⟨77037807035409625005960631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102717076047212833341280841 77037807035409625005960631)
      ·
        refine ⟨115556710553114437508940947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77037807035409625005960631 115556710553114437508940947)
        ·
          refine ⟨173335065829671656263411421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115556710553114437508940947 173335065829671656263411421)
          ·
            refine ⟨65000649686126871098779283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 173335065829671656263411421 65000649686126871098779283)
            ·
              refine ⟨97500974529190306648168925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65000649686126871098779283 97500974529190306648168925)
              ·
                refine ⟨36562865448446364993063347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97500974529190306648168925 36562865448446364993063347)
                ·
                  refine ⟨54844298172669547489595021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36562865448446364993063347 54844298172669547489595021)
                  ·
                    refine ⟨20566611814751080308598133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54844298172669547489595021 20566611814751080308598133)
                    ·
                      refine ⟨1928119857632913778931075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20566611814751080308598133 1928119857632913778931075)
                      ·
                        rfl

theorem cell23_3755000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 3, 1, 3, 5].length) (baseStart_3755000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3755000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3755000 prefixEnd_3755000 := by exact prefixLift 3755000
  have htrace : WordTrace (prefixWord ++ tailWord_3755000) baseStart_3755000 baseEnd_3755000 := by
    simpa [prefixWord, tailWord_3755000, baseEnd_3755000] using wordTrace_append hprefix tailTrace_3755000
  have hstable : (prefixWord ++ tailWord_3755000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3755000).length < 2 ^ (prefixWord ++ tailWord_3755000).sum := by decide
  have hdescent : baseEnd_3755000 < baseStart_3755000 := by decide
  rcases family_descends (prefixWord ++ tailWord_3755000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3755031 : List Nat := [1, 1, 3, 5, 1, 1, 3, 1, 1, 4, 2]
def baseStart_3755031 : Nat := 118140960795 + 3755031 * 2 ^ 59
def prefixEnd_3755031 : Nat := 4983230072969 + 3 ^ 40 * 3755031 * 2
def baseEnd_3755031 : Nat := 1928135775533203157643433

theorem tailTrace_3755031 : CollatzResearch.WordTrace tailWord_3755031 prefixEnd_3755031 1928135775533203157643433 := by
  unfold tailWord_3755031
  simp only [CollatzResearch.WordTrace]
  refine ⟨136957232059171470082752947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91304821372780980055168631 136957232059171470082752947)
  ·
    refine ⟨205435848088757205124129421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136957232059171470082752947 205435848088757205124129421)
    ·
      refine ⟨77038443033283951921548533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205435848088757205124129421 77038443033283951921548533)
      ·
        refine ⟨7222354034370370492645175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 77038443033283951921548533 7222354034370370492645175)
        ·
          refine ⟨10833531051555555738967763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7222354034370370492645175 10833531051555555738967763)
          ·
            refine ⟨16250296577333333608451645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10833531051555555738967763 16250296577333333608451645)
            ·
              refine ⟨6093861216500000103169367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16250296577333333608451645 6093861216500000103169367)
              ·
                refine ⟨9140791824750000154754051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6093861216500000103169367 9140791824750000154754051)
                ·
                  refine ⟨13711187737125000232131077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9140791824750000154754051 13711187737125000232131077)
                  ·
                    refine ⟨2570847700710937543524577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13711187737125000232131077 2570847700710937543524577)
                    ·
                      refine ⟨1928135775533203157643433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2570847700710937543524577 1928135775533203157643433)
                      ·
                        rfl

theorem cell23_3755031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 3, 1, 1, 4, 2].length) (baseStart_3755031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3755031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3755031 prefixEnd_3755031 := by exact prefixLift 3755031
  have htrace : WordTrace (prefixWord ++ tailWord_3755031) baseStart_3755031 baseEnd_3755031 := by
    simpa [prefixWord, tailWord_3755031, baseEnd_3755031] using wordTrace_append hprefix tailTrace_3755031
  have hstable : (prefixWord ++ tailWord_3755031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3755031).length < 2 ^ (prefixWord ++ tailWord_3755031).sum := by decide
  have hdescent : baseEnd_3755031 < baseStart_3755031 := by decide
  rcases family_descends (prefixWord ++ tailWord_3755031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3755104 : List Nat := [2, 1, 1, 3, 2, 2, 4, 1, 2, 1, 4]
def baseStart_3755104 : Nat := 118140960795 + 3755104 * 2 ^ 59
def prefixEnd_3755104 : Nat := 4983230072969 + 3 ^ 40 * 3755104 * 2
def baseEnd_3755104 : Nat := 1928173259620981372030597

theorem tailTrace_3755104 : CollatzResearch.WordTrace tailWord_3755104 prefixEnd_3755104 1928173259620981372030597 := by
  unfold tailWord_3755104
  simp only [CollatzResearch.WordTrace]
  refine ⟨68479947293953501775080183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91306596391938002366773577 68479947293953501775080183)
  ·
    refine ⟨102719920940930252662620275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68479947293953501775080183 102719920940930252662620275)
    ·
      refine ⟨154079881411395378993930413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102719920940930252662620275 154079881411395378993930413)
      ·
        refine ⟨57779955529273267122723905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154079881411395378993930413 57779955529273267122723905)
        ·
          refine ⟨43334966646954950342042929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57779955529273267122723905 43334966646954950342042929)
          ·
            refine ⟨32501224985216212756532197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43334966646954950342042929 32501224985216212756532197)
            ·
              refine ⟨6093979684728039891849787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32501224985216212756532197 6093979684728039891849787)
              ·
                refine ⟨9140969527092059837774681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6093979684728039891849787 9140969527092059837774681)
                ·
                  refine ⟨6855727145319044878331011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9140969527092059837774681 6855727145319044878331011)
                  ·
                    refine ⟨10283590717978567317496517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6855727145319044878331011 10283590717978567317496517)
                    ·
                      refine ⟨1928173259620981372030597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10283590717978567317496517 1928173259620981372030597)
                      ·
                        rfl

theorem cell23_3755104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 4, 1, 2, 1, 4].length) (baseStart_3755104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3755104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3755104 prefixEnd_3755104 := by exact prefixLift 3755104
  have htrace : WordTrace (prefixWord ++ tailWord_3755104) baseStart_3755104 baseEnd_3755104 := by
    simpa [prefixWord, tailWord_3755104, baseEnd_3755104] using wordTrace_append hprefix tailTrace_3755104
  have hstable : (prefixWord ++ tailWord_3755104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3755104).length < 2 ^ (prefixWord ++ tailWord_3755104).sum := by decide
  have hdescent : baseEnd_3755104 < baseStart_3755104 := by decide
  rcases family_descends (prefixWord ++ tailWord_3755104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3755178 : List Nat := [3, 1, 5, 1, 1, 3, 1, 2, 6]
def baseStart_3755178 : Nat := 118140960795 + 3755178 * 2 ^ 59
def prefixEnd_3755178 : Nat := 4983230072969 + 3 ^ 40 * 3755178 * 2
def baseEnd_3755178 : Nat := 214245695243268231389473

theorem tailTrace_3755178 : CollatzResearch.WordTrace tailWord_3755178 prefixEnd_3755178 214245695243268231389473 := by
  unfold tailWord_3755178
  simp only [CollatzResearch.WordTrace]
  refine ⟨34240648397409728547088547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91308395726425942792236125 34240648397409728547088547)
  ·
    refine ⟨51360972596114592820632821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34240648397409728547088547 51360972596114592820632821)
    ·
      refine ⟨4815091180885743076934327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51360972596114592820632821 4815091180885743076934327)
      ·
        refine ⟨7222636771328614615401491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4815091180885743076934327 7222636771328614615401491)
        ·
          refine ⟨10833955156992921923102237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7222636771328614615401491 10833955156992921923102237)
          ·
            refine ⟨4062733183872345721163339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10833955156992921923102237 4062733183872345721163339)
            ·
              refine ⟨6094099775808518581745009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4062733183872345721163339 6094099775808518581745009)
              ·
                refine ⟨4570574831856388936308757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6094099775808518581745009 4570574831856388936308757)
                ·
                  refine ⟨214245695243268231389473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4570574831856388936308757 214245695243268231389473)
                  ·
                    rfl

theorem cell23_3755178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 1, 2, 6].length) (baseStart_3755178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3755178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3755178 prefixEnd_3755178 := by exact prefixLift 3755178
  have htrace : WordTrace (prefixWord ++ tailWord_3755178) baseStart_3755178 baseEnd_3755178 := by
    simpa [prefixWord, tailWord_3755178, baseEnd_3755178] using wordTrace_append hprefix tailTrace_3755178
  have hstable : (prefixWord ++ tailWord_3755178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3755178).length < 2 ^ (prefixWord ++ tailWord_3755178).sum := by decide
  have hdescent : baseEnd_3755178 < baseStart_3755178 := by decide
  rcases family_descends (prefixWord ++ tailWord_3755178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3755187 : List Nat := [1, 1, 1, 2, 3, 2, 2, 2, 3, 6]
def baseStart_3755187 : Nat := 118140960795 + 3755187 * 2 ^ 59
def prefixEnd_3755187 : Nat := 4983230072969 + 3 ^ 40 * 3755187 * 2
def baseEnd_3755187 : Nat := 642738626171768182430905

theorem tailTrace_3755187 : CollatzResearch.WordTrace tailWord_3755187 prefixEnd_3755187 642738626171768182430905 := by
  unfold tailWord_3755187
  simp only [CollatzResearch.WordTrace]
  refine ⟨136962921846606308725431815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91308614564404205816954543 136962921846606308725431815)
  ·
    refine ⟨205444382769909463088147723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136962921846606308725431815 205444382769909463088147723)
    ·
      refine ⟨308166574154864194632221585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205444382769909463088147723 308166574154864194632221585)
      ·
        refine ⟨231124930616148145974166189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 308166574154864194632221585 231124930616148145974166189)
        ·
          refine ⟨86671848981055554740312321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 231124930616148145974166189 86671848981055554740312321)
          ·
            refine ⟨65003886735791666055234241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86671848981055554740312321 65003886735791666055234241)
            ·
              refine ⟨48752915051843749541425681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65003886735791666055234241 48752915051843749541425681)
              ·
                refine ⟨36564686288882812156069261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48752915051843749541425681 36564686288882812156069261)
                ·
                  refine ⟨13711757358331054558525973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36564686288882812156069261 13711757358331054558525973)
                  ·
                    refine ⟨642738626171768182430905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13711757358331054558525973 642738626171768182430905)
                    ·
                      rfl

theorem cell23_3755187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 2, 3, 6].length) (baseStart_3755187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3755187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3755187 prefixEnd_3755187 := by exact prefixLift 3755187
  have htrace : WordTrace (prefixWord ++ tailWord_3755187) baseStart_3755187 baseEnd_3755187 := by
    simpa [prefixWord, tailWord_3755187, baseEnd_3755187] using wordTrace_append hprefix tailTrace_3755187
  have hstable : (prefixWord ++ tailWord_3755187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3755187).length < 2 ^ (prefixWord ++ tailWord_3755187).sum := by decide
  have hdescent : baseEnd_3755187 < baseStart_3755187 := by decide
  rcases family_descends (prefixWord ++ tailWord_3755187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3755211 : List Nat := [1, 1, 1, 1, 3, 2, 2, 3, 5, 2, 2]
def baseStart_3755211 : Nat := 118140960795 + 3755211 * 2 ^ 59
def prefixEnd_3755211 : Nat := 4983230072969 + 3 ^ 40 * 3755211 * 2
def baseEnd_3755211 : Nat := 1928228202051012453392605

theorem tailTrace_3755211 : CollatzResearch.WordTrace tailWord_3755211 prefixEnd_3755211 1928228202051012453392605 := by
  unfold tailWord_3755211
  simp only [CollatzResearch.WordTrace]
  refine ⟨136963797198519360824305487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91309198132346240549536991 136963797198519360824305487)
  ·
    refine ⟨205445695797779041236458231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136963797198519360824305487 205445695797779041236458231)
    ·
      refine ⟨308168543696668561854687347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205445695797779041236458231 308168543696668561854687347)
      ·
        refine ⟨462252815545002842782031021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308168543696668561854687347 462252815545002842782031021)
        ·
          refine ⟨173344805829376066043261633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 462252815545002842782031021 173344805829376066043261633)
          ·
            refine ⟨130008604372032049532446225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173344805829376066043261633 130008604372032049532446225)
            ·
              refine ⟨97506453279024037149334669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130008604372032049532446225 97506453279024037149334669)
              ·
                refine ⟨36564919979634013931000501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97506453279024037149334669 36564919979634013931000501)
                ·
                  refine ⟨3427961248090688806031297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36564919979634013931000501 3427961248090688806031297)
                  ·
                    refine ⟨2570970936068016604523473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3427961248090688806031297 2570970936068016604523473)
                    ·
                      refine ⟨1928228202051012453392605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2570970936068016604523473 1928228202051012453392605)
                      ·
                        rfl

theorem cell23_3755211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 3, 5, 2, 2].length) (baseStart_3755211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3755211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3755211 prefixEnd_3755211 := by exact prefixLift 3755211
  have htrace : WordTrace (prefixWord ++ tailWord_3755211) baseStart_3755211 baseEnd_3755211 := by
    simpa [prefixWord, tailWord_3755211, baseEnd_3755211] using wordTrace_append hprefix tailTrace_3755211
  have hstable : (prefixWord ++ tailWord_3755211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3755211).length < 2 ^ (prefixWord ++ tailWord_3755211).sum := by decide
  have hdescent : baseEnd_3755211 < baseStart_3755211 := by decide
  rcases family_descends (prefixWord ++ tailWord_3755211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3755221 : List Nat := [1, 3, 2, 4, 1, 1, 1, 2, 4, 4]
def baseStart_3755221 : Nat := 118140960795 + 3755221 * 2 ^ 59
def prefixEnd_3755221 : Nat := 4983230072969 + 3 ^ 40 * 3755221 * 2
def baseEnd_3755221 : Nat := 642744445619185804755853

theorem tailTrace_3755221 : CollatzResearch.WordTrace tailWord_3755221 prefixEnd_3755221 642744445619185804755853 := by
  unfold tailWord_3755221
  simp only [CollatzResearch.WordTrace]
  refine ⟨136964161928483132532169517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91309441285655421688113011 136964161928483132532169517)
  ·
    refine ⟨51361560723181174699563569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136964161928483132532169517 51361560723181174699563569)
    ·
      refine ⟨38521170542385881024672677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51361560723181174699563569 38521170542385881024672677)
      ·
        refine ⟨7222719476697352692126127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38521170542385881024672677 7222719476697352692126127)
        ·
          refine ⟨10834079215046029038189191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7222719476697352692126127 10834079215046029038189191)
          ·
            refine ⟨16251118822569043557283787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10834079215046029038189191 16251118822569043557283787)
            ·
              refine ⟨24376678233853565335925681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16251118822569043557283787 24376678233853565335925681)
              ·
                refine ⟨18282508675390174001944261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24376678233853565335925681 18282508675390174001944261)
                ·
                  refine ⟨3427970376635657625364549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18282508675390174001944261 3427970376635657625364549)
                  ·
                    refine ⟨642744445619185804755853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3427970376635657625364549 642744445619185804755853)
                    ·
                      rfl

theorem cell23_3755221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 2, 4, 4].length) (baseStart_3755221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3755221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3755221 prefixEnd_3755221 := by exact prefixLift 3755221
  have htrace : WordTrace (prefixWord ++ tailWord_3755221) baseStart_3755221 baseEnd_3755221 := by
    simpa [prefixWord, tailWord_3755221, baseEnd_3755221] using wordTrace_append hprefix tailTrace_3755221
  have hstable : (prefixWord ++ tailWord_3755221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3755221).length < 2 ^ (prefixWord ++ tailWord_3755221).sum := by decide
  have hdescent : baseEnd_3755221 < baseStart_3755221 := by decide
  rcases family_descends (prefixWord ++ tailWord_3755221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3755231 : List Nat := [1, 1, 2, 3, 2, 1, 4, 3, 1, 2, 3]
def baseStart_3755231 : Nat := 118140960795 + 3755231 * 2 ^ 59
def prefixEnd_3755231 : Nat := 4983230072969 + 3 ^ 40 * 3755231 * 2
def baseEnd_3755231 : Nat := 1928238471664102375142513

theorem tailTrace_3755231 : CollatzResearch.WordTrace tailWord_3755231 prefixEnd_3755231 1928238471664102375142513 := by
  unfold tailWord_3755231
  simp only [CollatzResearch.WordTrace]
  refine ⟨136964526658446904240033547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91309684438964602826689031 136964526658446904240033547)
  ·
    refine ⟨205446789987670356360050321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136964526658446904240033547 205446789987670356360050321)
    ·
      refine ⟨154085092490752767270037741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205446789987670356360050321 154085092490752767270037741)
      ·
        refine ⟨57781909684032287726264153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154085092490752767270037741 57781909684032287726264153)
        ·
          refine ⟨43336432263024215794698115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57781909684032287726264153 43336432263024215794698115)
          ·
            refine ⟨65004648394536323692047173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43336432263024215794698115 65004648394536323692047173)
            ·
              refine ⟨12188371573975560692258845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65004648394536323692047173 12188371573975560692258845)
              ·
                refine ⟨4570639340240835259597067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12188371573975560692258845 4570639340240835259597067)
                ·
                  refine ⟨6855959010361252889395601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4570639340240835259597067 6855959010361252889395601)
                  ·
                    refine ⟨5141969257770939667046701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6855959010361252889395601 5141969257770939667046701)
                    ·
                      refine ⟨1928238471664102375142513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5141969257770939667046701 1928238471664102375142513)
                      ·
                        rfl

theorem cell23_3755231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 3, 1, 2, 3].length) (baseStart_3755231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3755231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3755231 prefixEnd_3755231 := by exact prefixLift 3755231
  have htrace : WordTrace (prefixWord ++ tailWord_3755231) baseStart_3755231 baseEnd_3755231 := by
    simpa [prefixWord, tailWord_3755231, baseEnd_3755231] using wordTrace_append hprefix tailTrace_3755231
  have hstable : (prefixWord ++ tailWord_3755231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3755231).length < 2 ^ (prefixWord ++ tailWord_3755231).sum := by decide
  have hdescent : baseEnd_3755231 < baseStart_3755231 := by decide
  rcases family_descends (prefixWord ++ tailWord_3755231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3755245 : List Nat := [1, 5, 1, 2, 2, 1, 3, 1, 3, 2, 2]
def baseStart_3755245 : Nat := 118140960795 + 3755245 * 2 ^ 59
def prefixEnd_3755245 : Nat := 4983230072969 + 3 ^ 40 * 3755245 * 2
def baseEnd_3755245 : Nat := 1928245660393265320367449

theorem tailTrace_3755245 : CollatzResearch.WordTrace tailWord_3755245 prefixEnd_3755245 1928245660393265320367449 := by
  unfold tailWord_3755245
  simp only [CollatzResearch.WordTrace]
  refine ⟨136965037280396184631043189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91310024853597456420695459 136965037280396184631043189)
  ·
    refine ⟨12840472245037142309160299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 136965037280396184631043189 12840472245037142309160299)
    ·
      refine ⟨19260708367555713463740449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12840472245037142309160299 19260708367555713463740449)
      ·
        refine ⟨14445531275666785097805337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19260708367555713463740449 14445531275666785097805337)
        ·
          refine ⟨10834148456750088823354003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14445531275666785097805337 10834148456750088823354003)
          ·
            refine ⟨16251222685125133235031005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10834148456750088823354003 16251222685125133235031005)
            ·
              refine ⟨6094208506921924963136627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16251222685125133235031005 6094208506921924963136627)
              ·
                refine ⟨9141312760382887444704941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6094208506921924963136627 9141312760382887444704941)
                ·
                  refine ⟨3427992285143582791764353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9141312760382887444704941 3427992285143582791764353)
                  ·
                    refine ⟨2570994213857687093823265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3427992285143582791764353 2570994213857687093823265)
                    ·
                      refine ⟨1928245660393265320367449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2570994213857687093823265 1928245660393265320367449)
                      ·
                        rfl

theorem cell23_3755245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 3, 1, 3, 2, 2].length) (baseStart_3755245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3755245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3755245 prefixEnd_3755245 := by exact prefixLift 3755245
  have htrace : WordTrace (prefixWord ++ tailWord_3755245) baseStart_3755245 baseEnd_3755245 := by
    simpa [prefixWord, tailWord_3755245, baseEnd_3755245] using wordTrace_append hprefix tailTrace_3755245
  have hstable : (prefixWord ++ tailWord_3755245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3755245).length < 2 ^ (prefixWord ++ tailWord_3755245).sum := by decide
  have hdescent : baseEnd_3755245 < baseStart_3755245 := by decide
  rcases family_descends (prefixWord ++ tailWord_3755245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3755254 : List Nat := [5, 1, 1, 1, 1, 1, 1, 1, 1, 4, 6]
def baseStart_3755254 : Nat := 118140960795 + 3755254 * 2 ^ 59
def prefixEnd_3755254 : Nat := 4983230072969 + 3 ^ 40 * 3755254 * 2
def baseEnd_3755254 : Nat := 1928250281719155785154907

theorem tailTrace_3755254 : CollatzResearch.WordTrace tailWord_3755254 prefixEnd_3755254 1928250281719155785154907 := by
  unfold tailWord_3755254
  simp only [CollatzResearch.WordTrace]
  refine ⟨8560335346085223698007551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 91310243691575719445413877 8560335346085223698007551)
  ·
    refine ⟨12840503019127835547011327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8560335346085223698007551 12840503019127835547011327)
    ·
      refine ⟨19260754528691753320516991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12840503019127835547011327 19260754528691753320516991)
      ·
        refine ⟨28891131793037629980775487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19260754528691753320516991 28891131793037629980775487)
        ·
          refine ⟨43336697689556444971163231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28891131793037629980775487 43336697689556444971163231)
          ·
            refine ⟨65005046534334667456744847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43336697689556444971163231 65005046534334667456744847)
            ·
              refine ⟨97507569801502001185117271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65005046534334667456744847 97507569801502001185117271)
              ·
                refine ⟨146261354702253001777675907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97507569801502001185117271 146261354702253001777675907)
                ·
                  refine ⟨219392032053379502666513861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 146261354702253001777675907 219392032053379502666513861)
                  ·
                    refine ⟨41136006010008656749971349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 219392032053379502666513861 41136006010008656749971349)
                    ·
                      refine ⟨1928250281719155785154907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41136006010008656749971349 1928250281719155785154907)
                      ·
                        rfl

theorem cell23_3755254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 1, 4, 6].length) (baseStart_3755254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3755254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3755254 prefixEnd_3755254 := by exact prefixLift 3755254
  have htrace : WordTrace (prefixWord ++ tailWord_3755254) baseStart_3755254 baseEnd_3755254 := by
    simpa [prefixWord, tailWord_3755254, baseEnd_3755254] using wordTrace_append hprefix tailTrace_3755254
  have hstable : (prefixWord ++ tailWord_3755254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3755254).length < 2 ^ (prefixWord ++ tailWord_3755254).sum := by decide
  have hdescent : baseEnd_3755254 < baseStart_3755254 := by decide
  rcases family_descends (prefixWord ++ tailWord_3755254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3755282 : List Nat := [3, 2, 4, 2, 2, 1, 1, 1, 1, 1, 5]
def baseStart_3755282 : Nat := 118140960795 + 3755282 * 2 ^ 59
def prefixEnd_3755282 : Nat := 4983230072969 + 3 ^ 40 * 3755282 * 2
def baseEnd_3755282 : Nat := 1928264659177481675604779

theorem tailTrace_3755282 : CollatzResearch.WordTrace tailWord_3755282 prefixEnd_3755282 1928264659177481675604779 := by
  unfold tailWord_3755282
  simp only [CollatzResearch.WordTrace]
  refine ⟨34241596695315534987535025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91310924520841426633426733 34241596695315534987535025)
  ·
    refine ⟨25681197521486651240651269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34241596695315534987535025 25681197521486651240651269)
    ·
      refine ⟨4815224535278747107622113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25681197521486651240651269 4815224535278747107622113)
      ·
        refine ⟨3611418401459060330716585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4815224535278747107622113 3611418401459060330716585)
        ·
          refine ⟨2708563801094295248037439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3611418401459060330716585 2708563801094295248037439)
          ·
            refine ⟨4062845701641442872056159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2708563801094295248037439 4062845701641442872056159)
            ·
              refine ⟨6094268552462164308084239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4062845701641442872056159 6094268552462164308084239)
              ·
                refine ⟨9141402828693246462126359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6094268552462164308084239 9141402828693246462126359)
                ·
                  refine ⟨13712104243039869693189539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9141402828693246462126359 13712104243039869693189539)
                  ·
                    refine ⟨20568156364559804539784309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13712104243039869693189539 20568156364559804539784309)
                    ·
                      refine ⟨1928264659177481675604779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20568156364559804539784309 1928264659177481675604779)
                      ·
                        rfl

theorem cell23_3755282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_3755282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3755282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3755282 prefixEnd_3755282 := by exact prefixLift 3755282
  have htrace : WordTrace (prefixWord ++ tailWord_3755282) baseStart_3755282 baseEnd_3755282 := by
    simpa [prefixWord, tailWord_3755282, baseEnd_3755282] using wordTrace_append hprefix tailTrace_3755282
  have hstable : (prefixWord ++ tailWord_3755282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3755282).length < 2 ^ (prefixWord ++ tailWord_3755282).sum := by decide
  have hdescent : baseEnd_3755282 < baseStart_3755282 := by decide
  rcases family_descends (prefixWord ++ tailWord_3755282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3755295 : List Nat := [1, 1, 2, 4, 4, 1, 2, 2, 2, 1, 3]
def baseStart_3755295 : Nat := 118140960795 + 3755295 * 2 ^ 59
def prefixEnd_3755295 : Nat := 4983230072969 + 3 ^ 40 * 3755295 * 2
def baseEnd_3755295 : Nat := 1928271334425990124742219

theorem tailTrace_3755295 : CollatzResearch.WordTrace tailWord_3755295 prefixEnd_3755295 1928271334425990124742219 := by
  unfold tailWord_3755295
  simp only [CollatzResearch.WordTrace]
  refine ⟨136966860930215043170363339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91311240620143362113575559 136966860930215043170363339)
  ·
    refine ⟨205450291395322564755545009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136966860930215043170363339 205450291395322564755545009)
    ·
      refine ⟨154087718546491923566658757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205450291395322564755545009 154087718546491923566658757)
      ·
        refine ⟨28891447227467235668748517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 154087718546491923566658757 28891447227467235668748517)
        ·
          refine ⟨5417146355150106687890347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28891447227467235668748517 5417146355150106687890347)
          ·
            refine ⟨8125719532725160031835521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5417146355150106687890347 8125719532725160031835521)
            ·
              refine ⟨6094289649543870023876641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8125719532725160031835521 6094289649543870023876641)
              ·
                refine ⟨4570717237157902517907481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6094289649543870023876641 4570717237157902517907481)
                ·
                  refine ⟨3428037927868426888430611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4570717237157902517907481 3428037927868426888430611)
                  ·
                    refine ⟨5142056891802640332645917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3428037927868426888430611 5142056891802640332645917)
                    ·
                      refine ⟨1928271334425990124742219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5142056891802640332645917 1928271334425990124742219)
                      ·
                        rfl

theorem cell23_3755295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 2, 2, 2, 1, 3].length) (baseStart_3755295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3755295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3755295 prefixEnd_3755295 := by exact prefixLift 3755295
  have htrace : WordTrace (prefixWord ++ tailWord_3755295) baseStart_3755295 baseEnd_3755295 := by
    simpa [prefixWord, tailWord_3755295, baseEnd_3755295] using wordTrace_append hprefix tailTrace_3755295
  have hstable : (prefixWord ++ tailWord_3755295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3755295).length < 2 ^ (prefixWord ++ tailWord_3755295).sum := by decide
  have hdescent : baseEnd_3755295 < baseStart_3755295 := by decide
  rcases family_descends (prefixWord ++ tailWord_3755295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3755296 : List Nat := [2, 1, 1, 5, 4, 1, 2, 2, 1, 2, 2]
def baseStart_3755296 : Nat := 118140960795 + 3755296 * 2 ^ 59
def prefixEnd_3755296 : Nat := 4983230072969 + 3 ^ 40 * 3755296 * 2
def baseEnd_3755296 : Nat := 1928271847906644620829715

theorem tailTrace_3755296 : CollatzResearch.WordTrace tailWord_3755296 prefixEnd_3755296 1928271847906644620829715 := by
  unfold tailWord_3755296
  simp only [CollatzResearch.WordTrace]
  refine ⟨68483448701605710170574871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91311264935474280227433161 68483448701605710170574871)
  ·
    refine ⟨102725173052408565255862307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68483448701605710170574871 102725173052408565255862307)
    ·
      refine ⟨154087759578612847883793461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102725173052408565255862307 154087759578612847883793461)
      ·
        refine ⟨14445727460494954489105637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 154087759578612847883793461 14445727460494954489105637)
        ·
          refine ⟨2708573898842803966707307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14445727460494954489105637 2708573898842803966707307)
          ·
            refine ⟨4062860848264205950060961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2708573898842803966707307 4062860848264205950060961)
            ·
              refine ⟨3047145636198154462545721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4062860848264205950060961 3047145636198154462545721)
              ·
                refine ⟨2285359227148615846909291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3047145636198154462545721 2285359227148615846909291)
                ·
                  refine ⟨3428038840722923770363937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2285359227148615846909291 3428038840722923770363937)
                  ·
                    refine ⟨2571029130542192827772953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3428038840722923770363937 2571029130542192827772953)
                    ·
                      refine ⟨1928271847906644620829715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2571029130542192827772953 1928271847906644620829715)
                      ·
                        rfl

theorem cell23_3755296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 2, 2, 1, 2, 2].length) (baseStart_3755296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3755296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3755296 prefixEnd_3755296 := by exact prefixLift 3755296
  have htrace : WordTrace (prefixWord ++ tailWord_3755296) baseStart_3755296 baseEnd_3755296 := by
    simpa [prefixWord, tailWord_3755296, baseEnd_3755296] using wordTrace_append hprefix tailTrace_3755296
  have hstable : (prefixWord ++ tailWord_3755296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3755296).length < 2 ^ (prefixWord ++ tailWord_3755296).sum := by decide
  have hdescent : baseEnd_3755296 < baseStart_3755296 := by decide
  rcases family_descends (prefixWord ++ tailWord_3755296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3755324 : List Nat := [2, 2, 2, 2, 1, 3, 1, 1, 9]
def baseStart_3755324 : Nat := 118140960795 + 3755324 * 2 ^ 59
def prefixEnd_3755324 : Nat := 4983230072969 + 3 ^ 40 * 3755324 * 2
def baseEnd_3755324 : Nat := 214254025040552279031065

theorem tailTrace_3755324 : CollatzResearch.WordTrace tailWord_3755324 prefixEnd_3755324 214254025040552279031065 := by
  unfold tailWord_3755324
  simp only [CollatzResearch.WordTrace]
  refine ⟨68483959323554990561584513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91311945764739987415446017 68483959323554990561584513)
  ·
    refine ⟨51362969492666242921188385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68483959323554990561584513 51362969492666242921188385)
    ·
      refine ⟨38522227119499682190891289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51362969492666242921188385 38522227119499682190891289)
      ·
        refine ⟨28891670339624761643168467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38522227119499682190891289 28891670339624761643168467)
        ·
          refine ⟨43337505509437142464752701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28891670339624761643168467 43337505509437142464752701)
          ·
            refine ⟨16251564566038928424282263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43337505509437142464752701 16251564566038928424282263)
            ·
              refine ⟨24377346849058392636423395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16251564566038928424282263 24377346849058392636423395)
              ·
                refine ⟨36566020273587588954635093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24377346849058392636423395 36566020273587588954635093)
                ·
                  refine ⟨214254025040552279031065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 36566020273587588954635093 214254025040552279031065)
                  ·
                    rfl

theorem cell23_3755324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 1, 9].length) (baseStart_3755324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3755324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3755324 prefixEnd_3755324 := by exact prefixLift 3755324
  have htrace : WordTrace (prefixWord ++ tailWord_3755324) baseStart_3755324 baseEnd_3755324 := by
    simpa [prefixWord, tailWord_3755324, baseEnd_3755324] using wordTrace_append hprefix tailTrace_3755324
  have hstable : (prefixWord ++ tailWord_3755324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3755324).length < 2 ^ (prefixWord ++ tailWord_3755324).sum := by decide
  have hdescent : baseEnd_3755324 < baseStart_3755324 := by decide
  rcases family_descends (prefixWord ++ tailWord_3755324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3755351 : List Nat := [1, 1, 3, 2, 3, 2, 1, 2, 2, 3, 3]
def baseStart_3755351 : Nat := 118140960795 + 3755351 * 2 ^ 59
def prefixEnd_3755351 : Nat := 4983230072969 + 3 ^ 40 * 3755351 * 2
def baseEnd_3755351 : Nat := 1928300089342641905641961

theorem tailTrace_3755351 : CollatzResearch.WordTrace tailWord_3755351 prefixEnd_3755351 1928300089342641905641961 := by
  unfold tailWord_3755351
  simp only [CollatzResearch.WordTrace]
  refine ⟨136968903418012164734401907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91312602278674776489601271 136968903418012164734401907)
  ·
    refine ⟨205453355127018247101602861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136968903418012164734401907 205453355127018247101602861)
    ·
      refine ⟨77045008172631842663101073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205453355127018247101602861 77045008172631842663101073)
      ·
        refine ⟨57783756129473881997325805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77045008172631842663101073 57783756129473881997325805)
        ·
          refine ⟨21668908548552705748997177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57783756129473881997325805 21668908548552705748997177)
          ·
            refine ⟨16251681411414529311747883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21668908548552705748997177 16251681411414529311747883)
            ·
              refine ⟨24377522117121793967621825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16251681411414529311747883 24377522117121793967621825)
              ·
                refine ⟨18283141587841345475716369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24377522117121793967621825 18283141587841345475716369)
                ·
                  refine ⟨13712356190881009106787277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18283141587841345475716369 13712356190881009106787277)
                  ·
                    refine ⟨5142133571580378415045229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13712356190881009106787277 5142133571580378415045229)
                    ·
                      refine ⟨1928300089342641905641961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5142133571580378415045229 1928300089342641905641961)
                      ·
                        rfl

theorem cell23_3755351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 2, 2, 3, 3].length) (baseStart_3755351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3755351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3755351 prefixEnd_3755351 := by exact prefixLift 3755351
  have htrace : WordTrace (prefixWord ++ tailWord_3755351) baseStart_3755351 baseEnd_3755351 := by
    simpa [prefixWord, tailWord_3755351, baseEnd_3755351] using wordTrace_append hprefix tailTrace_3755351
  have hstable : (prefixWord ++ tailWord_3755351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3755351).length < 2 ^ (prefixWord ++ tailWord_3755351).sum := by decide
  have hdescent : baseEnd_3755351 < baseStart_3755351 := by decide
  rcases family_descends (prefixWord ++ tailWord_3755351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3755361 : List Nat := [1, 2, 3, 1, 1, 1, 1, 3, 1, 7, 2]
def baseStart_3755361 : Nat := 118140960795 + 3755361 * 2 ^ 59
def prefixEnd_3755361 : Nat := 4983230072969 + 3 ^ 40 * 3755361 * 2
def baseEnd_3755361 : Nat := 1928305224149186866516915

theorem tailTrace_3755361 : CollatzResearch.WordTrace tailWord_3755361 prefixEnd_3755361 1928305224149186866516915 := by
  unfold tailWord_3755361
  simp only [CollatzResearch.WordTrace]
  refine ⟨136969268147975936442265937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91312845431983957628177291 136969268147975936442265937)
  ·
    refine ⟨102726951110981952331699453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136969268147975936442265937 102726951110981952331699453)
    ·
      refine ⟨38522606666618232124387295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102726951110981952331699453 38522606666618232124387295)
      ·
        refine ⟨57783909999927348186580943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38522606666618232124387295 57783909999927348186580943)
        ·
          refine ⟨86675864999891022279871415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57783909999927348186580943 86675864999891022279871415)
          ·
            refine ⟨130013797499836533419807123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86675864999891022279871415 130013797499836533419807123)
            ·
              refine ⟨195020696249754800129710685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130013797499836533419807123 195020696249754800129710685)
              ·
                refine ⟨73132761093658050048641507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 195020696249754800129710685 73132761093658050048641507)
                ·
                  refine ⟨109699141640487075072962261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73132761093658050048641507 109699141640487075072962261)
                  ·
                    refine ⟨2571073632198915822022553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 109699141640487075072962261 2571073632198915822022553)
                    ·
                      refine ⟨1928305224149186866516915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2571073632198915822022553 1928305224149186866516915)
                      ·
                        rfl

theorem cell23_3755361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 7, 2].length) (baseStart_3755361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3755361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3755361 prefixEnd_3755361 := by exact prefixLift 3755361
  have htrace : WordTrace (prefixWord ++ tailWord_3755361) baseStart_3755361 baseEnd_3755361 := by
    simpa [prefixWord, tailWord_3755361, baseEnd_3755361] using wordTrace_append hprefix tailTrace_3755361
  have hstable : (prefixWord ++ tailWord_3755361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3755361).length < 2 ^ (prefixWord ++ tailWord_3755361).sum := by decide
  have hdescent : baseEnd_3755361 < baseStart_3755361 := by decide
  rcases family_descends (prefixWord ++ tailWord_3755361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3755445 : List Nat := [1, 3, 3, 2, 2, 2, 2, 1, 2, 2, 3]
def baseStart_3755445 : Nat := 118140960795 + 3755445 * 2 ^ 59
def prefixEnd_3755445 : Nat := 4983230072969 + 3 ^ 40 * 3755445 * 2
def baseEnd_3755445 : Nat := 1928348356524164537866529

theorem tailTrace_3755445 : CollatzResearch.WordTrace tailWord_3755445 prefixEnd_3755445 1928348356524164537866529 := by
  unfold tailWord_3755445
  simp only [CollatzResearch.WordTrace]
  refine ⟨136972331879671618788323789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91314887919781079192215859 136972331879671618788323789)
  ·
    refine ⟨51364624454876857045621421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136972331879671618788323789 51364624454876857045621421)
    ·
      refine ⟨19261734170578821392108033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51364624454876857045621421 19261734170578821392108033)
      ·
        refine ⟨14446300627934116044081025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19261734170578821392108033 14446300627934116044081025)
        ·
          refine ⟨10834725470950587033060769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14446300627934116044081025 10834725470950587033060769)
          ·
            refine ⟨8126044103212940274795577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10834725470950587033060769 8126044103212940274795577)
            ·
              refine ⟨6094533077409705206096683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8126044103212940274795577 6094533077409705206096683)
              ·
                refine ⟨9141799616114557809145025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6094533077409705206096683 9141799616114557809145025)
                ·
                  refine ⟨6856349712085918356858769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9141799616114557809145025 6856349712085918356858769)
                  ·
                    refine ⟨5142262284064438767644077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6856349712085918356858769 5142262284064438767644077)
                    ·
                      refine ⟨1928348356524164537866529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5142262284064438767644077 1928348356524164537866529)
                      ·
                        rfl

theorem cell23_3755445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 2, 1, 2, 2, 3].length) (baseStart_3755445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3755445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3755445 prefixEnd_3755445 := by exact prefixLift 3755445
  have htrace : WordTrace (prefixWord ++ tailWord_3755445) baseStart_3755445 baseEnd_3755445 := by
    simpa [prefixWord, tailWord_3755445, baseEnd_3755445] using wordTrace_append hprefix tailTrace_3755445
  have hstable : (prefixWord ++ tailWord_3755445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3755445).length < 2 ^ (prefixWord ++ tailWord_3755445).sum := by decide
  have hdescent : baseEnd_3755445 < baseStart_3755445 := by decide
  rcases family_descends (prefixWord ++ tailWord_3755445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3755509 : List Nat := [1, 3, 5, 1, 1, 1, 1, 5, 1, 1, 3]
def baseStart_3755509 : Nat := 118140960795 + 3755509 * 2 ^ 59
def prefixEnd_3755509 : Nat := 4983230072969 + 3 ^ 40 * 3755509 * 2
def baseEnd_3755509 : Nat := 1928381219286052287466235

theorem tailTrace_3755509 : CollatzResearch.WordTrace tailWord_3755509 prefixEnd_3755509 1928381219286052287466235 := by
  unfold tailWord_3755509
  simp only [CollatzResearch.WordTrace]
  refine ⟨136974666151439757718653581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91316444100959838479102387 136974666151439757718653581)
  ·
    refine ⟨51365499806789909144495093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136974666151439757718653581 51365499806789909144495093)
    ·
      refine ⟨4815515606886553982296415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51365499806789909144495093 4815515606886553982296415)
      ·
        refine ⟨7223273410329830973444623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4815515606886553982296415 7223273410329830973444623)
        ·
          refine ⟨10834910115494746460166935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7223273410329830973444623 10834910115494746460166935)
          ·
            refine ⟨16252365173242119690250403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10834910115494746460166935 16252365173242119690250403)
            ·
              refine ⟨24378547759863179535375605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16252365173242119690250403 24378547759863179535375605)
              ·
                refine ⟨2285488852487173081441463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24378547759863179535375605 2285488852487173081441463)
                ·
                  refine ⟨3428233278730759622162195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2285488852487173081441463 3428233278730759622162195)
                  ·
                    refine ⟨5142349918096139433243293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3428233278730759622162195 5142349918096139433243293)
                    ·
                      refine ⟨1928381219286052287466235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5142349918096139433243293 1928381219286052287466235)
                      ·
                        rfl

theorem cell23_3755509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 5, 1, 1, 3].length) (baseStart_3755509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3755509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3755509 prefixEnd_3755509 := by exact prefixLift 3755509
  have htrace : WordTrace (prefixWord ++ tailWord_3755509) baseStart_3755509 baseEnd_3755509 := by
    simpa [prefixWord, tailWord_3755509, baseEnd_3755509] using wordTrace_append hprefix tailTrace_3755509
  have hstable : (prefixWord ++ tailWord_3755509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3755509).length < 2 ^ (prefixWord ++ tailWord_3755509).sum := by decide
  have hdescent : baseEnd_3755509 < baseStart_3755509 := by decide
  rcases family_descends (prefixWord ++ tailWord_3755509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3755511 : List Nat := [1, 1, 3, 1, 1, 1, 1, 5, 3, 2, 4]
def baseStart_3755511 : Nat := 118140960795 + 3755511 * 2 ^ 59
def prefixEnd_3755511 : Nat := 4983230072969 + 3 ^ 40 * 3755511 * 2
def baseEnd_3755511 : Nat := 1928382246247361279641225

theorem tailTrace_3755511 : CollatzResearch.WordTrace tailWord_3755511 prefixEnd_3755511 1928382246247361279641225 := by
  unfold tailWord_3755511
  simp only [CollatzResearch.WordTrace]
  refine ⟨136974739097432512060226387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91316492731621674706817591 136974739097432512060226387)
  ·
    refine ⟨205462108646148768090339581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136974739097432512060226387 205462108646148768090339581)
    ·
      refine ⟨77048290742305788033877343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205462108646148768090339581 77048290742305788033877343)
      ·
        refine ⟨115572436113458682050816015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77048290742305788033877343 115572436113458682050816015)
        ·
          refine ⟨173358654170188023076224023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115572436113458682050816015 173358654170188023076224023)
          ·
            refine ⟨260037981255282034614336035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173358654170188023076224023 260037981255282034614336035)
            ·
              refine ⟨390056971882923051921504053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 260037981255282034614336035 390056971882923051921504053)
              ·
                refine ⟨36567841114024036117641005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 390056971882923051921504053 36567841114024036117641005)
                ·
                  refine ⟨13712940417759013544115377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36567841114024036117641005 13712940417759013544115377)
                  ·
                    refine ⟨10284705313319260158086533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13712940417759013544115377 10284705313319260158086533)
                    ·
                      refine ⟨1928382246247361279641225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10284705313319260158086533 1928382246247361279641225)
                      ·
                        rfl

theorem cell23_3755511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 5, 3, 2, 4].length) (baseStart_3755511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3755511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3755511 prefixEnd_3755511 := by exact prefixLift 3755511
  have htrace : WordTrace (prefixWord ++ tailWord_3755511) baseStart_3755511 baseEnd_3755511 := by
    simpa [prefixWord, tailWord_3755511, baseEnd_3755511] using wordTrace_append hprefix tailTrace_3755511
  have hstable : (prefixWord ++ tailWord_3755511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3755511).length < 2 ^ (prefixWord ++ tailWord_3755511).sum := by decide
  have hdescent : baseEnd_3755511 < baseStart_3755511 := by decide
  rcases family_descends (prefixWord ++ tailWord_3755511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3755551 : List Nat := [1, 1, 2, 4, 1, 1, 2, 2, 2, 7]
def baseStart_3755551 : Nat := 118140960795 + 3755551 * 2 ^ 59
def prefixEnd_3755551 : Nat := 4983230072969 + 3 ^ 40 * 3755551 * 2
def baseEnd_3755551 : Nat := 642800928491180374380347

theorem tailTrace_3755551 : CollatzResearch.WordTrace tailWord_3755551 prefixEnd_3755551 642800928491180374380347 := by
  unfold tailWord_3755551
  simp only [CollatzResearch.WordTrace]
  refine ⟨136976198017287598891682507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91317465344858399261121671 136976198017287598891682507)
  ·
    refine ⟨205464297025931398337523761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136976198017287598891682507 205464297025931398337523761)
    ·
      refine ⟨154098222769448548753142821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205464297025931398337523761 154098222769448548753142821)
      ·
        refine ⟨28893416769271602891214279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 154098222769448548753142821 28893416769271602891214279)
        ·
          refine ⟨43340125153907404336821419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28893416769271602891214279 43340125153907404336821419)
          ·
            refine ⟨65010187730861106505232129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43340125153907404336821419 65010187730861106505232129)
            ·
              refine ⟨48757640798145829878924097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65010187730861106505232129 48757640798145829878924097)
              ·
                refine ⟨36568230598609372409193073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48757640798145829878924097 36568230598609372409193073)
                ·
                  refine ⟨27426172948957029306894805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36568230598609372409193073 27426172948957029306894805)
                  ·
                    refine ⟨642800928491180374380347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27426172948957029306894805 642800928491180374380347)
                    ·
                      rfl

theorem cell23_3755551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 2, 2, 7].length) (baseStart_3755551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3755551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3755551 prefixEnd_3755551 := by exact prefixLift 3755551
  have htrace : WordTrace (prefixWord ++ tailWord_3755551) baseStart_3755551 baseEnd_3755551 := by
    simpa [prefixWord, tailWord_3755551, baseEnd_3755551] using wordTrace_append hprefix tailTrace_3755551
  have hstable : (prefixWord ++ tailWord_3755551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3755551).length < 2 ^ (prefixWord ++ tailWord_3755551).sum := by decide
  have hdescent : baseEnd_3755551 < baseStart_3755551 := by decide
  rcases family_descends (prefixWord ++ tailWord_3755551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3755552 : List Nat := [2, 1, 1, 6, 1, 2, 2, 2, 1, 2, 3]
def baseStart_3755552 : Nat := 118140960795 + 3755552 * 2 ^ 59
def prefixEnd_3755552 : Nat := 4983230072969 + 3 ^ 40 * 3755552 * 2
def baseEnd_3755552 : Nat := 1928403298954195619228537

theorem tailTrace_3755552 : CollatzResearch.WordTrace tailWord_3755552 prefixEnd_3755552 1928403298954195619228537 := by
  unfold tailWord_3755552
  simp only [CollatzResearch.WordTrace]
  refine ⟨68488117245141988031234455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91317489660189317374979273 68488117245141988031234455)
  ·
    refine ⟨102732175867712982046851683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68488117245141988031234455 102732175867712982046851683)
    ·
      refine ⟨154098263801569473070277525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102732175867712982046851683 154098263801569473070277525)
      ·
        refine ⟨7223356115698569050169259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 154098263801569473070277525 7223356115698569050169259)
        ·
          refine ⟨10835034173547853575253889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7223356115698569050169259 10835034173547853575253889)
          ·
            refine ⟨8126275630160890181440417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10835034173547853575253889 8126275630160890181440417)
            ·
              refine ⟨6094706722620667636080313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8126275630160890181440417 6094706722620667636080313)
              ·
                refine ⟨4571030041965500727060235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6094706722620667636080313 4571030041965500727060235)
                ·
                  refine ⟨6856545062948251090590353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4571030041965500727060235 6856545062948251090590353)
                  ·
                    refine ⟨5142408797211188317942765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6856545062948251090590353 5142408797211188317942765)
                    ·
                      refine ⟨1928403298954195619228537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5142408797211188317942765 1928403298954195619228537)
                      ·
                        rfl

theorem cell23_3755552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_3755552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3755552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3755552 prefixEnd_3755552 := by exact prefixLift 3755552
  have htrace : WordTrace (prefixWord ++ tailWord_3755552) baseStart_3755552 baseEnd_3755552 := by
    simpa [prefixWord, tailWord_3755552, baseEnd_3755552] using wordTrace_append hprefix tailTrace_3755552
  have hstable : (prefixWord ++ tailWord_3755552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3755552).length < 2 ^ (prefixWord ++ tailWord_3755552).sum := by decide
  have hdescent : baseEnd_3755552 < baseStart_3755552 := by decide
  rcases family_descends (prefixWord ++ tailWord_3755552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3755555 : List Nat := [1, 1, 1, 4, 5, 2, 2, 7]
def baseStart_3755555 : Nat := 118140960795 + 3755555 * 2 ^ 59
def prefixEnd_3755555 : Nat := 4983230072969 + 3 ^ 40 * 3755555 * 2
def baseEnd_3755555 : Nat := 71422401459117003981149

theorem tailTrace_3755555 : CollatzResearch.WordTrace tailWord_3755555 prefixEnd_3755555 71422401459117003981149 := by
  unfold tailWord_3755555
  simp only [CollatzResearch.WordTrace]
  refine ⟨136976343909273107574828119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91317562606182071716552079 136976343909273107574828119)
  ·
    refine ⟨205464515863909661362242179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136976343909273107574828119 205464515863909661362242179)
    ·
      refine ⟨308196773795864492043363269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205464515863909661362242179 308196773795864492043363269)
      ·
        refine ⟨57786895086724592258130613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 308196773795864492043363269 57786895086724592258130613)
        ·
          refine ⟨5417521414380430524199745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 57786895086724592258130613 5417521414380430524199745)
          ·
            refine ⟨4063141060785322893149809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5417521414380430524199745 4063141060785322893149809)
            ·
              refine ⟨3047355795588992169862357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4063141060785322893149809 3047355795588992169862357)
              ·
                refine ⟨71422401459117003981149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3047355795588992169862357 71422401459117003981149)
                ·
                  rfl

theorem cell23_3755555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 2, 7].length) (baseStart_3755555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3755555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3755555 prefixEnd_3755555 := by exact prefixLift 3755555
  have htrace : WordTrace (prefixWord ++ tailWord_3755555) baseStart_3755555 baseEnd_3755555 := by
    simpa [prefixWord, tailWord_3755555, baseEnd_3755555] using wordTrace_append hprefix tailTrace_3755555
  have hstable : (prefixWord ++ tailWord_3755555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3755555).length < 2 ^ (prefixWord ++ tailWord_3755555).sum := by decide
  have hdescent : baseEnd_3755555 < baseStart_3755555 := by decide
  rcases family_descends (prefixWord ++ tailWord_3755555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3755566 : List Nat := [4, 1, 3, 1, 2, 1, 3, 3, 1, 2, 2]
def baseStart_3755566 : Nat := 118140960795 + 3755566 * 2 ^ 59
def prefixEnd_3755566 : Nat := 4983230072969 + 3 ^ 40 * 3755566 * 2
def baseEnd_3755566 : Nat := 1928410487683358564453473

theorem tailTrace_3755566 : CollatzResearch.WordTrace tailWord_3755566 prefixEnd_3755566 1928410487683358564453473 := by
  unfold tailWord_3755566
  simp only [CollatzResearch.WordTrace]
  refine ⟨17122093139029157056684819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91317830074822170968985701 17122093139029157056684819)
  ·
    refine ⟨25683139708543735585027229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17122093139029157056684819 25683139708543735585027229)
    ·
      refine ⟨9631177390703900844385211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25683139708543735585027229 9631177390703900844385211)
      ·
        refine ⟨14446766086055851266577817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9631177390703900844385211 14446766086055851266577817)
        ·
          refine ⟨10835074564541888449933363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14446766086055851266577817 10835074564541888449933363)
          ·
            refine ⟨16252611846812832674900045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10835074564541888449933363 16252611846812832674900045)
            ·
              refine ⟨6094729442554812253087517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16252611846812832674900045 6094729442554812253087517)
              ·
                refine ⟨2285523540958054594907819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6094729442554812253087517 2285523540958054594907819)
                ·
                  refine ⟨3428285311437081892361729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2285523540958054594907819 3428285311437081892361729)
                  ·
                    refine ⟨2571213983577811419271297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3428285311437081892361729 2571213983577811419271297)
                    ·
                      refine ⟨1928410487683358564453473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2571213983577811419271297 1928410487683358564453473)
                      ·
                        rfl

theorem cell23_3755566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 3, 3, 1, 2, 2].length) (baseStart_3755566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3755566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3755566 prefixEnd_3755566 := by exact prefixLift 3755566
  have htrace : WordTrace (prefixWord ++ tailWord_3755566) baseStart_3755566 baseEnd_3755566 := by
    simpa [prefixWord, tailWord_3755566, baseEnd_3755566] using wordTrace_append hprefix tailTrace_3755566
  have hstable : (prefixWord ++ tailWord_3755566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3755566).length < 2 ^ (prefixWord ++ tailWord_3755566).sum := by decide
  have hdescent : baseEnd_3755566 < baseStart_3755566 := by decide
  rcases family_descends (prefixWord ++ tailWord_3755566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3755605 : List Nat := [1, 3, 2, 2, 1, 1, 1, 5, 1, 4, 2]
def baseStart_3755605 : Nat := 118140960795 + 3755605 * 2 ^ 59
def prefixEnd_3755605 : Nat := 4983230072969 + 3 ^ 40 * 3755605 * 2
def baseEnd_3755605 : Nat := 1928430513428883911865793

theorem tailTrace_3755605 : CollatzResearch.WordTrace tailWord_3755605 prefixEnd_3755605 1928430513428883911865793 := by
  unfold tailWord_3755605
  simp only [CollatzResearch.WordTrace]
  refine ⟨136978167559091966114148269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91318778372727977409432179 136978167559091966114148269)
  ·
    refine ⟨51366812834659487292805601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136978167559091966114148269 51366812834659487292805601)
    ·
      refine ⟨38525109625994615469604201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51366812834659487292805601 38525109625994615469604201)
      ·
        refine ⟨28893832219495961602203151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38525109625994615469604201 28893832219495961602203151)
        ·
          refine ⟨43340748329243942403304727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28893832219495961602203151 43340748329243942403304727)
          ·
            refine ⟨65011122493865913604957091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43340748329243942403304727 65011122493865913604957091)
            ·
              refine ⟨97516683740798870407435637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65011122493865913604957091 97516683740798870407435637)
              ·
                refine ⟨9142189100699894100697091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 97516683740798870407435637 9142189100699894100697091)
                ·
                  refine ⟨13713283651049841151045637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9142189100699894100697091 13713283651049841151045637)
                  ·
                    refine ⟨2571240684571845215821057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13713283651049841151045637 2571240684571845215821057)
                    ·
                      refine ⟨1928430513428883911865793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2571240684571845215821057 1928430513428883911865793)
                      ·
                        rfl

theorem cell23_3755605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 5, 1, 4, 2].length) (baseStart_3755605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3755605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3755605 prefixEnd_3755605 := by exact prefixLift 3755605
  have htrace : WordTrace (prefixWord ++ tailWord_3755605) baseStart_3755605 baseEnd_3755605 := by
    simpa [prefixWord, tailWord_3755605, baseEnd_3755605] using wordTrace_append hprefix tailTrace_3755605
  have hstable : (prefixWord ++ tailWord_3755605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3755605).length < 2 ^ (prefixWord ++ tailWord_3755605).sum := by decide
  have hdescent : baseEnd_3755605 < baseStart_3755605 := by decide
  rcases family_descends (prefixWord ++ tailWord_3755605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3755655 : List Nat := [1, 1, 4, 2, 1, 4, 1, 1, 2, 3, 3]
def baseStart_3755655 : Nat := 118140960795 + 3755655 * 2 ^ 59
def prefixEnd_3755655 : Nat := 4983230072969 + 3 ^ 40 * 3755655 * 2
def baseEnd_3755655 : Nat := 1928456187461608716240563

theorem tailTrace_3755655 : CollatzResearch.WordTrace tailWord_3755655 prefixEnd_3755655 1928456187461608716240563 := by
  unfold tailWord_3755655
  simp only [CollatzResearch.WordTrace]
  refine ⟨136979991208910824653468419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91319994139273883102312279 136979991208910824653468419)
  ·
    refine ⟨205469986813366236980202629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136979991208910824653468419 205469986813366236980202629)
    ·
      refine ⟨38525622527506169433787993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 205469986813366236980202629 38525622527506169433787993)
      ·
        refine ⟨28894216895629627075340995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38525622527506169433787993 28894216895629627075340995)
        ·
          refine ⟨43341325343444440613011493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28894216895629627075340995 43341325343444440613011493)
          ·
            refine ⟨8126498501895832614939655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43341325343444440613011493 8126498501895832614939655)
            ·
              refine ⟨12189747752843748922409483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8126498501895832614939655 12189747752843748922409483)
              ·
                refine ⟨18284621629265623383614225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12189747752843748922409483 18284621629265623383614225)
                ·
                  refine ⟨13713466221949217537710669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18284621629265623383614225 13713466221949217537710669)
                  ·
                    refine ⟨5142549833230956576641501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13713466221949217537710669 5142549833230956576641501)
                    ·
                      refine ⟨1928456187461608716240563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5142549833230956576641501 1928456187461608716240563)
                      ·
                        rfl

theorem cell23_3755655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 1, 2, 3, 3].length) (baseStart_3755655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3755655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3755655 prefixEnd_3755655 := by exact prefixLift 3755655
  have htrace : WordTrace (prefixWord ++ tailWord_3755655) baseStart_3755655 baseEnd_3755655 := by
    simpa [prefixWord, tailWord_3755655, baseEnd_3755655] using wordTrace_append hprefix tailTrace_3755655
  have hstable : (prefixWord ++ tailWord_3755655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3755655).length < 2 ^ (prefixWord ++ tailWord_3755655).sum := by decide
  have hdescent : baseEnd_3755655 < baseStart_3755655 := by decide
  rcases family_descends (prefixWord ++ tailWord_3755655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3755679 : List Nat := [1, 1, 2, 7, 1, 1, 2, 3, 5]
def baseStart_3755679 : Nat := 118140960795 + 3755679 * 2 ^ 59
def prefixEnd_3755679 : Nat := 4983230072969 + 3 ^ 40 * 3755679 * 2
def baseEnd_3755679 : Nat := 214274278999701846926717

theorem tailTrace_3755679 : CollatzResearch.WordTrace tailWord_3755679 prefixEnd_3755679 214274278999701846926717 := by
  unfold tailWord_3755679
  simp only [CollatzResearch.WordTrace]
  refine ⟨136980866560823876752342091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91320577707215917834894727 136980866560823876752342091)
  ·
    refine ⟨205471299841235815128513137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136980866560823876752342091 205471299841235815128513137)
    ·
      refine ⟨154103474880926861346384853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205471299841235815128513137 154103474880926861346384853)
      ·
        refine ⟨3611800192521723312805895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 154103474880926861346384853 3611800192521723312805895)
        ·
          refine ⟨5417700288782584969208843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3611800192521723312805895 5417700288782584969208843)
          ·
            refine ⟨8126550433173877453813265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5417700288782584969208843 8126550433173877453813265)
            ·
              refine ⟨6094912824880408090359949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8126550433173877453813265 6094912824880408090359949)
              ·
                refine ⟨2285592309330153033884981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6094912824880408090359949 2285592309330153033884981)
                ·
                  refine ⟨214274278999701846926717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2285592309330153033884981 214274278999701846926717)
                  ·
                    rfl

theorem cell23_3755679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 2, 3, 5].length) (baseStart_3755679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3755679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3755679 prefixEnd_3755679 := by exact prefixLift 3755679
  have htrace : WordTrace (prefixWord ++ tailWord_3755679) baseStart_3755679 baseEnd_3755679 := by
    simpa [prefixWord, tailWord_3755679, baseEnd_3755679] using wordTrace_append hprefix tailTrace_3755679
  have hstable : (prefixWord ++ tailWord_3755679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3755679).length < 2 ^ (prefixWord ++ tailWord_3755679).sum := by decide
  have hdescent : baseEnd_3755679 < baseStart_3755679 := by decide
  rcases family_descends (prefixWord ++ tailWord_3755679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3755695 : List Nat := [1, 1, 2, 1, 2, 4, 1, 1, 4, 4, 2]
def baseStart_3755695 : Nat := 118140960795 + 3755695 * 2 ^ 59
def prefixEnd_3755695 : Nat := 4983230072969 + 3 ^ 40 * 3755695 * 2
def baseEnd_3755695 : Nat := 1928476726687788559740379

theorem tailTrace_3755695 : CollatzResearch.WordTrace tailWord_3755695 prefixEnd_3755695 1928476726687788559740379 := by
  unfold tailWord_3755695
  simp only [CollatzResearch.WordTrace]
  refine ⟨136981450128765911484924539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91320966752510607656616359 136981450128765911484924539)
  ·
    refine ⟨205472175193148867227386809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136981450128765911484924539 205472175193148867227386809)
    ·
      refine ⟨154104131394861650420540107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205472175193148867227386809 154104131394861650420540107)
      ·
        refine ⟨231156197092292475630810161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154104131394861650420540107 231156197092292475630810161)
        ·
          refine ⟨173367147819219356723107621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231156197092292475630810161 173367147819219356723107621)
          ·
            refine ⟨32506340216103629385582679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 173367147819219356723107621 32506340216103629385582679)
            ·
              refine ⟨48759510324155444078374019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32506340216103629385582679 48759510324155444078374019)
              ·
                refine ⟨73139265486233166117561029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48759510324155444078374019 73139265486233166117561029)
                ·
                  refine ⟨13713612278668718647042693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73139265486233166117561029 13713612278668718647042693)
                  ·
                    refine ⟨2571302302250384746320505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13713612278668718647042693 2571302302250384746320505)
                    ·
                      refine ⟨1928476726687788559740379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2571302302250384746320505 1928476726687788559740379)
                      ·
                        rfl

theorem cell23_3755695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 4, 4, 2].length) (baseStart_3755695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3755695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3755695 prefixEnd_3755695 := by exact prefixLift 3755695
  have htrace : WordTrace (prefixWord ++ tailWord_3755695) baseStart_3755695 baseEnd_3755695 := by
    simpa [prefixWord, tailWord_3755695, baseEnd_3755695] using wordTrace_append hprefix tailTrace_3755695
  have hstable : (prefixWord ++ tailWord_3755695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3755695).length < 2 ^ (prefixWord ++ tailWord_3755695).sum := by decide
  have hdescent : baseEnd_3755695 < baseStart_3755695 := by decide
  rcases family_descends (prefixWord ++ tailWord_3755695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3755698 : List Nat := [3, 2, 1, 1, 1, 2, 2, 1, 2, 3, 5]
def baseStart_3755698 : Nat := 118140960795 + 3755698 * 2 ^ 59
def prefixEnd_3755698 : Nat := 4983230072969 + 3 ^ 40 * 3755698 * 2
def baseEnd_3755698 : Nat := 1928478267129752048002865

theorem tailTrace_3755698 : CollatzResearch.WordTrace tailWord_3755698 prefixEnd_3755698 1928478267129752048002865 := by
  unfold tailWord_3755698
  simp only [CollatzResearch.WordTrace]
  refine ⟨34245389886938760749320937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91321039698503361998189165 34245389886938760749320937)
  ·
    refine ⟨25684042415204070561990703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34245389886938760749320937 25684042415204070561990703)
    ·
      refine ⟨38526063622806105842986055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25684042415204070561990703 38526063622806105842986055)
      ·
        refine ⟨57789095434209158764479083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38526063622806105842986055 57789095434209158764479083)
        ·
          refine ⟨86683643151313738146718625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57789095434209158764479083 86683643151313738146718625)
          ·
            refine ⟨65012732363485303610038969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86683643151313738146718625 65012732363485303610038969)
            ·
              refine ⟨48759549272613977707529227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65012732363485303610038969 48759549272613977707529227)
              ·
                refine ⟨73139323908920966561293841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48759549272613977707529227 73139323908920966561293841)
                ·
                  refine ⟨54854492931690724920970381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73139323908920966561293841 54854492931690724920970381)
                  ·
                    refine ⟨20570434849384021845363893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54854492931690724920970381 20570434849384021845363893)
                    ·
                      refine ⟨1928478267129752048002865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20570434849384021845363893 1928478267129752048002865)
                      ·
                        rfl

theorem cell23_3755698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 2, 3, 5].length) (baseStart_3755698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3755698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3755698 prefixEnd_3755698 := by exact prefixLift 3755698
  have htrace : WordTrace (prefixWord ++ tailWord_3755698) baseStart_3755698 baseEnd_3755698 := by
    simpa [prefixWord, tailWord_3755698, baseEnd_3755698] using wordTrace_append hprefix tailTrace_3755698
  have hstable : (prefixWord ++ tailWord_3755698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3755698).length < 2 ^ (prefixWord ++ tailWord_3755698).sum := by decide
  have hdescent : baseEnd_3755698 < baseStart_3755698 := by decide
  rcases family_descends (prefixWord ++ tailWord_3755698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3755705 : List Nat := [1, 2, 1, 4, 1, 1, 3, 3, 3, 4]
def baseStart_3755705 : Nat := 118140960795 + 3755705 * 2 ^ 59
def prefixEnd_3755705 : Nat := 4983230072969 + 3 ^ 40 * 3755705 * 2
def baseEnd_3755705 : Nat := 642827287164777840205111

theorem tailTrace_3755705 : CollatzResearch.WordTrace tailWord_3755705 prefixEnd_3755705 642827287164777840205111 := by
  unfold tailWord_3755705
  simp only [CollatzResearch.WordTrace]
  refine ⟨136981814858729683192788569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91321209905819788795192379 136981814858729683192788569)
  ·
    refine ⟨102736361144047262394591427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136981814858729683192788569 102736361144047262394591427)
    ·
      refine ⟨154104541716070893591887141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102736361144047262394591427 154104541716070893591887141)
      ·
        refine ⟨28894601571763292548478839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 154104541716070893591887141 28894601571763292548478839)
        ·
          refine ⟨43341902357644938822718259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28894601571763292548478839 43341902357644938822718259)
          ·
            refine ⟨65012853536467408234077389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43341902357644938822718259 65012853536467408234077389)
            ·
              refine ⟨24379820076175278087779021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65012853536467408234077389 24379820076175278087779021)
              ·
                refine ⟨9142432528565729282917133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24379820076175278087779021 9142432528565729282917133)
                ·
                  refine ⟨3428412198212148481093925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9142432528565729282917133 3428412198212148481093925)
                  ·
                    refine ⟨642827287164777840205111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3428412198212148481093925 642827287164777840205111)
                    ·
                      rfl

theorem cell23_3755705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 3, 3, 4].length) (baseStart_3755705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3755705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3755705 prefixEnd_3755705 := by exact prefixLift 3755705
  have htrace : WordTrace (prefixWord ++ tailWord_3755705) baseStart_3755705 baseEnd_3755705 := by
    simpa [prefixWord, tailWord_3755705, baseEnd_3755705] using wordTrace_append hprefix tailTrace_3755705
  have hstable : (prefixWord ++ tailWord_3755705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3755705).length < 2 ^ (prefixWord ++ tailWord_3755705).sum := by decide
  have hdescent : baseEnd_3755705 < baseStart_3755705 := by decide
  rcases family_descends (prefixWord ++ tailWord_3755705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3755732 : List Nat := [2, 4, 1, 3, 1, 1, 2, 1, 1, 4, 3]
def baseStart_3755732 : Nat := 118140960795 + 3755732 * 2 ^ 59
def prefixEnd_3755732 : Nat := 4983230072969 + 3 ^ 40 * 3755732 * 2
def baseEnd_3755732 : Nat := 1928495725472004914977709

theorem tailTrace_3755732 : CollatzResearch.WordTrace tailWord_3755732 prefixEnd_3755732 1928495725472004914977709 := by
  unfold tailWord_3755732
  simp only [CollatzResearch.WordTrace]
  refine ⟨68491399814815933402010725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91321866419754577869347633 68491399814815933402010725)
  ·
    refine ⟨12842137465277987512877011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68491399814815933402010725 12842137465277987512877011)
    ·
      refine ⟨19263206197916981269315517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12842137465277987512877011 19263206197916981269315517)
      ·
        refine ⟨7223702324218867975993319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19263206197916981269315517 7223702324218867975993319)
        ·
          refine ⟨10835553486328301963989979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7223702324218867975993319 10835553486328301963989979)
          ·
            refine ⟨16253330229492452945984969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10835553486328301963989979 16253330229492452945984969)
            ·
              refine ⟨12189997672119339709488727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16253330229492452945984969 12189997672119339709488727)
              ·
                refine ⟨18284996508179009564233091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12189997672119339709488727 18284996508179009564233091)
                ·
                  refine ⟨27427494762268514346349637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18284996508179009564233091 27427494762268514346349637)
                  ·
                    refine ⟨5142655267925346439940557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27427494762268514346349637 5142655267925346439940557)
                    ·
                      refine ⟨1928495725472004914977709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5142655267925346439940557 1928495725472004914977709)
                      ·
                        rfl

theorem cell23_3755732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_3755732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3755732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3755732 prefixEnd_3755732 := by exact prefixLift 3755732
  have htrace : WordTrace (prefixWord ++ tailWord_3755732) baseStart_3755732 baseEnd_3755732 := by
    simpa [prefixWord, tailWord_3755732, baseEnd_3755732] using wordTrace_append hprefix tailTrace_3755732
  have hstable : (prefixWord ++ tailWord_3755732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3755732).length < 2 ^ (prefixWord ++ tailWord_3755732).sum := by decide
  have hdescent : baseEnd_3755732 < baseStart_3755732 := by decide
  rcases family_descends (prefixWord ++ tailWord_3755732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3755772 : List Nat := [2, 2, 2, 1, 3, 1, 1, 2, 4, 3, 2]
def baseStart_3755772 : Nat := 118140960795 + 3755772 * 2 ^ 59
def prefixEnd_3755772 : Nat := 4983230072969 + 3 ^ 40 * 3755772 * 2
def baseEnd_3755772 : Nat := 1928516264698184758477525

theorem tailTrace_3755772 : CollatzResearch.WordTrace tailWord_3755772 prefixEnd_3755772 1928516264698184758477525 := by
  unfold tailWord_3755772
  simp only [CollatzResearch.WordTrace]
  refine ⟨68492129274743476817738785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91322839032991302423651713 68492129274743476817738785)
  ·
    refine ⟨51369096956057607613304089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68492129274743476817738785 51369096956057607613304089)
    ·
      refine ⟨38526822717043205709978067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51369096956057607613304089 38526822717043205709978067)
      ·
        refine ⟨57790234075564808564967101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38526822717043205709978067 57790234075564808564967101)
        ·
          refine ⟨21671337778336803211862663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57790234075564808564967101 21671337778336803211862663)
          ·
            refine ⟨32507006667505204817793995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21671337778336803211862663 32507006667505204817793995)
            ·
              refine ⟨48760510001257807226690993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32507006667505204817793995 48760510001257807226690993)
              ·
                refine ⟨36570382500943355420018245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48760510001257807226690993 36570382500943355420018245)
                ·
                  refine ⟨6856946718926879141253421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36570382500943355420018245 6856946718926879141253421)
                  ·
                    refine ⟨2571355019597579677970033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6856946718926879141253421 2571355019597579677970033)
                    ·
                      refine ⟨1928516264698184758477525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2571355019597579677970033 1928516264698184758477525)
                      ·
                        rfl

theorem cell23_3755772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 2, 4, 3, 2].length) (baseStart_3755772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3755772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3755772 prefixEnd_3755772 := by exact prefixLift 3755772
  have htrace : WordTrace (prefixWord ++ tailWord_3755772) baseStart_3755772 baseEnd_3755772 := by
    simpa [prefixWord, tailWord_3755772, baseEnd_3755772] using wordTrace_append hprefix tailTrace_3755772
  have hstable : (prefixWord ++ tailWord_3755772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3755772).length < 2 ^ (prefixWord ++ tailWord_3755772).sum := by decide
  have hdescent : baseEnd_3755772 < baseStart_3755772 := by decide
  rcases family_descends (prefixWord ++ tailWord_3755772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3755795 : List Nat := [1, 1, 1, 2, 1, 3, 2, 4, 4, 4]
def baseStart_3755795 : Nat := 118140960795 + 3755795 * 2 ^ 59
def prefixEnd_3755795 : Nat := 4983230072969 + 3 ^ 40 * 3755795 * 2
def baseEnd_3755795 : Nat := 642842691584412722829973

theorem tailTrace_3755795 : CollatzResearch.WordTrace tailWord_3755795 prefixEnd_3755795 642842691584412722829973 := by
  unfold tailWord_3755795
  simp only [CollatzResearch.WordTrace]
  refine ⟨136985097428403628563564839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91323398285602419042376559 136985097428403628563564839)
  ·
    refine ⟨205477646142605442845347259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136985097428403628563564839 205477646142605442845347259)
    ·
      refine ⟨308216469213908164268020889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205477646142605442845347259 308216469213908164268020889)
      ·
        refine ⟨231162351910431123201015667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 308216469213908164268020889 231162351910431123201015667)
        ·
          refine ⟨346743527865646684801523501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231162351910431123201015667 346743527865646684801523501)
          ·
            refine ⟨130028822949617506800571313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 346743527865646684801523501 130028822949617506800571313)
            ·
              refine ⟨97521617212213130100428485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130028822949617506800571313 97521617212213130100428485)
              ·
                refine ⟨18285303227289961893830341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 97521617212213130100428485 18285303227289961893830341)
                ·
                  refine ⟨3428494355116867855093189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18285303227289961893830341 3428494355116867855093189)
                  ·
                    refine ⟨642842691584412722829973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3428494355116867855093189 642842691584412722829973)
                    ·
                      rfl

theorem cell23_3755795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 4, 4, 4].length) (baseStart_3755795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3755795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3755795 prefixEnd_3755795 := by exact prefixLift 3755795
  have htrace : WordTrace (prefixWord ++ tailWord_3755795) baseStart_3755795 baseEnd_3755795 := by
    simpa [prefixWord, tailWord_3755795, baseEnd_3755795] using wordTrace_append hprefix tailTrace_3755795
  have hstable : (prefixWord ++ tailWord_3755795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3755795).length < 2 ^ (prefixWord ++ tailWord_3755795).sum := by decide
  have hdescent : baseEnd_3755795 < baseStart_3755795 := by decide
  rcases family_descends (prefixWord ++ tailWord_3755795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3755799 : List Nat := [1, 1, 3, 4, 2, 2, 3, 1, 1, 5]
def baseStart_3755799 : Nat := 118140960795 + 3755799 * 2 ^ 59
def prefixEnd_3755799 : Nat := 4983230072969 + 3 ^ 40 * 3755799 * 2
def baseEnd_3755799 : Nat := 642843376225285384279967

theorem tailTrace_3755799 : CollatzResearch.WordTrace tailWord_3755799 prefixEnd_3755799 642843376225285384279967 := by
  unfold tailWord_3755799
  simp only [CollatzResearch.WordTrace]
  refine ⟨136985243320389137246710451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91323495546926091497806967 136985243320389137246710451)
  ·
    refine ⟨205477864980583705870065677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136985243320389137246710451 205477864980583705870065677)
    ·
      refine ⟨77054199367718889701274629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205477864980583705870065677 77054199367718889701274629)
      ·
        refine ⟨14447662381447291818988993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77054199367718889701274629 14447662381447291818988993)
        ·
          refine ⟨10835746786085468864241745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14447662381447291818988993 10835746786085468864241745)
          ·
            refine ⟨8126810089564101648181309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10835746786085468864241745 8126810089564101648181309)
            ·
              refine ⟨3047553783586538118067991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8126810089564101648181309 3047553783586538118067991)
              ·
                refine ⟨4571330675379807177101987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3047553783586538118067991 4571330675379807177101987)
                ·
                  refine ⟨6856996013069710765652981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4571330675379807177101987 6856996013069710765652981)
                  ·
                    refine ⟨642843376225285384279967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6856996013069710765652981 642843376225285384279967)
                    ·
                      rfl

theorem cell23_3755799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 3, 1, 1, 5].length) (baseStart_3755799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3755799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3755799 prefixEnd_3755799 := by exact prefixLift 3755799
  have htrace : WordTrace (prefixWord ++ tailWord_3755799) baseStart_3755799 baseEnd_3755799 := by
    simpa [prefixWord, tailWord_3755799, baseEnd_3755799] using wordTrace_append hprefix tailTrace_3755799
  have hstable : (prefixWord ++ tailWord_3755799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3755799).length < 2 ^ (prefixWord ++ tailWord_3755799).sum := by decide
  have hdescent : baseEnd_3755799 < baseStart_3755799 := by decide
  rcases family_descends (prefixWord ++ tailWord_3755799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3755813 : List Nat := [1, 3, 1, 2, 3, 4, 2, 2, 1, 1, 3]
def baseStart_3755813 : Nat := 118140960795 + 3755813 * 2 ^ 59
def prefixEnd_3755813 : Nat := 4983230072969 + 3 ^ 40 * 3755813 * 2
def baseEnd_3755813 : Nat := 1928537317405019098064837

theorem tailTrace_3755813 : CollatzResearch.WordTrace tailWord_3755813 prefixEnd_3755813 1928537317405019098064837 := by
  unfold tailWord_3755813
  simp only [CollatzResearch.WordTrace]
  refine ⟨136985753942338417637720093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91323835961558945091813395 136985753942338417637720093)
  ·
    refine ⟨51369657728376906614145035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136985753942338417637720093 51369657728376906614145035)
    ·
      refine ⟨77054486592565359921217553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51369657728376906614145035 77054486592565359921217553)
      ·
        refine ⟨57790864944424019940913165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77054486592565359921217553 57790864944424019940913165)
        ·
          refine ⟨21671574354159007477842437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57790864944424019940913165 21671574354159007477842437)
          ·
            refine ⟨4063420191404813902095457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21671574354159007477842437 4063420191404813902095457)
            ·
              refine ⟨3047565143553610426571593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4063420191404813902095457 3047565143553610426571593)
              ·
                refine ⟨2285673857665207819928695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3047565143553610426571593 2285673857665207819928695)
                ·
                  refine ⟨3428510786497811729893043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2285673857665207819928695 3428510786497811729893043)
                  ·
                    refine ⟨5142766179746717594839565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3428510786497811729893043 5142766179746717594839565)
                    ·
                      refine ⟨1928537317405019098064837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5142766179746717594839565 1928537317405019098064837)
                      ·
                        rfl

theorem cell23_3755813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 2, 2, 1, 1, 3].length) (baseStart_3755813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3755813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3755813 prefixEnd_3755813 := by exact prefixLift 3755813
  have htrace : WordTrace (prefixWord ++ tailWord_3755813) baseStart_3755813 baseEnd_3755813 := by
    simpa [prefixWord, tailWord_3755813, baseEnd_3755813] using wordTrace_append hprefix tailTrace_3755813
  have hstable : (prefixWord ++ tailWord_3755813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3755813).length < 2 ^ (prefixWord ++ tailWord_3755813).sum := by decide
  have hdescent : baseEnd_3755813 < baseStart_3755813 := by decide
  rcases family_descends (prefixWord ++ tailWord_3755813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3755825 : List Nat := [1, 2, 2, 3, 2, 2, 3, 8]
def baseStart_3755825 : Nat := 118140960795 + 3755825 * 2 ^ 59
def prefixEnd_3755825 : Nat := 4983230072969 + 3 ^ 40 * 3755825 * 2
def baseEnd_3755825 : Nat := 71427536265661964856103

theorem tailTrace_3755825 : CollatzResearch.WordTrace tailWord_3755825 prefixEnd_3755825 71427536265661964856103 := by
  unfold tailWord_3755825
  simp only [CollatzResearch.WordTrace]
  refine ⟨136986191618294943687156929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91324127745529962458104619 136986191618294943687156929)
  ·
    refine ⟨102739643713721207765367697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136986191618294943687156929 102739643713721207765367697)
    ·
      refine ⟨77054732785290905824025773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102739643713721207765367697 77054732785290905824025773)
      ·
        refine ⟨28895524794484089684009665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77054732785290905824025773 28895524794484089684009665)
        ·
          refine ⟨21671643595863067263007249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28895524794484089684009665 21671643595863067263007249)
          ·
            refine ⟨16253732696897300447255437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21671643595863067263007249 16253732696897300447255437)
            ·
              refine ⟨6095149761336487667720789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16253732696897300447255437 6095149761336487667720789)
              ·
                refine ⟨71427536265661964856103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6095149761336487667720789 71427536265661964856103)
                ·
                  rfl

theorem cell23_3755825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 3, 8].length) (baseStart_3755825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3755825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3755825 prefixEnd_3755825 := by exact prefixLift 3755825
  have htrace : WordTrace (prefixWord ++ tailWord_3755825) baseStart_3755825 baseEnd_3755825 := by
    simpa [prefixWord, tailWord_3755825, baseEnd_3755825] using wordTrace_append hprefix tailTrace_3755825
  have hstable : (prefixWord ++ tailWord_3755825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3755825).length < 2 ^ (prefixWord ++ tailWord_3755825).sum := by decide
  have hdescent : baseEnd_3755825 < baseStart_3755825 := by decide
  rcases family_descends (prefixWord ++ tailWord_3755825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3755832 : List Nat := [2, 1, 2, 1, 3, 4, 2, 1, 1, 2, 4]
def baseStart_3755832 : Nat := 118140960795 + 3755832 * 2 ^ 59
def prefixEnd_3755832 : Nat := 4983230072969 + 3 ^ 40 * 3755832 * 2
def baseEnd_3755832 : Nat := 1928547073537454523727249

theorem tailTrace_3755832 : CollatzResearch.WordTrace tailWord_3755832 prefixEnd_3755832 1928547073537454523727249 := by
  unfold tailWord_3755832
  simp only [CollatzResearch.WordTrace]
  refine ⟨68493223464634791941330875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91324297952846389255107833 68493223464634791941330875)
  ·
    refine ⟨102739835196952187911996313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68493223464634791941330875 102739835196952187911996313)
    ·
      refine ⟨77054876397714140933997235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102739835196952187911996313 77054876397714140933997235)
      ·
        refine ⟨115582314596571211400995853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77054876397714140933997235 115582314596571211400995853)
        ·
          refine ⟨43343367973714204275373445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115582314596571211400995853 43343367973714204275373445)
          ·
            refine ⟨8126881495071413301632521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43343367973714204275373445 8126881495071413301632521)
            ·
              refine ⟨6095161121303559976224391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8126881495071413301632521 6095161121303559976224391)
              ·
                refine ⟨9142741681955339964336587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6095161121303559976224391 9142741681955339964336587)
                ·
                  refine ⟨13714112522933009946504881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9142741681955339964336587 13714112522933009946504881)
                  ·
                    refine ⟨10285584392199757459878661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13714112522933009946504881 10285584392199757459878661)
                    ·
                      refine ⟨1928547073537454523727249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10285584392199757459878661 1928547073537454523727249)
                      ·
                        rfl

theorem cell23_3755832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 2, 1, 1, 2, 4].length) (baseStart_3755832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3755832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3755832 prefixEnd_3755832 := by exact prefixLift 3755832
  have htrace : WordTrace (prefixWord ++ tailWord_3755832) baseStart_3755832 baseEnd_3755832 := by
    simpa [prefixWord, tailWord_3755832, baseEnd_3755832] using wordTrace_append hprefix tailTrace_3755832
  have hstable : (prefixWord ++ tailWord_3755832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3755832).length < 2 ^ (prefixWord ++ tailWord_3755832).sum := by decide
  have hdescent : baseEnd_3755832 < baseStart_3755832 := by decide
  rcases family_descends (prefixWord ++ tailWord_3755832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3755853 : List Nat := [1, 6, 1, 2, 1, 3, 2, 1, 1, 1, 4]
def baseStart_3755853 : Nat := 118140960795 + 3755853 * 2 ^ 59
def prefixEnd_3755853 : Nat := 4983230072969 + 3 ^ 40 * 3755853 * 2
def baseEnd_3755853 : Nat := 1928557856631198941564653

theorem tailTrace_3755853 : CollatzResearch.WordTrace tailWord_3755853 prefixEnd_3755853 1928557856631198941564653 := by
  unfold tailWord_3755853
  simp only [CollatzResearch.WordTrace]
  refine ⟨136987212862193504469176213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91324808574795669646117475 136987212862193504469176213)
  ·
    refine ⟨6421275602915320521992635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 136987212862193504469176213 6421275602915320521992635)
    ·
      refine ⟨9631913404372980782988953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6421275602915320521992635 9631913404372980782988953)
      ·
        refine ⟨7223935053279735587241715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9631913404372980782988953 7223935053279735587241715)
        ·
          refine ⟨10835902579919603380862573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7223935053279735587241715 10835902579919603380862573)
          ·
            refine ⟨4063463467469851267823465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10835902579919603380862573 4063463467469851267823465)
            ·
              refine ⟨3047597600602388450867599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4063463467469851267823465 3047597600602388450867599)
              ·
                refine ⟨4571396400903582676301399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3047597600602388450867599 4571396400903582676301399)
                ·
                  refine ⟨6857094601355374014452099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4571396400903582676301399 6857094601355374014452099)
                  ·
                    refine ⟨10285641902033061021678149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6857094601355374014452099 10285641902033061021678149)
                    ·
                      refine ⟨1928557856631198941564653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10285641902033061021678149 1928557856631198941564653)
                      ·
                        rfl

theorem cell23_3755853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 2, 1, 1, 1, 4].length) (baseStart_3755853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3755853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3755853 prefixEnd_3755853 := by exact prefixLift 3755853
  have htrace : WordTrace (prefixWord ++ tailWord_3755853) baseStart_3755853 baseEnd_3755853 := by
    simpa [prefixWord, tailWord_3755853, baseEnd_3755853] using wordTrace_append hprefix tailTrace_3755853
  have hstable : (prefixWord ++ tailWord_3755853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3755853).length < 2 ^ (prefixWord ++ tailWord_3755853).sum := by decide
  have hdescent : baseEnd_3755853 < baseStart_3755853 := by decide
  rcases family_descends (prefixWord ++ tailWord_3755853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3755886 : List Nat := [4, 1, 2, 3, 1, 3, 1, 1, 1, 3, 3]
def baseStart_3755886 : Nat := 118140960795 + 3755886 * 2 ^ 59
def prefixEnd_3755886 : Nat := 4983230072969 + 3 ^ 40 * 3755886 * 2
def baseEnd_3755886 : Nat := 1928574801492797312452001

theorem tailTrace_3755886 : CollatzResearch.WordTrace tailWord_3755886 prefixEnd_3755886 1928574801492797312452001 := by
  unfold tailWord_3755886
  simp only [CollatzResearch.WordTrace]
  refine ⟨17123552058884243888140939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91325610980715967403418341 17123552058884243888140939)
  ·
    refine ⟨25685328088326365832211409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17123552058884243888140939 25685328088326365832211409)
    ·
      refine ⟨19263996066244774374158557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25685328088326365832211409 19263996066244774374158557)
      ·
        refine ⟨7223998524841790390309459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19263996066244774374158557 7223998524841790390309459)
        ·
          refine ⟨10835997787262685585464189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7223998524841790390309459 10835997787262685585464189)
          ·
            refine ⟨4063499170223507094549071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10835997787262685585464189 4063499170223507094549071)
            ·
              refine ⟨6095248755335260641823607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4063499170223507094549071 6095248755335260641823607)
              ·
                refine ⟨9142873133002890962735411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6095248755335260641823607 9142873133002890962735411)
                ·
                  refine ⟨13714309699504336444103117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9142873133002890962735411 13714309699504336444103117)
                  ·
                    refine ⟨5142866137314126166538669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13714309699504336444103117 5142866137314126166538669)
                    ·
                      refine ⟨1928574801492797312452001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5142866137314126166538669 1928574801492797312452001)
                      ·
                        rfl

theorem cell23_3755886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_3755886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3755886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3755886 prefixEnd_3755886 := by exact prefixLift 3755886
  have htrace : WordTrace (prefixWord ++ tailWord_3755886) baseStart_3755886 baseEnd_3755886 := by
    simpa [prefixWord, tailWord_3755886, baseEnd_3755886] using wordTrace_append hprefix tailTrace_3755886
  have hstable : (prefixWord ++ tailWord_3755886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3755886).length < 2 ^ (prefixWord ++ tailWord_3755886).sum := by decide
  have hdescent : baseEnd_3755886 < baseStart_3755886 := by decide
  rcases family_descends (prefixWord ++ tailWord_3755886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3755909 : List Nat := [1, 3, 1, 1, 3, 2, 1, 1, 6, 2, 2]
def baseStart_3755909 : Nat := 118140960795 + 3755909 * 2 ^ 59
def prefixEnd_3755909 : Nat := 4983230072969 + 3 ^ 40 * 3755909 * 2
def baseEnd_3755909 : Nat := 1928586611547850722464395

theorem tailTrace_3755909 : CollatzResearch.WordTrace tailWord_3755909 prefixEnd_3755909 1928586611547850722464395 := by
  unfold tailWord_3755909
  simp only [CollatzResearch.WordTrace]
  refine ⟨136989255349990626033214781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91326170233327084022143187 136989255349990626033214781)
  ·
    refine ⟨51370970756246484762455543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136989255349990626033214781 51370970756246484762455543)
    ·
      refine ⟨77056456134369727143683315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51370970756246484762455543 77056456134369727143683315)
      ·
        refine ⟨115584684201554590715524973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77056456134369727143683315 115584684201554590715524973)
        ·
          refine ⟨43344256575582971518321865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115584684201554590715524973 43344256575582971518321865)
          ·
            refine ⟨32508192431687228638741399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43344256575582971518321865 32508192431687228638741399)
            ·
              refine ⟨48762288647530842958112099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32508192431687228638741399 48762288647530842958112099)
              ·
                refine ⟨73143432971296264437168149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48762288647530842958112099 73143432971296264437168149)
                ·
                  refine ⟨3428598420529512395492257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 73143432971296264437168149 3428598420529512395492257)
                  ·
                    refine ⟨2571448815397134296619193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3428598420529512395492257 2571448815397134296619193)
                    ·
                      refine ⟨1928586611547850722464395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2571448815397134296619193 1928586611547850722464395)
                      ·
                        rfl

theorem cell23_3755909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 6, 2, 2].length) (baseStart_3755909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3755909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3755909 prefixEnd_3755909 := by exact prefixLift 3755909
  have htrace : WordTrace (prefixWord ++ tailWord_3755909) baseStart_3755909 baseEnd_3755909 := by
    simpa [prefixWord, tailWord_3755909, baseEnd_3755909] using wordTrace_append hprefix tailTrace_3755909
  have hstable : (prefixWord ++ tailWord_3755909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3755909).length < 2 ^ (prefixWord ++ tailWord_3755909).sum := by decide
  have hdescent : baseEnd_3755909 < baseStart_3755909 := by decide
  rcases family_descends (prefixWord ++ tailWord_3755909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3755925 : List Nat := [1, 3, 2, 1, 1, 3, 1, 1, 1, 2, 7]
def baseStart_3755925 : Nat := 118140960795 + 3755925 * 2 ^ 59
def prefixEnd_3755925 : Nat := 4983230072969 + 3 ^ 40 * 3755925 * 2
def baseEnd_3755925 : Nat := 1928594827238322659864321

theorem tailTrace_3755925 : CollatzResearch.WordTrace tailWord_3755925 prefixEnd_3755925 1928594827238322659864321 := by
  unfold tailWord_3755925
  simp only [CollatzResearch.WordTrace]
  refine ⟨136989838917932660765797229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91326559278621773843864819 136989838917932660765797229)
  ·
    refine ⟨51371189594224747787173961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136989838917932660765797229 51371189594224747787173961)
    ·
      refine ⟨38528392195668560840380471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51371189594224747787173961 38528392195668560840380471)
      ·
        refine ⟨57792588293502841260570707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38528392195668560840380471 57792588293502841260570707)
        ·
          refine ⟨86688882440254261890856061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57792588293502841260570707 86688882440254261890856061)
          ·
            refine ⟨32508330915095348209071023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86688882440254261890856061 32508330915095348209071023)
            ·
              refine ⟨48762496372643022313606535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32508330915095348209071023 48762496372643022313606535)
              ·
                refine ⟨73143744558964533470409803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48762496372643022313606535 73143744558964533470409803)
                ·
                  refine ⟨109715616838446800205614705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73143744558964533470409803 109715616838446800205614705)
                  ·
                    refine ⟨82286712628835100154211029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 109715616838446800205614705 82286712628835100154211029)
                    ·
                      refine ⟨1928594827238322659864321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 82286712628835100154211029 1928594827238322659864321)
                      ·
                        rfl

theorem cell23_3755925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 2, 7].length) (baseStart_3755925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3755925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3755925 prefixEnd_3755925 := by exact prefixLift 3755925
  have htrace : WordTrace (prefixWord ++ tailWord_3755925) baseStart_3755925 baseEnd_3755925 := by
    simpa [prefixWord, tailWord_3755925, baseEnd_3755925] using wordTrace_append hprefix tailTrace_3755925
  have hstable : (prefixWord ++ tailWord_3755925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3755925).length < 2 ^ (prefixWord ++ tailWord_3755925).sum := by decide
  have hdescent : baseEnd_3755925 < baseStart_3755925 := by decide
  rcases family_descends (prefixWord ++ tailWord_3755925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3755943 : List Nat := [1, 1, 6, 1, 2, 2, 1, 3, 2, 2, 2]
def baseStart_3755943 : Nat := 118140960795 + 3755943 * 2 ^ 59
def prefixEnd_3755943 : Nat := 4983230072969 + 3 ^ 40 * 3755943 * 2
def baseEnd_3755943 : Nat := 1928604069890103589439239

theorem tailTrace_3755943 : CollatzResearch.WordTrace tailWord_3755943 prefixEnd_3755943 1928604069890103589439239 := by
  unfold tailWord_3755943
  simp only [CollatzResearch.WordTrace]
  refine ⟨136990495431867449839952483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91326996954578299893301655 136990495431867449839952483)
  ·
    refine ⟨205485743147801174759928725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136990495431867449839952483 205485743147801174759928725)
    ·
      refine ⟨9632144210053180066871659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 205485743147801174759928725 9632144210053180066871659)
      ·
        refine ⟨14448216315079770100307489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9632144210053180066871659 14448216315079770100307489)
        ·
          refine ⟨10836162236309827575230617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14448216315079770100307489 10836162236309827575230617)
          ·
            refine ⟨8127121677232370681422963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10836162236309827575230617 8127121677232370681422963)
            ·
              refine ⟨12190682515848556022134445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8127121677232370681422963 12190682515848556022134445)
              ·
                refine ⟨4571505943443208508300417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12190682515848556022134445 4571505943443208508300417)
                ·
                  refine ⟨3428629457582406381225313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4571505943443208508300417 3428629457582406381225313)
                  ·
                    refine ⟨2571472093186804785918985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3428629457582406381225313 2571472093186804785918985)
                    ·
                      refine ⟨1928604069890103589439239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2571472093186804785918985 1928604069890103589439239)
                      ·
                        rfl

theorem cell23_3755943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 3, 2, 2, 2].length) (baseStart_3755943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3755943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3755943 prefixEnd_3755943 := by exact prefixLift 3755943
  have htrace : WordTrace (prefixWord ++ tailWord_3755943) baseStart_3755943 baseEnd_3755943 := by
    simpa [prefixWord, tailWord_3755943, baseEnd_3755943] using wordTrace_append hprefix tailTrace_3755943
  have hstable : (prefixWord ++ tailWord_3755943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3755943).length < 2 ^ (prefixWord ++ tailWord_3755943).sum := by decide
  have hdescent : baseEnd_3755943 < baseStart_3755943 := by decide
  rcases family_descends (prefixWord ++ tailWord_3755943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3755945 : List Nat := [1, 2, 1, 1, 1, 1, 4, 4, 1, 7]
def baseStart_3755945 : Nat := 118140960795 + 3755945 * 2 ^ 59
def prefixEnd_3755945 : Nat := 4983230072969 + 3 ^ 40 * 3755945 * 2
def baseEnd_3755945 : Nat := 642868365617137527204743

theorem tailTrace_3755945 : CollatzResearch.WordTrace tailWord_3755945 prefixEnd_3755945 642868365617137527204743 := by
  unfold tailWord_3755945
  simp only [CollatzResearch.WordTrace]
  refine ⟨136990568377860204181525289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91327045585240136121016859 136990568377860204181525289)
  ·
    refine ⟨102742926283395153136143967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136990568377860204181525289 102742926283395153136143967)
    ·
      refine ⟨154114389425092729704215951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102742926283395153136143967 154114389425092729704215951)
      ·
        refine ⟨231171584137639094556323927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154114389425092729704215951 231171584137639094556323927)
        ·
          refine ⟨346757376206458641834485891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231171584137639094556323927 346757376206458641834485891)
          ·
            refine ⟨520136064309687962751728837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 346757376206458641834485891 520136064309687962751728837)
            ·
              refine ⟨97525512058066493015949157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 520136064309687962751728837 97525512058066493015949157)
              ·
                refine ⟨18286033510887467440490467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 97525512058066493015949157 18286033510887467440490467)
                ·
                  refine ⟨27429050266331201160735701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18286033510887467440490467 27429050266331201160735701)
                  ·
                    refine ⟨642868365617137527204743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27429050266331201160735701 642868365617137527204743)
                    ·
                      rfl

theorem cell23_3755945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 4, 1, 7].length) (baseStart_3755945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3755945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3755945 prefixEnd_3755945 := by exact prefixLift 3755945
  have htrace : WordTrace (prefixWord ++ tailWord_3755945) baseStart_3755945 baseEnd_3755945 := by
    simpa [prefixWord, tailWord_3755945, baseEnd_3755945] using wordTrace_append hprefix tailTrace_3755945
  have hstable : (prefixWord ++ tailWord_3755945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3755945).length < 2 ^ (prefixWord ++ tailWord_3755945).sum := by decide
  have hdescent : baseEnd_3755945 < baseStart_3755945 := by decide
  rcases family_descends (prefixWord ++ tailWord_3755945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3755955 : List Nat := [1, 1, 1, 2, 3, 1, 3, 2, 1, 1, 7]
def baseStart_3755955 : Nat := 118140960795 + 3755955 * 2 ^ 59
def prefixEnd_3755955 : Nat := 4983230072969 + 3 ^ 40 * 3755955 * 2
def baseEnd_3755955 : Nat := 1928610231657957542489183

theorem tailTrace_3755955 : CollatzResearch.WordTrace tailWord_3755955 prefixEnd_3755955 1928610231657957542489183 := by
  unfold tailWord_3755955
  simp only [CollatzResearch.WordTrace]
  refine ⟨136990933107823975889389319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91327288738549317259592879 136990933107823975889389319)
  ·
    refine ⟨205486399661735963834083979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136990933107823975889389319 205486399661735963834083979)
    ·
      refine ⟨308229599492603945751125969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205486399661735963834083979 308229599492603945751125969)
      ·
        refine ⟨231172199619452959313344477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 308229599492603945751125969 231172199619452959313344477)
        ·
          refine ⟨86689574857294859742504179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 231172199619452959313344477 86689574857294859742504179)
          ·
            refine ⟨130034362285942289613756269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86689574857294859742504179 130034362285942289613756269)
            ·
              refine ⟨48762885857228358605158601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 130034362285942289613756269 48762885857228358605158601)
              ·
                refine ⟨36572164392921268953868951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48762885857228358605158601 36572164392921268953868951)
                ·
                  refine ⟨54858246589381903430803427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36572164392921268953868951 54858246589381903430803427)
                  ·
                    refine ⟨82287369884072855146205141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54858246589381903430803427 82287369884072855146205141)
                    ·
                      refine ⟨1928610231657957542489183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 82287369884072855146205141 1928610231657957542489183)
                      ·
                        rfl

theorem cell23_3755955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 2, 1, 1, 7].length) (baseStart_3755955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3755955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3755955 prefixEnd_3755955 := by exact prefixLift 3755955
  have htrace : WordTrace (prefixWord ++ tailWord_3755955) baseStart_3755955 baseEnd_3755955 := by
    simpa [prefixWord, tailWord_3755955, baseEnd_3755955] using wordTrace_append hprefix tailTrace_3755955
  have hstable : (prefixWord ++ tailWord_3755955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3755955).length < 2 ^ (prefixWord ++ tailWord_3755955).sum := by decide
  have hdescent : baseEnd_3755955 < baseStart_3755955 := by decide
  rcases family_descends (prefixWord ++ tailWord_3755955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3755999 : List Nat := [1, 1, 2, 3, 4, 1, 1, 1, 1, 6, 2]
def baseStart_3755999 : Nat := 118140960795 + 3755999 * 2 ^ 59
def prefixEnd_3755999 : Nat := 4983230072969 + 3 ^ 40 * 3755999 * 2
def baseEnd_3755999 : Nat := 1928632824806755370338981

theorem tailTrace_3755999 : CollatzResearch.WordTrace tailWord_3755999 prefixEnd_3755999 1928632824806755370338981 := by
  unfold tailWord_3755999
  simp only [CollatzResearch.WordTrace]
  refine ⟨136992537919664571403991051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91328358613109714269327367 136992537919664571403991051)
  ·
    refine ⟨205488806879496857105986577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136992537919664571403991051 205488806879496857105986577)
    ·
      refine ⟨154116605159622642829489933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205488806879496857105986577 154116605159622642829489933)
      ·
        refine ⟨57793726934858491061058725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154116605159622642829489933 57793726934858491061058725)
        ·
          refine ⟨10836323800285967073948511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57793726934858491061058725 10836323800285967073948511)
          ·
            refine ⟨16254485700428950610922767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10836323800285967073948511 16254485700428950610922767)
            ·
              refine ⟨24381728550643425916384151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16254485700428950610922767 24381728550643425916384151)
              ·
                refine ⟨36572592825965138874576227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24381728550643425916384151 36572592825965138874576227)
                ·
                  refine ⟨54858889238947708311864341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36572592825965138874576227 54858889238947708311864341)
                  ·
                    refine ⟨2571510433075673827118641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 54858889238947708311864341 2571510433075673827118641)
                    ·
                      refine ⟨1928632824806755370338981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2571510433075673827118641 1928632824806755370338981)
                      ·
                        rfl

theorem cell23_3755999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 1, 6, 2].length) (baseStart_3755999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3755999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3755999 prefixEnd_3755999 := by exact prefixLift 3755999
  have htrace : WordTrace (prefixWord ++ tailWord_3755999) baseStart_3755999 baseEnd_3755999 := by
    simpa [prefixWord, tailWord_3755999, baseEnd_3755999] using wordTrace_append hprefix tailTrace_3755999
  have hstable : (prefixWord ++ tailWord_3755999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3755999).length < 2 ^ (prefixWord ++ tailWord_3755999).sum := by decide
  have hdescent : baseEnd_3755999 < baseStart_3755999 := by decide
  rcases family_descends (prefixWord ++ tailWord_3755999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3756013 : List Nat := [1, 5, 1, 4, 1, 2, 1, 1, 2, 5]
def baseStart_3756013 : Nat := 118140960795 + 3756013 * 2 ^ 59
def prefixEnd_3756013 : Nat := 4983230072969 + 3 ^ 40 * 3756013 * 2
def baseEnd_3756013 : Nat := 642880004511972771854639

theorem tailTrace_3756013 : CollatzResearch.WordTrace tailWord_3756013 prefixEnd_3756013 642880004511972771854639 := by
  unfold tailWord_3756013
  simp only [CollatzResearch.WordTrace]
  refine ⟨136993048541613851795000693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91328699027742567863333795 136993048541613851795000693)
  ·
    refine ⟨12843098300776298605781315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 136993048541613851795000693 12843098300776298605781315)
    ·
      refine ⟨19264647451164447908671973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12843098300776298605781315 19264647451164447908671973)
      ·
        refine ⟨3612121397093333982875995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19264647451164447908671973 3612121397093333982875995)
        ·
          refine ⟨5418182095640000974313993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3612121397093333982875995 5418182095640000974313993)
          ·
            refine ⟨4063636571730000730735495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5418182095640000974313993 4063636571730000730735495)
            ·
              refine ⟨6095454857595001096103243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4063636571730000730735495 6095454857595001096103243)
              ·
                refine ⟨9143182286392501644154865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6095454857595001096103243 9143182286392501644154865)
                ·
                  refine ⟨6857386714794376233116149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9143182286392501644154865 6857386714794376233116149)
                  ·
                    refine ⟨642880004511972771854639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6857386714794376233116149 642880004511972771854639)
                    ·
                      rfl

theorem cell23_3756013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 1, 1, 2, 5].length) (baseStart_3756013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3756013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3756013 prefixEnd_3756013 := by exact prefixLift 3756013
  have htrace : WordTrace (prefixWord ++ tailWord_3756013) baseStart_3756013 baseEnd_3756013 := by
    simpa [prefixWord, tailWord_3756013, baseEnd_3756013] using wordTrace_append hprefix tailTrace_3756013
  have hstable : (prefixWord ++ tailWord_3756013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3756013).length < 2 ^ (prefixWord ++ tailWord_3756013).sum := by decide
  have hdescent : baseEnd_3756013 < baseStart_3756013 := by decide
  rcases family_descends (prefixWord ++ tailWord_3756013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3756039 : List Nat := [1, 1, 4, 3, 1, 2, 3, 2, 6]
def baseStart_3756039 : Nat := 118140960795 + 3756039 * 2 ^ 59
def prefixEnd_3756039 : Nat := 4983230072969 + 3 ^ 40 * 3756039 * 2
def baseEnd_3756039 : Nat := 214294818225881690426533

theorem tailTrace_3756039 : CollatzResearch.WordTrace tailWord_3756039 prefixEnd_3756039 214294818225881690426533 := by
  unfold tailWord_3756039
  simp only [CollatzResearch.WordTrace]
  refine ⟨136993996839519658235447171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91329331226346438823631447 136993996839519658235447171)
  ·
    refine ⟨205490995259279487353170757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136993996839519658235447171 205490995259279487353170757)
    ·
      refine ⟨38529561611114903878719517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 205490995259279487353170757 38529561611114903878719517)
      ·
        refine ⟨14448585604168088954519819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38529561611114903878719517 14448585604168088954519819)
        ·
          refine ⟨21672878406252133431779729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14448585604168088954519819 21672878406252133431779729)
          ·
            refine ⟨16254658804689100073834797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21672878406252133431779729 16254658804689100073834797)
            ·
              refine ⟨6095497051758412527688049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16254658804689100073834797 6095497051758412527688049)
              ·
                refine ⟨4571622788818809395766037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6095497051758412527688049 4571622788818809395766037)
                ·
                  refine ⟨214294818225881690426533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4571622788818809395766037 214294818225881690426533)
                  ·
                    rfl

theorem cell23_3756039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 3, 2, 6].length) (baseStart_3756039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3756039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3756039 prefixEnd_3756039 := by exact prefixLift 3756039
  have htrace : WordTrace (prefixWord ++ tailWord_3756039) baseStart_3756039 baseEnd_3756039 := by
    simpa [prefixWord, tailWord_3756039, baseEnd_3756039] using wordTrace_append hprefix tailTrace_3756039
  have hstable : (prefixWord ++ tailWord_3756039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3756039).length < 2 ^ (prefixWord ++ tailWord_3756039).sum := by decide
  have hdescent : baseEnd_3756039 < baseStart_3756039 := by decide
  rcases family_descends (prefixWord ++ tailWord_3756039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3756059 : List Nat := [1, 1, 1, 1, 1, 1, 3, 3, 6, 3, 2]
def baseStart_3756059 : Nat := 118140960795 + 3756059 * 2 ^ 59
def prefixEnd_3756059 : Nat := 4983230072969 + 3 ^ 40 * 3756059 * 2
def baseEnd_3756059 : Nat := 1928663633646025135588705

theorem tailTrace_3756059 : CollatzResearch.WordTrace tailWord_3756059 prefixEnd_3756059 1928663633646025135588705 := by
  unfold tailWord_3756059
  simp only [CollatzResearch.WordTrace]
  refine ⟨136994726299447201651175231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91329817532964801100783487 136994726299447201651175231)
  ·
    refine ⟨205492089449170802476762847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136994726299447201651175231 205492089449170802476762847)
    ·
      refine ⟨308238134173756203715144271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205492089449170802476762847 308238134173756203715144271)
      ·
        refine ⟨462357201260634305572716407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308238134173756203715144271 462357201260634305572716407)
        ·
          refine ⟨693535801890951458359074611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 462357201260634305572716407 693535801890951458359074611)
          ·
            refine ⟨1040303702836427187538611917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 693535801890951458359074611 1040303702836427187538611917)
            ·
              refine ⟨390113888563660195326979469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1040303702836427187538611917 390113888563660195326979469)
              ·
                refine ⟨146292708211372573247617301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 390113888563660195326979469 146292708211372573247617301)
                ·
                  refine ⟨6857470697408089370982061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 146292708211372573247617301 6857470697408089370982061)
                  ·
                    refine ⟨2571551511528033514118273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6857470697408089370982061 2571551511528033514118273)
                    ·
                      refine ⟨1928663633646025135588705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2571551511528033514118273 1928663633646025135588705)
                      ·
                        rfl

theorem cell23_3756059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 6, 3, 2].length) (baseStart_3756059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3756059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3756059 prefixEnd_3756059 := by exact prefixLift 3756059
  have htrace : WordTrace (prefixWord ++ tailWord_3756059) baseStart_3756059 baseEnd_3756059 := by
    simpa [prefixWord, tailWord_3756059, baseEnd_3756059] using wordTrace_append hprefix tailTrace_3756059
  have hstable : (prefixWord ++ tailWord_3756059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3756059).length < 2 ^ (prefixWord ++ tailWord_3756059).sum := by decide
  have hdescent : baseEnd_3756059 < baseStart_3756059 := by decide
  rcases family_descends (prefixWord ++ tailWord_3756059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3756066 : List Nat := [3, 3, 1, 1, 1, 2, 1, 4, 3, 1, 3]
def baseStart_3756066 : Nat := 118140960795 + 3756066 * 2 ^ 59
def prefixEnd_3756066 : Nat := 4983230072969 + 3 ^ 40 * 3756066 * 2
def baseEnd_3756066 : Nat := 1928667228010606608201173

theorem tailTrace_3756066 : CollatzResearch.WordTrace tailWord_3756066 prefixEnd_3756066 1928667228010606608201173 := by
  unfold tailWord_3756066
  simp only [CollatzResearch.WordTrace]
  refine ⟨34248745402605460461670013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91329987740281227897786701 34248745402605460461670013)
  ·
    refine ⟨12843279525977047673126255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34248745402605460461670013 12843279525977047673126255)
    ·
      refine ⟨19264919288965571509689383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12843279525977047673126255 19264919288965571509689383)
      ·
        refine ⟨28897378933448357264534075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19264919288965571509689383 28897378933448357264534075)
        ·
          refine ⟨43346068400172535896801113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28897378933448357264534075 43346068400172535896801113)
          ·
            refine ⟨32509551300129401922600835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43346068400172535896801113 32509551300129401922600835)
            ·
              refine ⟨48764326950194102883901253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32509551300129401922600835 48764326950194102883901253)
              ·
                refine ⟨9143311303161394290731485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48764326950194102883901253 9143311303161394290731485)
                ·
                  refine ⟨3428741738685522859024307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9143311303161394290731485 3428741738685522859024307)
                  ·
                    refine ⟨5143112608028284288536461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3428741738685522859024307 5143112608028284288536461)
                    ·
                      refine ⟨1928667228010606608201173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5143112608028284288536461 1928667228010606608201173)
                      ·
                        rfl

theorem cell23_3756066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 4, 3, 1, 3].length) (baseStart_3756066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3756066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3756066 prefixEnd_3756066 := by exact prefixLift 3756066
  have htrace : WordTrace (prefixWord ++ tailWord_3756066) baseStart_3756066 baseEnd_3756066 := by
    simpa [prefixWord, tailWord_3756066, baseEnd_3756066] using wordTrace_append hprefix tailTrace_3756066
  have hstable : (prefixWord ++ tailWord_3756066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3756066).length < 2 ^ (prefixWord ++ tailWord_3756066).sum := by decide
  have hdescent : baseEnd_3756066 < baseStart_3756066 := by decide
  rcases family_descends (prefixWord ++ tailWord_3756066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3756069 : List Nat := [1, 3, 1, 2, 2, 3, 1, 4, 1, 5]
def baseStart_3756069 : Nat := 118140960795 + 3756069 * 2 ^ 59
def prefixEnd_3756069 : Nat := 4983230072969 + 3 ^ 40 * 3756069 * 2
def baseEnd_3756069 : Nat := 642889589484190032154553

theorem tailTrace_3756069 : CollatzResearch.WordTrace tailWord_3756069 prefixEnd_3756069 642889589484190032154553 := by
  unfold tailWord_3756069
  simp only [CollatzResearch.WordTrace]
  refine ⟨136995091029410973359039261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91330060686273982239359507 136995091029410973359039261)
  ·
    refine ⟨51373159136029115009639723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136995091029410973359039261 51373159136029115009639723)
    ·
      refine ⟨77059738704043672514459585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51373159136029115009639723 77059738704043672514459585)
      ·
        refine ⟨57794804028032754385844689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77059738704043672514459585 57794804028032754385844689)
        ·
          refine ⟨43346103021024565789383517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57794804028032754385844689 43346103021024565789383517)
          ·
            refine ⟨16254788632884212171018819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43346103021024565789383517 16254788632884212171018819)
            ·
              refine ⟨24382182949326318256528229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16254788632884212171018819 24382182949326318256528229)
              ·
                refine ⟨4571659302998684673099043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24382182949326318256528229 4571659302998684673099043)
                ·
                  refine ⟨6857488954498027009648565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4571659302998684673099043 6857488954498027009648565)
                  ·
                    refine ⟨642889589484190032154553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6857488954498027009648565 642889589484190032154553)
                    ·
                      rfl

theorem cell23_3756069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 4, 1, 5].length) (baseStart_3756069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3756069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3756069 prefixEnd_3756069 := by exact prefixLift 3756069
  have htrace : WordTrace (prefixWord ++ tailWord_3756069) baseStart_3756069 baseEnd_3756069 := by
    simpa [prefixWord, tailWord_3756069, baseEnd_3756069] using wordTrace_append hprefix tailTrace_3756069
  have hstable : (prefixWord ++ tailWord_3756069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3756069).length < 2 ^ (prefixWord ++ tailWord_3756069).sum := by decide
  have hdescent : baseEnd_3756069 < baseStart_3756069 := by decide
  rcases family_descends (prefixWord ++ tailWord_3756069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3756083 : List Nat := [1, 1, 1, 2, 4, 1, 5, 3, 1, 1, 3]
def baseStart_3756083 : Nat := 118140960795 + 3756083 * 2 ^ 59
def prefixEnd_3756083 : Nat := 4983230072969 + 3 ^ 40 * 3756083 * 2
def baseEnd_3756083 : Nat := 1928675957181733041688595

theorem tailTrace_3756083 : CollatzResearch.WordTrace tailWord_3756083 prefixEnd_3756083 1928675957181733041688595 := by
  unfold tailWord_3756083
  simp only [CollatzResearch.WordTrace]
  refine ⟨136995601651360253750048903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91330401100906835833365935 136995601651360253750048903)
  ·
    refine ⟨205493402477040380625073355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136995601651360253750048903 205493402477040380625073355)
    ·
      refine ⟨308240103715560570937610033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205493402477040380625073355 308240103715560570937610033)
      ·
        refine ⟨231180077786670428203207525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 308240103715560570937610033 231180077786670428203207525)
        ·
          refine ⟨43346264585000705288101411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 231180077786670428203207525 43346264585000705288101411)
          ·
            refine ⟨65019396877501057932152117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43346264585000705288101411 65019396877501057932152117)
            ·
              refine ⟨6095568457265724181139261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65019396877501057932152117 6095568457265724181139261)
              ·
                refine ⟨2285838171474646567927223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6095568457265724181139261 2285838171474646567927223)
                ·
                  refine ⟨3428757257211969851890835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2285838171474646567927223 3428757257211969851890835)
                  ·
                    refine ⟨5143135885817954777836253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3428757257211969851890835 5143135885817954777836253)
                    ·
                      refine ⟨1928675957181733041688595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5143135885817954777836253 1928675957181733041688595)
                      ·
                        rfl

theorem cell23_3756083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 5, 3, 1, 1, 3].length) (baseStart_3756083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3756083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3756083 prefixEnd_3756083 := by exact prefixLift 3756083
  have htrace : WordTrace (prefixWord ++ tailWord_3756083) baseStart_3756083 baseEnd_3756083 := by
    simpa [prefixWord, tailWord_3756083, baseEnd_3756083] using wordTrace_append hprefix tailTrace_3756083
  have hstable : (prefixWord ++ tailWord_3756083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3756083).length < 2 ^ (prefixWord ++ tailWord_3756083).sum := by decide
  have hdescent : baseEnd_3756083 < baseStart_3756083 := by decide
  rcases family_descends (prefixWord ++ tailWord_3756083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3756086 : List Nat := [5, 1, 2, 1, 1, 1, 1, 5, 1, 5]
def baseStart_3756086 : Nat := 118140960795 + 3756086 * 2 ^ 59
def prefixEnd_3756086 : Nat := 4983230072969 + 3 ^ 40 * 3756086 * 2
def baseEnd_3756086 : Nat := 642892499207898843317027

theorem tailTrace_3756086 : CollatzResearch.WordTrace tailWord_3756086 prefixEnd_3756086 642892499207898843317027 := by
  unfold tailWord_3756086
  simp only [CollatzResearch.WordTrace]
  refine ⟨8562231941896836578900507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 91330474046899590174938741 8562231941896836578900507)
  ·
    refine ⟨12843347912845254868350761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8562231941896836578900507 12843347912845254868350761)
    ·
      refine ⟨9632510934633941151263071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12843347912845254868350761 9632510934633941151263071)
      ·
        refine ⟨14448766401950911726894607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9632510934633941151263071 14448766401950911726894607)
        ·
          refine ⟨21673149602926367590341911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14448766401950911726894607 21673149602926367590341911)
          ·
            refine ⟨32509724404389551385512867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21673149602926367590341911 32509724404389551385512867)
            ·
              refine ⟨48764586606584327078269301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32509724404389551385512867 48764586606584327078269301)
              ·
                refine ⟨4571679994367280663587747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48764586606584327078269301 4571679994367280663587747)
                ·
                  refine ⟨6857519991550920995381621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4571679994367280663587747 6857519991550920995381621)
                  ·
                    refine ⟨642892499207898843317027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6857519991550920995381621 642892499207898843317027)
                    ·
                      rfl

theorem cell23_3756086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 5, 1, 5].length) (baseStart_3756086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3756086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3756086 prefixEnd_3756086 := by exact prefixLift 3756086
  have htrace : WordTrace (prefixWord ++ tailWord_3756086) baseStart_3756086 baseEnd_3756086 := by
    simpa [prefixWord, tailWord_3756086, baseEnd_3756086] using wordTrace_append hprefix tailTrace_3756086
  have hstable : (prefixWord ++ tailWord_3756086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3756086).length < 2 ^ (prefixWord ++ tailWord_3756086).sum := by decide
  have hdescent : baseEnd_3756086 < baseStart_3756086 := by decide
  rcases family_descends (prefixWord ++ tailWord_3756086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3756143 : List Nat := [1, 1, 2, 1, 3, 5, 3, 1, 1, 2, 3]
def baseStart_3756143 : Nat := 118140960795 + 3756143 * 2 ^ 59
def prefixEnd_3756143 : Nat := 4983230072969 + 3 ^ 40 * 3756143 * 2
def baseEnd_3756143 : Nat := 1928706766021002806938319

theorem tailTrace_3756143 : CollatzResearch.WordTrace tailWord_3756143 prefixEnd_3756143 1928706766021002806938319 := by
  unfold tailWord_3756143
  simp only [CollatzResearch.WordTrace]
  refine ⟨136997790031142883997233083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91331860020761922664822055 136997790031142883997233083)
  ·
    refine ⟨205496685046714325995849625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136997790031142883997233083 205496685046714325995849625)
    ·
      refine ⟨154122513785035744496887219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205496685046714325995849625 154122513785035744496887219)
      ·
        refine ⟨231183770677553616745330829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154122513785035744496887219 231183770677553616745330829)
        ·
          refine ⟨86693914004082606279499061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 231183770677553616745330829 86693914004082606279499061)
          ·
            refine ⟨8127554437882744338703037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 86693914004082606279499061 8127554437882744338703037)
            ·
              refine ⟨3047832914206029127013639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8127554437882744338703037 3047832914206029127013639)
              ·
                refine ⟨4571749371309043690520459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3047832914206029127013639 4571749371309043690520459)
                ·
                  refine ⟨6857624056963565535780689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4571749371309043690520459 6857624056963565535780689)
                  ·
                    refine ⟨5143218042722674151835517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6857624056963565535780689 5143218042722674151835517)
                    ·
                      refine ⟨1928706766021002806938319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5143218042722674151835517 1928706766021002806938319)
                      ·
                        rfl

theorem cell23_3756143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 3, 1, 1, 2, 3].length) (baseStart_3756143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3756143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3756143 prefixEnd_3756143 := by exact prefixLift 3756143
  have htrace : WordTrace (prefixWord ++ tailWord_3756143) baseStart_3756143 baseEnd_3756143 := by
    simpa [prefixWord, tailWord_3756143, baseEnd_3756143] using wordTrace_append hprefix tailTrace_3756143
  have hstable : (prefixWord ++ tailWord_3756143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3756143).length < 2 ^ (prefixWord ++ tailWord_3756143).sum := by decide
  have hdescent : baseEnd_3756143 < baseStart_3756143 := by decide
  rcases family_descends (prefixWord ++ tailWord_3756143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3756157 : List Nat := [1, 4, 1, 1, 3, 2, 4, 2, 1, 2, 2]
def baseStart_3756157 : Nat := 118140960795 + 3756157 * 2 ^ 59
def prefixEnd_3756157 : Nat := 4983230072969 + 3 ^ 40 * 3756157 * 2
def baseEnd_3756157 : Nat := 1928713954750165752163255

theorem tailTrace_3756157 : CollatzResearch.WordTrace tailWord_3756157 prefixEnd_3756157 1928713954750165752163255 := by
  unfold tailWord_3756157
  simp only [CollatzResearch.WordTrace]
  refine ⟨136998300653092164388242725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91332200435394776258828483 136998300653092164388242725)
  ·
    refine ⟨25687181372454780822795511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136998300653092164388242725 25687181372454780822795511)
    ·
      refine ⟨38530772058682171234193267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25687181372454780822795511 38530772058682171234193267)
      ·
        refine ⟨57796158088023256851289901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38530772058682171234193267 57796158088023256851289901)
        ·
          refine ⟨21673559283008721319233713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57796158088023256851289901 21673559283008721319233713)
          ·
            refine ⟨16255169462256540989425285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21673559283008721319233713 16255169462256540989425285)
            ·
              refine ⟨3047844274173101435517241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16255169462256540989425285 3047844274173101435517241)
              ·
                refine ⟨2285883205629826076637931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3047844274173101435517241 2285883205629826076637931)
                ·
                  refine ⟨3428824808444739114956897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2285883205629826076637931 3428824808444739114956897)
                  ·
                    refine ⟨2571618606333554336217673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3428824808444739114956897 2571618606333554336217673)
                    ·
                      refine ⟨1928713954750165752163255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2571618606333554336217673 1928713954750165752163255)
                      ·
                        rfl

theorem cell23_3756157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 4, 2, 1, 2, 2].length) (baseStart_3756157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3756157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3756157 prefixEnd_3756157 := by exact prefixLift 3756157
  have htrace : WordTrace (prefixWord ++ tailWord_3756157) baseStart_3756157 baseEnd_3756157 := by
    simpa [prefixWord, tailWord_3756157, baseEnd_3756157] using wordTrace_append hprefix tailTrace_3756157
  have hstable : (prefixWord ++ tailWord_3756157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3756157).length < 2 ^ (prefixWord ++ tailWord_3756157).sum := by decide
  have hdescent : baseEnd_3756157 < baseStart_3756157 := by decide
  rcases family_descends (prefixWord ++ tailWord_3756157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3756219 : List Nat := [1, 1, 1, 1, 1, 2, 8, 1, 7]
def baseStart_3756219 : Nat := 118140960795 + 3756219 * 2 ^ 59
def prefixEnd_3756219 : Nat := 4983230072969 + 3 ^ 40 * 3756219 * 2
def baseEnd_3756219 : Nat := 214305087838971612176441

theorem tailTrace_3756219 : CollatzResearch.WordTrace tailWord_3756219 prefixEnd_3756219 214305087838971612176441 := by
  unfold tailWord_3756219
  simp only [CollatzResearch.WordTrace]
  refine ⟨137000561978867548976999711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91333707985911699317999807 137000561978867548976999711)
  ·
    refine ⟨205500842968301323465499567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137000561978867548976999711 205500842968301323465499567)
    ·
      refine ⟨308251264452451985198249351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205500842968301323465499567 308251264452451985198249351)
      ·
        refine ⟨462376896678677977797374027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308251264452451985198249351 462376896678677977797374027)
        ·
          refine ⟨693565345018016966696061041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 462376896678677977797374027 693565345018016966696061041)
          ·
            refine ⟨520174008763512725022045781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 693565345018016966696061041 520174008763512725022045781)
            ·
              refine ⟨6095789165197414746352099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 520174008763512725022045781 6095789165197414746352099)
              ·
                refine ⟨9143683747796122119528149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6095789165197414746352099 9143683747796122119528149)
                ·
                  refine ⟨214305087838971612176441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9143683747796122119528149 214305087838971612176441)
                  ·
                    rfl

theorem cell23_3756219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 8, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 8, 1, 7].length) (baseStart_3756219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3756219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3756219 prefixEnd_3756219 := by exact prefixLift 3756219
  have htrace : WordTrace (prefixWord ++ tailWord_3756219) baseStart_3756219 baseEnd_3756219 := by
    simpa [prefixWord, tailWord_3756219, baseEnd_3756219] using wordTrace_append hprefix tailTrace_3756219
  have hstable : (prefixWord ++ tailWord_3756219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3756219).length < 2 ^ (prefixWord ++ tailWord_3756219).sum := by decide
  have hdescent : baseEnd_3756219 < baseStart_3756219 := by decide
  rcases family_descends (prefixWord ++ tailWord_3756219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3756249 : List Nat := [1, 2, 1, 2, 3, 1, 4, 1, 1, 7]
def baseStart_3756249 : Nat := 118140960795 + 3756249 * 2 ^ 59
def prefixEnd_3756249 : Nat := 4983230072969 + 3 ^ 40 * 3756249 * 2
def baseEnd_3756249 : Nat := 642920398323459797404277

theorem tailTrace_3756249 : CollatzResearch.WordTrace tailWord_3756249 prefixEnd_3756249 642920398323459797404277 := by
  unfold tailWord_3756249
  simp only [CollatzResearch.WordTrace]
  refine ⟨137001656168758864100591801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91334437445839242733727867 137001656168758864100591801)
  ·
    refine ⟨102751242126569148075443851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137001656168758864100591801 102751242126569148075443851)
    ·
      refine ⟨154126863189853722113165777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102751242126569148075443851 154126863189853722113165777)
      ·
        refine ⟨115595147392390291584874333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154126863189853722113165777 115595147392390291584874333)
        ·
          refine ⟨43348180272146359344327875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115595147392390291584874333 43348180272146359344327875)
          ·
            refine ⟨65022270408219539016491813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43348180272146359344327875 65022270408219539016491813)
            ·
              refine ⟨12191675701541163565592215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65022270408219539016491813 12191675701541163565592215)
              ·
                refine ⟨18287513552311745348388323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12191675701541163565592215 18287513552311745348388323)
                ·
                  refine ⟨27431270328467618022582485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18287513552311745348388323 27431270328467618022582485)
                  ·
                    refine ⟨642920398323459797404277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27431270328467618022582485 642920398323459797404277)
                    ·
                      rfl

theorem cell23_3756249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 1, 1, 7].length) (baseStart_3756249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3756249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3756249 prefixEnd_3756249 := by exact prefixLift 3756249
  have htrace : WordTrace (prefixWord ++ tailWord_3756249) baseStart_3756249 baseEnd_3756249 := by
    simpa [prefixWord, tailWord_3756249, baseEnd_3756249] using wordTrace_append hprefix tailTrace_3756249
  have hstable : (prefixWord ++ tailWord_3756249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3756249).length < 2 ^ (prefixWord ++ tailWord_3756249).sum := by decide
  have hdescent : baseEnd_3756249 < baseStart_3756249 := by decide
  rcases family_descends (prefixWord ++ tailWord_3756249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3756266 : List Nat := [3, 1, 3, 1, 1, 2, 3, 2, 2, 5]
def baseStart_3756266 : Nat := 118140960795 + 3756266 * 2 ^ 59
def prefixEnd_3756266 : Nat := 4983230072969 + 3 ^ 40 * 3756266 * 2
def baseEnd_3756266 : Nat := 642923308047168608566751

theorem tailTrace_3756266 : CollatzResearch.WordTrace tailWord_3756266 prefixEnd_3756266 642923308047168608566751 := by
  unfold tailWord_3756266
  simp only [CollatzResearch.WordTrace]
  refine ⟨34250569052424319000990163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91334850806464850669307101 34250569052424319000990163)
  ·
    refine ⟨51375853578636478501485245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34250569052424319000990163 51375853578636478501485245)
    ·
      refine ⟨19265945091988679438056967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51375853578636478501485245 19265945091988679438056967)
      ·
        refine ⟨28898917637983019157085451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19265945091988679438056967 28898917637983019157085451)
        ·
          refine ⟨43348376456974528735628177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28898917637983019157085451 43348376456974528735628177)
          ·
            refine ⟨32511282342730896551721133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43348376456974528735628177 32511282342730896551721133)
            ·
              refine ⟨12191730878524086206895425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32511282342730896551721133 12191730878524086206895425)
              ·
                refine ⟨9143798158893064655171569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12191730878524086206895425 9143798158893064655171569)
                ·
                  refine ⟨6857848619169798491378677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9143798158893064655171569 6857848619169798491378677)
                  ·
                    refine ⟨642923308047168608566751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6857848619169798491378677 642923308047168608566751)
                    ·
                      rfl

theorem cell23_3756266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 2, 2, 5].length) (baseStart_3756266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3756266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3756266 prefixEnd_3756266 := by exact prefixLift 3756266
  have htrace : WordTrace (prefixWord ++ tailWord_3756266) baseStart_3756266 baseEnd_3756266 := by
    simpa [prefixWord, tailWord_3756266, baseEnd_3756266] using wordTrace_append hprefix tailTrace_3756266
  have hstable : (prefixWord ++ tailWord_3756266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3756266).length < 2 ^ (prefixWord ++ tailWord_3756266).sum := by decide
  have hdescent : baseEnd_3756266 < baseStart_3756266 := by decide
  rcases family_descends (prefixWord ++ tailWord_3756266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3756309 : List Nat := [1, 3, 2, 1, 2, 1, 2, 1, 10]
def baseStart_3756309 : Nat := 118140960795 + 3756309 * 2 ^ 59
def prefixEnd_3756309 : Nat := 4983230072969 + 3 ^ 40 * 3756309 * 2
def baseEnd_3756309 : Nat := 214310222645516573051395

theorem tailTrace_3756309 : CollatzResearch.WordTrace tailWord_3756309 prefixEnd_3756309 214310222645516573051395 := by
  unfold tailWord_3756309
  simp only [CollatzResearch.WordTrace]
  refine ⟨137003844548541494347775981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91335896365694329565183987 137003844548541494347775981)
  ·
    refine ⟨51376441705703060380415993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137003844548541494347775981 51376441705703060380415993)
    ·
      refine ⟨38532331279277295285311995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51376441705703060380415993 38532331279277295285311995)
      ·
        refine ⟨57798496918915942927967993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38532331279277295285311995 57798496918915942927967993)
        ·
          refine ⟨43348872689186957195975995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57798496918915942927967993 43348872689186957195975995)
          ·
            refine ⟨65023309033780435793963993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43348872689186957195975995 65023309033780435793963993)
            ·
              refine ⟨48767481775335326845472995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65023309033780435793963993 48767481775335326845472995)
              ·
                refine ⟨73151222663002990268209493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48767481775335326845472995 73151222663002990268209493)
                ·
                  refine ⟨214310222645516573051395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 73151222663002990268209493 214310222645516573051395)
                  ·
                    rfl

theorem cell23_3756309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 10].length) (baseStart_3756309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3756309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3756309 prefixEnd_3756309 := by exact prefixLift 3756309
  have htrace : WordTrace (prefixWord ++ tailWord_3756309) baseStart_3756309 baseEnd_3756309 := by
    simpa [prefixWord, tailWord_3756309, baseEnd_3756309] using wordTrace_append hprefix tailTrace_3756309
  have hstable : (prefixWord ++ tailWord_3756309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3756309).length < 2 ^ (prefixWord ++ tailWord_3756309).sum := by decide
  have hdescent : baseEnd_3756309 < baseStart_3756309 := by decide
  rcases family_descends (prefixWord ++ tailWord_3756309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3756363 : List Nat := [1, 1, 1, 1, 3, 1, 1, 7, 2, 3, 2]
def baseStart_3756363 : Nat := 118140960795 + 3756363 * 2 ^ 59
def prefixEnd_3756363 : Nat := 4983230072969 + 3 ^ 40 * 3756363 * 2
def baseEnd_3756363 : Nat := 1928819731764991946187307

theorem tailTrace_3756363 : CollatzResearch.WordTrace tailWord_3756363 prefixEnd_3756363 1928819731764991946187307 := by
  unfold tailWord_3756363
  simp only [CollatzResearch.WordTrace]
  refine ⟨137005814090345861570241743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91337209393563907713494495 137005814090345861570241743)
  ·
    refine ⟨205508721135518792355362615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137005814090345861570241743 205508721135518792355362615)
    ·
      refine ⟨308263081703278188533043923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205508721135518792355362615 308263081703278188533043923)
      ·
        refine ⟨462394622554917282799565885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308263081703278188533043923 462394622554917282799565885)
        ·
          refine ⟨173397983458093981049837207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 462394622554917282799565885 173397983458093981049837207)
          ·
            refine ⟨260096975187140971574755811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173397983458093981049837207 260096975187140971574755811)
            ·
              refine ⟨390145462780711457362133717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 260096975187140971574755811 390145462780711457362133717)
              ·
                refine ⟨9144034283922924781925009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 390145462780711457362133717 9144034283922924781925009)
                ·
                  refine ⟨6858025712942193586443757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9144034283922924781925009 6858025712942193586443757)
                  ·
                    refine ⟨2571759642353322594916409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6858025712942193586443757 2571759642353322594916409)
                    ·
                      refine ⟨1928819731764991946187307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2571759642353322594916409 1928819731764991946187307)
                      ·
                        rfl

theorem cell23_3756363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 7, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 7, 2, 3, 2].length) (baseStart_3756363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3756363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3756363 prefixEnd_3756363 := by exact prefixLift 3756363
  have htrace : WordTrace (prefixWord ++ tailWord_3756363) baseStart_3756363 baseEnd_3756363 := by
    simpa [prefixWord, tailWord_3756363, baseEnd_3756363] using wordTrace_append hprefix tailTrace_3756363
  have hstable : (prefixWord ++ tailWord_3756363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3756363).length < 2 ^ (prefixWord ++ tailWord_3756363).sum := by decide
  have hdescent : baseEnd_3756363 < baseStart_3756363 := by decide
  rcases family_descends (prefixWord ++ tailWord_3756363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3756376 : List Nat := [2, 1, 2, 2, 1, 1, 2, 2, 5, 1, 4]
def baseStart_3756376 : Nat := 118140960795 + 3756376 * 2 ^ 59
def prefixEnd_3756376 : Nat := 4983230072969 + 3 ^ 40 * 3756376 * 2
def baseEnd_3756376 : Nat := 1928826407013500395324747

theorem tailTrace_3756376 : CollatzResearch.WordTrace tailWord_3756376 prefixEnd_3756376 1928826407013500395324747 := by
  unfold tailWord_3756376
  simp only [CollatzResearch.WordTrace]
  refine ⟨68503144119649382395232491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91337525492865843193643321 68503144119649382395232491)
  ·
    refine ⟨102754716179474073592848737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68503144119649382395232491 102754716179474073592848737)
    ·
      refine ⟨77066037134605555194636553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102754716179474073592848737 77066037134605555194636553)
      ·
        refine ⟨57799527850954166395977415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77066037134605555194636553 57799527850954166395977415)
        ·
          refine ⟨86699291776431249593966123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57799527850954166395977415 86699291776431249593966123)
          ·
            refine ⟨130048937664646874390949185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86699291776431249593966123 130048937664646874390949185)
            ·
              refine ⟨97536703248485155793211889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130048937664646874390949185 97536703248485155793211889)
              ·
                refine ⟨73152527436363866844908917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97536703248485155793211889 73152527436363866844908917)
                ·
                  refine ⟨6858049447159112516710211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73152527436363866844908917 6858049447159112516710211)
                  ·
                    refine ⟨10287074170738668775065317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6858049447159112516710211 10287074170738668775065317)
                    ·
                      refine ⟨1928826407013500395324747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10287074170738668775065317 1928826407013500395324747)
                      ·
                        rfl

theorem cell23_3756376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 5, 1, 4].length) (baseStart_3756376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3756376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3756376 prefixEnd_3756376 := by exact prefixLift 3756376
  have htrace : WordTrace (prefixWord ++ tailWord_3756376) baseStart_3756376 baseEnd_3756376 := by
    simpa [prefixWord, tailWord_3756376, baseEnd_3756376] using wordTrace_append hprefix tailTrace_3756376
  have hstable : (prefixWord ++ tailWord_3756376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3756376).length < 2 ^ (prefixWord ++ tailWord_3756376).sum := by decide
  have hdescent : baseEnd_3756376 < baseStart_3756376 := by decide
  rcases family_descends (prefixWord ++ tailWord_3756376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3756379 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 9]
def baseStart_3756379 : Nat := 118140960795 + 3756379 * 2 ^ 59
def prefixEnd_3756379 : Nat := 4983230072969 + 3 ^ 40 * 3756379 * 2
def baseEnd_3756379 : Nat := 1928827947455463883587233

theorem tailTrace_3756379 : CollatzResearch.WordTrace tailWord_3756379 prefixEnd_3756379 1928827947455463883587233 := by
  unfold tailWord_3756379
  simp only [CollatzResearch.WordTrace]
  refine ⟨137006397658287896302824191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91337598438858597535216127 137006397658287896302824191)
  ·
    refine ⟨205509596487431844454236287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137006397658287896302824191 205509596487431844454236287)
    ·
      refine ⟨308264394731147766681354431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205509596487431844454236287 308264394731147766681354431)
      ·
        refine ⟨462396592096721650022031647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308264394731147766681354431 462396592096721650022031647)
        ·
          refine ⟨693594888145082475033047471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 462396592096721650022031647 693594888145082475033047471)
          ·
            refine ⟨1040392332217623712549571207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 693594888145082475033047471 1040392332217623712549571207)
            ·
              refine ⟨1560588498326435568824356811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1040392332217623712549571207 1560588498326435568824356811)
              ·
                refine ⟨2340882747489653353236535217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1560588498326435568824356811 2340882747489653353236535217)
                ·
                  refine ⟨1755662060617240014927401413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2340882747489653353236535217 1755662060617240014927401413)
                  ·
                    refine ⟨329186636365732502798887765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1755662060617240014927401413 329186636365732502798887765)
                    ·
                      refine ⟨1928827947455463883587233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 329186636365732502798887765 1928827947455463883587233)
                      ·
                        rfl

theorem cell23_3756379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 9].length) (baseStart_3756379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3756379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3756379 prefixEnd_3756379 := by exact prefixLift 3756379
  have htrace : WordTrace (prefixWord ++ tailWord_3756379) baseStart_3756379 baseEnd_3756379 := by
    simpa [prefixWord, tailWord_3756379, baseEnd_3756379] using wordTrace_append hprefix tailTrace_3756379
  have hstable : (prefixWord ++ tailWord_3756379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3756379).length < 2 ^ (prefixWord ++ tailWord_3756379).sum := by decide
  have hdescent : baseEnd_3756379 < baseStart_3756379 := by decide
  rcases family_descends (prefixWord ++ tailWord_3756379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3756430 : List Nat := [4, 1, 1, 4, 1, 2, 2, 1, 1, 1, 5]
def baseStart_3756430 : Nat := 118140960795 + 3756430 * 2 ^ 59
def prefixEnd_3756430 : Nat := 4983230072969 + 3 ^ 40 * 3756430 * 2
def baseEnd_3756430 : Nat := 1928854134968843184049499

theorem tailTrace_3756430 : CollatzResearch.WordTrace tailWord_3756430 prefixEnd_3756430 1928854134968843184049499 := by
  unfold tailWord_3756430
  simp only [CollatzResearch.WordTrace]
  refine ⟨17126032222637891501616343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91338838520735421341953829 17126032222637891501616343)
  ·
    refine ⟨25689048333956837252424515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17126032222637891501616343 25689048333956837252424515)
    ·
      refine ⟨38533572500935255878636773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25689048333956837252424515 38533572500935255878636773)
      ·
        refine ⟨7225044843925360477244395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38533572500935255878636773 7225044843925360477244395)
        ·
          refine ⟨10837567265888040715866593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7225044843925360477244395 10837567265888040715866593)
          ·
            refine ⟨8128175449416030536899945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10837567265888040715866593 8128175449416030536899945)
            ·
              refine ⟨6096131587062022902674959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8128175449416030536899945 6096131587062022902674959)
              ·
                refine ⟨9144197380593034354012439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6096131587062022902674959 9144197380593034354012439)
                ·
                  refine ⟨13716296070889551531018659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9144197380593034354012439 13716296070889551531018659)
                  ·
                    refine ⟨20574444106334327296527989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13716296070889551531018659 20574444106334327296527989)
                    ·
                      refine ⟨1928854134968843184049499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20574444106334327296527989 1928854134968843184049499)
                      ·
                        rfl

theorem cell23_3756430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_3756430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3756430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3756430 prefixEnd_3756430 := by exact prefixLift 3756430
  have htrace : WordTrace (prefixWord ++ tailWord_3756430) baseStart_3756430 baseEnd_3756430 := by
    simpa [prefixWord, tailWord_3756430, baseEnd_3756430] using wordTrace_append hprefix tailTrace_3756430
  have hstable : (prefixWord ++ tailWord_3756430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3756430).length < 2 ^ (prefixWord ++ tailWord_3756430).sum := by decide
  have hdescent : baseEnd_3756430 < baseStart_3756430 := by decide
  rcases family_descends (prefixWord ++ tailWord_3756430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3756438 : List Nat := [5, 3, 1, 2, 1, 2, 1, 1, 3, 1, 3]
def baseStart_3756438 : Nat := 118140960795 + 3756438 * 2 ^ 59
def prefixEnd_3756438 : Nat := 4983230072969 + 3 ^ 40 * 3756438 * 2
def baseEnd_3756438 : Nat := 1928858242814079152749463

theorem tailTrace_3756438 : CollatzResearch.WordTrace tailWord_3756438 prefixEnd_3756438 1928858242814079152749463 := by
  unfold tailWord_3756438
  simp only [CollatzResearch.WordTrace]
  refine ⟨8563034347817134336201373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 91339033043382766252814645 8563034347817134336201373)
  ·
    refine ⟨3211137880431425376075515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8563034347817134336201373 3211137880431425376075515)
    ·
      refine ⟨4816706820647138064113273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3211137880431425376075515 4816706820647138064113273)
      ·
        refine ⟨3612530115485353548084955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4816706820647138064113273 3612530115485353548084955)
        ·
          refine ⟨5418795173228030322127433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3612530115485353548084955 5418795173228030322127433)
          ·
            refine ⟨4064096379921022741595575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5418795173228030322127433 4064096379921022741595575)
            ·
              refine ⟨6096144569881534112393363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4064096379921022741595575 6096144569881534112393363)
              ·
                refine ⟨9144216854822301168590045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6096144569881534112393363 9144216854822301168590045)
                ·
                  refine ⟨3429081320558362938221267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9144216854822301168590045 3429081320558362938221267)
                  ·
                    refine ⟨5143621980837544407331901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3429081320558362938221267 5143621980837544407331901)
                    ·
                      refine ⟨1928858242814079152749463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5143621980837544407331901 1928858242814079152749463)
                      ·
                        rfl

theorem cell23_3756438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_3756438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3756438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3756438 prefixEnd_3756438 := by exact prefixLift 3756438
  have htrace : WordTrace (prefixWord ++ tailWord_3756438) baseStart_3756438 baseEnd_3756438 := by
    simpa [prefixWord, tailWord_3756438, baseEnd_3756438] using wordTrace_append hprefix tailTrace_3756438
  have hstable : (prefixWord ++ tailWord_3756438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3756438).length < 2 ^ (prefixWord ++ tailWord_3756438).sum := by decide
  have hdescent : baseEnd_3756438 < baseStart_3756438 := by decide
  rcases family_descends (prefixWord ++ tailWord_3756438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3756481 : List Nat := [1, 2, 7, 1, 2, 1, 1, 1, 1, 1, 5]
def baseStart_3756481 : Nat := 118140960795 + 3756481 * 2 ^ 59
def prefixEnd_3756481 : Nat := 4983230072969 + 3 ^ 40 * 3756481 * 2
def baseEnd_3756481 : Nat := 1928880322482222484511765

theorem tailTrace_3756481 : CollatzResearch.WordTrace tailWord_3756481 prefixEnd_3756481 1928880322482222484511765 := by
  unfold tailWord_3756481
  simp only [CollatzResearch.WordTrace]
  refine ⟨137010117903918367723037297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91340078602612245148691531 137010117903918367723037297)
  ·
    refine ⟨102757588427938775792277973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137010117903918367723037297 102757588427938775792277973)
    ·
      refine ⟨2408380978779815057631515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 102757588427938775792277973 2408380978779815057631515)
      ·
        refine ⟨3612571468169722586447273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2408380978779815057631515 3612571468169722586447273)
        ·
          refine ⟨2709428601127291939835455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3612571468169722586447273 2709428601127291939835455)
          ·
            refine ⟨4064142901690937909753183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2709428601127291939835455 4064142901690937909753183)
            ·
              refine ⟨6096214352536406864629775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4064142901690937909753183 6096214352536406864629775)
              ·
                refine ⟨9144321528804610296944663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6096214352536406864629775 9144321528804610296944663)
                ·
                  refine ⟨13716482293206915445416995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9144321528804610296944663 13716482293206915445416995)
                  ·
                    refine ⟨20574723439810373168125493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13716482293206915445416995 20574723439810373168125493)
                    ·
                      refine ⟨1928880322482222484511765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20574723439810373168125493 1928880322482222484511765)
                      ·
                        rfl

theorem cell23_3756481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_3756481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3756481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3756481 prefixEnd_3756481 := by exact prefixLift 3756481
  have htrace : WordTrace (prefixWord ++ tailWord_3756481) baseStart_3756481 baseEnd_3756481 := by
    simpa [prefixWord, tailWord_3756481, baseEnd_3756481] using wordTrace_append hprefix tailTrace_3756481
  have hstable : (prefixWord ++ tailWord_3756481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3756481).length < 2 ^ (prefixWord ++ tailWord_3756481).sum := by decide
  have hdescent : baseEnd_3756481 < baseStart_3756481 := by decide
  rcases family_descends (prefixWord ++ tailWord_3756481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3756513 : List Nat := [1, 2, 3, 1, 2, 2, 3, 1, 2, 2, 4]
def baseStart_3756513 : Nat := 118140960795 + 3756513 * 2 ^ 59
def prefixEnd_3756513 : Nat := 4983230072969 + 3 ^ 40 * 3756513 * 2
def baseEnd_3756513 : Nat := 1928896753863166359311617

theorem tailTrace_3756513 : CollatzResearch.WordTrace tailWord_3756513 prefixEnd_3756513 1928896753863166359311617 := by
  unfold tailWord_3756513
  simp only [CollatzResearch.WordTrace]
  refine ⟨137011285039802437188202193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91340856693201624792134795 137011285039802437188202193)
  ·
    refine ⟨102758463779851827891151645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137011285039802437188202193 102758463779851827891151645)
    ·
      refine ⟨38534423917444435459181867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102758463779851827891151645 38534423917444435459181867)
      ·
        refine ⟨57801635876166653188772801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38534423917444435459181867 57801635876166653188772801)
        ·
          refine ⟨43351226907124989891579601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57801635876166653188772801 43351226907124989891579601)
          ·
            refine ⟨32513420180343742418684701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43351226907124989891579601 32513420180343742418684701)
            ·
              refine ⟨12192532567628903407006763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32513420180343742418684701 12192532567628903407006763)
              ·
                refine ⟨18288798851443355110510145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12192532567628903407006763 18288798851443355110510145)
                ·
                  refine ⟨13716599138582516332882609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18288798851443355110510145 13716599138582516332882609)
                  ·
                    refine ⟨10287449353936887249661957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13716599138582516332882609 10287449353936887249661957)
                    ·
                      refine ⟨1928896753863166359311617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10287449353936887249661957 1928896753863166359311617)
                      ·
                        rfl

theorem cell23_3756513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 1, 2, 2, 4].length) (baseStart_3756513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3756513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3756513 prefixEnd_3756513 := by exact prefixLift 3756513
  have htrace : WordTrace (prefixWord ++ tailWord_3756513) baseStart_3756513 baseEnd_3756513 := by
    simpa [prefixWord, tailWord_3756513, baseEnd_3756513] using wordTrace_append hprefix tailTrace_3756513
  have hstable : (prefixWord ++ tailWord_3756513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3756513).length < 2 ^ (prefixWord ++ tailWord_3756513).sum := by decide
  have hdescent : baseEnd_3756513 < baseStart_3756513 := by decide
  rcases family_descends (prefixWord ++ tailWord_3756513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3756551 : List Nat := [1, 1, 4, 3, 3, 2, 1, 2, 2, 2, 2]
def baseStart_3756551 : Nat := 118140960795 + 3756551 * 2 ^ 59
def prefixEnd_3756551 : Nat := 4983230072969 + 3 ^ 40 * 3756551 * 2
def baseEnd_3756551 : Nat := 1928916266128037210636443

theorem tailTrace_3756551 : CollatzResearch.WordTrace tailWord_3756551 prefixEnd_3756551 1928916266128037210636443 := by
  unfold tailWord_3756551
  simp only [CollatzResearch.WordTrace]
  refine ⟨137012671013664769678085507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91341780675776513118723671 137012671013664769678085507)
  ·
    refine ⟨205519006520497154517128261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137012671013664769678085507 205519006520497154517128261)
    ·
      refine ⟨38534813722593216471961549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 205519006520497154517128261 38534813722593216471961549)
      ·
        refine ⟨14450555145972456176985581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38534813722593216471961549 14450555145972456176985581)
        ·
          refine ⟨5418958179739671066369593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14450555145972456176985581 5418958179739671066369593)
          ·
            refine ⟨4064218634804753299777195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5418958179739671066369593 4064218634804753299777195)
            ·
              refine ⟨6096327952207129949665793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4064218634804753299777195 6096327952207129949665793)
              ·
                refine ⟨4572245964155347462249345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6096327952207129949665793 4572245964155347462249345)
                ·
                  refine ⟨3429184473116510596687009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4572245964155347462249345 3429184473116510596687009)
                  ·
                    refine ⟨2571888354837382947515257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3429184473116510596687009 2571888354837382947515257)
                    ·
                      refine ⟨1928916266128037210636443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2571888354837382947515257 1928916266128037210636443)
                      ·
                        rfl

theorem cell23_3756551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 1, 2, 2, 2, 2].length) (baseStart_3756551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3756551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3756551 prefixEnd_3756551 := by exact prefixLift 3756551
  have htrace : WordTrace (prefixWord ++ tailWord_3756551) baseStart_3756551 baseEnd_3756551 := by
    simpa [prefixWord, tailWord_3756551, baseEnd_3756551] using wordTrace_append hprefix tailTrace_3756551
  have hstable : (prefixWord ++ tailWord_3756551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3756551).length < 2 ^ (prefixWord ++ tailWord_3756551).sum := by decide
  have hdescent : baseEnd_3756551 < baseStart_3756551 := by decide
  rcases family_descends (prefixWord ++ tailWord_3756551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3756557 : List Nat := [1, 7, 1, 1, 1, 1, 1, 3, 7]
def baseStart_3756557 : Nat := 118140960795 + 3756557 * 2 ^ 59
def prefixEnd_3756557 : Nat := 4983230072969 + 3 ^ 40 * 3756557 * 2
def baseEnd_3756557 : Nat := 214324371890218243017935

theorem tailTrace_3756557 : CollatzResearch.WordTrace tailWord_3756557 prefixEnd_3756557 214324371890218243017935 := by
  unfold tailWord_3756557
  simp only [CollatzResearch.WordTrace]
  refine ⟨137012889851643032702803925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91341926567762021801869283 137012889851643032702803925)
  ·
    refine ⟨3211239605897883578971967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 137012889851643032702803925 3211239605897883578971967)
    ·
      refine ⟨4816859408846825368457951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3211239605897883578971967 4816859408846825368457951)
      ·
        refine ⟨7225289113270238052686927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4816859408846825368457951 7225289113270238052686927)
        ·
          refine ⟨10837933669905357079030391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7225289113270238052686927 10837933669905357079030391)
          ·
            refine ⟨16256900504858035618545587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10837933669905357079030391 16256900504858035618545587)
            ·
              refine ⟨24385350757287053427818381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16256900504858035618545587 24385350757287053427818381)
              ·
                refine ⟨9144506533982645035431893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24385350757287053427818381 9144506533982645035431893)
                ·
                  refine ⟨214324371890218243017935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9144506533982645035431893 214324371890218243017935)
                  ·
                    rfl

theorem cell23_3756557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 3, 7].length) (baseStart_3756557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3756557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3756557 prefixEnd_3756557 := by exact prefixLift 3756557
  have htrace : WordTrace (prefixWord ++ tailWord_3756557) baseStart_3756557 baseEnd_3756557 := by
    simpa [prefixWord, tailWord_3756557, baseEnd_3756557] using wordTrace_append hprefix tailTrace_3756557
  have hstable : (prefixWord ++ tailWord_3756557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3756557).length < 2 ^ (prefixWord ++ tailWord_3756557).sum := by decide
  have hdescent : baseEnd_3756557 < baseStart_3756557 := by decide
  rcases family_descends (prefixWord ++ tailWord_3756557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3756613 : List Nat := [1, 3, 1, 1, 1, 5, 2, 1, 8]
def baseStart_3756613 : Nat := 118140960795 + 3756613 * 2 ^ 59
def prefixEnd_3756613 : Nat := 4983230072969 + 3 ^ 40 * 3756613 * 2
def baseEnd_3756613 : Nat := 214327566880957329784573

theorem tailTrace_3756613 : CollatzResearch.WordTrace tailWord_3756613 prefixEnd_3756613 214327566880957329784573 := by
  unfold tailWord_3756613
  simp only [CollatzResearch.WordTrace]
  refine ⟨137014932339440154266842493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91343288226293436177894995 137014932339440154266842493)
  ·
    refine ⟨51380599627290057850065935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137014932339440154266842493 51380599627290057850065935)
    ·
      refine ⟨77070899440935086775098903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51380599627290057850065935 77070899440935086775098903)
      ·
        refine ⟨115606349161402630162648355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77070899440935086775098903 115606349161402630162648355)
        ·
          refine ⟨173409523742103945243972533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115606349161402630162648355 173409523742103945243972533)
          ·
            refine ⟨16257142850822244866622425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 173409523742103945243972533 16257142850822244866622425)
            ·
              refine ⟨12192857138116683649966819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16257142850822244866622425 12192857138116683649966819)
              ·
                refine ⟨18289285707175025474950229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12192857138116683649966819 18289285707175025474950229)
                ·
                  refine ⟨214327566880957329784573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18289285707175025474950229 214327566880957329784573)
                  ·
                    rfl

theorem cell23_3756613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 1, 8].length) (baseStart_3756613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3756613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3756613 prefixEnd_3756613 := by exact prefixLift 3756613
  have htrace : WordTrace (prefixWord ++ tailWord_3756613) baseStart_3756613 baseEnd_3756613 := by
    simpa [prefixWord, tailWord_3756613, baseEnd_3756613] using wordTrace_append hprefix tailTrace_3756613
  have hstable : (prefixWord ++ tailWord_3756613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3756613).length < 2 ^ (prefixWord ++ tailWord_3756613).sum := by decide
  have hdescent : baseEnd_3756613 < baseStart_3756613 := by decide
  rcases family_descends (prefixWord ++ tailWord_3756613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3756754 : List Nat := [3, 2, 2, 2, 3, 2, 2, 7]
def baseStart_3756754 : Nat := 118140960795 + 3756754 * 2 ^ 59
def prefixEnd_3756754 : Nat := 4983230072969 + 3 ^ 40 * 3756754 * 2
def baseEnd_3756754 : Nat := 71445203803737033940667

theorem tailTrace_3756754 : CollatzResearch.WordTrace tailWord_3756754 prefixEnd_3756754 71445203803737033940667 := by
  unfold tailWord_3756754
  simp only [CollatzResearch.WordTrace]
  refine ⟨34255018757982333836931329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91346716687952890231816877 34255018757982333836931329)
  ·
    refine ⟨25691264068486750377698497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34255018757982333836931329 25691264068486750377698497)
    ·
      refine ⟨19268448051365062783273873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25691264068486750377698497 19268448051365062783273873)
      ·
        refine ⟨14451336038523797087455405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19268448051365062783273873 14451336038523797087455405)
        ·
          refine ⟨5419251014446423907795777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14451336038523797087455405 5419251014446423907795777)
          ·
            refine ⟨4064438260834817930846833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5419251014446423907795777 4064438260834817930846833)
            ·
              refine ⟨3048328695626113448135125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4064438260834817930846833 3048328695626113448135125)
              ·
                refine ⟨71445203803737033940667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3048328695626113448135125 71445203803737033940667)
                ·
                  rfl

theorem cell23_3756754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 2, 7].length) (baseStart_3756754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3756754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3756754 prefixEnd_3756754 := by exact prefixLift 3756754
  have htrace : WordTrace (prefixWord ++ tailWord_3756754) baseStart_3756754 baseEnd_3756754 := by
    simpa [prefixWord, tailWord_3756754, baseEnd_3756754] using wordTrace_append hprefix tailTrace_3756754
  have hstable : (prefixWord ++ tailWord_3756754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3756754).length < 2 ^ (prefixWord ++ tailWord_3756754).sum := by decide
  have hdescent : baseEnd_3756754 < baseStart_3756754 := by decide
  rcases family_descends (prefixWord ++ tailWord_3756754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3756760 : List Nat := [2, 1, 2, 2, 3, 2, 1, 1, 2, 2, 5]
def baseStart_3756760 : Nat := 118140960795 + 3756760 * 2 ^ 59
def prefixEnd_3756760 : Nat := 4983230072969 + 3 ^ 40 * 3756760 * 2
def baseEnd_3756760 : Nat := 1929023583584826892922981

theorem tailTrace_3756760 : CollatzResearch.WordTrace tailWord_3756760 prefixEnd_3756760 1929023583584826892922981 := by
  unfold tailWord_3756760
  simp only [CollatzResearch.WordTrace]
  refine ⟨68510146934953799186221867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91346862579938398914962489 68510146934953799186221867)
  ·
    refine ⟨102765220402430698779332801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68510146934953799186221867 102765220402430698779332801)
    ·
      refine ⟨77073915301823024084499601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102765220402430698779332801 77073915301823024084499601)
      ·
        refine ⟨57805436476367268063374701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77073915301823024084499601 57805436476367268063374701)
        ·
          refine ⟨21677038678637725523765513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57805436476367268063374701 21677038678637725523765513)
          ·
            refine ⟨16257779008978294142824135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21677038678637725523765513 16257779008978294142824135)
            ·
              refine ⟨24386668513467441214236203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16257779008978294142824135 24386668513467441214236203)
              ·
                refine ⟨36580002770201161821354305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24386668513467441214236203 36580002770201161821354305)
                ·
                  refine ⟨27435002077650871366015729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36580002770201161821354305 27435002077650871366015729)
                  ·
                    refine ⟨20576251558238153524511797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27435002077650871366015729 20576251558238153524511797)
                    ·
                      refine ⟨1929023583584826892922981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20576251558238153524511797 1929023583584826892922981)
                      ·
                        rfl

theorem cell23_3756760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 1, 2, 2, 5].length) (baseStart_3756760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3756760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3756760 prefixEnd_3756760 := by exact prefixLift 3756760
  have htrace : WordTrace (prefixWord ++ tailWord_3756760) baseStart_3756760 baseEnd_3756760 := by
    simpa [prefixWord, tailWord_3756760, baseEnd_3756760] using wordTrace_append hprefix tailTrace_3756760
  have hstable : (prefixWord ++ tailWord_3756760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3756760).length < 2 ^ (prefixWord ++ tailWord_3756760).sum := by decide
  have hdescent : baseEnd_3756760 < baseStart_3756760 := by decide
  rcases family_descends (prefixWord ++ tailWord_3756760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3756798 : List Nat := [4, 2, 2, 1, 2, 1, 4, 1, 2, 1, 3]
def baseStart_3756798 : Nat := 118140960795 + 3756798 * 2 ^ 59
def prefixEnd_3756798 : Nat := 4983230072969 + 3 ^ 40 * 3756798 * 2
def baseEnd_3756798 : Nat := 1929043095849697744247807

theorem tailTrace_3756798 : CollatzResearch.WordTrace tailWord_3756798 prefixEnd_3756798 1929043095849697744247807 := by
  unfold tailWord_3756798
  simp only [CollatzResearch.WordTrace]
  refine ⟨17127709980471241357790881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91347786562513287241551365 17127709980471241357790881)
  ·
    refine ⟨12845782485353431018343161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17127709980471241357790881 12845782485353431018343161)
    ·
      refine ⟨9634336864015073263757371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12845782485353431018343161 9634336864015073263757371)
      ·
        refine ⟨14451505296022609895636057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9634336864015073263757371 14451505296022609895636057)
        ·
          refine ⟨10838628972016957421727043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14451505296022609895636057 10838628972016957421727043)
          ·
            refine ⟨16257943458025436132590565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10838628972016957421727043 16257943458025436132590565)
            ·
              refine ⟨3048364398379769274860731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16257943458025436132590565 3048364398379769274860731)
              ·
                refine ⟨4572546597569653912291097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3048364398379769274860731 4572546597569653912291097)
                ·
                  refine ⟨3429409948177240434218323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4572546597569653912291097 3429409948177240434218323)
                  ·
                    refine ⟨5144114922265860651327485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3429409948177240434218323 5144114922265860651327485)
                    ·
                      refine ⟨1929043095849697744247807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5144114922265860651327485 1929043095849697744247807)
                      ·
                        rfl

theorem cell23_3756798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 4, 1, 2, 1, 3].length) (baseStart_3756798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3756798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3756798 prefixEnd_3756798 := by exact prefixLift 3756798
  have htrace : WordTrace (prefixWord ++ tailWord_3756798) baseStart_3756798 baseEnd_3756798 := by
    simpa [prefixWord, tailWord_3756798, baseEnd_3756798] using wordTrace_append hprefix tailTrace_3756798
  have hstable : (prefixWord ++ tailWord_3756798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3756798).length < 2 ^ (prefixWord ++ tailWord_3756798).sum := by decide
  have hdescent : baseEnd_3756798 < baseStart_3756798 := by decide
  rcases family_descends (prefixWord ++ tailWord_3756798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3756804 : List Nat := [2, 3, 2, 2, 1, 1, 2, 3, 1, 4, 2]
def baseStart_3756804 : Nat := 118140960795 + 3756804 * 2 ^ 59
def prefixEnd_3756804 : Nat := 4983230072969 + 3 ^ 40 * 3756804 * 2
def baseEnd_3756804 : Nat := 1929046176733624720772779

theorem tailTrace_3756804 : CollatzResearch.WordTrace tailWord_3756804 prefixEnd_3756804 1929046176733624720772779 := by
  unfold tailWord_3756804
  simp only [CollatzResearch.WordTrace]
  refine ⟨68510949340874096943522733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91347932454498795924696977 68510949340874096943522733)
  ·
    refine ⟨25691606002827786353821025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68510949340874096943522733 25691606002827786353821025)
    ·
      refine ⟨19268704502120839765365769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25691606002827786353821025 19268704502120839765365769)
      ·
        refine ⟨14451528376590629824024327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19268704502120839765365769 14451528376590629824024327)
        ·
          refine ⟨21677292564885944736036491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14451528376590629824024327 21677292564885944736036491)
          ·
            refine ⟨32515938847328917104054737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21677292564885944736036491 32515938847328917104054737)
            ·
              refine ⟨24386954135496687828041053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32515938847328917104054737 24386954135496687828041053)
              ·
                refine ⟨9145107800811257935515395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24386954135496687828041053 9145107800811257935515395)
                ·
                  refine ⟨13717661701216886903273093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9145107800811257935515395 13717661701216886903273093)
                  ·
                    refine ⟨2572061568978166294363705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13717661701216886903273093 2572061568978166294363705)
                    ·
                      refine ⟨1929046176733624720772779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2572061568978166294363705 1929046176733624720772779)
                      ·
                        rfl

theorem cell23_3756804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 3, 1, 4, 2].length) (baseStart_3756804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3756804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3756804 prefixEnd_3756804 := by exact prefixLift 3756804
  have htrace : WordTrace (prefixWord ++ tailWord_3756804) baseStart_3756804 baseEnd_3756804 := by
    simpa [prefixWord, tailWord_3756804, baseEnd_3756804] using wordTrace_append hprefix tailTrace_3756804
  have hstable : (prefixWord ++ tailWord_3756804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3756804).length < 2 ^ (prefixWord ++ tailWord_3756804).sum := by decide
  have hdescent : baseEnd_3756804 < baseStart_3756804 := by decide
  rcases family_descends (prefixWord ++ tailWord_3756804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3756807 : List Nat := [1, 1, 4, 4, 1, 1, 1, 2, 2, 1, 5]
def baseStart_3756807 : Nat := 118140960795 + 3756807 * 2 ^ 59
def prefixEnd_3756807 : Nat := 4983230072969 + 3 ^ 40 * 3756807 * 2
def baseEnd_3756807 : Nat := 1929047717175588209035265

theorem tailTrace_3756807 : CollatzResearch.WordTrace tailWord_3756807 prefixEnd_3756807 1929047717175588209035265 := by
  unfold tailWord_3756807
  simp only [CollatzResearch.WordTrace]
  refine ⟨137022008100737325399404675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91348005400491550266269783 137022008100737325399404675)
  ·
    refine ⟨205533012151105988099107013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137022008100737325399404675 205533012151105988099107013)
    ·
      refine ⟨38537439778332372768582565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 205533012151105988099107013 38537439778332372768582565)
      ·
        refine ⟨7225769958437319894109231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38537439778332372768582565 7225769958437319894109231)
        ·
          refine ⟨10838654937655979841163847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7225769958437319894109231 10838654937655979841163847)
          ·
            refine ⟨16257982406483969761745771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10838654937655979841163847 16257982406483969761745771)
            ·
              refine ⟨24386973609725954642618657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16257982406483969761745771 24386973609725954642618657)
              ·
                refine ⟨18290230207294465981963993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24386973609725954642618657 18290230207294465981963993)
                ·
                  refine ⟨13717672655470849486472995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18290230207294465981963993 13717672655470849486472995)
                  ·
                    refine ⟨20576508983206274229709493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13717672655470849486472995 20576508983206274229709493)
                    ·
                      refine ⟨1929047717175588209035265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20576508983206274229709493 1929047717175588209035265)
                      ·
                        rfl

theorem cell23_3756807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_3756807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3756807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3756807 prefixEnd_3756807 := by exact prefixLift 3756807
  have htrace : WordTrace (prefixWord ++ tailWord_3756807) baseStart_3756807 baseEnd_3756807 := by
    simpa [prefixWord, tailWord_3756807, baseEnd_3756807] using wordTrace_append hprefix tailTrace_3756807
  have hstable : (prefixWord ++ tailWord_3756807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3756807).length < 2 ^ (prefixWord ++ tailWord_3756807).sum := by decide
  have hdescent : baseEnd_3756807 < baseStart_3756807 := by decide
  rcases family_descends (prefixWord ++ tailWord_3756807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3756810 : List Nat := [3, 1, 2, 2, 1, 2, 2, 1, 9]
def baseStart_3756810 : Nat := 118140960795 + 3756810 * 2 ^ 59
def prefixEnd_3756810 : Nat := 4983230072969 + 3 ^ 40 * 3756810 * 2
def baseEnd_3756810 : Nat := 214338806401950188588639

theorem tailTrace_3756810 : CollatzResearch.WordTrace tailWord_3756810 prefixEnd_3756810 214338806401950188588639 := by
  unfold tailWord_3756810
  simp only [CollatzResearch.WordTrace]
  refine ⟨34255529379931614227940971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91348078346484304607842589 34255529379931614227940971)
  ·
    refine ⟨51383294069897421341911457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34255529379931614227940971 51383294069897421341911457)
    ·
      refine ⟨38537470552423066006433593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51383294069897421341911457 38537470552423066006433593)
      ·
        refine ⟨28903102914317299504825195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38537470552423066006433593 28903102914317299504825195)
        ·
          refine ⟨43354654371475949257237793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28903102914317299504825195 43354654371475949257237793)
          ·
            refine ⟨32515990778606961942928345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43354654371475949257237793 32515990778606961942928345)
            ·
              refine ⟨24386993083955221457196259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32515990778606961942928345 24386993083955221457196259)
              ·
                refine ⟨36580489625932832185794389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24386993083955221457196259 36580489625932832185794389)
                ·
                  refine ⟨214338806401950188588639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 36580489625932832185794389 214338806401950188588639)
                  ·
                    rfl

theorem cell23_3756810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 1, 9].length) (baseStart_3756810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3756810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3756810 prefixEnd_3756810 := by exact prefixLift 3756810
  have htrace : WordTrace (prefixWord ++ tailWord_3756810) baseStart_3756810 baseEnd_3756810 := by
    simpa [prefixWord, tailWord_3756810, baseEnd_3756810] using wordTrace_append hprefix tailTrace_3756810
  have hstable : (prefixWord ++ tailWord_3756810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3756810).length < 2 ^ (prefixWord ++ tailWord_3756810).sum := by decide
  have hdescent : baseEnd_3756810 < baseStart_3756810 := by decide
  rcases family_descends (prefixWord ++ tailWord_3756810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3756837 : List Nat := [1, 3, 1, 2, 3, 1, 2, 2, 2, 3, 3]
def baseStart_3756837 : Nat := 118140960795 + 3756837 * 2 ^ 59
def prefixEnd_3756837 : Nat := 4983230072969 + 3 ^ 40 * 3756837 * 2
def baseEnd_3756837 : Nat := 1929063121595223091660127

theorem tailTrace_3756837 : CollatzResearch.WordTrace tailWord_3756837 prefixEnd_3756837 1929063121595223091660127 := by
  unfold tailWord_3756837
  simp only [CollatzResearch.WordTrace]
  refine ⟨137023102290628640522996765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91348734860419093681997843 137023102290628640522996765)
  ·
    refine ⟨51383663358985740196123787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137023102290628640522996765 51383663358985740196123787)
    ·
      refine ⟨77075495038478610294185681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51383663358985740196123787 77075495038478610294185681)
      ·
        refine ⟨57806621278858957720639261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77075495038478610294185681 57806621278858957720639261)
        ·
          refine ⟨21677482979572109145239723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57806621278858957720639261 21677482979572109145239723)
          ·
            refine ⟨32516224469358163717859585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21677482979572109145239723 32516224469358163717859585)
            ·
              refine ⟨24387168352018622788394689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32516224469358163717859585 24387168352018622788394689)
              ·
                refine ⟨18290376264013967091296017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24387168352018622788394689 18290376264013967091296017)
                ·
                  refine ⟨13717782198010475318472013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18290376264013967091296017 13717782198010475318472013)
                  ·
                    refine ⟨5144168324253928244427005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13717782198010475318472013 5144168324253928244427005)
                    ·
                      refine ⟨1929063121595223091660127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5144168324253928244427005 1929063121595223091660127)
                      ·
                        rfl

theorem cell23_3756837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 2, 2, 3, 3].length) (baseStart_3756837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3756837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3756837 prefixEnd_3756837 := by exact prefixLift 3756837
  have htrace : WordTrace (prefixWord ++ tailWord_3756837) baseStart_3756837 baseEnd_3756837 := by
    simpa [prefixWord, tailWord_3756837, baseEnd_3756837] using wordTrace_append hprefix tailTrace_3756837
  have hstable : (prefixWord ++ tailWord_3756837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3756837).length < 2 ^ (prefixWord ++ tailWord_3756837).sum := by decide
  have hdescent : baseEnd_3756837 < baseStart_3756837 := by decide
  rcases family_descends (prefixWord ++ tailWord_3756837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3756904 : List Nat := [2, 1, 4, 2, 1, 2, 1, 3, 3, 4]
def baseStart_3756904 : Nat := 118140960795 + 3756904 * 2 ^ 59
def prefixEnd_3756904 : Nat := 4983230072969 + 3 ^ 40 * 3756904 * 2
def baseEnd_3756904 : Nat := 643032508266358109840773

theorem tailTrace_3756904 : CollatzResearch.WordTrace tailWord_3756904 prefixEnd_3756904 643032508266358109840773 := by
  unfold tailWord_3756904
  simp only [CollatzResearch.WordTrace]
  refine ⟨68512772990692955482842883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91350363987590607310457177 68512772990692955482842883)
  ·
    refine ⟨102769159486039433224264325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68512772990692955482842883 102769159486039433224264325)
    ·
      refine ⟨19269217403632393729549561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102769159486039433224264325 19269217403632393729549561)
      ·
        refine ⟨14451913052724295297162171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19269217403632393729549561 14451913052724295297162171)
        ·
          refine ⟨21677869579086442945743257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14451913052724295297162171 21677869579086442945743257)
          ·
            refine ⟨16258402184314832209307443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21677869579086442945743257 16258402184314832209307443)
            ·
              refine ⟨24387603276472248313961165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16258402184314832209307443 24387603276472248313961165)
              ·
                refine ⟨9145351228677093117735437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24387603276472248313961165 9145351228677093117735437)
                ·
                  refine ⟨3429506710753909919150789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9145351228677093117735437 3429506710753909919150789)
                  ·
                    refine ⟨643032508266358109840773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3429506710753909919150789 643032508266358109840773)
                    ·
                      rfl

theorem cell23_3756904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 3, 3, 4].length) (baseStart_3756904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3756904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3756904 prefixEnd_3756904 := by exact prefixLift 3756904
  have htrace : WordTrace (prefixWord ++ tailWord_3756904) baseStart_3756904 baseEnd_3756904 := by
    simpa [prefixWord, tailWord_3756904, baseEnd_3756904] using wordTrace_append hprefix tailTrace_3756904
  have hstable : (prefixWord ++ tailWord_3756904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3756904).length < 2 ^ (prefixWord ++ tailWord_3756904).sum := by decide
  have hdescent : baseEnd_3756904 < baseStart_3756904 := by decide
  rcases family_descends (prefixWord ++ tailWord_3756904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3756938 : List Nat := [3, 1, 2, 4, 1, 1, 3, 3, 1, 4]
def baseStart_3756938 : Nat := 118140960795 + 3756938 * 2 ^ 59
def prefixEnd_3756938 : Nat := 4983230072969 + 3 ^ 40 * 3756938 * 2
def baseEnd_3756938 : Nat := 643038327713775732165721

theorem tailTrace_3756938 : CollatzResearch.WordTrace tailWord_3756938 prefixEnd_3756938 643038327713775732165721 := by
  unfold tailWord_3756938
  simp only [CollatzResearch.WordTrace]
  refine ⟨34256696515815683693105867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91351190708841823181615645 34256696515815683693105867)
  ·
    refine ⟨51385044773723525539658801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34256696515815683693105867 51385044773723525539658801)
    ·
      refine ⟨38538783580292644154744101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51385044773723525539658801 38538783580292644154744101)
      ·
        refine ⟨7226021921304870779014519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38538783580292644154744101 7226021921304870779014519)
        ·
          refine ⟨10839032881957306168521779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7226021921304870779014519 10839032881957306168521779)
          ·
            refine ⟨16258549322935959252782669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10839032881957306168521779 16258549322935959252782669)
            ·
              refine ⟨6096955996100984719793501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16258549322935959252782669 6096955996100984719793501)
              ·
                refine ⟨2286358498537869269922563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6096955996100984719793501 2286358498537869269922563)
                ·
                  refine ⟨3429537747806803904883845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2286358498537869269922563 3429537747806803904883845)
                  ·
                    refine ⟨643038327713775732165721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3429537747806803904883845 643038327713775732165721)
                    ·
                      rfl

theorem cell23_3756938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 3, 3, 1, 4].length) (baseStart_3756938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3756938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3756938 prefixEnd_3756938 := by exact prefixLift 3756938
  have htrace : WordTrace (prefixWord ++ tailWord_3756938) baseStart_3756938 baseEnd_3756938 := by
    simpa [prefixWord, tailWord_3756938, baseEnd_3756938] using wordTrace_append hprefix tailTrace_3756938
  have hstable : (prefixWord ++ tailWord_3756938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3756938).length < 2 ^ (prefixWord ++ tailWord_3756938).sum := by decide
  have hdescent : baseEnd_3756938 < baseStart_3756938 := by decide
  rcases family_descends (prefixWord ++ tailWord_3756938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3756982 : List Nat := [5, 1, 4, 1, 1, 1, 2, 1, 2, 2, 3]
def baseStart_3756982 : Nat := 118140960795 + 3756982 * 2 ^ 59
def prefixEnd_3756982 : Nat := 4983230072969 + 3 ^ 40 * 3756982 * 2
def baseEnd_3756982 : Nat := 1929137576290125024346961

theorem tailTrace_3756982 : CollatzResearch.WordTrace tailWord_3756982 prefixEnd_3756982 1929137576290125024346961 := by
  unfold tailWord_3756982
  simp only [CollatzResearch.WordTrace]
  refine ⟨8564274429693958142939075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 91352260583402220191350133 8564274429693958142939075)
  ·
    refine ⟨12846411644540937214408613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8564274429693958142939075 12846411644540937214408613)
    ·
      refine ⟨2408702183351425727701615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12846411644540937214408613 2408702183351425727701615)
      ·
        refine ⟨3613053275027138591552423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2408702183351425727701615 3613053275027138591552423)
        ·
          refine ⟨5419579912540707887328635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3613053275027138591552423 5419579912540707887328635)
          ·
            refine ⟨8129369868811061830992953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5419579912540707887328635 8129369868811061830992953)
            ·
              refine ⟨6097027401608296373244715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8129369868811061830992953 6097027401608296373244715)
              ·
                refine ⟨9145541102412444559867073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6097027401608296373244715 9145541102412444559867073)
                ·
                  refine ⟨6859155826809333419900305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9145541102412444559867073 6859155826809333419900305)
                  ·
                    refine ⟨5144366870107000064925229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6859155826809333419900305 5144366870107000064925229)
                    ·
                      refine ⟨1929137576290125024346961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5144366870107000064925229 1929137576290125024346961)
                      ·
                        rfl

theorem cell23_3756982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_3756982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3756982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3756982 prefixEnd_3756982 := by exact prefixLift 3756982
  have htrace : WordTrace (prefixWord ++ tailWord_3756982) baseStart_3756982 baseEnd_3756982 := by
    simpa [prefixWord, tailWord_3756982, baseEnd_3756982] using wordTrace_append hprefix tailTrace_3756982
  have hstable : (prefixWord ++ tailWord_3756982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3756982).length < 2 ^ (prefixWord ++ tailWord_3756982).sum := by decide
  have hdescent : baseEnd_3756982 < baseStart_3756982 := by decide
  rcases family_descends (prefixWord ++ tailWord_3756982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3756984 : List Nat := [2, 1, 2, 1, 2, 5, 1, 1, 3, 1, 4]
def baseStart_3756984 : Nat := 118140960795 + 3756984 * 2 ^ 59
def prefixEnd_3756984 : Nat := 4983230072969 + 3 ^ 40 * 3756984 * 2
def baseEnd_3756984 : Nat := 1929138603251434016521951

theorem tailTrace_3756984 : CollatzResearch.WordTrace tailWord_3756984 prefixEnd_3756984 1929138603251434016521951 := by
  unfold tailWord_3756984
  simp only [CollatzResearch.WordTrace]
  refine ⟨68514231910548042314299003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91352309214064056419065337 68514231910548042314299003)
  ·
    refine ⟨102771347865822063471448505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68514231910548042314299003 102771347865822063471448505)
    ·
      refine ⟨77078510899366547603586379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102771347865822063471448505 77078510899366547603586379)
      ·
        refine ⟨115617766349049821405379569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77078510899366547603586379 115617766349049821405379569)
        ·
          refine ⟨86713324761787366054034677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115617766349049821405379569 86713324761787366054034677)
          ·
            refine ⟨8129374196417565567565751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 86713324761787366054034677 8129374196417565567565751)
            ·
              refine ⟨12194061294626348351348627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8129374196417565567565751 12194061294626348351348627)
              ·
                refine ⟨18291091941939522527022941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12194061294626348351348627 18291091941939522527022941)
                ·
                  refine ⟨6859159478227320947633603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18291091941939522527022941 6859159478227320947633603)
                  ·
                    refine ⟨10288739217340981421450405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6859159478227320947633603 10288739217340981421450405)
                    ·
                      refine ⟨1929138603251434016521951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10288739217340981421450405 1929138603251434016521951)
                      ·
                        rfl

theorem cell23_3756984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 1, 3, 1, 4].length) (baseStart_3756984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3756984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3756984 prefixEnd_3756984 := by exact prefixLift 3756984
  have htrace : WordTrace (prefixWord ++ tailWord_3756984) baseStart_3756984 baseEnd_3756984 := by
    simpa [prefixWord, tailWord_3756984, baseEnd_3756984] using wordTrace_append hprefix tailTrace_3756984
  have hstable : (prefixWord ++ tailWord_3756984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3756984).length < 2 ^ (prefixWord ++ tailWord_3756984).sum := by decide
  have hdescent : baseEnd_3756984 < baseStart_3756984 := by decide
  rcases family_descends (prefixWord ++ tailWord_3756984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3757012 : List Nat := [2, 4, 1, 2, 1, 4, 2, 2, 1, 1, 3]
def baseStart_3757012 : Nat := 118140960795 + 3757012 * 2 ^ 59
def prefixEnd_3757012 : Nat := 4983230072969 + 3 ^ 40 * 3757012 * 2
def baseEnd_3757012 : Nat := 1929152980709759906971823

theorem tailTrace_3757012 : CollatzResearch.WordTrace tailWord_3757012 prefixEnd_3757012 1929152980709759906971823 := by
  unfold tailWord_3757012
  simp only [CollatzResearch.WordTrace]
  refine ⟨68514742532497322705308645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91352990043329763607078193 68514742532497322705308645)
  ·
    refine ⟨12846514224843248007245371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68514742532497322705308645 12846514224843248007245371)
    ·
      refine ⟨19269771337264872010868057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12846514224843248007245371 19269771337264872010868057)
      ·
        refine ⟨14452328502948654008151043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19269771337264872010868057 14452328502948654008151043)
        ·
          refine ⟨21678492754422981012226565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14452328502948654008151043 21678492754422981012226565)
          ·
            refine ⟨4064717391454308939792481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21678492754422981012226565 4064717391454308939792481)
            ·
              refine ⟨3048538043590731704844361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4064717391454308939792481 3048538043590731704844361)
              ·
                refine ⟨2286403532693048778633271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3048538043590731704844361 2286403532693048778633271)
                ·
                  refine ⟨3429605299039573167949907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2286403532693048778633271 3429605299039573167949907)
                  ·
                    refine ⟨5144407948559359751924861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3429605299039573167949907 5144407948559359751924861)
                    ·
                      refine ⟨1929152980709759906971823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5144407948559359751924861 1929152980709759906971823)
                      ·
                        rfl

theorem cell23_3757012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 2, 2, 1, 1, 3].length) (baseStart_3757012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3757012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3757012 prefixEnd_3757012 := by exact prefixLift 3757012
  have htrace : WordTrace (prefixWord ++ tailWord_3757012) baseStart_3757012 baseEnd_3757012 := by
    simpa [prefixWord, tailWord_3757012, baseEnd_3757012] using wordTrace_append hprefix tailTrace_3757012
  have hstable : (prefixWord ++ tailWord_3757012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3757012).length < 2 ^ (prefixWord ++ tailWord_3757012).sum := by decide
  have hdescent : baseEnd_3757012 < baseStart_3757012 := by decide
  rcases family_descends (prefixWord ++ tailWord_3757012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3757021 : List Nat := [1, 4, 3, 1, 2, 1, 1, 2, 3, 2, 3]
def baseStart_3757021 : Nat := 118140960795 + 3757021 * 2 ^ 59
def prefixEnd_3757021 : Nat := 4983230072969 + 3 ^ 40 * 3757021 * 2
def baseEnd_3757021 : Nat := 1929157602035650371759281

theorem tailTrace_3757021 : CollatzResearch.WordTrace tailWord_3757021 prefixEnd_3757021 1929157602035650371759281 := by
  unfold tailWord_3757021
  simp only [CollatzResearch.WordTrace]
  refine ⟨137029813321962039947694917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91353208881308026631796611 137029813321962039947694917)
  ·
    refine ⟨25693089997867882490192797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137029813321962039947694917 25693089997867882490192797)
    ·
      refine ⟨9634908749200455933822299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25693089997867882490192797 9634908749200455933822299)
      ·
        refine ⟨14452363123800683900733449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9634908749200455933822299 14452363123800683900733449)
        ·
          refine ⟨10839272342850512925550087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14452363123800683900733449 10839272342850512925550087)
          ·
            refine ⟨16258908514275769388325131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10839272342850512925550087 16258908514275769388325131)
            ·
              refine ⟨24388362771413654082487697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16258908514275769388325131 24388362771413654082487697)
              ·
                refine ⟨18291272078560240561865773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24388362771413654082487697 18291272078560240561865773)
                ·
                  refine ⟨6859227029460090210699665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18291272078560240561865773 6859227029460090210699665)
                  ·
                    refine ⟨5144420272095067658024749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6859227029460090210699665 5144420272095067658024749)
                    ·
                      refine ⟨1929157602035650371759281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5144420272095067658024749 1929157602035650371759281)
                      ·
                        rfl

theorem cell23_3757021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 2, 3, 2, 3].length) (baseStart_3757021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3757021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3757021 prefixEnd_3757021 := by exact prefixLift 3757021
  have htrace : WordTrace (prefixWord ++ tailWord_3757021) baseStart_3757021 baseEnd_3757021 := by
    simpa [prefixWord, tailWord_3757021, baseEnd_3757021] using wordTrace_append hprefix tailTrace_3757021
  have hstable : (prefixWord ++ tailWord_3757021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3757021).length < 2 ^ (prefixWord ++ tailWord_3757021).sum := by decide
  have hdescent : baseEnd_3757021 < baseStart_3757021 := by decide
  rcases family_descends (prefixWord ++ tailWord_3757021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3757031 : List Nat := [1, 1, 5, 2, 2, 2, 2, 1, 1, 2, 4]
def baseStart_3757031 : Nat := 118140960795 + 3757031 * 2 ^ 59
def prefixEnd_3757031 : Nat := 4983230072969 + 3 ^ 40 * 3757031 * 2
def baseEnd_3757031 : Nat := 1929162736842195332634235

theorem tailTrace_3757031 : CollatzResearch.WordTrace tailWord_3757031 prefixEnd_3757031 1929162736842195332634235 := by
  unfold tailWord_3757031
  simp only [CollatzResearch.WordTrace]
  refine ⟨137030178051925811655558947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91353452034617207770372631 137030178051925811655558947)
  ·
    refine ⟨205545267077888717483338421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137030178051925811655558947 205545267077888717483338421)
    ·
      refine ⟨19269868788552067264062977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 205545267077888717483338421 19269868788552067264062977)
      ·
        refine ⟨14452401591414050448047233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19269868788552067264062977 14452401591414050448047233)
        ·
          refine ⟨10839301193560537836035425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14452401591414050448047233 10839301193560537836035425)
          ·
            refine ⟨8129475895170403377026569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10839301193560537836035425 8129475895170403377026569)
            ·
              refine ⟨6097106921377802532769927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8129475895170403377026569 6097106921377802532769927)
              ·
                refine ⟨9145660382066703799154891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6097106921377802532769927 9145660382066703799154891)
                ·
                  refine ⟨13718490573100055698732337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9145660382066703799154891 13718490573100055698732337)
                  ·
                    refine ⟨10288867929825041774049253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13718490573100055698732337 10288867929825041774049253)
                    ·
                      refine ⟨1929162736842195332634235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10288867929825041774049253 1929162736842195332634235)
                      ·
                        rfl

theorem cell23_3757031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 2, 1, 1, 2, 4].length) (baseStart_3757031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3757031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3757031 prefixEnd_3757031 := by exact prefixLift 3757031
  have htrace : WordTrace (prefixWord ++ tailWord_3757031) baseStart_3757031 baseEnd_3757031 := by
    simpa [prefixWord, tailWord_3757031, baseEnd_3757031] using wordTrace_append hprefix tailTrace_3757031
  have hstable : (prefixWord ++ tailWord_3757031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3757031).length < 2 ^ (prefixWord ++ tailWord_3757031).sum := by decide
  have hdescent : baseEnd_3757031 < baseStart_3757031 := by decide
  rcases family_descends (prefixWord ++ tailWord_3757031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3757068 : List Nat := [2, 2, 1, 2, 3, 2, 3, 2, 2, 1, 3]
def baseStart_3757068 : Nat := 118140960795 + 3757068 * 2 ^ 59
def prefixEnd_3757068 : Nat := 4983230072969 + 3 ^ 40 * 3757068 * 2
def baseEnd_3757068 : Nat := 1929181735626411687871565

theorem tailTrace_3757068 : CollatzResearch.WordTrace tailWord_3757068 prefixEnd_3757068 1929181735626411687871565 := by
  unfold tailWord_3757068
  simp only [CollatzResearch.WordTrace]
  refine ⟨68515763776395883487327929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91354351701861177983103905 68515763776395883487327929)
  ·
    refine ⟨51386822832296912615495947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68515763776395883487327929 51386822832296912615495947)
    ·
      refine ⟨77080234248445368923243921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51386822832296912615495947 77080234248445368923243921)
      ·
        refine ⟨57810175686334026692432941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77080234248445368923243921 57810175686334026692432941)
        ·
          refine ⟨21678815882375260009662353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57810175686334026692432941 21678815882375260009662353)
          ·
            refine ⟨16259111911781445007246765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21678815882375260009662353 16259111911781445007246765)
            ·
              refine ⟨6097166966918041877717537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16259111911781445007246765 6097166966918041877717537)
              ·
                refine ⟨4572875225188531408288153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6097166966918041877717537 4572875225188531408288153)
                ·
                  refine ⟨3429656418891398556216115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4572875225188531408288153 3429656418891398556216115)
                  ·
                    refine ⟨5144484628337097834324173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3429656418891398556216115 5144484628337097834324173)
                    ·
                      refine ⟨1929181735626411687871565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5144484628337097834324173 1929181735626411687871565)
                      ·
                        rfl

theorem cell23_3757068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 3, 2, 2, 1, 3].length) (baseStart_3757068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3757068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3757068 prefixEnd_3757068 := by exact prefixLift 3757068
  have htrace : WordTrace (prefixWord ++ tailWord_3757068) baseStart_3757068 baseEnd_3757068 := by
    simpa [prefixWord, tailWord_3757068, baseEnd_3757068] using wordTrace_append hprefix tailTrace_3757068
  have hstable : (prefixWord ++ tailWord_3757068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3757068).length < 2 ^ (prefixWord ++ tailWord_3757068).sum := by decide
  have hdescent : baseEnd_3757068 < baseStart_3757068 := by decide
  rcases family_descends (prefixWord ++ tailWord_3757068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3757085 : List Nat := [1, 4, 2, 2, 4, 1, 1, 1, 1, 3, 3]
def baseStart_3757085 : Nat := 118140960795 + 3757085 * 2 ^ 59
def prefixEnd_3757085 : Nat := 4983230072969 + 3 ^ 40 * 3757085 * 2
def baseEnd_3757085 : Nat := 1929190464797538121358987

theorem tailTrace_3757085 : CollatzResearch.WordTrace tailWord_3757085 prefixEnd_3757085 1929190464797538121358987 := by
  unfold tailWord_3757085
  simp only [CollatzResearch.WordTrace]
  refine ⟨137032147593730178878024709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91354765062486785918683139 137032147593730178878024709)
  ·
    refine ⟨25693527673824408539629633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137032147593730178878024709 25693527673824408539629633)
    ·
      refine ⟨19270145755368306404722225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25693527673824408539629633 19270145755368306404722225)
      ·
        refine ⟨14452609316526229803541669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19270145755368306404722225 14452609316526229803541669)
        ·
          refine ⟨2709864246848668088164063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14452609316526229803541669 2709864246848668088164063)
          ·
            refine ⟨4064796370273002132246095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2709864246848668088164063 4064796370273002132246095)
            ·
              refine ⟨6097194555409503198369143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4064796370273002132246095 6097194555409503198369143)
              ·
                refine ⟨9145791833114254797553715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6097194555409503198369143 9145791833114254797553715)
                ·
                  refine ⟨13718687749671382196330573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9145791833114254797553715 13718687749671382196330573)
                  ·
                    refine ⟨5144507906126768323623965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13718687749671382196330573 5144507906126768323623965)
                    ·
                      refine ⟨1929190464797538121358987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5144507906126768323623965 1929190464797538121358987)
                      ·
                        rfl

theorem cell23_3757085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 1, 1, 1, 3, 3].length) (baseStart_3757085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3757085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3757085 prefixEnd_3757085 := by exact prefixLift 3757085
  have htrace : WordTrace (prefixWord ++ tailWord_3757085) baseStart_3757085 baseEnd_3757085 := by
    simpa [prefixWord, tailWord_3757085, baseEnd_3757085] using wordTrace_append hprefix tailTrace_3757085
  have hstable : (prefixWord ++ tailWord_3757085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3757085).length < 2 ^ (prefixWord ++ tailWord_3757085).sum := by decide
  have hdescent : baseEnd_3757085 < baseStart_3757085 := by decide
  rcases family_descends (prefixWord ++ tailWord_3757085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3757095 : List Nat := [1, 1, 7, 1, 1, 1, 1, 4, 1, 3, 2]
def baseStart_3757095 : Nat := 118140960795 + 3757095 * 2 ^ 59
def prefixEnd_3757095 : Nat := 4983230072969 + 3 ^ 40 * 3757095 * 2
def baseEnd_3757095 : Nat := 1929195599604083082233941

theorem tailTrace_3757095 : CollatzResearch.WordTrace tailWord_3757095 prefixEnd_3757095 1929195599604083082233941 := by
  unfold tailWord_3757095
  simp only [CollatzResearch.WordTrace]
  refine ⟨137032512323693950585888739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91355008215795967057259159 137032512323693950585888739)
  ·
    refine ⟨205548768485540925878833109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137032512323693950585888739 205548768485540925878833109)
    ·
      refine ⟨4817549261379865450285151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 205548768485540925878833109 4817549261379865450285151)
      ·
        refine ⟨7226323892069798175427727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4817549261379865450285151 7226323892069798175427727)
        ·
          refine ⟨10839485838104697263141591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7226323892069798175427727 10839485838104697263141591)
          ·
            refine ⟨16259228757157045894712387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10839485838104697263141591 16259228757157045894712387)
            ·
              refine ⟨24388843135735568842068581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16259228757157045894712387 24388843135735568842068581)
              ·
                refine ⟨4572908087950419157887859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24388843135735568842068581 4572908087950419157887859)
                ·
                  refine ⟨6859362131925628736831789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4572908087950419157887859 6859362131925628736831789)
                  ·
                    refine ⟨2572260799472110776311921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6859362131925628736831789 2572260799472110776311921)
                    ·
                      refine ⟨1929195599604083082233941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2572260799472110776311921 1929195599604083082233941)
                      ·
                        rfl

theorem cell23_3757095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 4, 1, 3, 2].length) (baseStart_3757095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3757095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3757095 prefixEnd_3757095 := by exact prefixLift 3757095
  have htrace : WordTrace (prefixWord ++ tailWord_3757095) baseStart_3757095 baseEnd_3757095 := by
    simpa [prefixWord, tailWord_3757095, baseEnd_3757095] using wordTrace_append hprefix tailTrace_3757095
  have hstable : (prefixWord ++ tailWord_3757095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3757095).length < 2 ^ (prefixWord ++ tailWord_3757095).sum := by decide
  have hdescent : baseEnd_3757095 < baseStart_3757095 := by decide
  rcases family_descends (prefixWord ++ tailWord_3757095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3757144 : List Nat := [2, 1, 2, 2, 1, 3, 1, 2, 4, 5]
def baseStart_3757144 : Nat := 118140960795 + 3757144 * 2 ^ 59
def prefixEnd_3757144 : Nat := 4983230072969 + 3 ^ 40 * 3757144 * 2
def baseEnd_3757144 : Nat := 643073586718717796840405

theorem tailTrace_3757144 : CollatzResearch.WordTrace tailWord_3757144 prefixEnd_3757144 643073586718717796840405 := by
  unfold tailWord_3757144
  simp only [CollatzResearch.WordTrace]
  refine ⟨68517149750258215977211243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91356199667010954636281657 68517149750258215977211243)
  ·
    refine ⟨102775724625387323965816865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68517149750258215977211243 102775724625387323965816865)
    ·
      refine ⟨77081793469040492974362649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102775724625387323965816865 77081793469040492974362649)
      ·
        refine ⟨57811345101780369730771987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77081793469040492974362649 57811345101780369730771987)
        ·
          refine ⟨86717017652670554596157981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57811345101780369730771987 86717017652670554596157981)
          ·
            refine ⟨32518881619751457973559243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86717017652670554596157981 32518881619751457973559243)
            ·
              refine ⟨48778322429627186960338865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32518881619751457973559243 48778322429627186960338865)
              ·
                refine ⟨36583741822220390220254149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48778322429627186960338865 36583741822220390220254149)
                ·
                  refine ⟨6859451591666323166297653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36583741822220390220254149 6859451591666323166297653)
                  ·
                    refine ⟨643073586718717796840405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6859451591666323166297653 643073586718717796840405)
                    ·
                      rfl

theorem cell23_3757144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 2, 4, 5].length) (baseStart_3757144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3757144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3757144 prefixEnd_3757144 := by exact prefixLift 3757144
  have htrace : WordTrace (prefixWord ++ tailWord_3757144) baseStart_3757144 baseEnd_3757144 := by
    simpa [prefixWord, tailWord_3757144, baseEnd_3757144] using wordTrace_append hprefix tailTrace_3757144
  have hstable : (prefixWord ++ tailWord_3757144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3757144).length < 2 ^ (prefixWord ++ tailWord_3757144).sum := by decide
  have hdescent : baseEnd_3757144 < baseStart_3757144 := by decide
  rcases family_descends (prefixWord ++ tailWord_3757144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3757161 : List Nat := [1, 2, 1, 1, 1, 7, 2, 1, 2, 5]
def baseStart_3757161 : Nat := 118140960795 + 3757161 * 2 ^ 59
def prefixEnd_3757161 : Nat := 4983230072969 + 3 ^ 40 * 3757161 * 2
def baseEnd_3757161 : Nat := 643076496442426608002879

theorem tailTrace_3757161 : CollatzResearch.WordTrace tailWord_3757161 prefixEnd_3757161 643076496442426608002879 := by
  unfold tailWord_3757161
  simp only [CollatzResearch.WordTrace]
  refine ⟨137034919541454843857791337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91356613027636562571860891 137034919541454843857791337)
  ·
    refine ⟨102776189656091132893343503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137034919541454843857791337 102776189656091132893343503)
    ·
      refine ⟨154164284484136699340015255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102776189656091132893343503 154164284484136699340015255)
      ·
        refine ⟨231246426726205049010022883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154164284484136699340015255 231246426726205049010022883)
        ·
          refine ⟨346869640089307573515034325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231246426726205049010022883 346869640089307573515034325)
          ·
            refine ⟨8129757189593146254258617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 346869640089307573515034325 8129757189593146254258617)
            ·
              refine ⟨6097317892194859690693963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8129757189593146254258617 6097317892194859690693963)
              ·
                refine ⟨9145976838292289536040945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6097317892194859690693963 9145976838292289536040945)
                ·
                  refine ⟨6859482628719217152030709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9145976838292289536040945 6859482628719217152030709)
                  ·
                    refine ⟨643076496442426608002879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6859482628719217152030709 643076496442426608002879)
                    ·
                      rfl

theorem cell23_3757161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 2, 1, 2, 5].length) (baseStart_3757161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3757161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3757161 prefixEnd_3757161 := by exact prefixLift 3757161
  have htrace : WordTrace (prefixWord ++ tailWord_3757161) baseStart_3757161 baseEnd_3757161 := by
    simpa [prefixWord, tailWord_3757161, baseEnd_3757161] using wordTrace_append hprefix tailTrace_3757161
  have hstable : (prefixWord ++ tailWord_3757161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3757161).length < 2 ^ (prefixWord ++ tailWord_3757161).sum := by decide
  have hdescent : baseEnd_3757161 < baseStart_3757161 := by decide
  rcases family_descends (prefixWord ++ tailWord_3757161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3757181 : List Nat := [1, 4, 1, 1, 3, 1, 1, 4, 2, 1, 4]
def baseStart_3757181 : Nat := 118140960795 + 3757181 * 2 ^ 59
def prefixEnd_3757181 : Nat := 4983230072969 + 3 ^ 40 * 3757181 * 2
def baseEnd_3757181 : Nat := 1929239758940369745758545

theorem tailTrace_3757181 : CollatzResearch.WordTrace tailWord_3757181 prefixEnd_3757181 1929239758940369745758545 := by
  unfold tailWord_3757181
  simp only [CollatzResearch.WordTrace]
  refine ⟨137035649001382387273519397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91357099334254924849012931 137035649001382387273519397)
  ·
    refine ⟨25694184187759197613784887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137035649001382387273519397 25694184187759197613784887)
    ·
      refine ⟨38541276281638796420677331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25694184187759197613784887 38541276281638796420677331)
      ·
        refine ⟨57811914422458194631015997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38541276281638796420677331 57811914422458194631015997)
        ·
          refine ⟨21679467908421822986630999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57811914422458194631015997 21679467908421822986630999)
          ·
            refine ⟨32519201862632734479946499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21679467908421822986630999 32519201862632734479946499)
            ·
              refine ⟨48778802793949101719919749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32519201862632734479946499 48778802793949101719919749)
              ·
                refine ⟨9146025523865456572484953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48778802793949101719919749 9146025523865456572484953)
                ·
                  refine ⟨6859519142899092429363715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9146025523865456572484953 6859519142899092429363715)
                  ·
                    refine ⟨10289278714348638644045573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6859519142899092429363715 10289278714348638644045573)
                    ·
                      refine ⟨1929239758940369745758545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10289278714348638644045573 1929239758940369745758545)
                      ·
                        rfl

theorem cell23_3757181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 4, 2, 1, 4].length) (baseStart_3757181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3757181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3757181 prefixEnd_3757181 := by exact prefixLift 3757181
  have htrace : WordTrace (prefixWord ++ tailWord_3757181) baseStart_3757181 baseEnd_3757181 := by
    simpa [prefixWord, tailWord_3757181, baseEnd_3757181] using wordTrace_append hprefix tailTrace_3757181
  have hstable : (prefixWord ++ tailWord_3757181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3757181).length < 2 ^ (prefixWord ++ tailWord_3757181).sum := by decide
  have hdescent : baseEnd_3757181 < baseStart_3757181 := by decide
  rcases family_descends (prefixWord ++ tailWord_3757181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3757191 : List Nat := [1, 1, 4, 2, 1, 1, 1, 5, 3, 4]
def baseStart_3757191 : Nat := 118140960795 + 3757191 * 2 ^ 59
def prefixEnd_3757191 : Nat := 4983230072969 + 3 ^ 40 * 3757191 * 2
def baseEnd_3757191 : Nat := 643081631248971568877833

theorem tailTrace_3757191 : CollatzResearch.WordTrace tailWord_3757191 prefixEnd_3757191 643081631248971568877833 := by
  unfold tailWord_3757191
  simp only [CollatzResearch.WordTrace]
  refine ⟨137036013731346158981383427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91357342487564105987588951 137036013731346158981383427)
  ·
    refine ⟨205554020597019238472075141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137036013731346158981383427 205554020597019238472075141)
    ·
      refine ⟨38541378861941107213514089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 205554020597019238472075141 38541378861941107213514089)
      ·
        refine ⟨28906034146455830410135567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38541378861941107213514089 28906034146455830410135567)
        ·
          refine ⟨43359051219683745615203351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28906034146455830410135567 43359051219683745615203351)
          ·
            refine ⟨65038576829525618422805027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43359051219683745615203351 65038576829525618422805027)
            ·
              refine ⟨97557865244288427634207541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65038576829525618422805027 97557865244288427634207541)
              ·
                refine ⟨9146049866652040090706957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 97557865244288427634207541 9146049866652040090706957)
                ·
                  refine ⟨3429768699994515034015109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9146049866652040090706957 3429768699994515034015109)
                  ·
                    refine ⟨643081631248971568877833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3429768699994515034015109 643081631248971568877833)
                    ·
                      rfl

theorem cell23_3757191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 5, 3, 4].length) (baseStart_3757191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3757191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3757191 prefixEnd_3757191 := by exact prefixLift 3757191
  have htrace : WordTrace (prefixWord ++ tailWord_3757191) baseStart_3757191 baseEnd_3757191 := by
    simpa [prefixWord, tailWord_3757191, baseEnd_3757191] using wordTrace_append hprefix tailTrace_3757191
  have hstable : (prefixWord ++ tailWord_3757191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3757191).length < 2 ^ (prefixWord ++ tailWord_3757191).sum := by decide
  have hdescent : baseEnd_3757191 < baseStart_3757191 := by decide
  rcases family_descends (prefixWord ++ tailWord_3757191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3757198 : List Nat := [4, 1, 1, 3, 2, 1, 1, 1, 1, 6, 2]
def baseStart_3757198 : Nat := 118140960795 + 3757198 * 2 ^ 59
def prefixEnd_3757198 : Nat := 4983230072969 + 3 ^ 40 * 3757198 * 2
def baseEnd_3757198 : Nat := 1929248488111496179245967

theorem tailTrace_3757198 : CollatzResearch.WordTrace tailWord_3757198 prefixEnd_3757198 1929248488111496179245967 := by
  unfold tailWord_3757198
  simp only [CollatzResearch.WordTrace]
  refine ⟨17129533630290099897111031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91357512694880532784592165 17129533630290099897111031)
  ·
    refine ⟨25694300445435149845666547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17129533630290099897111031 25694300445435149845666547)
    ·
      refine ⟨38541450668152724768499821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25694300445435149845666547 38541450668152724768499821)
      ·
        refine ⟨14453044000557271788187433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38541450668152724768499821 14453044000557271788187433)
        ·
          refine ⟨10839783000417953841140575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14453044000557271788187433 10839783000417953841140575)
          ·
            refine ⟨16259674500626930761710863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10839783000417953841140575 16259674500626930761710863)
            ·
              refine ⟨24389511750940396142566295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16259674500626930761710863 24389511750940396142566295)
              ·
                refine ⟨36584267626410594213849443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24389511750940396142566295 36584267626410594213849443)
                ·
                  refine ⟨54876401439615891320774165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36584267626410594213849443 54876401439615891320774165)
                  ·
                    refine ⟨2572331317481994905661289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 54876401439615891320774165 2572331317481994905661289)
                    ·
                      refine ⟨1929248488111496179245967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2572331317481994905661289 1929248488111496179245967)
                      ·
                        rfl

theorem cell23_3757198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 1, 1, 6, 2].length) (baseStart_3757198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3757198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3757198 prefixEnd_3757198 := by exact prefixLift 3757198
  have htrace : WordTrace (prefixWord ++ tailWord_3757198) baseStart_3757198 baseEnd_3757198 := by
    simpa [prefixWord, tailWord_3757198, baseEnd_3757198] using wordTrace_append hprefix tailTrace_3757198
  have hstable : (prefixWord ++ tailWord_3757198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3757198).length < 2 ^ (prefixWord ++ tailWord_3757198).sum := by decide
  have hdescent : baseEnd_3757198 < baseStart_3757198 := by decide
  rcases family_descends (prefixWord ++ tailWord_3757198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3757208 : List Nat := [2, 1, 2, 4, 2, 2, 1, 2, 3, 4]
def baseStart_3757208 : Nat := 118140960795 + 3757208 * 2 ^ 59
def prefixEnd_3757208 : Nat := 4983230072969 + 3 ^ 40 * 3757208 * 2
def baseEnd_3757208 : Nat := 643084540972680380040307

theorem tailTrace_3757208 : CollatzResearch.WordTrace tailWord_3757208 prefixEnd_3757208 643084540972680380040307 := by
  unfold tailWord_3757208
  simp only [CollatzResearch.WordTrace]
  refine ⟨68518316886142285442376139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91357755848189713923168185 68518316886142285442376139)
  ·
    refine ⟨102777475329213428163564209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68518316886142285442376139 102777475329213428163564209)
    ·
      refine ⟨77083106496910071122673157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102777475329213428163564209 77083106496910071122673157)
      ·
        refine ⟨14453082468170638335501217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77083106496910071122673157 14453082468170638335501217)
        ·
          refine ⟨10839811851127978751625913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14453082468170638335501217 10839811851127978751625913)
          ·
            refine ⟨8129858888345984063719435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10839811851127978751625913 8129858888345984063719435)
            ·
              refine ⟨12194788332518976095579153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8129858888345984063719435 12194788332518976095579153)
              ·
                refine ⟨9146091249389232071684365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12194788332518976095579153 9146091249389232071684365)
                ·
                  refine ⟨3429784218520962026881637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9146091249389232071684365 3429784218520962026881637)
                  ·
                    refine ⟨643084540972680380040307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3429784218520962026881637 643084540972680380040307)
                    ·
                      rfl

theorem cell23_3757208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 2, 3, 4].length) (baseStart_3757208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3757208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3757208 prefixEnd_3757208 := by exact prefixLift 3757208
  have htrace : WordTrace (prefixWord ++ tailWord_3757208) baseStart_3757208 baseEnd_3757208 := by
    simpa [prefixWord, tailWord_3757208, baseEnd_3757208] using wordTrace_append hprefix tailTrace_3757208
  have hstable : (prefixWord ++ tailWord_3757208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3757208).length < 2 ^ (prefixWord ++ tailWord_3757208).sum := by decide
  have hdescent : baseEnd_3757208 < baseStart_3757208 := by decide
  rcases family_descends (prefixWord ++ tailWord_3757208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3757215 : List Nat := [1, 1, 2, 6, 2, 2, 1, 1, 2, 1, 4]
def baseStart_3757215 : Nat := 118140960795 + 3757215 * 2 ^ 59
def prefixEnd_3757215 : Nat := 4983230072969 + 3 ^ 40 * 3757215 * 2
def baseEnd_3757215 : Nat := 1929257217282622612733389

theorem tailTrace_3757215 : CollatzResearch.WordTrace tailWord_3757215 prefixEnd_3757215 1929257217282622612733389 := by
  unfold tailWord_3757215
  simp only [CollatzResearch.WordTrace]
  refine ⟨137036889083259211080257099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91357926055506140720171399 137036889083259211080257099)
  ·
    refine ⟨205555333624888816620385649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137036889083259211080257099 205555333624888816620385649)
    ·
      refine ⟨154166500218666612465289237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205555333624888816620385649 154166500218666612465289237)
      ·
        refine ⟨7226554697749997459310433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 154166500218666612465289237 7226554697749997459310433)
        ·
          refine ⟨5419916023312498094482825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7226554697749997459310433 5419916023312498094482825)
          ·
            refine ⟨4064937017484373570862119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5419916023312498094482825 4064937017484373570862119)
            ·
              refine ⟨6097405526226560356293179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4064937017484373570862119 6097405526226560356293179)
              ·
                refine ⟨9146108289339840534439769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6097405526226560356293179 9146108289339840534439769)
                ·
                  refine ⟨6859581217004880400829827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9146108289339840534439769 6859581217004880400829827)
                  ·
                    refine ⟨10289371825507320601244741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6859581217004880400829827 10289371825507320601244741)
                    ·
                      refine ⟨1929257217282622612733389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10289371825507320601244741 1929257217282622612733389)
                      ·
                        rfl

theorem cell23_3757215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_3757215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3757215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3757215 prefixEnd_3757215 := by exact prefixLift 3757215
  have htrace : WordTrace (prefixWord ++ tailWord_3757215) baseStart_3757215 baseEnd_3757215 := by
    simpa [prefixWord, tailWord_3757215, baseEnd_3757215] using wordTrace_append hprefix tailTrace_3757215
  have hstable : (prefixWord ++ tailWord_3757215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3757215).length < 2 ^ (prefixWord ++ tailWord_3757215).sum := by decide
  have hdescent : baseEnd_3757215 < baseStart_3757215 := by decide
  rcases family_descends (prefixWord ++ tailWord_3757215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3757258 : List Nat := [3, 1, 2, 1, 3, 2, 1, 2, 1, 5, 2]
def baseStart_3757258 : Nat := 118140960795 + 3757258 * 2 ^ 59
def prefixEnd_3757258 : Nat := 4983230072969 + 3 ^ 40 * 3757258 * 2
def baseEnd_3757258 : Nat := 1929279296950765944495691

theorem tailTrace_3757258 : CollatzResearch.WordTrace tailWord_3757258 prefixEnd_3757258 1929279296950765944495691 := by
  unfold tailWord_3757258
  simp only [CollatzResearch.WordTrace]
  refine ⟨34259614355525857356018107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91358971614735619616048285 34259614355525857356018107)
  ·
    refine ⟨51389421533288786034027161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34259614355525857356018107 51389421533288786034027161)
    ·
      refine ⟨38542066149966589525520371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51389421533288786034027161 38542066149966589525520371)
      ·
        refine ⟨57813099224949884288280557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38542066149966589525520371 57813099224949884288280557)
        ·
          refine ⟨21679912209356206608105209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57813099224949884288280557 21679912209356206608105209)
          ·
            refine ⟨16259934157017154956078907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21679912209356206608105209 16259934157017154956078907)
            ·
              refine ⟨24389901235525732434118361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16259934157017154956078907 24389901235525732434118361)
              ·
                refine ⟨18292425926644299325588771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24389901235525732434118361 18292425926644299325588771)
                ·
                  refine ⟨27438638889966448988383157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18292425926644299325588771 27438638889966448988383157)
                  ·
                    refine ⟨2572372395934354592660921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27438638889966448988383157 2572372395934354592660921)
                    ·
                      refine ⟨1929279296950765944495691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2572372395934354592660921 1929279296950765944495691)
                      ·
                        rfl

theorem cell23_3757258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 2, 1, 5, 2].length) (baseStart_3757258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3757258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3757258 prefixEnd_3757258 := by exact prefixLift 3757258
  have htrace : WordTrace (prefixWord ++ tailWord_3757258) baseStart_3757258 baseEnd_3757258 := by
    simpa [prefixWord, tailWord_3757258, baseEnd_3757258] using wordTrace_append hprefix tailTrace_3757258
  have hstable : (prefixWord ++ tailWord_3757258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3757258).length < 2 ^ (prefixWord ++ tailWord_3757258).sum := by decide
  have hdescent : baseEnd_3757258 < baseStart_3757258 := by decide
  rcases family_descends (prefixWord ++ tailWord_3757258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3757271 : List Nat := [1, 1, 3, 2, 1, 2, 2, 3, 3, 1, 4]
def baseStart_3757271 : Nat := 118140960795 + 3757271 * 2 ^ 59
def prefixEnd_3757271 : Nat := 4983230072969 + 3 ^ 40 * 3757271 * 2
def baseEnd_3757271 : Nat := 1929285972199274393633131

theorem tailTrace_3757271 : CollatzResearch.WordTrace tailWord_3757271 prefixEnd_3757271 1929285972199274393633131 := by
  unfold tailWord_3757271
  simp only [CollatzResearch.WordTrace]
  refine ⟨137038931571056332644295667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91359287714037555096197111 137038931571056332644295667)
  ·
    refine ⟨205558397356584498966443501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137038931571056332644295667 205558397356584498966443501)
    ·
      refine ⟨77084399008719187112416313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205558397356584498966443501 77084399008719187112416313)
      ·
        refine ⟨57813299256539390334312235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77084399008719187112416313 57813299256539390334312235)
        ·
          refine ⟨86719948884809085501468353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57813299256539390334312235 86719948884809085501468353)
          ·
            refine ⟨65039961663606814126101265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86719948884809085501468353 65039961663606814126101265)
            ·
              refine ⟨48779971247705110594575949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65039961663606814126101265 48779971247705110594575949)
              ·
                refine ⟨18292489217889416472965981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48779971247705110594575949 18292489217889416472965981)
                ·
                  refine ⟨6859683456708531177362243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18292489217889416472965981 6859683456708531177362243)
                  ·
                    refine ⟨10289525185062796766043365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6859683456708531177362243 10289525185062796766043365)
                    ·
                      refine ⟨1929285972199274393633131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10289525185062796766043365 1929285972199274393633131)
                      ·
                        rfl

theorem cell23_3757271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 3, 3, 1, 4].length) (baseStart_3757271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3757271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3757271 prefixEnd_3757271 := by exact prefixLift 3757271
  have htrace : WordTrace (prefixWord ++ tailWord_3757271) baseStart_3757271 baseEnd_3757271 := by
    simpa [prefixWord, tailWord_3757271, baseEnd_3757271] using wordTrace_append hprefix tailTrace_3757271
  have hstable : (prefixWord ++ tailWord_3757271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3757271).length < 2 ^ (prefixWord ++ tailWord_3757271).sum := by decide
  have hdescent : baseEnd_3757271 < baseStart_3757271 := by decide
  rcases family_descends (prefixWord ++ tailWord_3757271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3757288 : List Nat := [2, 1, 4, 1, 2, 1, 1, 5, 1, 1, 4]
def baseStart_3757288 : Nat := 118140960795 + 3757288 * 2 ^ 59
def prefixEnd_3757288 : Nat := 4983230072969 + 3 ^ 40 * 3757288 * 2
def baseEnd_3757288 : Nat := 1929294701370400827120553

theorem tailTrace_3757288 : CollatzResearch.WordTrace tailWord_3757288 prefixEnd_3757288 1929294701370400827120553 := by
  unfold tailWord_3757288
  simp only [CollatzResearch.WordTrace]
  refine ⟨68519775805997372273832259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91359701074663163031776345 68519775805997372273832259)
  ·
    refine ⟨102779663708996058410748389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68519775805997372273832259 102779663708996058410748389)
    ·
      refine ⟨19271186945436760952015323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102779663708996058410748389 19271186945436760952015323)
      ·
        refine ⟨28906780418155141428022985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19271186945436760952015323 28906780418155141428022985)
        ·
          refine ⟨21680085313616356071017239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28906780418155141428022985 21680085313616356071017239)
          ·
            refine ⟨32520127970424534106525859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21680085313616356071017239 32520127970424534106525859)
            ·
              refine ⟨48780191955636801159788789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32520127970424534106525859 48780191955636801159788789)
              ·
                refine ⟨4573142995840950108730199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48780191955636801159788789 4573142995840950108730199)
                ·
                  refine ⟨6859714493761425163095299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4573142995840950108730199 6859714493761425163095299)
                  ·
                    refine ⟨10289571740642137744642949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6859714493761425163095299 10289571740642137744642949)
                    ·
                      refine ⟨1929294701370400827120553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10289571740642137744642949 1929294701370400827120553)
                      ·
                        rfl

theorem cell23_3757288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 5, 1, 1, 4].length) (baseStart_3757288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3757288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3757288 prefixEnd_3757288 := by exact prefixLift 3757288
  have htrace : WordTrace (prefixWord ++ tailWord_3757288) baseStart_3757288 baseEnd_3757288 := by
    simpa [prefixWord, tailWord_3757288, baseEnd_3757288] using wordTrace_append hprefix tailTrace_3757288
  have hstable : (prefixWord ++ tailWord_3757288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3757288).length < 2 ^ (prefixWord ++ tailWord_3757288).sum := by decide
  have hdescent : baseEnd_3757288 < baseStart_3757288 := by decide
  rcases family_descends (prefixWord ++ tailWord_3757288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3757291 : List Nat := [1, 1, 1, 1, 2, 6, 1, 3, 1, 1, 5]
def baseStart_3757291 : Nat := 118140960795 + 3757291 * 2 ^ 59
def prefixEnd_3757291 : Nat := 4983230072969 + 3 ^ 40 * 3757291 * 2
def baseEnd_3757291 : Nat := 1929296241812364315383039

theorem tailTrace_3757291 : CollatzResearch.WordTrace tailWord_3757291 prefixEnd_3757291 1929296241812364315383039 := by
  unfold tailWord_3757291
  simp only [CollatzResearch.WordTrace]
  refine ⟨137039661030983876060023727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91359774020655917373349151 137039661030983876060023727)
  ·
    refine ⟨205559491546475814090035591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137039661030983876060023727 205559491546475814090035591)
    ·
      refine ⟨308339237319713721135053387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205559491546475814090035591 308339237319713721135053387)
      ·
        refine ⟨462508855979570581702580081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308339237319713721135053387 462508855979570581702580081)
        ·
          refine ⟨346881641984677936276935061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 462508855979570581702580081 346881641984677936276935061)
          ·
            refine ⟨16260076968031778262981331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 346881641984677936276935061 16260076968031778262981331)
            ·
              refine ⟨24390115452047667394471997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16260076968031778262981331 24390115452047667394471997)
              ·
                refine ⟨9146293294517875272926999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24390115452047667394471997 9146293294517875272926999)
                ·
                  refine ⟨13719439941776812909390499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9146293294517875272926999 13719439941776812909390499)
                  ·
                    refine ⟨20579159912665219364085749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13719439941776812909390499 20579159912665219364085749)
                    ·
                      refine ⟨1929296241812364315383039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20579159912665219364085749 1929296241812364315383039)
                      ·
                        rfl

theorem cell23_3757291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 3, 1, 1, 5].length) (baseStart_3757291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3757291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3757291 prefixEnd_3757291 := by exact prefixLift 3757291
  have htrace : WordTrace (prefixWord ++ tailWord_3757291) baseStart_3757291 baseEnd_3757291 := by
    simpa [prefixWord, tailWord_3757291, baseEnd_3757291] using wordTrace_append hprefix tailTrace_3757291
  have hstable : (prefixWord ++ tailWord_3757291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3757291).length < 2 ^ (prefixWord ++ tailWord_3757291).sum := by decide
  have hdescent : baseEnd_3757291 < baseStart_3757291 := by decide
  rcases family_descends (prefixWord ++ tailWord_3757291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3757311 : List Nat := [1, 1, 2, 2, 1, 6, 2, 8]
def baseStart_3757311 : Nat := 118140960795 + 3757311 * 2 ^ 59
def prefixEnd_3757311 : Nat := 4983230072969 + 3 ^ 40 * 3757311 * 2
def baseEnd_3757311 : Nat := 71455796719461268041961

theorem tailTrace_3757311 : CollatzResearch.WordTrace tailWord_3757311 prefixEnd_3757311 71455796719461268041961 := by
  unfold tailWord_3757311
  simp only [CollatzResearch.WordTrace]
  refine ⟨137040390490911419475751787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91360260327274279650501191 137040390490911419475751787)
  ·
    refine ⟨205560585736367129213627681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137040390490911419475751787 205560585736367129213627681)
    ·
      refine ⟨154170439302275346910220761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205560585736367129213627681 154170439302275346910220761)
      ·
        refine ⟨115627829476706510182665571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154170439302275346910220761 115627829476706510182665571)
        ·
          refine ⟨173441744215059765273998357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115627829476706510182665571 173441744215059765273998357)
          ·
            refine ⟨8130081760080926497218673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 173441744215059765273998357 8130081760080926497218673)
            ·
              refine ⟨6097561320060694872914005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8130081760080926497218673 6097561320060694872914005)
              ·
                refine ⟨71455796719461268041961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6097561320060694872914005 71455796719461268041961)
                ·
                  rfl

theorem cell23_3757311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 2, 8].length) (baseStart_3757311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3757311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3757311 prefixEnd_3757311 := by exact prefixLift 3757311
  have htrace : WordTrace (prefixWord ++ tailWord_3757311) baseStart_3757311 baseEnd_3757311 := by
    simpa [prefixWord, tailWord_3757311, baseEnd_3757311] using wordTrace_append hprefix tailTrace_3757311
  have hstable : (prefixWord ++ tailWord_3757311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3757311).length < 2 ^ (prefixWord ++ tailWord_3757311).sum := by decide
  have hdescent : baseEnd_3757311 < baseStart_3757311 := by decide
  rcases family_descends (prefixWord ++ tailWord_3757311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3757315 : List Nat := [1, 1, 1, 3, 2, 4, 4, 1, 2, 4]
def baseStart_3757315 : Nat := 118140960795 + 3757315 * 2 ^ 59
def prefixEnd_3757315 : Nat := 4983230072969 + 3 ^ 40 * 3757315 * 2
def baseEnd_3757315 : Nat := 643102855116024073827643

theorem tailTrace_3757315 : CollatzResearch.WordTrace tailWord_3757315 prefixEnd_3757315 643102855116024073827643 := by
  unfold tailWord_3757315
  simp only [CollatzResearch.WordTrace]
  refine ⟨137040536382896928158897399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91360357588597952105931599 137040536382896928158897399)
  ·
    refine ⟨205560804574345392238346099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137040536382896928158897399 205560804574345392238346099)
    ·
      refine ⟨308341206861518088357519149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205560804574345392238346099 308341206861518088357519149)
      ·
        refine ⟨115627952573069283134069681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 308341206861518088357519149 115627952573069283134069681)
        ·
          refine ⟨86720964429801962350552261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115627952573069283134069681 86720964429801962350552261)
          ·
            refine ⟨16260180830587867940728549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86720964429801962350552261 16260180830587867940728549)
            ·
              refine ⟨3048783905735225238886603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16260180830587867940728549 3048783905735225238886603)
              ·
                refine ⟨4573175858602837858329905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3048783905735225238886603 4573175858602837858329905)
                ·
                  refine ⟨3429881893952128393747429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4573175858602837858329905 3429881893952128393747429)
                  ·
                    refine ⟨643102855116024073827643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3429881893952128393747429 643102855116024073827643)
                    ·
                      rfl

theorem cell23_3757315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 4, 1, 2, 4].length) (baseStart_3757315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3757315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3757315 prefixEnd_3757315 := by exact prefixLift 3757315
  have htrace : WordTrace (prefixWord ++ tailWord_3757315) baseStart_3757315 baseEnd_3757315 := by
    simpa [prefixWord, tailWord_3757315, baseEnd_3757315] using wordTrace_append hprefix tailTrace_3757315
  have hstable : (prefixWord ++ tailWord_3757315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3757315).length < 2 ^ (prefixWord ++ tailWord_3757315).sum := by decide
  have hdescent : baseEnd_3757315 < baseStart_3757315 := by decide
  rcases family_descends (prefixWord ++ tailWord_3757315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3757338 : List Nat := [3, 1, 1, 3, 3, 1, 1, 1, 3, 3, 3]
def baseStart_3757338 : Nat := 118140960795 + 3757338 * 2 ^ 59
def prefixEnd_3757338 : Nat := 4983230072969 + 3 ^ 40 * 3757338 * 2
def baseEnd_3757338 : Nat := 1929320375403125631495323

theorem tailTrace_3757338 : CollatzResearch.WordTrace tailWord_3757338 prefixEnd_3757338 1929320375403125631495323 := by
  unfold tailWord_3757338
  simp only [CollatzResearch.WordTrace]
  refine ⟨34260343815453400771746167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91360916841209068724656445 34260343815453400771746167)
  ·
    refine ⟨51390515723180101157619251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34260343815453400771746167 51390515723180101157619251)
    ·
      refine ⟨77085773584770151736428877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51390515723180101157619251 77085773584770151736428877)
      ·
        refine ⟨28907165094288806901160829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77085773584770151736428877 28907165094288806901160829)
        ·
          refine ⟨10840186910358302587935311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28907165094288806901160829 10840186910358302587935311)
          ·
            refine ⟨16260280365537453881902967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10840186910358302587935311 16260280365537453881902967)
            ·
              refine ⟨24390420548306180822854451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16260280365537453881902967 24390420548306180822854451)
              ·
                refine ⟨36585630822459271234281677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24390420548306180822854451 36585630822459271234281677)
                ·
                  refine ⟨13719611558422226712855629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36585630822459271234281677 13719611558422226712855629)
                  ·
                    refine ⟨5144854334408335017320861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13719611558422226712855629 5144854334408335017320861)
                    ·
                      refine ⟨1929320375403125631495323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5144854334408335017320861 1929320375403125631495323)
                      ·
                        rfl

theorem cell23_3757338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 1, 3, 3, 3].length) (baseStart_3757338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3757338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3757338 prefixEnd_3757338 := by exact prefixLift 3757338
  have htrace : WordTrace (prefixWord ++ tailWord_3757338) baseStart_3757338 baseEnd_3757338 := by
    simpa [prefixWord, tailWord_3757338, baseEnd_3757338] using wordTrace_append hprefix tailTrace_3757338
  have hstable : (prefixWord ++ tailWord_3757338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3757338).length < 2 ^ (prefixWord ++ tailWord_3757338).sum := by decide
  have hdescent : baseEnd_3757338 < baseStart_3757338 := by decide
  rcases family_descends (prefixWord ++ tailWord_3757338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3757365 : List Nat := [1, 3, 3, 1, 2, 2, 1, 2, 3, 3, 2]
def baseStart_3757365 : Nat := 118140960795 + 3757365 * 2 ^ 59
def prefixEnd_3757365 : Nat := 4983230072969 + 3 ^ 40 * 3757365 * 2
def baseEnd_3757365 : Nat := 1929334239380797025857699

theorem tailTrace_3757365 : CollatzResearch.WordTrace tailWord_3757365 prefixEnd_3757365 1929334239380797025857699 := by
  unfold tailWord_3757365
  simp only [CollatzResearch.WordTrace]
  refine ⟨137042360032715786698217549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91361573355143857798811699 137042360032715786698217549)
  ·
    refine ⟨51390885012268420011831581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137042360032715786698217549 51390885012268420011831581)
    ·
      refine ⟨19271581879600657504436843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51390885012268420011831581 19271581879600657504436843)
      ·
        refine ⟨28907372819400986256655265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19271581879600657504436843 28907372819400986256655265)
        ·
          refine ⟨21680529614550739692491449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28907372819400986256655265 21680529614550739692491449)
          ·
            refine ⟨16260397210913054769368587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21680529614550739692491449 16260397210913054769368587)
            ·
              refine ⟨24390595816369582154052881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16260397210913054769368587 24390595816369582154052881)
              ·
                refine ⟨18292946862277186615539661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24390595816369582154052881 18292946862277186615539661)
                ·
                  refine ⟨6859855073353944980827373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18292946862277186615539661 6859855073353944980827373)
                  ·
                    refine ⟨2572445652507729367810265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6859855073353944980827373 2572445652507729367810265)
                    ·
                      refine ⟨1929334239380797025857699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2572445652507729367810265 1929334239380797025857699)
                      ·
                        rfl

theorem cell23_3757365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 2, 3, 3, 2].length) (baseStart_3757365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3757365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3757365 prefixEnd_3757365 := by exact prefixLift 3757365
  have htrace : WordTrace (prefixWord ++ tailWord_3757365) baseStart_3757365 baseEnd_3757365 := by
    simpa [prefixWord, tailWord_3757365, baseEnd_3757365] using wordTrace_append hprefix tailTrace_3757365
  have hstable : (prefixWord ++ tailWord_3757365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3757365).length < 2 ^ (prefixWord ++ tailWord_3757365).sum := by decide
  have hdescent : baseEnd_3757365 < baseStart_3757365 := by decide
  rcases family_descends (prefixWord ++ tailWord_3757365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3757381 : List Nat := [1, 3, 1, 1, 1, 2, 1, 3, 4, 1, 5]
def baseStart_3757381 : Nat := 118140960795 + 3757381 * 2 ^ 59
def prefixEnd_3757381 : Nat := 4983230072969 + 3 ^ 40 * 3757381 * 2
def baseEnd_3757381 : Nat := 1929342455071268963257625

theorem tailTrace_3757381 : CollatzResearch.WordTrace tailWord_3757381 prefixEnd_3757381 1929342455071268963257625 := by
  unfold tailWord_3757381
  simp only [CollatzResearch.WordTrace]
  refine ⟨137042943600657821430799997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91361962400438547620533331 137042943600657821430799997)
  ·
    refine ⟨51391103850246683036549999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137042943600657821430799997 51391103850246683036549999)
    ·
      refine ⟨77086655775370024554824999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51391103850246683036549999 77086655775370024554824999)
      ·
        refine ⟨115629983663055036832237499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77086655775370024554824999 115629983663055036832237499)
        ·
          refine ⟨173444975494582555248356249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115629983663055036832237499 173444975494582555248356249)
          ·
            refine ⟨130083731620936916436267187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173444975494582555248356249 130083731620936916436267187)
            ·
              refine ⟨195125597431405374654400781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130083731620936916436267187 195125597431405374654400781)
              ·
                refine ⟨73172099036777015495400293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 195125597431405374654400781 73172099036777015495400293)
                ·
                  refine ⟨13719768569395690405387555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73172099036777015495400293 13719768569395690405387555)
                  ·
                    refine ⟨20579652854093535608081333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13719768569395690405387555 20579652854093535608081333)
                    ·
                      refine ⟨1929342455071268963257625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20579652854093535608081333 1929342455071268963257625)
                      ·
                        rfl

theorem cell23_3757381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 4, 1, 5].length) (baseStart_3757381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3757381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3757381 prefixEnd_3757381 := by exact prefixLift 3757381
  have htrace : WordTrace (prefixWord ++ tailWord_3757381) baseStart_3757381 baseEnd_3757381 := by
    simpa [prefixWord, tailWord_3757381, baseEnd_3757381] using wordTrace_append hprefix tailTrace_3757381
  have hstable : (prefixWord ++ tailWord_3757381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3757381).length < 2 ^ (prefixWord ++ tailWord_3757381).sum := by decide
  have hdescent : baseEnd_3757381 < baseStart_3757381 := by decide
  rcases family_descends (prefixWord ++ tailWord_3757381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3757395 : List Nat := [1, 1, 1, 2, 1, 1, 6, 2, 4, 2, 2]
def baseStart_3757395 : Nat := 118140960795 + 3757395 * 2 ^ 59
def prefixEnd_3757395 : Nat := 4983230072969 + 3 ^ 40 * 3757395 * 2
def baseEnd_3757395 : Nat := 1929349643800431908482561

theorem tailTrace_3757395 : CollatzResearch.WordTrace tailWord_3757395 prefixEnd_3757395 1929349643800431908482561 := by
  unfold tailWord_3757395
  simp only [CollatzResearch.WordTrace]
  refine ⟨137043454222607101821809639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91362302815071401214539759 137043454222607101821809639)
  ·
    refine ⟨205565181333910652732714459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137043454222607101821809639 205565181333910652732714459)
    ·
      refine ⟨308347772000865979099071689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205565181333910652732714459 308347772000865979099071689)
      ·
        refine ⟨231260829000649484324303767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 308347772000865979099071689 231260829000649484324303767)
        ·
          refine ⟨346891243500974226486455651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231260829000649484324303767 346891243500974226486455651)
          ·
            refine ⟨520336865251461339729683477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 346891243500974226486455651 520336865251461339729683477)
            ·
              refine ⟨24390790558662250299828913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 520336865251461339729683477 24390790558662250299828913)
              ·
                refine ⟨18293092918996687724871685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24390790558662250299828913 18293092918996687724871685)
                ·
                  refine ⟨3429954922311878948413441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18293092918996687724871685 3429954922311878948413441)
                  ·
                    refine ⟨2572466191733909211310081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3429954922311878948413441 2572466191733909211310081)
                    ·
                      refine ⟨1929349643800431908482561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2572466191733909211310081 1929349643800431908482561)
                      ·
                        rfl

theorem cell23_3757395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 2, 4, 2, 2].length) (baseStart_3757395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3757395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3757395 prefixEnd_3757395 := by exact prefixLift 3757395
  have htrace : WordTrace (prefixWord ++ tailWord_3757395) baseStart_3757395 baseEnd_3757395 := by
    simpa [prefixWord, tailWord_3757395, baseEnd_3757395] using wordTrace_append hprefix tailTrace_3757395
  have hstable : (prefixWord ++ tailWord_3757395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3757395).length < 2 ^ (prefixWord ++ tailWord_3757395).sum := by decide
  have hdescent : baseEnd_3757395 < baseStart_3757395 := by decide
  rcases family_descends (prefixWord ++ tailWord_3757395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3757399 : List Nat := [1, 1, 3, 2, 3, 4, 2, 1, 1, 3, 2]
def baseStart_3757399 : Nat := 118140960795 + 3757399 * 2 ^ 59
def prefixEnd_3757399 : Nat := 4983230072969 + 3 ^ 40 * 3757399 * 2
def baseEnd_3757399 : Nat := 1929351697723049892832543

theorem tailTrace_3757399 : CollatzResearch.WordTrace tailWord_3757399 prefixEnd_3757399 1929351697723049892832543 := by
  unfold tailWord_3757399
  simp only [CollatzResearch.WordTrace]
  refine ⟨137043600114592610504955251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91362400076395073669970167 137043600114592610504955251)
  ·
    refine ⟨205565400171888915757432877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137043600114592610504955251 205565400171888915757432877)
    ·
      refine ⟨77087025064458343409037329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205565400171888915757432877 77087025064458343409037329)
      ·
        refine ⟨57815268798343757556777997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77087025064458343409037329 57815268798343757556777997)
        ·
          refine ⟨21680725799378909083791749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57815268798343757556777997 21680725799378909083791749)
          ·
            refine ⟨4065136087383545453210953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21680725799378909083791749 4065136087383545453210953)
            ·
              refine ⟨3048852065537659089908215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4065136087383545453210953 3048852065537659089908215)
              ·
                refine ⟨4573278098306488634862323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3048852065537659089908215 4573278098306488634862323)
                ·
                  refine ⟨6859917147459732952293485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4573278098306488634862323 6859917147459732952293485)
                  ·
                    refine ⟨2572468930297399857110057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6859917147459732952293485 2572468930297399857110057)
                    ·
                      refine ⟨1929351697723049892832543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2572468930297399857110057 1929351697723049892832543)
                      ·
                        rfl

theorem cell23_3757399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 2, 1, 1, 3, 2].length) (baseStart_3757399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3757399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3757399 prefixEnd_3757399 := by exact prefixLift 3757399
  have htrace : WordTrace (prefixWord ++ tailWord_3757399) baseStart_3757399 baseEnd_3757399 := by
    simpa [prefixWord, tailWord_3757399, baseEnd_3757399] using wordTrace_append hprefix tailTrace_3757399
  have hstable : (prefixWord ++ tailWord_3757399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3757399).length < 2 ^ (prefixWord ++ tailWord_3757399).sum := by decide
  have hdescent : baseEnd_3757399 < baseStart_3757399 := by decide
  rcases family_descends (prefixWord ++ tailWord_3757399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3757408 : List Nat := [2, 1, 1, 3, 4, 1, 1, 2, 2, 2, 4]
def baseStart_3757408 : Nat := 118140960795 + 3757408 * 2 ^ 59
def prefixEnd_3757408 : Nat := 4983230072969 + 3 ^ 40 * 3757408 * 2
def baseEnd_3757408 : Nat := 1929356319048940357620001

theorem tailTrace_3757408 : CollatzResearch.WordTrace tailWord_3757408 prefixEnd_3757408 1929356319048940357620001 := by
  unfold tailWord_3757408
  simp only [CollatzResearch.WordTrace]
  refine ⟨68521964185780002521016439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91362618914373336694688585 68521964185780002521016439)
  ·
    refine ⟨102782946278670003781524659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68521964185780002521016439 102782946278670003781524659)
    ·
      refine ⟨154174419418005005672286989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102782946278670003781524659 154174419418005005672286989)
      ·
        refine ⟨57815407281751877127107621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154174419418005005672286989 57815407281751877127107621)
        ·
          refine ⟨10840388865328476961332679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57815407281751877127107621 10840388865328476961332679)
          ·
            refine ⟨16260583297992715441999019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10840388865328476961332679 16260583297992715441999019)
            ·
              refine ⟨24390874946989073162998529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16260583297992715441999019 24390874946989073162998529)
              ·
                refine ⟨18293156210241804872248897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24390874946989073162998529 18293156210241804872248897)
                ·
                  refine ⟨13719867157681353654186673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18293156210241804872248897 13719867157681353654186673)
                  ·
                    refine ⟨10289900368261015240640005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13719867157681353654186673 10289900368261015240640005)
                    ·
                      refine ⟨1929356319048940357620001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10289900368261015240640005 1929356319048940357620001)
                      ·
                        rfl

theorem cell23_3757408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 2, 2, 2, 4].length) (baseStart_3757408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3757408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3757408 prefixEnd_3757408 := by exact prefixLift 3757408
  have htrace : WordTrace (prefixWord ++ tailWord_3757408) baseStart_3757408 baseEnd_3757408 := by
    simpa [prefixWord, tailWord_3757408, baseEnd_3757408] using wordTrace_append hprefix tailTrace_3757408
  have hstable : (prefixWord ++ tailWord_3757408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3757408).length < 2 ^ (prefixWord ++ tailWord_3757408).sum := by decide
  have hdescent : baseEnd_3757408 < baseStart_3757408 := by decide
  rcases family_descends (prefixWord ++ tailWord_3757408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3757412 : List Nat := [2, 3, 1, 1, 3, 3, 1, 1, 4, 2, 2]
def baseStart_3757412 : Nat := 118140960795 + 3757412 * 2 ^ 59
def prefixEnd_3757412 : Nat := 4983230072969 + 3 ^ 40 * 3757412 * 2
def baseEnd_3757412 : Nat := 1929358372971558341969983

theorem tailTrace_3757412 : CollatzResearch.WordTrace tailWord_3757412 prefixEnd_3757412 1929358372971558341969983 := by
  unfold tailWord_3757412
  simp only [CollatzResearch.WordTrace]
  refine ⟨68522037131772756862589245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91362716175697009150118993 68522037131772756862589245)
  ·
    refine ⟨25695763924414783823470967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68522037131772756862589245 25695763924414783823470967)
    ·
      refine ⟨38543645886622175735206451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25695763924414783823470967 38543645886622175735206451)
      ·
        refine ⟨57815468829933263602809677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38543645886622175735206451 57815468829933263602809677)
        ·
          refine ⟨21680800811224973851053629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57815468829933263602809677 21680800811224973851053629)
          ·
            refine ⟨8130300304209365194145111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21680800811224973851053629 8130300304209365194145111)
            ·
              refine ⟨12195450456314047791217667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8130300304209365194145111 12195450456314047791217667)
              ·
                refine ⟨18293175684471071686826501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12195450456314047791217667 18293175684471071686826501)
                ·
                  refine ⟨3429970440838325941279969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18293175684471071686826501 3429970440838325941279969)
                  ·
                    refine ⟨2572477830628744455959977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3429970440838325941279969 2572477830628744455959977)
                    ·
                      refine ⟨1929358372971558341969983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2572477830628744455959977 1929358372971558341969983)
                      ·
                        rfl

theorem cell23_3757412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 1, 4, 2, 2].length) (baseStart_3757412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3757412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3757412 prefixEnd_3757412 := by exact prefixLift 3757412
  have htrace : WordTrace (prefixWord ++ tailWord_3757412) baseStart_3757412 baseEnd_3757412 := by
    simpa [prefixWord, tailWord_3757412, baseEnd_3757412] using wordTrace_append hprefix tailTrace_3757412
  have hstable : (prefixWord ++ tailWord_3757412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3757412).length < 2 ^ (prefixWord ++ tailWord_3757412).sum := by decide
  have hdescent : baseEnd_3757412 < baseStart_3757412 := by decide
  rcases family_descends (prefixWord ++ tailWord_3757412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3757429 : List Nat := [1, 3, 4, 1, 3, 2, 1, 1, 1, 4, 2]
def baseStart_3757429 : Nat := 118140960795 + 3757429 * 2 ^ 59
def prefixEnd_3757429 : Nat := 4983230072969 + 3 ^ 40 * 3757429 * 2
def baseEnd_3757429 : Nat := 1929367102142684775457405

theorem tailTrace_3757429 : CollatzResearch.WordTrace tailWord_3757429 prefixEnd_3757429 1929367102142684775457405 := by
  unfold tailWord_3757429
  simp only [CollatzResearch.WordTrace]
  refine ⟨137044694304483925628547341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91363129536322617085698227 137044694304483925628547341)
  ·
    refine ⟨51391760364181472110705253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137044694304483925628547341 51391760364181472110705253)
    ·
      refine ⟨9635955068284026020757235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51391760364181472110705253 9635955068284026020757235)
      ·
        refine ⟨14453932602426039031135853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9635955068284026020757235 14453932602426039031135853)
        ·
          refine ⟨5420224725909764636675945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14453932602426039031135853 5420224725909764636675945)
          ·
            refine ⟨4065168544432323477506959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5420224725909764636675945 4065168544432323477506959)
            ·
              refine ⟨6097752816648485216260439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4065168544432323477506959 6097752816648485216260439)
              ·
                refine ⟨9146629224972727824390659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6097752816648485216260439 9146629224972727824390659)
                ·
                  refine ⟨13719943837459091736585989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9146629224972727824390659 13719943837459091736585989)
                  ·
                    refine ⟨2572489469523579700609873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13719943837459091736585989 2572489469523579700609873)
                    ·
                      refine ⟨1929367102142684775457405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2572489469523579700609873 1929367102142684775457405)
                      ·
                        rfl

theorem cell23_3757429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 1, 1, 1, 4, 2].length) (baseStart_3757429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3757429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3757429 prefixEnd_3757429 := by exact prefixLift 3757429
  have htrace : WordTrace (prefixWord ++ tailWord_3757429) baseStart_3757429 baseEnd_3757429 := by
    simpa [prefixWord, tailWord_3757429, baseEnd_3757429] using wordTrace_append hprefix tailTrace_3757429
  have hstable : (prefixWord ++ tailWord_3757429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3757429).length < 2 ^ (prefixWord ++ tailWord_3757429).sum := by decide
  have hdescent : baseEnd_3757429 < baseStart_3757429 := by decide
  rcases family_descends (prefixWord ++ tailWord_3757429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3757431 : List Nat := [1, 1, 3, 1, 1, 2, 3, 1, 3, 7]
def baseStart_3757431 : Nat := 118140960795 + 3757431 * 2 ^ 59
def prefixEnd_3757431 : Nat := 4983230072969 + 3 ^ 40 * 3757431 * 2
def baseEnd_3757431 : Nat := 643122709701331255877465

theorem tailTrace_3757431 : CollatzResearch.WordTrace tailWord_3757431 prefixEnd_3757431 643122709701331255877465 := by
  unfold tailWord_3757431
  simp only [CollatzResearch.WordTrace]
  refine ⟨137044767250476679970120147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91363178166984453313413431 137044767250476679970120147)
  ·
    refine ⟨205567150875715019955180221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137044767250476679970120147 205567150875715019955180221)
    ·
      refine ⟨77087681578393132483192583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205567150875715019955180221 77087681578393132483192583)
      ·
        refine ⟨115631522367589698724788875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77087681578393132483192583 115631522367589698724788875)
        ·
          refine ⟨173447283551384548087183313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115631522367589698724788875 173447283551384548087183313)
          ·
            refine ⟨130085462663538411065387485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173447283551384548087183313 130085462663538411065387485)
            ·
              refine ⟨48782048498826904149520307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 130085462663538411065387485 48782048498826904149520307)
              ·
                refine ⟨73173072748240356224280461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48782048498826904149520307 73173072748240356224280461)
                ·
                  refine ⟨27439902280590133584105173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73173072748240356224280461 27439902280590133584105173)
                  ·
                    refine ⟨643122709701331255877465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27439902280590133584105173 643122709701331255877465)
                    ·
                      rfl

theorem cell23_3757431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 3, 7].length) (baseStart_3757431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3757431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3757431 prefixEnd_3757431 := by exact prefixLift 3757431
  have htrace : WordTrace (prefixWord ++ tailWord_3757431) baseStart_3757431 baseEnd_3757431 := by
    simpa [prefixWord, tailWord_3757431, baseEnd_3757431] using wordTrace_append hprefix tailTrace_3757431
  have hstable : (prefixWord ++ tailWord_3757431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3757431).length < 2 ^ (prefixWord ++ tailWord_3757431).sum := by decide
  have hdescent : baseEnd_3757431 < baseStart_3757431 := by decide
  rcases family_descends (prefixWord ++ tailWord_3757431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3757448 : List Nat := [2, 1, 3, 3, 1, 2, 2, 1, 1, 7]
def baseStart_3757448 : Nat := 118140960795 + 3757448 * 2 ^ 59
def prefixEnd_3757448 : Nat := 4983230072969 + 3 ^ 40 * 3757448 * 2
def baseEnd_3757448 : Nat := 643125619425040067039939

theorem tailTrace_3757448 : CollatzResearch.WordTrace tailWord_3757448 prefixEnd_3757448 643125619425040067039939 := by
  unfold tailWord_3757448
  simp only [CollatzResearch.WordTrace]
  refine ⟨68522693645707545936744499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91363591527610061248992665 68522693645707545936744499)
  ·
    refine ⟨102784040468561318905116749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68522693645707545936744499 102784040468561318905116749)
    ·
      refine ⟨38544015175710494589418781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102784040468561318905116749 38544015175710494589418781)
      ·
        refine ⟨14454005690891435471032043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38544015175710494589418781 14454005690891435471032043)
        ·
          refine ⟨21681008536337153206548065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14454005690891435471032043 21681008536337153206548065)
          ·
            refine ⟨16260756402252864904911049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21681008536337153206548065 16260756402252864904911049)
            ·
              refine ⟨12195567301689648678683287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16260756402252864904911049 12195567301689648678683287)
              ·
                refine ⟨18293350952534473018024931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12195567301689648678683287 18293350952534473018024931)
                ·
                  refine ⟨27440026428801709527037397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18293350952534473018024931 27440026428801709527037397)
                  ·
                    refine ⟨643125619425040067039939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27440026428801709527037397 643125619425040067039939)
                    ·
                      rfl

theorem cell23_3757448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 1, 1, 7].length) (baseStart_3757448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3757448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3757448 prefixEnd_3757448 := by exact prefixLift 3757448
  have htrace : WordTrace (prefixWord ++ tailWord_3757448) baseStart_3757448 baseEnd_3757448 := by
    simpa [prefixWord, tailWord_3757448, baseEnd_3757448] using wordTrace_append hprefix tailTrace_3757448
  have hstable : (prefixWord ++ tailWord_3757448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3757448).length < 2 ^ (prefixWord ++ tailWord_3757448).sum := by decide
  have hdescent : baseEnd_3757448 < baseStart_3757448 := by decide
  rcases family_descends (prefixWord ++ tailWord_3757448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3757480 : List Nat := [2, 1, 6, 1, 3, 1, 2, 1, 2, 2, 2]
def baseStart_3757480 : Nat := 118140960795 + 3757480 * 2 ^ 59
def prefixEnd_3757480 : Nat := 4983230072969 + 3 ^ 40 * 3757480 * 2
def baseEnd_3757480 : Nat := 1929393289656064075919671

theorem tailTrace_3757480 : CollatzResearch.WordTrace tailWord_3757480 prefixEnd_3757480 1929393289656064075919671 := by
  unfold tailWord_3757480
  simp only [CollatzResearch.WordTrace]
  refine ⟨68523277213649580669326947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91364369618199440892435929 68523277213649580669326947)
  ·
    refine ⟨102784915820474371003990421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68523277213649580669326947 102784915820474371003990421)
    ·
      refine ⟨4818042929084736140812051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 102784915820474371003990421 4818042929084736140812051)
      ·
        refine ⟨7227064393627104211218077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4818042929084736140812051 7227064393627104211218077)
        ·
          refine ⟨2710149147610164079206779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7227064393627104211218077 2710149147610164079206779)
          ·
            refine ⟨4065223721415246118810169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2710149147610164079206779 4065223721415246118810169)
            ·
              refine ⟨3048917791061434589107627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4065223721415246118810169 3048917791061434589107627)
              ·
                refine ⟨4573376686592151883661441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3048917791061434589107627 4573376686592151883661441)
                ·
                  refine ⟨3430032514944113912746081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4573376686592151883661441 3430032514944113912746081)
                  ·
                    refine ⟨2572524386208085434559561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3430032514944113912746081 2572524386208085434559561)
                    ·
                      refine ⟨1929393289656064075919671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2572524386208085434559561 1929393289656064075919671)
                      ·
                        rfl

theorem cell23_3757480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 2, 1, 2, 2, 2].length) (baseStart_3757480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3757480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3757480 prefixEnd_3757480 := by exact prefixLift 3757480
  have htrace : WordTrace (prefixWord ++ tailWord_3757480) baseStart_3757480 baseEnd_3757480 := by
    simpa [prefixWord, tailWord_3757480, baseEnd_3757480] using wordTrace_append hprefix tailTrace_3757480
  have hstable : (prefixWord ++ tailWord_3757480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3757480).length < 2 ^ (prefixWord ++ tailWord_3757480).sum := by decide
  have hdescent : baseEnd_3757480 < baseStart_3757480 := by decide
  rcases family_descends (prefixWord ++ tailWord_3757480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3757488 : List Nat := [2, 1, 1, 1, 2, 1, 1, 6, 1, 4, 3]
def baseStart_3757488 : Nat := 118140960795 + 3757488 * 2 ^ 59
def prefixEnd_3757488 : Nat := 4983230072969 + 3 ^ 40 * 3757488 * 2
def baseEnd_3757488 : Nat := 1929397397501300044619633

theorem tailTrace_3757488 : CollatzResearch.WordTrace tailWord_3757488 prefixEnd_3757488 1929397397501300044619633 := by
  unfold tailWord_3757488
  simp only [CollatzResearch.WordTrace]
  refine ⟨68523423105635089352472559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91364564140846785803296745 68523423105635089352472559)
  ·
    refine ⟨102785134658452634028708839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68523423105635089352472559 102785134658452634028708839)
    ·
      refine ⟨154177701987678951043063259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102785134658452634028708839 154177701987678951043063259)
      ·
        refine ⟨231266552981518426564594889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154177701987678951043063259 231266552981518426564594889)
        ·
          refine ⟨173449914736138819923446167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231266552981518426564594889 173449914736138819923446167)
          ·
            refine ⟨260174872104208229885169251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173449914736138819923446167 260174872104208229885169251)
            ·
              refine ⟨390262308156312344827753877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 260174872104208229885169251 390262308156312344827753877)
              ·
                refine ⟨18293545694827141163800963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 390262308156312344827753877 18293545694827141163800963)
                ·
                  refine ⟨27440318542240711745701445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18293545694827141163800963 27440318542240711745701445)
                  ·
                    refine ⟨5145059726670133452319021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27440318542240711745701445 5145059726670133452319021)
                    ·
                      refine ⟨1929397397501300044619633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5145059726670133452319021 1929397397501300044619633)
                      ·
                        rfl

theorem cell23_3757488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 6, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 6, 1, 4, 3].length) (baseStart_3757488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3757488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3757488 prefixEnd_3757488 := by exact prefixLift 3757488
  have htrace : WordTrace (prefixWord ++ tailWord_3757488) baseStart_3757488 baseEnd_3757488 := by
    simpa [prefixWord, tailWord_3757488, baseEnd_3757488] using wordTrace_append hprefix tailTrace_3757488
  have hstable : (prefixWord ++ tailWord_3757488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3757488).length < 2 ^ (prefixWord ++ tailWord_3757488).sum := by decide
  have hdescent : baseEnd_3757488 < baseStart_3757488 := by decide
  rcases family_descends (prefixWord ++ tailWord_3757488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3757512 : List Nat := [2, 1, 3, 1, 3, 1, 2, 5, 1, 4]
def baseStart_3757512 : Nat := 118140960795 + 3757512 * 2 ^ 59
def prefixEnd_3757512 : Nat := 4983230072969 + 3 ^ 40 * 3757512 * 2
def baseEnd_3757512 : Nat := 643136573679002650239841

theorem tailTrace_3757512 : CollatzResearch.WordTrace tailWord_3757512 prefixEnd_3757512 643136573679002650239841 := by
  unfold tailWord_3757512
  simp only [CollatzResearch.WordTrace]
  refine ⟨68523860781591615401909395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91365147708788820535879193 68523860781591615401909395)
  ·
    refine ⟨102785791172387423102864093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68523860781591615401909395 102785791172387423102864093)
    ·
      refine ⟨38544671689645283663574035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102785791172387423102864093 38544671689645283663574035)
      ·
        refine ⟨57817007534467925495361053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38544671689645283663574035 57817007534467925495361053)
        ·
          refine ⟨21681377825425472060760395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57817007534467925495361053 21681377825425472060760395)
          ·
            refine ⟨32522066738138208091140593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21681377825425472060760395 32522066738138208091140593)
            ·
              refine ⟨24391550053603656068355445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32522066738138208091140593 24391550053603656068355445)
              ·
                refine ⟨2286707817525342756408323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24391550053603656068355445 2286707817525342756408323)
                ·
                  refine ⟨3430061726288014134612485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2286707817525342756408323 3430061726288014134612485)
                  ·
                    refine ⟨643136573679002650239841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3430061726288014134612485 643136573679002650239841)
                    ·
                      rfl

theorem cell23_3757512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 5, 1, 4].length) (baseStart_3757512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3757512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3757512 prefixEnd_3757512 := by exact prefixLift 3757512
  have htrace : WordTrace (prefixWord ++ tailWord_3757512) baseStart_3757512 baseEnd_3757512 := by
    simpa [prefixWord, tailWord_3757512, baseEnd_3757512] using wordTrace_append hprefix tailTrace_3757512
  have hstable : (prefixWord ++ tailWord_3757512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3757512).length < 2 ^ (prefixWord ++ tailWord_3757512).sum := by decide
  have hdescent : baseEnd_3757512 < baseStart_3757512 := by decide
  rcases family_descends (prefixWord ++ tailWord_3757512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3757525 : List Nat := [1, 3, 2, 3, 1, 1, 4, 2, 6]
def baseStart_3757525 : Nat := 118140960795 + 3757525 * 2 ^ 59
def prefixEnd_3757525 : Nat := 4983230072969 + 3 ^ 40 * 3757525 * 2
def baseEnd_3757525 : Nat := 214379599587279599984107

theorem tailTrace_3757525 : CollatzResearch.WordTrace tailWord_3757525 prefixEnd_3757525 214379599587279599984107 := by
  unfold tailWord_3757525
  simp only [CollatzResearch.WordTrace]
  refine ⟨137048195712136134024042029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91365463808090756016028019 137048195712136134024042029)
  ·
    refine ⟨51393073392051050259015761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137048195712136134024042029 51393073392051050259015761)
    ·
      refine ⟨38544805044038287694261821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51393073392051050259015761 38544805044038287694261821)
      ·
        refine ⟨14454301891514357885348183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38544805044038287694261821 14454301891514357885348183)
        ·
          refine ⟨21681452837271536828022275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14454301891514357885348183 21681452837271536828022275)
          ·
            refine ⟨32522179255907305242033413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21681452837271536828022275 32522179255907305242033413)
            ·
              refine ⟨6097908610482619732881265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32522179255907305242033413 6097908610482619732881265)
              ·
                refine ⟨4573431457861964799660949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6097908610482619732881265 4573431457861964799660949)
                ·
                  refine ⟨214379599587279599984107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4573431457861964799660949 214379599587279599984107)
                  ·
                    rfl

theorem cell23_3757525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 4, 2, 6].length) (baseStart_3757525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3757525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3757525 prefixEnd_3757525 := by exact prefixLift 3757525
  have htrace : WordTrace (prefixWord ++ tailWord_3757525) baseStart_3757525 baseEnd_3757525 := by
    simpa [prefixWord, tailWord_3757525, baseEnd_3757525] using wordTrace_append hprefix tailTrace_3757525
  have hstable : (prefixWord ++ tailWord_3757525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3757525).length < 2 ^ (prefixWord ++ tailWord_3757525).sum := by decide
  have hdescent : baseEnd_3757525 < baseStart_3757525 := by decide
  rcases family_descends (prefixWord ++ tailWord_3757525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3757529 : List Nat := [1, 2, 1, 2, 4, 2, 4, 2, 1, 4]
def baseStart_3757529 : Nat := 118140960795 + 3757529 * 2 ^ 59
def prefixEnd_3757529 : Nat := 4983230072969 + 3 ^ 40 * 3757529 * 2
def baseEnd_3757529 : Nat := 643139483402711461402315

theorem tailTrace_3757529 : CollatzResearch.WordTrace tailWord_3757529 prefixEnd_3757529 643139483402711461402315 := by
  unfold tailWord_3757529
  simp only [CollatzResearch.WordTrace]
  refine ⟨137048341604121642707187641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91365561069414428471458427 137048341604121642707187641)
  ·
    refine ⟨102786256203091232030390731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137048341604121642707187641 102786256203091232030390731)
    ·
      refine ⟨154179384304636848045586097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102786256203091232030390731 154179384304636848045586097)
      ·
        refine ⟨115634538228477636034189573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154179384304636848045586097 115634538228477636034189573)
        ·
          refine ⟨21681475917839556756410545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115634538228477636034189573 21681475917839556756410545)
          ·
            refine ⟨16261106938379667567307909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21681475917839556756410545 16261106938379667567307909)
            ·
              refine ⟨3048957550946187668870233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16261106938379667567307909 3048957550946187668870233)
              ·
                refine ⟨2286718163209640751652675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3048957550946187668870233 2286718163209640751652675)
                ·
                  refine ⟨3430077244814461127479013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2286718163209640751652675 3430077244814461127479013)
                  ·
                    refine ⟨643139483402711461402315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3430077244814461127479013 643139483402711461402315)
                    ·
                      rfl

theorem cell23_3757529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 4, 2, 1, 4].length) (baseStart_3757529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3757529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3757529 prefixEnd_3757529 := by exact prefixLift 3757529
  have htrace : WordTrace (prefixWord ++ tailWord_3757529) baseStart_3757529 baseEnd_3757529 := by
    simpa [prefixWord, tailWord_3757529, baseEnd_3757529] using wordTrace_append hprefix tailTrace_3757529
  have hstable : (prefixWord ++ tailWord_3757529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3757529).length < 2 ^ (prefixWord ++ tailWord_3757529).sum := by decide
  have hdescent : baseEnd_3757529 < baseStart_3757529 := by decide
  rcases family_descends (prefixWord ++ tailWord_3757529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3757552 : List Nat := [2, 1, 1, 1, 3, 5, 1, 2, 3, 1, 3]
def baseStart_3757552 : Nat := 118140960795 + 3757552 * 2 ^ 59
def prefixEnd_3757552 : Nat := 4983230072969 + 3 ^ 40 * 3757552 * 2
def baseEnd_3757552 : Nat := 1929430260263187794219339

theorem tailTrace_3757552 : CollatzResearch.WordTrace tailWord_3757552 prefixEnd_3757552 1929430260263187794219339 := by
  unfold tailWord_3757552
  simp only [CollatzResearch.WordTrace]
  refine ⟨68524590241519158817637455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91366120322025545090183273 68524590241519158817637455)
  ·
    refine ⟨102786885362278738226456183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68524590241519158817637455 102786885362278738226456183)
    ·
      refine ⟨154180328043418107339684275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102786885362278738226456183 154180328043418107339684275)
      ·
        refine ⟨231270492065127161009526413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154180328043418107339684275 231270492065127161009526413)
        ·
          refine ⟨86726434524422685378572405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 231270492065127161009526413 86726434524422685378572405)
          ·
            refine ⟨8130603236664626754241163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 86726434524422685378572405 8130603236664626754241163)
            ·
              refine ⟨12195904854996940131361745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8130603236664626754241163 12195904854996940131361745)
              ·
                refine ⟨9146928641247705098521309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12195904854996940131361745 9146928641247705098521309)
                ·
                  refine ⟨3430098240467889411945491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9146928641247705098521309 3430098240467889411945491)
                  ·
                    refine ⟨5145147360701834117918237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3430098240467889411945491 5145147360701834117918237)
                    ·
                      refine ⟨1929430260263187794219339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5145147360701834117918237 1929430260263187794219339)
                      ·
                        rfl

theorem cell23_3757552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 2, 3, 1, 3].length) (baseStart_3757552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3757552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3757552 prefixEnd_3757552 := by exact prefixLift 3757552
  have htrace : WordTrace (prefixWord ++ tailWord_3757552) baseStart_3757552 baseEnd_3757552 := by
    simpa [prefixWord, tailWord_3757552, baseEnd_3757552] using wordTrace_append hprefix tailTrace_3757552
  have hstable : (prefixWord ++ tailWord_3757552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3757552).length < 2 ^ (prefixWord ++ tailWord_3757552).sum := by decide
  have hdescent : baseEnd_3757552 < baseStart_3757552 := by decide
  rcases family_descends (prefixWord ++ tailWord_3757552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3757585 : List Nat := [1, 2, 2, 1, 1, 2, 5, 1, 4, 4]
def baseStart_3757585 : Nat := 118140960795 + 3757585 * 2 ^ 59
def prefixEnd_3757585 : Nat := 4983230072969 + 3 ^ 40 * 3757585 * 2
def baseEnd_3757585 : Nat := 643149068374928721702229

theorem tailTrace_3757585 : CollatzResearch.WordTrace tailWord_3757585 prefixEnd_3757585 643149068374928721702229 := by
  unfold tailWord_3757585
  simp only [CollatzResearch.WordTrace]
  refine ⟨137050384091918764271226209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91366922727945842847484139 137050384091918764271226209)
  ·
    refine ⟨102787788068939073203419657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137050384091918764271226209 102787788068939073203419657)
    ·
      refine ⟨77090841051704304902564743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102787788068939073203419657 77090841051704304902564743)
      ·
        refine ⟨115636261577556457353847115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77090841051704304902564743 115636261577556457353847115)
        ·
          refine ⟨173454392366334686030770673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115636261577556457353847115 173454392366334686030770673)
          ·
            refine ⟨130090794274751014523078005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173454392366334686030770673 130090794274751014523078005)
            ·
              refine ⟨12196011963257907611538563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 130090794274751014523078005 12196011963257907611538563)
              ·
                refine ⟨18294017944886861417307845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12196011963257907611538563 18294017944886861417307845)
                ·
                  refine ⟨3430128364666286515745221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18294017944886861417307845 3430128364666286515745221)
                  ·
                    refine ⟨643149068374928721702229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3430128364666286515745221 643149068374928721702229)
                    ·
                      rfl

theorem cell23_3757585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 1, 4, 4].length) (baseStart_3757585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3757585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3757585 prefixEnd_3757585 := by exact prefixLift 3757585
  have htrace : WordTrace (prefixWord ++ tailWord_3757585) baseStart_3757585 baseEnd_3757585 := by
    simpa [prefixWord, tailWord_3757585, baseEnd_3757585] using wordTrace_append hprefix tailTrace_3757585
  have hstable : (prefixWord ++ tailWord_3757585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3757585).length < 2 ^ (prefixWord ++ tailWord_3757585).sum := by decide
  have hdescent : baseEnd_3757585 < baseStart_3757585 := by decide
  rcases family_descends (prefixWord ++ tailWord_3757585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3757602 : List Nat := [3, 3, 1, 1, 1, 1, 2, 5, 2, 4]
def baseStart_3757602 : Nat := 118140960795 + 3757602 * 2 ^ 59
def prefixEnd_3757602 : Nat := 4983230072969 + 3 ^ 40 * 3757602 * 2
def baseEnd_3757602 : Nat := 643151978098637532864703

theorem tailTrace_3757602 : CollatzResearch.WordTrace tailWord_3757602 prefixEnd_3757602 643151978098637532864703 := by
  unfold tailWord_3757602
  simp only [CollatzResearch.WordTrace]
  refine ⟨34262751033214294043648765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91367336088571450783063373 34262751033214294043648765)
  ·
    refine ⟨12848531637455360266368287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34262751033214294043648765 12848531637455360266368287)
    ·
      refine ⟨19272797456183040399552431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12848531637455360266368287 19272797456183040399552431)
      ·
        refine ⟨28909196184274560599328647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19272797456183040399552431 28909196184274560599328647)
        ·
          refine ⟨43363794276411840898992971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28909196184274560599328647 43363794276411840898992971)
          ·
            refine ⟨65045691414617761348489457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43363794276411840898992971 65045691414617761348489457)
            ·
              refine ⟨48784268560963321011367093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65045691414617761348489457 48784268560963321011367093)
              ·
                refine ⟨4573525177590311344815665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48784268560963321011367093 4573525177590311344815665)
                ·
                  refine ⟨3430143883192733508611749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4573525177590311344815665 3430143883192733508611749)
                  ·
                    refine ⟨643151978098637532864703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3430143883192733508611749 643151978098637532864703)
                    ·
                      rfl

theorem cell23_3757602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 5, 2, 4].length) (baseStart_3757602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3757602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3757602 prefixEnd_3757602 := by exact prefixLift 3757602
  have htrace : WordTrace (prefixWord ++ tailWord_3757602) baseStart_3757602 baseEnd_3757602 := by
    simpa [prefixWord, tailWord_3757602, baseEnd_3757602] using wordTrace_append hprefix tailTrace_3757602
  have hstable : (prefixWord ++ tailWord_3757602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3757602).length < 2 ^ (prefixWord ++ tailWord_3757602).sum := by decide
  have hdescent : baseEnd_3757602 < baseStart_3757602 := by decide
  rcases family_descends (prefixWord ++ tailWord_3757602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3757642 : List Nat := [3, 1, 2, 1, 1, 3, 1, 3, 4, 1, 3]
def baseStart_3757642 : Nat := 118140960795 + 3757642 * 2 ^ 59
def prefixEnd_3757642 : Nat := 4983230072969 + 3 ^ 40 * 3757642 * 2
def baseEnd_3757642 : Nat := 1929476473522092442093925

theorem tailTrace_3757642 : CollatzResearch.WordTrace tailWord_3757642 prefixEnd_3757642 1929476473522092442093925 := by
  unfold tailWord_3757642
  simp only [CollatzResearch.WordTrace]
  refine ⟨34263115763178065751512795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91368308701808175337367453 34263115763178065751512795)
  ·
    refine ⟨51394673644767098627269193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34263115763178065751512795 51394673644767098627269193)
    ·
      refine ⟨38546005233575323970451895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51394673644767098627269193 38546005233575323970451895)
      ·
        refine ⟨57819007850362985955677843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38546005233575323970451895 57819007850362985955677843)
        ·
          refine ⟨86728511775544478933516765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57819007850362985955677843 86728511775544478933516765)
          ·
            refine ⟨32523191915829179600068787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86728511775544478933516765 32523191915829179600068787)
            ·
              refine ⟨48784787873743769400103181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32523191915829179600068787 48784787873743769400103181)
              ·
                refine ⟨18294295452653913525038693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48784787873743769400103181 18294295452653913525038693)
                ·
                  refine ⟨3430180397372608785944755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18294295452653913525038693 3430180397372608785944755)
                  ·
                    refine ⟨5145270596058913178917133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3430180397372608785944755 5145270596058913178917133)
                    ·
                      refine ⟨1929476473522092442093925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5145270596058913178917133 1929476473522092442093925)
                      ·
                        rfl

theorem cell23_3757642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 3, 4, 1, 3].length) (baseStart_3757642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3757642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3757642 prefixEnd_3757642 := by exact prefixLift 3757642
  have htrace : WordTrace (prefixWord ++ tailWord_3757642) baseStart_3757642 baseEnd_3757642 := by
    simpa [prefixWord, tailWord_3757642, baseEnd_3757642] using wordTrace_append hprefix tailTrace_3757642
  have hstable : (prefixWord ++ tailWord_3757642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3757642).length < 2 ^ (prefixWord ++ tailWord_3757642).sum := by decide
  have hdescent : baseEnd_3757642 < baseStart_3757642 := by decide
  rcases family_descends (prefixWord ++ tailWord_3757642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3757669 : List Nat := [1, 3, 1, 3, 3, 2, 1, 1, 3, 3, 2]
def baseStart_3757669 : Nat := 118140960795 + 3757669 * 2 ^ 59
def prefixEnd_3757669 : Nat := 4983230072969 + 3 ^ 40 * 3757669 * 2
def baseEnd_3757669 : Nat := 1929490337499763836456301

theorem tailTrace_3757669 : CollatzResearch.WordTrace tailWord_3757669 prefixEnd_3757669 1929490337499763836456301 := by
  unfold tailWord_3757669
  simp only [CollatzResearch.WordTrace]
  refine ⟨137053447823614446617284061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91368965215742964411522707 137053447823614446617284061)
  ·
    refine ⟨51395042933855417481481523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137053447823614446617284061 51395042933855417481481523)
    ·
      refine ⟨77092564400783126222222285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51395042933855417481481523 77092564400783126222222285)
      ·
        refine ⟨28909711650293672333333357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77092564400783126222222285 28909711650293672333333357)
        ·
          refine ⟨10841141868860127125000009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28909711650293672333333357 10841141868860127125000009)
          ·
            refine ⟨8130856401645095343750007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10841141868860127125000009 8130856401645095343750007)
            ·
              refine ⟨12196284602467643015625011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8130856401645095343750007 12196284602467643015625011)
              ·
                refine ⟨18294426903701464523437517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12196284602467643015625011 18294426903701464523437517)
                ·
                  refine ⟨6860410088888049196289069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18294426903701464523437517 6860410088888049196289069)
                  ·
                    refine ⟨2572653783333018448608401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6860410088888049196289069 2572653783333018448608401)
                    ·
                      refine ⟨1929490337499763836456301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2572653783333018448608401 1929490337499763836456301)
                      ·
                        rfl

theorem cell23_3757669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 1, 3, 3, 2].length) (baseStart_3757669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3757669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3757669 prefixEnd_3757669 := by exact prefixLift 3757669
  have htrace : WordTrace (prefixWord ++ tailWord_3757669) baseStart_3757669 baseEnd_3757669 := by
    simpa [prefixWord, tailWord_3757669, baseEnd_3757669] using wordTrace_append hprefix tailTrace_3757669
  have hstable : (prefixWord ++ tailWord_3757669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3757669).length < 2 ^ (prefixWord ++ tailWord_3757669).sum := by decide
  have hdescent : baseEnd_3757669 < baseStart_3757669 := by decide
  rcases family_descends (prefixWord ++ tailWord_3757669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3757750 : List Nat := [5, 1, 3, 1, 1, 1, 3, 2, 2, 2, 2]
def baseStart_3757750 : Nat := 118140960795 + 3757750 * 2 ^ 59
def prefixEnd_3757750 : Nat := 4983230072969 + 3 ^ 40 * 3757750 * 2
def baseEnd_3757750 : Nat := 1929531929432778019543429

theorem tailTrace_3757750 : CollatzResearch.WordTrace tailWord_3757750 prefixEnd_3757750 1929531929432778019543429 := by
  unfold tailWord_3757750
  simp only [CollatzResearch.WordTrace]
  refine ⟨8566025133520062340686419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 91370934757547331633988469 8566025133520062340686419)
  ·
    refine ⟨12849037700280093511029629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8566025133520062340686419 12849037700280093511029629)
    ·
      refine ⟨4818389137605035066636111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12849037700280093511029629 4818389137605035066636111)
      ·
        refine ⟨7227583706407552599954167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4818389137605035066636111 7227583706407552599954167)
        ·
          refine ⟨10841375559611328899931251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7227583706407552599954167 10841375559611328899931251)
          ·
            refine ⟨16262063339416993349896877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10841375559611328899931251 16262063339416993349896877)
            ·
              refine ⟨6098273752281372506211329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16262063339416993349896877 6098273752281372506211329)
              ·
                refine ⟨4573705314211029379658497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6098273752281372506211329 4573705314211029379658497)
                ·
                  refine ⟨3430278985658272034743873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4573705314211029379658497 3430278985658272034743873)
                  ·
                    refine ⟨2572709239243704026057905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3430278985658272034743873 2572709239243704026057905)
                    ·
                      refine ⟨1929531929432778019543429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2572709239243704026057905 1929531929432778019543429)
                      ·
                        rfl

theorem cell23_3757750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 3, 2, 2, 2, 2].length) (baseStart_3757750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3757750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3757750 prefixEnd_3757750 := by exact prefixLift 3757750
  have htrace : WordTrace (prefixWord ++ tailWord_3757750) baseStart_3757750 baseEnd_3757750 := by
    simpa [prefixWord, tailWord_3757750, baseEnd_3757750] using wordTrace_append hprefix tailTrace_3757750
  have hstable : (prefixWord ++ tailWord_3757750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3757750).length < 2 ^ (prefixWord ++ tailWord_3757750).sum := by decide
  have hdescent : baseEnd_3757750 < baseStart_3757750 := by decide
  rcases family_descends (prefixWord ++ tailWord_3757750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3757792 : List Nat := [2, 1, 1, 3, 1, 2, 4, 1, 1, 4, 3]
def baseStart_3757792 : Nat := 118140960795 + 3757792 * 2 ^ 59
def prefixEnd_3757792 : Nat := 4983230072969 + 3 ^ 40 * 3757792 * 2
def baseEnd_3757792 : Nat := 1929553495620266855218235

theorem tailTrace_3757792 : CollatzResearch.WordTrace tailWord_3757792 prefixEnd_3757792 1929553495620266855218235 := by
  unfold tailWord_3757792
  simp only [CollatzResearch.WordTrace]
  refine ⟨68528967001084419312005815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91371956001445892416007753 68528967001084419312005815)
  ·
    refine ⟨102793450501626628968008723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68528967001084419312005815 102793450501626628968008723)
    ·
      refine ⟨154190175752439943452013085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102793450501626628968008723 154190175752439943452013085)
      ·
        refine ⟨57821315907164978794504907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154190175752439943452013085 57821315907164978794504907)
        ·
          refine ⟨86731973860747468191757361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57821315907164978794504907 86731973860747468191757361)
          ·
            refine ⟨65048980395560601143818021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86731973860747468191757361 65048980395560601143818021)
            ·
              refine ⟨12196683824167612714465879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65048980395560601143818021 12196683824167612714465879)
              ·
                refine ⟨18295025736251419071698819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12196683824167612714465879 18295025736251419071698819)
                ·
                  refine ⟨27442538604377128607548229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18295025736251419071698819 27442538604377128607548229)
                  ·
                    refine ⟨5145475988320711613915293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27442538604377128607548229 5145475988320711613915293)
                    ·
                      refine ⟨1929553495620266855218235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5145475988320711613915293 1929553495620266855218235)
                      ·
                        rfl

theorem cell23_3757792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 1, 1, 4, 3].length) (baseStart_3757792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3757792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3757792 prefixEnd_3757792 := by exact prefixLift 3757792
  have htrace : WordTrace (prefixWord ++ tailWord_3757792) baseStart_3757792 baseEnd_3757792 := by
    simpa [prefixWord, tailWord_3757792, baseEnd_3757792] using wordTrace_append hprefix tailTrace_3757792
  have hstable : (prefixWord ++ tailWord_3757792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3757792).length < 2 ^ (prefixWord ++ tailWord_3757792).sum := by decide
  have hdescent : baseEnd_3757792 < baseStart_3757792 := by decide
  rcases family_descends (prefixWord ++ tailWord_3757792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3757809 : List Nat := [1, 2, 2, 2, 2, 4, 1, 2, 2, 2, 3]
def baseStart_3757809 : Nat := 118140960795 + 3757809 * 2 ^ 59
def prefixEnd_3757809 : Nat := 4983230072969 + 3 ^ 40 * 3757809 * 2
def baseEnd_3757809 : Nat := 1929562224791393288705657

theorem tailTrace_3757809 : CollatzResearch.WordTrace tailWord_3757809 prefixEnd_3757809 1929562224791393288705657 := by
  unfold tailWord_3757809
  simp only [CollatzResearch.WordTrace]
  refine ⟨137058554043107250527380481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91372369362071500351586987 137058554043107250527380481)
  ·
    refine ⟨102793915532330437895535361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137058554043107250527380481 102793915532330437895535361)
    ·
      refine ⟨77095436649247828421651521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102793915532330437895535361 77095436649247828421651521)
      ·
        refine ⟨57821577486935871316238641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77095436649247828421651521 57821577486935871316238641)
        ·
          refine ⟨43366183115201903487178981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57821577486935871316238641 43366183115201903487178981)
          ·
            refine ⟨8131159334100356903846059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43366183115201903487178981 8131159334100356903846059)
            ·
              refine ⟨12196739001150535355769089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8131159334100356903846059 12196739001150535355769089)
              ·
                refine ⟨9147554250862901516826817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12196739001150535355769089 9147554250862901516826817)
                ·
                  refine ⟨6860665688147176137620113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9147554250862901516826817 6860665688147176137620113)
                  ·
                    refine ⟨5145499266110382103215085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6860665688147176137620113 5145499266110382103215085)
                    ·
                      refine ⟨1929562224791393288705657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5145499266110382103215085 1929562224791393288705657)
                      ·
                        rfl

theorem cell23_3757809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 2, 2, 2, 3].length) (baseStart_3757809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3757809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3757809 prefixEnd_3757809 := by exact prefixLift 3757809
  have htrace : WordTrace (prefixWord ++ tailWord_3757809) baseStart_3757809 baseEnd_3757809 := by
    simpa [prefixWord, tailWord_3757809, baseEnd_3757809] using wordTrace_append hprefix tailTrace_3757809
  have hstable : (prefixWord ++ tailWord_3757809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3757809).length < 2 ^ (prefixWord ++ tailWord_3757809).sum := by decide
  have hdescent : baseEnd_3757809 < baseStart_3757809 := by decide
  rcases family_descends (prefixWord ++ tailWord_3757809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3757815 : List Nat := [1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 8]
def baseStart_3757815 : Nat := 118140960795 + 3757815 * 2 ^ 59
def prefixEnd_3757815 : Nat := 4983230072969 + 3 ^ 40 * 3757815 * 2
def baseEnd_3757815 : Nat := 1929565305675320265230629

theorem tailTrace_3757815 : CollatzResearch.WordTrace tailWord_3757815 prefixEnd_3757815 1929565305675320265230629 := by
  unfold tailWord_3757815
  simp only [CollatzResearch.WordTrace]
  refine ⟨137058772881085513552098899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91372515254057009034732599 137058772881085513552098899)
  ·
    refine ⟨205588159321628270328148349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137058772881085513552098899 205588159321628270328148349)
    ·
      refine ⟨77095559745610601373055631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205588159321628270328148349 77095559745610601373055631)
      ·
        refine ⟨115643339618415902059583447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77095559745610601373055631 115643339618415902059583447)
        ·
          refine ⟨173465009427623853089375171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115643339618415902059583447 173465009427623853089375171)
          ·
            refine ⟨260197514141435779634062757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173465009427623853089375171 260197514141435779634062757)
            ·
              refine ⟨48787033901519208681386767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 260197514141435779634062757 48787033901519208681386767)
              ·
                refine ⟨73180550852278813022080151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48787033901519208681386767 73180550852278813022080151)
                ·
                  refine ⟨109770826278418219533120227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73180550852278813022080151 109770826278418219533120227)
                  ·
                    refine ⟨164656239417627329299680341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 109770826278418219533120227 164656239417627329299680341)
                    ·
                      refine ⟨1929565305675320265230629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 164656239417627329299680341 1929565305675320265230629)
                      ·
                        rfl

theorem cell23_3757815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 8].length) (baseStart_3757815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3757815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3757815 prefixEnd_3757815 := by exact prefixLift 3757815
  have htrace : WordTrace (prefixWord ++ tailWord_3757815) baseStart_3757815 baseEnd_3757815 := by
    simpa [prefixWord, tailWord_3757815, baseEnd_3757815] using wordTrace_append hprefix tailTrace_3757815
  have hstable : (prefixWord ++ tailWord_3757815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3757815).length < 2 ^ (prefixWord ++ tailWord_3757815).sum := by decide
  have hdescent : baseEnd_3757815 < baseStart_3757815 := by decide
  rcases family_descends (prefixWord ++ tailWord_3757815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3757873 : List Nat := [1, 2, 2, 3, 2, 3, 1, 4, 1, 1, 3]
def baseStart_3757873 : Nat := 118140960795 + 3757873 * 2 ^ 59
def prefixEnd_3757873 : Nat := 4983230072969 + 3 ^ 40 * 3757873 * 2
def baseEnd_3757873 : Nat := 1929595087553281038305363

theorem tailTrace_3757873 : CollatzResearch.WordTrace tailWord_3757873 prefixEnd_3757873 1929595087553281038305363 := by
  unfold tailWord_3757873
  simp only [CollatzResearch.WordTrace]
  refine ⟨137060888314875389457710273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91373925543250259638473515 137060888314875389457710273)
  ·
    refine ⟨102795666236156542093282705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137060888314875389457710273 102795666236156542093282705)
    ·
      refine ⟨77096749677117406569962029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102795666236156542093282705 77096749677117406569962029)
      ·
        refine ⟨28911281128919027463735761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77096749677117406569962029 28911281128919027463735761)
        ·
          refine ⟨21683460846689270597801821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28911281128919027463735761 21683460846689270597801821)
          ·
            refine ⟨8131297817508476474175683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21683460846689270597801821 8131297817508476474175683)
            ·
              refine ⟨12196946726262714711263525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8131297817508476474175683 12196946726262714711263525)
              ·
                refine ⟨2286927511174259008361911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12196946726262714711263525 2286927511174259008361911)
                ·
                  refine ⟨3430391266761388512542867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2286927511174259008361911 3430391266761388512542867)
                  ·
                    refine ⟨5145586900142082768814301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3430391266761388512542867 5145586900142082768814301)
                    ·
                      refine ⟨1929595087553281038305363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5145586900142082768814301 1929595087553281038305363)
                      ·
                        rfl

theorem cell23_3757873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 4, 1, 1, 3].length) (baseStart_3757873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3757873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3757873 prefixEnd_3757873 := by exact prefixLift 3757873
  have htrace : WordTrace (prefixWord ++ tailWord_3757873) baseStart_3757873 baseEnd_3757873 := by
    simpa [prefixWord, tailWord_3757873, baseEnd_3757873] using wordTrace_append hprefix tailTrace_3757873
  have hstable : (prefixWord ++ tailWord_3757873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3757873).length < 2 ^ (prefixWord ++ tailWord_3757873).sum := by decide
  have hdescent : baseEnd_3757873 < baseStart_3757873 := by decide
  rcases family_descends (prefixWord ++ tailWord_3757873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3757896 : List Nat := [2, 1, 3, 1, 1, 4, 1, 1, 5, 2, 2]
def baseStart_3757896 : Nat := 118140960795 + 3757896 * 2 ^ 59
def prefixEnd_3757896 : Nat := 4983230072969 + 3 ^ 40 * 3757896 * 2
def baseEnd_3757896 : Nat := 1929606897608334448317757

theorem tailTrace_3757896 : CollatzResearch.WordTrace tailWord_3757896 prefixEnd_3757896 1929606897608334448317757 := by
  unfold tailWord_3757896
  simp only [CollatzResearch.WordTrace]
  refine ⟨68530863596896032192898771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91374484795861376257198361 68530863596896032192898771)
  ·
    refine ⟨102796295395344048289348157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68530863596896032192898771 102796295395344048289348157)
    ·
      refine ⟨38548610773254018108505559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102796295395344048289348157 38548610773254018108505559)
      ·
        refine ⟨57822916159881027162758339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38548610773254018108505559 57822916159881027162758339)
        ·
          refine ⟨86734374239821540744137509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57822916159881027162758339 86734374239821540744137509)
          ·
            refine ⟨16262695169966538889525783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86734374239821540744137509 16262695169966538889525783)
            ·
              refine ⟨24394042754949808334288675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16262695169966538889525783 24394042754949808334288675)
              ·
                refine ⟨36591064132424712501433013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24394042754949808334288675 36591064132424712501433013)
                ·
                  refine ⟨3430412262414816797009345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36591064132424712501433013 3430412262414816797009345)
                  ·
                    refine ⟨2572809196811112597757009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3430412262414816797009345 2572809196811112597757009)
                    ·
                      refine ⟨1929606897608334448317757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2572809196811112597757009 1929606897608334448317757)
                      ·
                        rfl

theorem cell23_3757896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 1, 5, 2, 2].length) (baseStart_3757896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3757896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3757896 prefixEnd_3757896 := by exact prefixLift 3757896
  have htrace : WordTrace (prefixWord ++ tailWord_3757896) baseStart_3757896 baseEnd_3757896 := by
    simpa [prefixWord, tailWord_3757896, baseEnd_3757896] using wordTrace_append hprefix tailTrace_3757896
  have hstable : (prefixWord ++ tailWord_3757896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3757896).length < 2 ^ (prefixWord ++ tailWord_3757896).sum := by decide
  have hdescent : baseEnd_3757896 < baseStart_3757896 := by decide
  rcases family_descends (prefixWord ++ tailWord_3757896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3757900 : List Nat := [2, 2, 1, 3, 5, 1, 1, 1, 2, 3, 2]
def baseStart_3757900 : Nat := 118140960795 + 3757900 * 2 ^ 59
def prefixEnd_3757900 : Nat := 4983230072969 + 3 ^ 40 * 3757900 * 2
def baseEnd_3757900 : Nat := 1929608951530952432667739

theorem tailTrace_3757900 : CollatzResearch.WordTrace tailWord_3757900 prefixEnd_3757900 1929608951530952432667739 := by
  unfold tailWord_3757900
  simp only [CollatzResearch.WordTrace]
  refine ⟨68530936542888786534471577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91374582057185048712628769 68530936542888786534471577)
  ·
    refine ⟨51398202407166589900853683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68530936542888786534471577 51398202407166589900853683)
    ·
      refine ⟨77097303610749884851280525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51398202407166589900853683 77097303610749884851280525)
      ·
        refine ⟨28911488854031206819230197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77097303610749884851280525 28911488854031206819230197)
        ·
          refine ⟨2710452080065425639302831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28911488854031206819230197 2710452080065425639302831)
          ·
            refine ⟨4065678120098138458954247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2710452080065425639302831 4065678120098138458954247)
            ·
              refine ⟨6098517180147207688431371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4065678120098138458954247 6098517180147207688431371)
              ·
                refine ⟨9147775770220811532647057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6098517180147207688431371 9147775770220811532647057)
                ·
                  refine ⟨6860831827665608649485293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9147775770220811532647057 6860831827665608649485293)
                  ·
                    refine ⟨2572811935374603243556985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6860831827665608649485293 2572811935374603243556985)
                    ·
                      refine ⟨1929608951530952432667739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2572811935374603243556985 1929608951530952432667739)
                      ·
                        rfl

theorem cell23_3757900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 1, 1, 2, 3, 2].length) (baseStart_3757900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3757900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3757900 prefixEnd_3757900 := by exact prefixLift 3757900
  have htrace : WordTrace (prefixWord ++ tailWord_3757900) baseStart_3757900 baseEnd_3757900 := by
    simpa [prefixWord, tailWord_3757900, baseEnd_3757900] using wordTrace_append hprefix tailTrace_3757900
  have hstable : (prefixWord ++ tailWord_3757900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3757900).length < 2 ^ (prefixWord ++ tailWord_3757900).sum := by decide
  have hdescent : baseEnd_3757900 < baseStart_3757900 := by decide
  rcases family_descends (prefixWord ++ tailWord_3757900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3757909 : List Nat := [1, 3, 2, 2, 2, 2, 2, 2, 1, 2, 4]
def baseStart_3757909 : Nat := 118140960795 + 3757909 * 2 ^ 59
def prefixEnd_3757909 : Nat := 4983230072969 + 3 ^ 40 * 3757909 * 2
def baseEnd_3757909 : Nat := 1929613572856842897455197

theorem tailTrace_3757909 : CollatzResearch.WordTrace tailWord_3757909 prefixEnd_3757909 1929613572856842897455197 := by
  unfold tailWord_3757909
  simp only [CollatzResearch.WordTrace]
  refine ⟨137062201342744967606020781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91374800895163311737347187 137062201342744967606020781)
  ·
    refine ⟨51398325503529362852257793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137062201342744967606020781 51398325503529362852257793)
    ·
      refine ⟨38548744127647022139193345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51398325503529362852257793 38548744127647022139193345)
      ·
        refine ⟨28911558095735266604395009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38548744127647022139193345 28911558095735266604395009)
        ·
          refine ⟨21683668571801449953296257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28911558095735266604395009 21683668571801449953296257)
          ·
            refine ⟨16262751428851087464972193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21683668571801449953296257 16262751428851087464972193)
            ·
              refine ⟨12197063571638315598729145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16262751428851087464972193 12197063571638315598729145)
              ·
                refine ⟨9147797678728736699046859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12197063571638315598729145 9147797678728736699046859)
                ·
                  refine ⟨13721696518093105048570289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9147797678728736699046859 13721696518093105048570289)
                  ·
                    refine ⟨10291272388569828786427717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13721696518093105048570289 10291272388569828786427717)
                    ·
                      refine ⟨1929613572856842897455197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10291272388569828786427717 1929613572856842897455197)
                      ·
                        rfl

theorem cell23_3757909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 2, 1, 2, 4].length) (baseStart_3757909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3757909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3757909 prefixEnd_3757909 := by exact prefixLift 3757909
  have htrace : WordTrace (prefixWord ++ tailWord_3757909) baseStart_3757909 baseEnd_3757909 := by
    simpa [prefixWord, tailWord_3757909, baseEnd_3757909] using wordTrace_append hprefix tailTrace_3757909
  have hstable : (prefixWord ++ tailWord_3757909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3757909).length < 2 ^ (prefixWord ++ tailWord_3757909).sum := by decide
  have hdescent : baseEnd_3757909 < baseStart_3757909 := by decide
  rcases family_descends (prefixWord ++ tailWord_3757909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3757923 : List Nat := [1, 1, 1, 5, 4, 2, 1, 2, 2, 4]
def baseStart_3757923 : Nat := 118140960795 + 3757923 * 2 ^ 59
def prefixEnd_3757923 : Nat := 4983230072969 + 3 ^ 40 * 3757923 * 2
def baseEnd_3757923 : Nat := 643206920528668614226711

theorem tailTrace_3757923 : CollatzResearch.WordTrace tailWord_3757923 prefixEnd_3757923 643206920528668614226711 := by
  unfold tailWord_3757923
  simp only [CollatzResearch.WordTrace]
  refine ⟨137062711964694247997030423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91375141309796165331353615 137062711964694247997030423)
  ·
    refine ⟨205594067947041371995545635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137062711964694247997030423 205594067947041371995545635)
    ·
      refine ⟨308391101920562057993318453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205594067947041371995545635 308391101920562057993318453)
      ·
        refine ⟨28911665805052692936873605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 308391101920562057993318453 28911665805052692936873605)
        ·
          refine ⟨5420937338447379925663801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28911665805052692936873605 5420937338447379925663801)
          ·
            refine ⟨4065703003835534944247851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5420937338447379925663801 4065703003835534944247851)
            ·
              refine ⟨6098554505753302416371777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4065703003835534944247851 6098554505753302416371777)
              ·
                refine ⟨4573915879314976812278833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6098554505753302416371777 4573915879314976812278833)
                ·
                  refine ⟨3430436909486232609209125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4573915879314976812278833 3430436909486232609209125)
                  ·
                    refine ⟨643206920528668614226711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3430436909486232609209125 643206920528668614226711)
                    ·
                      rfl

theorem cell23_3757923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 1, 2, 2, 4].length) (baseStart_3757923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3757923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3757923 prefixEnd_3757923 := by exact prefixLift 3757923
  have htrace : WordTrace (prefixWord ++ tailWord_3757923) baseStart_3757923 baseEnd_3757923 := by
    simpa [prefixWord, tailWord_3757923, baseEnd_3757923] using wordTrace_append hprefix tailTrace_3757923
  have hstable : (prefixWord ++ tailWord_3757923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3757923).length < 2 ^ (prefixWord ++ tailWord_3757923).sum := by decide
  have hdescent : baseEnd_3757923 < baseStart_3757923 := by decide
  rcases family_descends (prefixWord ++ tailWord_3757923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3757946 : List Nat := [3, 1, 1, 1, 1, 1, 4, 5, 2, 1, 3]
def baseStart_3757946 : Nat := 118140960795 + 3757946 * 2 ^ 59
def prefixEnd_3757946 : Nat := 4983230072969 + 3 ^ 40 * 3757946 * 2
def baseEnd_3757946 : Nat := 1929632571641059252692527

theorem tailTrace_3757946 : CollatzResearch.WordTrace tailWord_3757946 prefixEnd_3757946 1929632571641059252692527 := by
  unfold tailWord_3757946
  simp only [CollatzResearch.WordTrace]
  refine ⟨34265887710902730731279423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91375700562407281950078461 34265887710902730731279423)
  ·
    refine ⟨51398831566354096096919135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34265887710902730731279423 51398831566354096096919135)
    ·
      refine ⟨77098247349531144145378703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51398831566354096096919135 77098247349531144145378703)
      ·
        refine ⟨115647371024296716218068055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77098247349531144145378703 115647371024296716218068055)
        ·
          refine ⟨173471056536445074327102083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115647371024296716218068055 173471056536445074327102083)
          ·
            refine ⟨260206584804667611490653125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173471056536445074327102083 260206584804667611490653125)
            ·
              refine ⟨48788734650875177154497461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 260206584804667611490653125 48788734650875177154497461)
              ·
                refine ⟨4573943873519547858234137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48788734650875177154497461 4573943873519547858234137)
                ·
                  refine ⟨3430457905139660893675603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4573943873519547858234137 3430457905139660893675603)
                  ·
                    refine ⟨5145686857709491340513405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3430457905139660893675603 5145686857709491340513405)
                    ·
                      refine ⟨1929632571641059252692527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5145686857709491340513405 1929632571641059252692527)
                      ·
                        rfl

theorem cell23_3757946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 5, 2, 1, 3].length) (baseStart_3757946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3757946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3757946 prefixEnd_3757946 := by exact prefixLift 3757946
  have htrace : WordTrace (prefixWord ++ tailWord_3757946) baseStart_3757946 baseEnd_3757946 := by
    simpa [prefixWord, tailWord_3757946, baseEnd_3757946] using wordTrace_append hprefix tailTrace_3757946
  have hstable : (prefixWord ++ tailWord_3757946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3757946).length < 2 ^ (prefixWord ++ tailWord_3757946).sum := by decide
  have hdescent : baseEnd_3757946 < baseStart_3757946 := by decide
  rcases family_descends (prefixWord ++ tailWord_3757946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3757950 : List Nat := [4, 2, 3, 1, 1, 2, 2, 2, 1, 2, 3]
def baseStart_3757950 : Nat := 118140960795 + 3757950 * 2 ^ 59
def prefixEnd_3757950 : Nat := 4983230072969 + 3 ^ 40 * 3757950 * 2
def baseEnd_3757950 : Nat := 1929634625563677237042509

theorem tailTrace_3757950 : CollatzResearch.WordTrace tailWord_3757950 prefixEnd_3757950 1929634625563677237042509 := by
  unfold tailWord_3757950
  simp only [CollatzResearch.WordTrace]
  refine ⟨17132962091949553951032913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91375797823730954405508869 17132962091949553951032913)
  ·
    refine ⟨12849721568962165463274685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17132962091949553951032913 12849721568962165463274685)
    ·
      refine ⟨4818645588360812048728007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12849721568962165463274685 4818645588360812048728007)
      ·
        refine ⟨7227968382541218073092011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4818645588360812048728007 7227968382541218073092011)
        ·
          refine ⟨10841952573811827109638017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7227968382541218073092011 10841952573811827109638017)
          ·
            refine ⟨8131464430358870332228513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10841952573811827109638017 8131464430358870332228513)
            ·
              refine ⟨6098598322769152749171385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8131464430358870332228513 6098598322769152749171385)
              ·
                refine ⟨4573948742076864561878539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6098598322769152749171385 4573948742076864561878539)
                ·
                  refine ⟨6860923113115296842817809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4573948742076864561878539 6860923113115296842817809)
                  ·
                    refine ⟨5145692334836472632113357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6860923113115296842817809 5145692334836472632113357)
                    ·
                      refine ⟨1929634625563677237042509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5145692334836472632113357 1929634625563677237042509)
                      ·
                        rfl

theorem cell23_3757950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_3757950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3757950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3757950 prefixEnd_3757950 := by exact prefixLift 3757950
  have htrace : WordTrace (prefixWord ++ tailWord_3757950) baseStart_3757950 baseEnd_3757950 := by
    simpa [prefixWord, tailWord_3757950, baseEnd_3757950] using wordTrace_append hprefix tailTrace_3757950
  have hstable : (prefixWord ++ tailWord_3757950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3757950).length < 2 ^ (prefixWord ++ tailWord_3757950).sum := by decide
  have hdescent : baseEnd_3757950 < baseStart_3757950 := by decide
  rcases family_descends (prefixWord ++ tailWord_3757950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3757953 : List Nat := [1, 2, 4, 4, 1, 2, 2, 7]
def baseStart_3757953 : Nat := 118140960795 + 3757953 * 2 ^ 59
def prefixEnd_3757953 : Nat := 4983230072969 + 3 ^ 40 * 3757953 * 2
def baseEnd_3757953 : Nat := 71468006148357063900185

theorem tailTrace_3757953 : CollatzResearch.WordTrace tailWord_3757953 prefixEnd_3757953 71468006148357063900185 := by
  unfold tailWord_3757953
  simp only [CollatzResearch.WordTrace]
  refine ⟨137063806154585563120622513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91375870769723708747081675 137063806154585563120622513)
  ·
    refine ⟨102797854615939172340466885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137063806154585563120622513 102797854615939172340466885)
    ·
      refine ⟨19274597740488594813837541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102797854615939172340466885 19274597740488594813837541)
      ·
        refine ⟨3613987076341611527594539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19274597740488594813837541 3613987076341611527594539)
        ·
          refine ⟨5420980614512417291391809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3613987076341611527594539 5420980614512417291391809)
          ·
            refine ⟨4065735460884312968543857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5420980614512417291391809 4065735460884312968543857)
            ·
              refine ⟨3049301595663234726407893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4065735460884312968543857 3049301595663234726407893)
              ·
                refine ⟨71468006148357063900185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3049301595663234726407893 71468006148357063900185)
                ·
                  rfl

theorem cell23_3757953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 2, 7].length) (baseStart_3757953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3757953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3757953 prefixEnd_3757953 := by exact prefixLift 3757953
  have htrace : WordTrace (prefixWord ++ tailWord_3757953) baseStart_3757953 baseEnd_3757953 := by
    simpa [prefixWord, tailWord_3757953, baseEnd_3757953] using wordTrace_append hprefix tailTrace_3757953
  have hstable : (prefixWord ++ tailWord_3757953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3757953).length < 2 ^ (prefixWord ++ tailWord_3757953).sum := by decide
  have hdescent : baseEnd_3757953 < baseStart_3757953 := by decide
  rcases family_descends (prefixWord ++ tailWord_3757953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3757956 : List Nat := [2, 3, 2, 1, 1, 1, 2, 3, 3, 3, 2]
def baseStart_3757956 : Nat := 118140960795 + 3757956 * 2 ^ 59
def prefixEnd_3757956 : Nat := 4983230072969 + 3 ^ 40 * 3757956 * 2
def baseEnd_3757956 : Nat := 1929637706447604213567481

theorem tailTrace_3757956 : CollatzResearch.WordTrace tailWord_3757956 prefixEnd_3757956 1929637706447604213567481 := by
  unfold tailWord_3757956
  simp only [CollatzResearch.WordTrace]
  refine ⟨68531957786787347316490861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91375943715716463088654481 68531957786787347316490861)
  ·
    refine ⟨25699484170045255243684073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68531957786787347316490861 25699484170045255243684073)
    ·
      refine ⟨19274613127533941432763055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25699484170045255243684073 19274613127533941432763055)
      ·
        refine ⟨28911919691300912149144583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19274613127533941432763055 28911919691300912149144583)
        ·
          refine ⟨43367879536951368223716875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28911919691300912149144583 43367879536951368223716875)
          ·
            refine ⟨65051819305427052335575313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43367879536951368223716875 65051819305427052335575313)
            ·
              refine ⟨48788864479070289251681485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65051819305427052335575313 48788864479070289251681485)
              ·
                refine ⟨18295824179651358469380557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48788864479070289251681485 18295824179651358469380557)
                ·
                  refine ⟨6860934067369259426017709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18295824179651358469380557 6860934067369259426017709)
                  ·
                    refine ⟨2572850275263472284756641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6860934067369259426017709 2572850275263472284756641)
                    ·
                      refine ⟨1929637706447604213567481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2572850275263472284756641 1929637706447604213567481)
                      ·
                        rfl

theorem cell23_3757956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 3, 3, 3, 2].length) (baseStart_3757956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3757956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3757956 prefixEnd_3757956 := by exact prefixLift 3757956
  have htrace : WordTrace (prefixWord ++ tailWord_3757956) baseStart_3757956 baseEnd_3757956 := by
    simpa [prefixWord, tailWord_3757956, baseEnd_3757956] using wordTrace_append hprefix tailTrace_3757956
  have hstable : (prefixWord ++ tailWord_3757956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3757956).length < 2 ^ (prefixWord ++ tailWord_3757956).sum := by decide
  have hdescent : baseEnd_3757956 < baseStart_3757956 := by decide
  rcases family_descends (prefixWord ++ tailWord_3757956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3758003 : List Nat := [1, 1, 1, 2, 3, 1, 5, 3, 2, 2, 2]
def baseStart_3758003 : Nat := 118140960795 + 3758003 * 2 ^ 59
def prefixEnd_3758003 : Nat := 4983230072969 + 3 ^ 40 * 3758003 * 2
def baseEnd_3758003 : Nat := 1929661840038365529679765

theorem tailTrace_3758003 : CollatzResearch.WordTrace tailWord_3758003 prefixEnd_3758003 1929661840038365529679765 := by
  unfold tailWord_3758003
  simp only [CollatzResearch.WordTrace]
  refine ⟨137065629804404421659942663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91377086536269614439961775 137065629804404421659942663)
  ·
    refine ⟨205598444706606632489913995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137065629804404421659942663 205598444706606632489913995)
    ·
      refine ⟨308397667059909948734870993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205598444706606632489913995 308397667059909948734870993)
      ·
        refine ⟨231298250294932461551153245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 308397667059909948734870993 231298250294932461551153245)
        ·
          refine ⟨86736843860599673081682467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 231298250294932461551153245 86736843860599673081682467)
          ·
            refine ⟨130105265790899509622523701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86736843860599673081682467 130105265790899509622523701)
            ·
              refine ⟨12197368667896829027111597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 130105265790899509622523701 12197368667896829027111597)
              ·
                refine ⟨4574013250461310885166849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12197368667896829027111597 4574013250461310885166849)
                ·
                  refine ⟨3430509937845983163875137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4574013250461310885166849 3430509937845983163875137)
                  ·
                    refine ⟨2572882453384487372906353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3430509937845983163875137 2572882453384487372906353)
                    ·
                      refine ⟨1929661840038365529679765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2572882453384487372906353 1929661840038365529679765)
                      ·
                        rfl

theorem cell23_3758003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 3, 2, 2, 2].length) (baseStart_3758003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3758003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3758003 prefixEnd_3758003 := by exact prefixLift 3758003
  have htrace : WordTrace (prefixWord ++ tailWord_3758003) baseStart_3758003 baseEnd_3758003 := by
    simpa [prefixWord, tailWord_3758003, baseEnd_3758003] using wordTrace_append hprefix tailTrace_3758003
  have hstable : (prefixWord ++ tailWord_3758003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3758003).length < 2 ^ (prefixWord ++ tailWord_3758003).sum := by decide
  have hdescent : baseEnd_3758003 < baseStart_3758003 := by decide
  rcases family_descends (prefixWord ++ tailWord_3758003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3758036 : List Nat := [2, 4, 1, 2, 1, 1, 2, 2, 2, 3, 3]
def baseStart_3758036 : Nat := 118140960795 + 3758036 * 2 ^ 59
def prefixEnd_3758036 : Nat := 4983230072969 + 3 ^ 40 * 3758036 * 2
def baseEnd_3758036 : Nat := 1929678784899963900567113

theorem tailTrace_3758036 : CollatzResearch.WordTrace tailWord_3758036 prefixEnd_3758036 1929678784899963900567113 := by
  unfold tailWord_3758036
  simp only [CollatzResearch.WordTrace]
  refine ⟨68533416706642434147946981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91377888942189912197262641 68533416706642434147946981)
  ·
    refine ⟨12850015632495456402740059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68533416706642434147946981 12850015632495456402740059)
    ·
      refine ⟨19275023448743184604110089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12850015632495456402740059 19275023448743184604110089)
      ·
        refine ⟨14456267586557388453082567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19275023448743184604110089 14456267586557388453082567)
        ·
          refine ⟨21684401379836082679623851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14456267586557388453082567 21684401379836082679623851)
          ·
            refine ⟨32526602069754124019435777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21684401379836082679623851 32526602069754124019435777)
            ·
              refine ⟨24394951552315593014576833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32526602069754124019435777 24394951552315593014576833)
              ·
                refine ⟨18296213664236694760932625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24394951552315593014576833 18296213664236694760932625)
                ·
                  refine ⟨13722160248177521070699469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18296213664236694760932625 13722160248177521070699469)
                  ·
                    refine ⟨5145810093066570401512301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13722160248177521070699469 5145810093066570401512301)
                    ·
                      refine ⟨1929678784899963900567113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5145810093066570401512301 1929678784899963900567113)
                      ·
                        rfl

theorem cell23_3758036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 2, 2, 3, 3].length) (baseStart_3758036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3758036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3758036 prefixEnd_3758036 := by exact prefixLift 3758036
  have htrace : WordTrace (prefixWord ++ tailWord_3758036) baseStart_3758036 baseEnd_3758036 := by
    simpa [prefixWord, tailWord_3758036, baseEnd_3758036] using wordTrace_append hprefix tailTrace_3758036
  have hstable : (prefixWord ++ tailWord_3758036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3758036).length < 2 ^ (prefixWord ++ tailWord_3758036).sum := by decide
  have hdescent : baseEnd_3758036 < baseStart_3758036 := by decide
  rcases family_descends (prefixWord ++ tailWord_3758036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3758039 : List Nat := [1, 1, 3, 2, 1, 1, 3, 4, 2, 5]
def baseStart_3758039 : Nat := 118140960795 + 3758039 * 2 ^ 59
def prefixEnd_3758039 : Nat := 4983230072969 + 3 ^ 40 * 3758039 * 2
def baseEnd_3758039 : Nat := 643226775113975796276533

theorem tailTrace_3758039 : CollatzResearch.WordTrace tailWord_3758039 prefixEnd_3758039 643226775113975796276533 := by
  unfold tailWord_3758039
  simp only [CollatzResearch.WordTrace]
  refine ⟨137066942832273999808253171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91377961888182666538835447 137066942832273999808253171)
  ·
    refine ⟨205600414248410999712379757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137066942832273999808253171 205600414248410999712379757)
    ·
      refine ⟨77100155343154124892142409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205600414248410999712379757 77100155343154124892142409)
      ·
        refine ⟨57825116507365593669106807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77100155343154124892142409 57825116507365593669106807)
        ·
          refine ⟨86737674761048390503660211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57825116507365593669106807 86737674761048390503660211)
          ·
            refine ⟨130106512141572585755490317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86737674761048390503660211 130106512141572585755490317)
            ·
              refine ⟨48789942053089719658308869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 130106512141572585755490317 48789942053089719658308869)
              ·
                refine ⟨9148114134954322435932913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48789942053089719658308869 9148114134954322435932913)
                ·
                  refine ⟨6861085601215741826949685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9148114134954322435932913 6861085601215741826949685)
                  ·
                    refine ⟨643226775113975796276533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6861085601215741826949685 643226775113975796276533)
                    ·
                      rfl

theorem cell23_3758039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 4, 2, 5].length) (baseStart_3758039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3758039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3758039 prefixEnd_3758039 := by exact prefixLift 3758039
  have htrace : WordTrace (prefixWord ++ tailWord_3758039) baseStart_3758039 baseEnd_3758039 := by
    simpa [prefixWord, tailWord_3758039, baseEnd_3758039] using wordTrace_append hprefix tailTrace_3758039
  have hstable : (prefixWord ++ tailWord_3758039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3758039).length < 2 ^ (prefixWord ++ tailWord_3758039).sum := by decide
  have hdescent : baseEnd_3758039 < baseStart_3758039 := by decide
  rcases family_descends (prefixWord ++ tailWord_3758039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3758049 : List Nat := [1, 2, 3, 1, 2, 1, 4, 1, 1, 2, 5]
def baseStart_3758049 : Nat := 118140960795 + 3758049 * 2 ^ 59
def prefixEnd_3758049 : Nat := 4983230072969 + 3 ^ 40 * 3758049 * 2
def baseEnd_3758049 : Nat := 1929685460148472349704553

theorem tailTrace_3758049 : CollatzResearch.WordTrace tailWord_3758049 prefixEnd_3758049 1929685460148472349704553 := by
  unfold tailWord_3758049
  simp only [CollatzResearch.WordTrace]
  refine ⟨137067307562237771516117201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91378205041491847677411467 137067307562237771516117201)
  ·
    refine ⟨102800480671678328637087901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137067307562237771516117201 102800480671678328637087901)
    ·
      refine ⟨38550180251879373238907963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102800480671678328637087901 38550180251879373238907963)
      ·
        refine ⟨57825270377819059858361945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38550180251879373238907963 57825270377819059858361945)
        ·
          refine ⟨43368952783364294893771459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57825270377819059858361945 43368952783364294893771459)
          ·
            refine ⟨65053429175046442340657189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43368952783364294893771459 65053429175046442340657189)
            ·
              refine ⟨12197517970321207938873223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65053429175046442340657189 12197517970321207938873223)
              ·
                refine ⟨18296276955481811908309835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12197517970321207938873223 18296276955481811908309835)
                ·
                  refine ⟨27444415433222717862464753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18296276955481811908309835 27444415433222717862464753)
                  ·
                    refine ⟨20583311574917038396848565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27444415433222717862464753 20583311574917038396848565)
                    ·
                      refine ⟨1929685460148472349704553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20583311574917038396848565 1929685460148472349704553)
                      ·
                        rfl

theorem cell23_3758049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 1, 1, 2, 5].length) (baseStart_3758049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3758049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3758049 prefixEnd_3758049 := by exact prefixLift 3758049
  have htrace : WordTrace (prefixWord ++ tailWord_3758049) baseStart_3758049 baseEnd_3758049 := by
    simpa [prefixWord, tailWord_3758049, baseEnd_3758049] using wordTrace_append hprefix tailTrace_3758049
  have hstable : (prefixWord ++ tailWord_3758049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3758049).length < 2 ^ (prefixWord ++ tailWord_3758049).sum := by decide
  have hdescent : baseEnd_3758049 < baseStart_3758049 := by decide
  rcases family_descends (prefixWord ++ tailWord_3758049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3758059 : List Nat := [1, 1, 1, 1, 2, 3, 1, 4, 4, 1, 4]
def baseStart_3758059 : Nat := 118140960795 + 3758059 * 2 ^ 59
def prefixEnd_3758059 : Nat := 4983230072969 + 3 ^ 40 * 3758059 * 2
def baseEnd_3758059 : Nat := 1929690594955017310579507

theorem tailTrace_3758059 : CollatzResearch.WordTrace tailWord_3758059 prefixEnd_3758059 1929690594955017310579507 := by
  unfold tailWord_3758059
  simp only [CollatzResearch.WordTrace]
  refine ⟨137067672292201543223981231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91378448194801028815987487 137067672292201543223981231)
  ·
    refine ⟨205601508438302314835971847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137067672292201543223981231 205601508438302314835971847)
    ·
      refine ⟨308402262657453472253957771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205601508438302314835971847 308402262657453472253957771)
      ·
        refine ⟨462603393986180208380936657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308402262657453472253957771 462603393986180208380936657)
        ·
          refine ⟨346952545489635156285702493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 462603393986180208380936657 346952545489635156285702493)
          ·
            refine ⟨130107204558613183607138435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 346952545489635156285702493 130107204558613183607138435)
            ·
              refine ⟨195160806837919775410707653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130107204558613183607138435 195160806837919775410707653)
              ·
                refine ⟨36592651282109957889507685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 195160806837919775410707653 36592651282109957889507685)
                ·
                  refine ⟨6861122115395617104282691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36592651282109957889507685 6861122115395617104282691)
                  ·
                    refine ⟨10291683173093425656424037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6861122115395617104282691 10291683173093425656424037)
                    ·
                      refine ⟨1929690594955017310579507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10291683173093425656424037 1929690594955017310579507)
                      ·
                        rfl

theorem cell23_3758059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 4, 4, 1, 4].length) (baseStart_3758059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3758059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3758059 prefixEnd_3758059 := by exact prefixLift 3758059
  have htrace : WordTrace (prefixWord ++ tailWord_3758059) baseStart_3758059 baseEnd_3758059 := by
    simpa [prefixWord, tailWord_3758059, baseEnd_3758059] using wordTrace_append hprefix tailTrace_3758059
  have hstable : (prefixWord ++ tailWord_3758059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3758059).length < 2 ^ (prefixWord ++ tailWord_3758059).sum := by decide
  have hdescent : baseEnd_3758059 < baseStart_3758059 := by decide
  rcases family_descends (prefixWord ++ tailWord_3758059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3758076 : List Nat := [2, 2, 2, 1, 2, 2, 1, 2, 1, 6, 2]
def baseStart_3758076 : Nat := 118140960795 + 3758076 * 2 ^ 59
def prefixEnd_3758076 : Nat := 4983230072969 + 3 ^ 40 * 3758076 * 2
def baseEnd_3758076 : Nat := 1929699324126143744066929

theorem tailTrace_3758076 : CollatzResearch.WordTrace tailWord_3758076 prefixEnd_3758076 1929699324126143744066929 := by
  unfold tailWord_3758076
  simp only [CollatzResearch.WordTrace]
  refine ⟨68534146166569977563675041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91378861555426636751566721 68534146166569977563675041)
  ·
    refine ⟨51400609624927483172756281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68534146166569977563675041 51400609624927483172756281)
    ·
      refine ⟨38550457218695612379567211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51400609624927483172756281 38550457218695612379567211)
      ·
        refine ⟨57825685828043418569350817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38550457218695612379567211 57825685828043418569350817)
        ·
          refine ⟨43369264371032563927013113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57825685828043418569350817 43369264371032563927013113)
          ·
            refine ⟨32526948278274422945259835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43369264371032563927013113 32526948278274422945259835)
            ·
              refine ⟨48790422417411634417889753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32526948278274422945259835 48790422417411634417889753)
              ·
                refine ⟨36592816813058725813417315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48790422417411634417889753 36592816813058725813417315)
                ·
                  refine ⟨54889225219588088720125973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36592816813058725813417315 54889225219588088720125973)
                  ·
                    refine ⟨2572932432168191658755905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 54889225219588088720125973 2572932432168191658755905)
                    ·
                      refine ⟨1929699324126143744066929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2572932432168191658755905 1929699324126143744066929)
                      ·
                        rfl

theorem cell23_3758076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 2, 1, 6, 2].length) (baseStart_3758076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3758076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3758076 prefixEnd_3758076 := by exact prefixLift 3758076
  have htrace : WordTrace (prefixWord ++ tailWord_3758076) baseStart_3758076 baseEnd_3758076 := by
    simpa [prefixWord, tailWord_3758076, baseEnd_3758076] using wordTrace_append hprefix tailTrace_3758076
  have hstable : (prefixWord ++ tailWord_3758076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3758076).length < 2 ^ (prefixWord ++ tailWord_3758076).sum := by decide
  have hdescent : baseEnd_3758076 < baseStart_3758076 := by decide
  rcases family_descends (prefixWord ++ tailWord_3758076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3758137 : List Nat := [1, 2, 1, 5, 3, 2, 1, 3, 1, 4]
def baseStart_3758137 : Nat := 118140960795 + 3758137 * 2 ^ 59
def prefixEnd_3758137 : Nat := 4983230072969 + 3 ^ 40 * 3758137 * 2
def baseEnd_3758137 : Nat := 643243548815356001801383

theorem tailTrace_3758137 : CollatzResearch.WordTrace tailWord_3758137 prefixEnd_3758137 643243548815356001801383 := by
  unfold tailWord_3758137
  simp only [CollatzResearch.WordTrace]
  refine ⟨137070517185918962545320665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91380344790612641696880443 137070517185918962545320665)
  ·
    refine ⟨102802887889439221908990499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137070517185918962545320665 102802887889439221908990499)
    ·
      refine ⟨154204331834158832863485749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102802887889439221908990499 154204331834158832863485749)
      ·
        refine ⟨14456656109452390580951789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 154204331834158832863485749 14456656109452390580951789)
        ·
          refine ⟨5421246041044646467856921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14456656109452390580951789 5421246041044646467856921)
          ·
            refine ⟨4065934530783484850892691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5421246041044646467856921 4065934530783484850892691)
            ·
              refine ⟨6098901796175227276339037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4065934530783484850892691 6098901796175227276339037)
              ·
                refine ⟨2287088173565710228627139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6098901796175227276339037 2287088173565710228627139)
                ·
                  refine ⟨3430632260348565342940709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2287088173565710228627139 3430632260348565342940709)
                  ·
                    refine ⟨643243548815356001801383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3430632260348565342940709 643243548815356001801383)
                    ·
                      rfl

theorem cell23_3758137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 1, 3, 1, 4].length) (baseStart_3758137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3758137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3758137 prefixEnd_3758137 := by exact prefixLift 3758137
  have htrace : WordTrace (prefixWord ++ tailWord_3758137) baseStart_3758137 baseEnd_3758137 := by
    simpa [prefixWord, tailWord_3758137, baseEnd_3758137] using wordTrace_append hprefix tailTrace_3758137
  have hstable : (prefixWord ++ tailWord_3758137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3758137).length < 2 ^ (prefixWord ++ tailWord_3758137).sum := by decide
  have hdescent : baseEnd_3758137 < baseStart_3758137 := by decide
  rcases family_descends (prefixWord ++ tailWord_3758137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3758153 : List Nat := [1, 2, 1, 1, 2, 2, 5, 2, 2, 3, 2]
def baseStart_3758153 : Nat := 118140960795 + 3758153 * 2 ^ 59
def prefixEnd_3758153 : Nat := 4983230072969 + 3 ^ 40 * 3758153 * 2
def baseEnd_3758153 : Nat := 1929738862136539942804075

theorem tailTrace_3758153 : CollatzResearch.WordTrace tailWord_3758153 prefixEnd_3758153 1929738862136539942804075 := by
  unfold tailWord_3758153
  simp only [CollatzResearch.WordTrace]
  refine ⟨137071100753860997277903113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91380733835907331518602075 137071100753860997277903113)
  ·
    refine ⟨102803325565395747958427335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137071100753860997277903113 102803325565395747958427335)
    ·
      refine ⟨154204988348093621937641003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102803325565395747958427335 154204988348093621937641003)
      ·
        refine ⟨231307482522140432906461505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154204988348093621937641003 231307482522140432906461505)
        ·
          refine ⟨173480611891605324679846129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231307482522140432906461505 173480611891605324679846129)
          ·
            refine ⟨130110458918703993509884597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173480611891605324679846129 130110458918703993509884597)
            ·
              refine ⟨12197855523628499391551681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 130110458918703993509884597 12197855523628499391551681)
              ·
                refine ⟨9148391642721374543663761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12197855523628499391551681 9148391642721374543663761)
                ·
                  refine ⟨6861293732041030907747821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9148391642721374543663761 6861293732041030907747821)
                  ·
                    refine ⟨2572985149515386590405433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6861293732041030907747821 2572985149515386590405433)
                    ·
                      refine ⟨1929738862136539942804075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2572985149515386590405433 1929738862136539942804075)
                      ·
                        rfl

theorem cell23_3758153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 2, 2, 3, 2].length) (baseStart_3758153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3758153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3758153 prefixEnd_3758153 := by exact prefixLift 3758153
  have htrace : WordTrace (prefixWord ++ tailWord_3758153) baseStart_3758153 baseEnd_3758153 := by
    simpa [prefixWord, tailWord_3758153, baseEnd_3758153] using wordTrace_append hprefix tailTrace_3758153
  have hstable : (prefixWord ++ tailWord_3758153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3758153).length < 2 ^ (prefixWord ++ tailWord_3758153).sum := by decide
  have hdescent : baseEnd_3758153 < baseStart_3758153 := by decide
  rcases family_descends (prefixWord ++ tailWord_3758153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3758159 : List Nat := [1, 1, 2, 1, 1, 2, 2, 4, 3, 6]
def baseStart_3758159 : Nat := 118140960795 + 3758159 * 2 ^ 59
def prefixEnd_3758159 : Nat := 4983230072969 + 3 ^ 40 * 3758159 * 2
def baseEnd_3758159 : Nat := 643247314340155639776349

theorem tailTrace_3758159 : CollatzResearch.WordTrace tailWord_3758159 prefixEnd_3758159 643247314340155639776349 := by
  unfold tailWord_3758159
  simp only [CollatzResearch.WordTrace]
  refine ⟨137071319591839260302621531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91380879727892840201747687 137071319591839260302621531)
  ·
    refine ⟨205606979387758890453932297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137071319591839260302621531 205606979387758890453932297)
    ·
      refine ⟨154205234540819167840449223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205606979387758890453932297 154205234540819167840449223)
      ·
        refine ⟨231307851811228751760673835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154205234540819167840449223 231307851811228751760673835)
        ·
          refine ⟨346961777716843127641010753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231307851811228751760673835 346961777716843127641010753)
          ·
            refine ⟨260221333287632345730758065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 346961777716843127641010753 260221333287632345730758065)
            ·
              refine ⟨195165999965724259298068549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 260221333287632345730758065 195165999965724259298068549)
              ·
                refine ⟨36593624993573298618387853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 195165999965724259298068549 36593624993573298618387853)
                ·
                  refine ⟨13722609372589986981895445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36593624993573298618387853 13722609372589986981895445)
                  ·
                    refine ⟨643247314340155639776349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13722609372589986981895445 643247314340155639776349)
                    ·
                      rfl

theorem cell23_3758159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 4, 3, 6].length) (baseStart_3758159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3758159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3758159 prefixEnd_3758159 := by exact prefixLift 3758159
  have htrace : WordTrace (prefixWord ++ tailWord_3758159) baseStart_3758159 baseEnd_3758159 := by
    simpa [prefixWord, tailWord_3758159, baseEnd_3758159] using wordTrace_append hprefix tailTrace_3758159
  have hstable : (prefixWord ++ tailWord_3758159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3758159).length < 2 ^ (prefixWord ++ tailWord_3758159).sum := by decide
  have hdescent : baseEnd_3758159 < baseStart_3758159 := by decide
  rcases family_descends (prefixWord ++ tailWord_3758159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3758217 : List Nat := [1, 2, 1, 1, 4, 2, 3, 4, 1, 2, 2]
def baseStart_3758217 : Nat := 118140960795 + 3758217 * 2 ^ 59
def prefixEnd_3758217 : Nat := 4983230072969 + 3 ^ 40 * 3758217 * 2
def baseEnd_3758217 : Nat := 1929771724898427692403781

theorem tailTrace_3758217 : CollatzResearch.WordTrace tailWord_3758217 prefixEnd_3758217 1929771724898427692403781 := by
  unfold tailWord_3758217
  simp only [CollatzResearch.WordTrace]
  refine ⟨137073435025629136208232905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91382290017086090805488603 137073435025629136208232905)
  ·
    refine ⟨102805076269221852156174679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137073435025629136208232905 102805076269221852156174679)
    ·
      refine ⟨154207614403832778234262019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102805076269221852156174679 154207614403832778234262019)
      ·
        refine ⟨231311421605749167351393029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154207614403832778234262019 231311421605749167351393029)
        ·
          refine ⟨43370891551077968878386193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 231311421605749167351393029 43370891551077968878386193)
          ·
            refine ⟨32528168663308476658789645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43370891551077968878386193 32528168663308476658789645)
            ·
              refine ⟨12198063248740678747046117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32528168663308476658789645 12198063248740678747046117)
              ·
                refine ⟨2287136859138877265071147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12198063248740678747046117 2287136859138877265071147)
                ·
                  refine ⟨3430705288708315897606721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2287136859138877265071147 3430705288708315897606721)
                  ·
                    refine ⟨2573028966531236923205041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3430705288708315897606721 2573028966531236923205041)
                    ·
                      refine ⟨1929771724898427692403781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2573028966531236923205041 1929771724898427692403781)
                      ·
                        rfl

theorem cell23_3758217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 4, 1, 2, 2].length) (baseStart_3758217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3758217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3758217 prefixEnd_3758217 := by exact prefixLift 3758217
  have htrace : WordTrace (prefixWord ++ tailWord_3758217) baseStart_3758217 baseEnd_3758217 := by
    simpa [prefixWord, tailWord_3758217, baseEnd_3758217] using wordTrace_append hprefix tailTrace_3758217
  have hstable : (prefixWord ++ tailWord_3758217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3758217).length < 2 ^ (prefixWord ++ tailWord_3758217).sum := by decide
  have hdescent : baseEnd_3758217 < baseStart_3758217 := by decide
  rcases family_descends (prefixWord ++ tailWord_3758217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3758236 : List Nat := [2, 2, 3, 2, 1, 1, 1, 2, 2, 7]
def baseStart_3758236 : Nat := 118140960795 + 3758236 * 2 ^ 59
def prefixEnd_3758236 : Nat := 4983230072969 + 3 ^ 40 * 3758236 * 2
def baseEnd_3758236 : Nat := 643260493676954372688731

theorem tailTrace_3758236 : CollatzResearch.WordTrace tailWord_3758236 prefixEnd_3758236 643260493676954372688731 := by
  unfold tailWord_3758236
  simp only [CollatzResearch.WordTrace]
  refine ⟨68537064006280151226587281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91382752008373534968783041 68537064006280151226587281)
  ·
    refine ⟨51402798004710113419940461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68537064006280151226587281 51402798004710113419940461)
    ·
      refine ⟨19276049251766292532477673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51402798004710113419940461 19276049251766292532477673)
      ·
        refine ⟨14457036938824719399358255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19276049251766292532477673 14457036938824719399358255)
        ·
          refine ⟨21685555408237079099037383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14457036938824719399358255 21685555408237079099037383)
          ·
            refine ⟨32528333112355618648556075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21685555408237079099037383 32528333112355618648556075)
            ·
              refine ⟨48792499668533427972834113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32528333112355618648556075 48792499668533427972834113)
              ·
                refine ⟨36594374751400070979625585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48792499668533427972834113 36594374751400070979625585)
                ·
                  refine ⟨27445781063550053234719189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36594374751400070979625585 27445781063550053234719189)
                  ·
                    refine ⟨643260493676954372688731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27445781063550053234719189 643260493676954372688731)
                    ·
                      rfl

theorem cell23_3758236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 2, 2, 7].length) (baseStart_3758236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3758236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3758236 prefixEnd_3758236 := by exact prefixLift 3758236
  have htrace : WordTrace (prefixWord ++ tailWord_3758236) baseStart_3758236 baseEnd_3758236 := by
    simpa [prefixWord, tailWord_3758236, baseEnd_3758236] using wordTrace_append hprefix tailTrace_3758236
  have hstable : (prefixWord ++ tailWord_3758236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3758236).length < 2 ^ (prefixWord ++ tailWord_3758236).sum := by decide
  have hdescent : baseEnd_3758236 < baseStart_3758236 := by decide
  rcases family_descends (prefixWord ++ tailWord_3758236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3758254 : List Nat := [4, 1, 4, 2, 1, 1, 1, 3, 1, 2, 3]
def baseStart_3758254 : Nat := 118140960795 + 3758254 * 2 ^ 59
def prefixEnd_3758254 : Nat := 4983230072969 + 3 ^ 40 * 3758254 * 2
def baseEnd_3758254 : Nat := 1929790723682644047641111

theorem tailTrace_3758254 : CollatzResearch.WordTrace tailWord_3758254 prefixEnd_3758254 1929790723682644047641111 := by
  unfold tailWord_3758254
  simp only [CollatzResearch.WordTrace]
  refine ⟨17134348065811886440916227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91383189684330061018219877 17134348065811886440916227)
  ·
    refine ⟨25701522098717829661374341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17134348065811886440916227 25701522098717829661374341)
    ·
      refine ⟨4819035393509593061507689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25701522098717829661374341 4819035393509593061507689)
      ·
        refine ⟨3614276545132194796130767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4819035393509593061507689 3614276545132194796130767)
        ·
          refine ⟨5421414817698292194196151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3614276545132194796130767 5421414817698292194196151)
          ·
            refine ⟨8132122226547438291294227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5421414817698292194196151 8132122226547438291294227)
            ·
              refine ⟨12198183339821157436941341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8132122226547438291294227 12198183339821157436941341)
              ·
                refine ⟨4574318752432934038853003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12198183339821157436941341 4574318752432934038853003)
                ·
                  refine ⟨6861478128649401058279505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4574318752432934038853003 6861478128649401058279505)
                  ·
                    refine ⟨5146108596487050793709629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6861478128649401058279505 5146108596487050793709629)
                    ·
                      refine ⟨1929790723682644047641111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5146108596487050793709629 1929790723682644047641111)
                      ·
                        rfl

theorem cell23_3758254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_3758254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3758254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3758254 prefixEnd_3758254 := by exact prefixLift 3758254
  have htrace : WordTrace (prefixWord ++ tailWord_3758254) baseStart_3758254 baseEnd_3758254 := by
    simpa [prefixWord, tailWord_3758254, baseEnd_3758254] using wordTrace_append hprefix tailTrace_3758254
  have hstable : (prefixWord ++ tailWord_3758254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3758254).length < 2 ^ (prefixWord ++ tailWord_3758254).sum := by decide
  have hdescent : baseEnd_3758254 < baseStart_3758254 := by decide
  rcases family_descends (prefixWord ++ tailWord_3758254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3758266 : List Nat := [3, 1, 1, 1, 2, 2, 3, 2, 2, 6]
def baseStart_3758266 : Nat := 118140960795 + 3758266 * 2 ^ 59
def prefixEnd_3758266 : Nat := 4983230072969 + 3 ^ 40 * 3758266 * 2
def baseEnd_3758266 : Nat := 643265628483499333563685

theorem tailTrace_3758266 : CollatzResearch.WordTrace tailWord_3758266 prefixEnd_3758266 643265628483499333563685 := by
  unfold tailWord_3758266
  simp only [CollatzResearch.WordTrace]
  refine ⟨34268805550612904394191663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91383481468301078384511101 34268805550612904394191663)
  ·
    refine ⟨51403208325919356591287495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34268805550612904394191663 51403208325919356591287495)
    ·
      refine ⟨77104812488879034886931243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51403208325919356591287495 77104812488879034886931243)
      ·
        refine ⟨115657218733318552330396865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77104812488879034886931243 115657218733318552330396865)
        ·
          refine ⟨86742914049988914247797649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115657218733318552330396865 86742914049988914247797649)
          ·
            refine ⟨65057185537491685685848237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86742914049988914247797649 65057185537491685685848237)
            ·
              refine ⟨24396444576559382132193089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65057185537491685685848237 24396444576559382132193089)
              ·
                refine ⟨18297333432419536599144817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24396444576559382132193089 18297333432419536599144817)
                ·
                  refine ⟨13723000074314652449358613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18297333432419536599144817 13723000074314652449358613)
                  ·
                    refine ⟨643265628483499333563685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13723000074314652449358613 643265628483499333563685)
                    ·
                      rfl

theorem cell23_3758266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 2, 2, 6].length) (baseStart_3758266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3758266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3758266 prefixEnd_3758266 := by exact prefixLift 3758266
  have htrace : WordTrace (prefixWord ++ tailWord_3758266) baseStart_3758266 baseEnd_3758266 := by
    simpa [prefixWord, tailWord_3758266, baseEnd_3758266] using wordTrace_append hprefix tailTrace_3758266
  have hstable : (prefixWord ++ tailWord_3758266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3758266).length < 2 ^ (prefixWord ++ tailWord_3758266).sum := by decide
  have hdescent : baseEnd_3758266 < baseStart_3758266 := by decide
  rcases family_descends (prefixWord ++ tailWord_3758266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3758284 : List Nat := [2, 2, 1, 6, 2, 1, 1, 1, 1, 3, 3]
def baseStart_3758284 : Nat := 118140960795 + 3758284 * 2 ^ 59
def prefixEnd_3758284 : Nat := 4983230072969 + 3 ^ 40 * 3758284 * 2
def baseEnd_3758284 : Nat := 1929806128102278930265973

theorem tailTrace_3758284 : CollatzResearch.WordTrace tailWord_3758284 prefixEnd_3758284 1929806128102278930265973 := by
  unfold tailWord_3758284
  simp only [CollatzResearch.WordTrace]
  refine ⟨68537939358193203325460953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91383919144257604433947937 68537939358193203325460953)
  ·
    refine ⟨51403454518644902494095715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68537939358193203325460953 51403454518644902494095715)
    ·
      refine ⟨77105181777967353741143573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51403454518644902494095715 77105181777967353741143573)
      ·
        refine ⟨3614305395842219706616105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 77105181777967353741143573 3614305395842219706616105)
        ·
          refine ⟨2710729046881664779962079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3614305395842219706616105 2710729046881664779962079)
          ·
            refine ⟨4066093570322497169943119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2710729046881664779962079 4066093570322497169943119)
            ·
              refine ⟨6099140355483745754914679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4066093570322497169943119 6099140355483745754914679)
              ·
                refine ⟨9148710533225618632372019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6099140355483745754914679 9148710533225618632372019)
                ·
                  refine ⟨13723065799838427948558029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9148710533225618632372019 13723065799838427948558029)
                  ·
                    refine ⟨5146149674939410480709261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13723065799838427948558029 5146149674939410480709261)
                    ·
                      refine ⟨1929806128102278930265973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5146149674939410480709261 1929806128102278930265973)
                      ·
                        rfl

theorem cell23_3758284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_3758284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3758284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3758284 prefixEnd_3758284 := by exact prefixLift 3758284
  have htrace : WordTrace (prefixWord ++ tailWord_3758284) baseStart_3758284 baseEnd_3758284 := by
    simpa [prefixWord, tailWord_3758284, baseEnd_3758284] using wordTrace_append hprefix tailTrace_3758284
  have hstable : (prefixWord ++ tailWord_3758284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3758284).length < 2 ^ (prefixWord ++ tailWord_3758284).sum := by decide
  have hdescent : baseEnd_3758284 < baseStart_3758284 := by decide
  rcases family_descends (prefixWord ++ tailWord_3758284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3758294 : List Nat := [5, 2, 1, 2, 1, 1, 1, 4, 1, 3, 2]
def baseStart_3758294 : Nat := 118140960795 + 3758294 * 2 ^ 59
def prefixEnd_3758294 : Nat := 4983230072969 + 3 ^ 40 * 3758294 * 2
def baseEnd_3758294 : Nat := 1929811262908823891140927

theorem tailTrace_3758294 : CollatzResearch.WordTrace tailWord_3758294 prefixEnd_3758294 1929811262908823891140927 := by
  unfold tailWord_3758294
  simp only [CollatzResearch.WordTrace]
  refine ⟨8567265215396886147424121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 91384162297566785572523957 8567265215396886147424121)
  ·
    refine ⟨6425448911547664610568091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8567265215396886147424121 6425448911547664610568091)
    ·
      refine ⟨9638173367321496915852137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6425448911547664610568091 9638173367321496915852137)
      ·
        refine ⟨7228630025491122686889103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9638173367321496915852137 7228630025491122686889103)
        ·
          refine ⟨10842945038236684030333655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7228630025491122686889103 10842945038236684030333655)
          ·
            refine ⟨16264417557355026045500483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10842945038236684030333655 16264417557355026045500483)
            ·
              refine ⟨24396626336032539068250725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16264417557355026045500483 24396626336032539068250725)
              ·
                refine ⟨4574367438006101075297011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24396626336032539068250725 4574367438006101075297011)
                ·
                  refine ⟨6861551157009151612945517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4574367438006101075297011 6861551157009151612945517)
                  ·
                    refine ⟨2573081683878431854854569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6861551157009151612945517 2573081683878431854854569)
                    ·
                      refine ⟨1929811262908823891140927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2573081683878431854854569 1929811262908823891140927)
                      ·
                        rfl

theorem cell23_3758294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 4, 1, 3, 2].length) (baseStart_3758294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3758294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3758294 prefixEnd_3758294 := by exact prefixLift 3758294
  have htrace : WordTrace (prefixWord ++ tailWord_3758294) baseStart_3758294 baseEnd_3758294 := by
    simpa [prefixWord, tailWord_3758294, baseEnd_3758294] using wordTrace_append hprefix tailTrace_3758294
  have hstable : (prefixWord ++ tailWord_3758294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3758294).length < 2 ^ (prefixWord ++ tailWord_3758294).sum := by decide
  have hdescent : baseEnd_3758294 < baseStart_3758294 := by decide
  rcases family_descends (prefixWord ++ tailWord_3758294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3758336 : List Nat := [2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 7]
def baseStart_3758336 : Nat := 118140960795 + 3758336 * 2 ^ 59
def prefixEnd_3758336 : Nat := 4983230072969 + 3 ^ 40 * 3758336 * 2
def baseEnd_3758336 : Nat := 1929832829096312726815733

theorem tailTrace_3758336 : CollatzResearch.WordTrace tailWord_3758336 prefixEnd_3758336 1929832829096312726815733 := by
  unfold tailWord_3758336
  simp only [CollatzResearch.WordTrace]
  refine ⟨68538887656099009765907431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91385183541465346354543241 68538887656099009765907431)
  ·
    refine ⟨102808331484148514648861147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68538887656099009765907431 102808331484148514648861147)
    ·
      refine ⟨154212497226222771973291721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102808331484148514648861147 154212497226222771973291721)
      ·
        refine ⟨115659372919667078979968791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154212497226222771973291721 115659372919667078979968791)
        ·
          refine ⟨173489059379500618469953187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115659372919667078979968791 173489059379500618469953187)
          ·
            refine ⟨260233589069250927704929781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173489059379500618469953187 260233589069250927704929781)
            ·
              refine ⟨24396898975242274472337167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 260233589069250927704929781 24396898975242274472337167)
              ·
                refine ⟨36595348462863411708505751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24396898975242274472337167 36595348462863411708505751)
                ·
                  refine ⟨54893022694295117562758627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36595348462863411708505751 54893022694295117562758627)
                  ·
                    refine ⟨82339534041442676344137941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54893022694295117562758627 82339534041442676344137941)
                    ·
                      refine ⟨1929832829096312726815733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 82339534041442676344137941 1929832829096312726815733)
                      ·
                        rfl

theorem cell23_3758336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 7].length) (baseStart_3758336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3758336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3758336 prefixEnd_3758336 := by exact prefixLift 3758336
  have htrace : WordTrace (prefixWord ++ tailWord_3758336) baseStart_3758336 baseEnd_3758336 := by
    simpa [prefixWord, tailWord_3758336, baseEnd_3758336] using wordTrace_append hprefix tailTrace_3758336
  have hstable : (prefixWord ++ tailWord_3758336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3758336).length < 2 ^ (prefixWord ++ tailWord_3758336).sum := by decide
  have hdescent : baseEnd_3758336 < baseStart_3758336 := by decide
  rcases family_descends (prefixWord ++ tailWord_3758336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3758363 : List Nat := [1, 1, 1, 1, 1, 1, 7, 3, 2, 1, 4]
def baseStart_3758363 : Nat := 118140960795 + 3758363 * 2 ^ 59
def prefixEnd_3758363 : Nat := 4983230072969 + 3 ^ 40 * 3758363 * 2
def baseEnd_3758363 : Nat := 1929846693073984121178109

theorem tailTrace_3758363 : CollatzResearch.WordTrace tailWord_3758363 prefixEnd_3758363 1929846693073984121178109 := by
  unfold tailWord_3758363
  simp only [CollatzResearch.WordTrace]
  refine ⟨137078760083100203143047743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91385840055400135428698495 137078760083100203143047743)
  ·
    refine ⟨205618140124650304714571615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137078760083100203143047743 205618140124650304714571615)
    ·
      refine ⟨308427210186975457071857423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205618140124650304714571615 308427210186975457071857423)
      ·
        refine ⟨462640815280463185607786135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308427210186975457071857423 462640815280463185607786135)
        ·
          refine ⟨693961222920694778411679203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 462640815280463185607786135 693961222920694778411679203)
          ·
            refine ⟨1040941834381042167617518805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 693961222920694778411679203 1040941834381042167617518805)
            ·
              refine ⟨24397074243305675803535597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1040941834381042167617518805 24397074243305675803535597)
              ·
                refine ⟨9148902841239628426325849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24397074243305675803535597 9148902841239628426325849)
                ·
                  refine ⟨6861677130929721319744387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9148902841239628426325849 6861677130929721319744387)
                  ·
                    refine ⟨10292515696394581979616581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6861677130929721319744387 10292515696394581979616581)
                    ·
                      refine ⟨1929846693073984121178109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10292515696394581979616581 1929846693073984121178109)
                      ·
                        rfl

theorem cell23_3758363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 3, 2, 1, 4].length) (baseStart_3758363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3758363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3758363 prefixEnd_3758363 := by exact prefixLift 3758363
  have htrace : WordTrace (prefixWord ++ tailWord_3758363) baseStart_3758363 baseEnd_3758363 := by
    simpa [prefixWord, tailWord_3758363, baseEnd_3758363] using wordTrace_append hprefix tailTrace_3758363
  have hstable : (prefixWord ++ tailWord_3758363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3758363).length < 2 ^ (prefixWord ++ tailWord_3758363).sum := by decide
  have hdescent : baseEnd_3758363 < baseStart_3758363 := by decide
  rcases family_descends (prefixWord ++ tailWord_3758363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3758381 : List Nat := [1, 5, 3, 1, 2, 2, 2, 2, 5]
def baseStart_3758381 : Nat := 118140960795 + 3758381 * 2 ^ 59
def prefixEnd_3758381 : Nat := 4983230072969 + 3 ^ 40 * 3758381 * 2
def baseEnd_3758381 : Nat := 214428437302862783417003

theorem tailTrace_3758381 : CollatzResearch.WordTrace tailWord_3758381 prefixEnd_3758381 214428437302862783417003 := by
  unfold tailWord_3758381
  simp only [CollatzResearch.WordTrace]
  refine ⟨137079416597034992217202997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91386277731356661478135331 137079416597034992217202997)
  ·
    refine ⟨12851195305972030520362781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 137079416597034992217202997 12851195305972030520362781)
    ·
      refine ⟨4819198239739511445136043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12851195305972030520362781 4819198239739511445136043)
      ·
        refine ⟨7228797359609267167704065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4819198239739511445136043 7228797359609267167704065)
        ·
          refine ⟨5421598019706950375778049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7228797359609267167704065 5421598019706950375778049)
          ·
            refine ⟨4066198514780212781833537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5421598019706950375778049 4066198514780212781833537)
            ·
              refine ⟨3049648886085159586375153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4066198514780212781833537 3049648886085159586375153)
              ·
                refine ⟨2287236664563869689781365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3049648886085159586375153 2287236664563869689781365)
                ·
                  refine ⟨214428437302862783417003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2287236664563869689781365 214428437302862783417003)
                  ·
                    rfl

theorem cell23_3758381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 2, 2, 5].length) (baseStart_3758381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3758381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3758381 prefixEnd_3758381 := by exact prefixLift 3758381
  have htrace : WordTrace (prefixWord ++ tailWord_3758381) baseStart_3758381 baseEnd_3758381 := by
    simpa [prefixWord, tailWord_3758381, baseEnd_3758381] using wordTrace_append hprefix tailTrace_3758381
  have hstable : (prefixWord ++ tailWord_3758381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3758381).length < 2 ^ (prefixWord ++ tailWord_3758381).sum := by decide
  have hdescent : baseEnd_3758381 < baseStart_3758381 := by decide
  rcases family_descends (prefixWord ++ tailWord_3758381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3758403 : List Nat := [1, 1, 1, 3, 1, 3, 4, 3, 6]
def baseStart_3758403 : Nat := 118140960795 + 3758403 * 2 ^ 59
def prefixEnd_3758403 : Nat := 4983230072969 + 3 ^ 40 * 3758403 * 2
def baseEnd_3758403 : Nat := 214429692477795996075325

theorem tailTrace_3758403 : CollatzResearch.WordTrace tailWord_3758403 prefixEnd_3758403 214429692477795996075325 := by
  unfold tailWord_3758403
  simp only [CollatzResearch.WordTrace]
  refine ⟨137080219002955289974503863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91386812668636859983002575 137080219002955289974503863)
  ·
    refine ⟨205620328504432934961755795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137080219002955289974503863 205620328504432934961755795)
    ·
      refine ⟨308430492756649402442633693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205620328504432934961755795 308430492756649402442633693)
      ·
        refine ⟨115661434783743525915987635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 308430492756649402442633693 115661434783743525915987635)
        ·
          refine ⟨173492152175615288873981453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115661434783743525915987635 173492152175615288873981453)
          ·
            refine ⟨65059557065855733327743045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 173492152175615288873981453 65059557065855733327743045)
            ·
              refine ⟨12198666949847949998951821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65059557065855733327743045 12198666949847949998951821)
              ·
                refine ⟨4574500106192981249606933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12198666949847949998951821 4574500106192981249606933)
                ·
                  refine ⟨214429692477795996075325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4574500106192981249606933 214429692477795996075325)
                  ·
                    rfl

theorem cell23_3758403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 3, 6].length) (baseStart_3758403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3758403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3758403 prefixEnd_3758403 := by exact prefixLift 3758403
  have htrace : WordTrace (prefixWord ++ tailWord_3758403) baseStart_3758403 baseEnd_3758403 := by
    simpa [prefixWord, tailWord_3758403, baseEnd_3758403] using wordTrace_append hprefix tailTrace_3758403
  have hstable : (prefixWord ++ tailWord_3758403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3758403).length < 2 ^ (prefixWord ++ tailWord_3758403).sum := by decide
  have hdescent : baseEnd_3758403 < baseStart_3758403 := by decide
  rcases family_descends (prefixWord ++ tailWord_3758403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3758417 : List Nat := [1, 2, 2, 1, 4, 4, 1, 1, 2, 2, 3]
def baseStart_3758417 : Nat := 118140960795 + 3758417 * 2 ^ 59
def prefixEnd_3758417 : Nat := 4983230072969 + 3 ^ 40 * 3758417 * 2
def baseEnd_3758417 : Nat := 1929874421029326909902861

theorem tailTrace_3758417 : CollatzResearch.WordTrace tailWord_3758417 prefixEnd_3758417 1929874421029326909902861 := by
  unfold tailWord_3758417
  simp only [CollatzResearch.WordTrace]
  refine ⟨137080729624904570365513505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91387153083269713577009003 137080729624904570365513505)
  ·
    refine ⟨102810547218678427774135129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137080729624904570365513505 102810547218678427774135129)
    ·
      refine ⟨77107910414008820830601347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102810547218678427774135129 77107910414008820830601347)
      ·
        refine ⟨115661865621013231245902021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77107910414008820830601347 115661865621013231245902021)
        ·
          refine ⟨21686599803939980858606629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115661865621013231245902021 21686599803939980858606629)
          ·
            refine ⟨4066237463238746410988743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21686599803939980858606629 4066237463238746410988743)
            ·
              refine ⟨6099356194858119616483115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4066237463238746410988743 6099356194858119616483115)
              ·
                refine ⟨9149034292287179424724673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6099356194858119616483115 9149034292287179424724673)
                ·
                  refine ⟨6861775719215384568543505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9149034292287179424724673 6861775719215384568543505)
                  ·
                    refine ⟨5146331789411538426407629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6861775719215384568543505 5146331789411538426407629)
                    ·
                      refine ⟨1929874421029326909902861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5146331789411538426407629 1929874421029326909902861)
                      ·
                        rfl

theorem cell23_3758417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 1, 1, 2, 2, 3].length) (baseStart_3758417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3758417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3758417 prefixEnd_3758417 := by exact prefixLift 3758417
  have htrace : WordTrace (prefixWord ++ tailWord_3758417) baseStart_3758417 baseEnd_3758417 := by
    simpa [prefixWord, tailWord_3758417, baseEnd_3758417] using wordTrace_append hprefix tailTrace_3758417
  have hstable : (prefixWord ++ tailWord_3758417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3758417).length < 2 ^ (prefixWord ++ tailWord_3758417).sum := by decide
  have hdescent : baseEnd_3758417 < baseStart_3758417 := by decide
  rcases family_descends (prefixWord ++ tailWord_3758417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3758467 : List Nat := [1, 1, 1, 3, 6, 1, 2, 2, 1, 5]
def baseStart_3758467 : Nat := 118140960795 + 3758467 * 2 ^ 59
def prefixEnd_3758467 : Nat := 4983230072969 + 3 ^ 40 * 3758467 * 2
def baseEnd_3758467 : Nat := 643300031687350571425877

theorem tailTrace_3758467 : CollatzResearch.WordTrace tailWord_3758467 prefixEnd_3758467 643300031687350571425877 := by
  unfold tailWord_3758467
  simp only [CollatzResearch.WordTrace]
  refine ⟨137082553274723428904833655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91388368849815619269889103 137082553274723428904833655)
  ·
    refine ⟨205623829912085143357250483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137082553274723428904833655 205623829912085143357250483)
    ·
      refine ⟨308435744868127715035875725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205623829912085143357250483 308435744868127715035875725)
      ·
        refine ⟨115663404325547893138453397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 308435744868127715035875725 115663404325547893138453397)
        ·
          refine ⟨5421722077760057490865003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 115663404325547893138453397 5421722077760057490865003)
          ·
            refine ⟨8132583116640086236297505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5421722077760057490865003 8132583116640086236297505)
            ·
              refine ⟨6099437337480064677223129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8132583116640086236297505 6099437337480064677223129)
              ·
                refine ⟨4574578003110048507917347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6099437337480064677223129 4574578003110048507917347)
                ·
                  refine ⟨6861867004665072761876021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4574578003110048507917347 6861867004665072761876021)
                  ·
                    refine ⟨643300031687350571425877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6861867004665072761876021 643300031687350571425877)
                    ·
                      rfl

theorem cell23_3758467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 2, 2, 1, 5].length) (baseStart_3758467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3758467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3758467 prefixEnd_3758467 := by exact prefixLift 3758467
  have htrace : WordTrace (prefixWord ++ tailWord_3758467) baseStart_3758467 baseEnd_3758467 := by
    simpa [prefixWord, tailWord_3758467, baseEnd_3758467] using wordTrace_append hprefix tailTrace_3758467
  have hstable : (prefixWord ++ tailWord_3758467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3758467).length < 2 ^ (prefixWord ++ tailWord_3758467).sum := by decide
  have hdescent : baseEnd_3758467 < baseStart_3758467 := by decide
  rcases family_descends (prefixWord ++ tailWord_3758467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3758487 : List Nat := [1, 1, 3, 3, 1, 1, 2, 2, 5, 2, 2]
def baseStart_3758487 : Nat := 118140960795 + 3758487 * 2 ^ 59
def prefixEnd_3758487 : Nat := 4983230072969 + 3 ^ 40 * 3758487 * 2
def baseEnd_3758487 : Nat := 1929910364675141636027539

theorem tailTrace_3758487 : CollatzResearch.WordTrace tailWord_3758487 prefixEnd_3758487 1929910364675141636027539 := by
  unfold tailWord_3758487
  simp only [CollatzResearch.WordTrace]
  refine ⟨137083282734650972320561715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91388855156433981547041143 137083282734650972320561715)
  ·
    refine ⟨205624924101976458480842573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137083282734650972320561715 205624924101976458480842573)
    ·
      refine ⟨77109346538241171930315965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205624924101976458480842573 77109346538241171930315965)
      ·
        refine ⟨28916004951840439473868487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77109346538241171930315965 28916004951840439473868487)
        ·
          refine ⟨43374007427760659210802731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28916004951840439473868487 43374007427760659210802731)
          ·
            refine ⟨65061011141640988816204097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43374007427760659210802731 65061011141640988816204097)
            ·
              refine ⟨48795758356230741612153073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65061011141640988816204097 48795758356230741612153073)
              ·
                refine ⟨36596818767173056209114805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48795758356230741612153073 36596818767173056209114805)
                ·
                  refine ⟨3430951759422474019604513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36596818767173056209114805 3430951759422474019604513)
                  ·
                    refine ⟨2573213819566855514703385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3430951759422474019604513 2573213819566855514703385)
                    ·
                      refine ⟨1929910364675141636027539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2573213819566855514703385 1929910364675141636027539)
                      ·
                        rfl

theorem cell23_3758487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 2, 5, 2, 2].length) (baseStart_3758487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3758487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3758487 prefixEnd_3758487 := by exact prefixLift 3758487
  have htrace : WordTrace (prefixWord ++ tailWord_3758487) baseStart_3758487 baseEnd_3758487 := by
    simpa [prefixWord, tailWord_3758487, baseEnd_3758487] using wordTrace_append hprefix tailTrace_3758487
  have hstable : (prefixWord ++ tailWord_3758487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3758487).length < 2 ^ (prefixWord ++ tailWord_3758487).sum := by decide
  have hdescent : baseEnd_3758487 < baseStart_3758487 := by decide
  rcases family_descends (prefixWord ++ tailWord_3758487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3758490 : List Nat := [3, 1, 1, 4, 1, 2, 1, 3, 1, 1, 5]
def baseStart_3758490 : Nat := 118140960795 + 3758490 * 2 ^ 59
def prefixEnd_3758490 : Nat := 4983230072969 + 3 ^ 40 * 3758490 * 2
def baseEnd_3758490 : Nat := 1929911905117105124290025

theorem tailTrace_3758490 : CollatzResearch.WordTrace tailWord_3758490 prefixEnd_3758490 1929911905117105124290025 := by
  unfold tailWord_3758490
  simp only [CollatzResearch.WordTrace]
  refine ⟨34270848038410025958230231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91388928102426735888613949 34270848038410025958230231)
  ·
    refine ⟨51406272057615038937345347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34270848038410025958230231 51406272057615038937345347)
    ·
      refine ⟨77109408086422558406018021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51406272057615038937345347 77109408086422558406018021)
      ·
        refine ⟨14458014016204229701128379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77109408086422558406018021 14458014016204229701128379)
        ·
          refine ⟨21687021024306344551692569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14458014016204229701128379 21687021024306344551692569)
          ·
            refine ⟨16265265768229758413769427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21687021024306344551692569 16265265768229758413769427)
            ·
              refine ⟨24397898652344637620654141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16265265768229758413769427 24397898652344637620654141)
              ·
                refine ⟨9149211994629239107745303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24397898652344637620654141 9149211994629239107745303)
                ·
                  refine ⟨13723817991943858661617955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9149211994629239107745303 13723817991943858661617955)
                  ·
                    refine ⟨20585726987915787992426933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13723817991943858661617955 20585726987915787992426933)
                    ·
                      refine ⟨1929911905117105124290025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20585726987915787992426933 1929911905117105124290025)
                      ·
                        rfl

theorem cell23_3758490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_3758490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3758490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3758490 prefixEnd_3758490 := by exact prefixLift 3758490
  have htrace : WordTrace (prefixWord ++ tailWord_3758490) baseStart_3758490 baseEnd_3758490 := by
    simpa [prefixWord, tailWord_3758490, baseEnd_3758490] using wordTrace_append hprefix tailTrace_3758490
  have hstable : (prefixWord ++ tailWord_3758490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3758490).length < 2 ^ (prefixWord ++ tailWord_3758490).sum := by decide
  have hdescent : baseEnd_3758490 < baseStart_3758490 := by decide
  rcases family_descends (prefixWord ++ tailWord_3758490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3758520 : List Nat := [2, 1, 2, 1, 2, 2, 1, 5, 1, 3, 3]
def baseStart_3758520 : Nat := 118140960795 + 3758520 * 2 ^ 59
def prefixEnd_3758520 : Nat := 4983230072969 + 3 ^ 40 * 3758520 * 2
def baseEnd_3758520 : Nat := 1929927309536740006914887

theorem tailTrace_3758520 : CollatzResearch.WordTrace tailWord_3758520 prefixEnd_3758520 1929927309536740006914887 := by
  unfold tailWord_3758520
  simp only [CollatzResearch.WordTrace]
  refine ⟨68542243171765709478256507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91389657562354279304342009 68542243171765709478256507)
  ·
    refine ⟨102813364757648564217384761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68542243171765709478256507 102813364757648564217384761)
    ·
      refine ⟨77110023568236423163038571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102813364757648564217384761 77110023568236423163038571)
      ·
        refine ⟨115665035352354634744557857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77110023568236423163038571 115665035352354634744557857)
        ·
          refine ⟨86748776514265976058418393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115665035352354634744557857 86748776514265976058418393)
          ·
            refine ⟨65061582385699482043813795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86748776514265976058418393 65061582385699482043813795)
            ·
              refine ⟨97592373578549223065720693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65061582385699482043813795 97592373578549223065720693)
              ·
                refine ⟨9149285022988989662411315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 97592373578549223065720693 9149285022988989662411315)
                ·
                  refine ⟨13723927534483484493616973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9149285022988989662411315 13723927534483484493616973)
                  ·
                    refine ⟨5146472825431306685106365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13723927534483484493616973 5146472825431306685106365)
                    ·
                      refine ⟨1929927309536740006914887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5146472825431306685106365 1929927309536740006914887)
                      ·
                        rfl

theorem cell23_3758520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 5, 1, 3, 3].length) (baseStart_3758520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3758520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3758520 prefixEnd_3758520 := by exact prefixLift 3758520
  have htrace : WordTrace (prefixWord ++ tailWord_3758520) baseStart_3758520 baseEnd_3758520 := by
    simpa [prefixWord, tailWord_3758520, baseEnd_3758520] using wordTrace_append hprefix tailTrace_3758520
  have hstable : (prefixWord ++ tailWord_3758520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3758520).length < 2 ^ (prefixWord ++ tailWord_3758520).sum := by decide
  have hdescent : baseEnd_3758520 < baseStart_3758520 := by decide
  rcases family_descends (prefixWord ++ tailWord_3758520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3758524 : List Nat := [2, 2, 2, 4, 1, 1, 3, 2, 1, 2, 3]
def baseStart_3758524 : Nat := 118140960795 + 3758524 * 2 ^ 59
def prefixEnd_3758524 : Nat := 4983230072969 + 3 ^ 40 * 3758524 * 2
def baseEnd_3758524 : Nat := 1929929363459357991264869

theorem tailTrace_3758524 : CollatzResearch.WordTrace tailWord_3758524 prefixEnd_3758524 1929929363459357991264869 := by
  unfold tailWord_3758524
  simp only [CollatzResearch.WordTrace]
  refine ⟨68542316117758463819829313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91389754823677951759772417 68542316117758463819829313)
  ·
    refine ⟨51406737088318847864871985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68542316117758463819829313 51406737088318847864871985)
    ·
      refine ⟨38555052816239135898653989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51406737088318847864871985 38555052816239135898653989)
      ·
        refine ⟨7229072403044837980997623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38555052816239135898653989 7229072403044837980997623)
        ·
          refine ⟨10843608604567256971496435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7229072403044837980997623 10843608604567256971496435)
          ·
            refine ⟨16265412906850885457244653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10843608604567256971496435 16265412906850885457244653)
            ·
              refine ⟨6099529840069082046466745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16265412906850885457244653 6099529840069082046466745)
              ·
                refine ⟨4574647380051811534850059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6099529840069082046466745 4574647380051811534850059)
                ·
                  refine ⟨6861971070077717302275089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4574647380051811534850059 6861971070077717302275089)
                  ·
                    refine ⟨5146478302558287976706317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6861971070077717302275089 5146478302558287976706317)
                    ·
                      refine ⟨1929929363459357991264869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5146478302558287976706317 1929929363459357991264869)
                      ·
                        rfl

theorem cell23_3758524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_3758524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3758524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3758524 prefixEnd_3758524 := by exact prefixLift 3758524
  have htrace : WordTrace (prefixWord ++ tailWord_3758524) baseStart_3758524 baseEnd_3758524 := by
    simpa [prefixWord, tailWord_3758524, baseEnd_3758524] using wordTrace_append hprefix tailTrace_3758524
  have hstable : (prefixWord ++ tailWord_3758524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3758524).length < 2 ^ (prefixWord ++ tailWord_3758524).sum := by decide
  have hdescent : baseEnd_3758524 < baseStart_3758524 := by decide
  rcases family_descends (prefixWord ++ tailWord_3758524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3758554 : List Nat := [3, 1, 1, 2, 3, 1, 4, 2, 2, 1, 3]
def baseStart_3758554 : Nat := 118140960795 + 3758554 * 2 ^ 59
def prefixEnd_3758554 : Nat := 4983230072969 + 3 ^ 40 * 3758554 * 2
def baseEnd_3758554 : Nat := 1929944767878992873889731

theorem tailTrace_3758554 : CollatzResearch.WordTrace tailWord_3758554 prefixEnd_3758554 1929944767878992873889731 := by
  unfold tailWord_3758554
  simp only [CollatzResearch.WordTrace]
  refine ⟨34271431606352060690812679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91390484283605495175500477 34271431606352060690812679)
  ·
    refine ⟨51407147409528091036219019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34271431606352060690812679 51407147409528091036219019)
    ·
      refine ⟨77110721114292136554328529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51407147409528091036219019 77110721114292136554328529)
      ·
        refine ⟨57833040835719102415746397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77110721114292136554328529 57833040835719102415746397)
        ·
          refine ⟨21687390313394663405904899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57833040835719102415746397 21687390313394663405904899)
          ·
            refine ⟨32531085470091995108857349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21687390313394663405904899 32531085470091995108857349)
            ·
              refine ⟨6099578525642249082910753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32531085470091995108857349 6099578525642249082910753)
              ·
                refine ⟨4574683894231686812183065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6099578525642249082910753 4574683894231686812183065)
                ·
                  refine ⟨3431012920673765109137299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4574683894231686812183065 3431012920673765109137299)
                  ·
                    refine ⟨5146519381010647663705949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3431012920673765109137299 5146519381010647663705949)
                    ·
                      refine ⟨1929944767878992873889731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5146519381010647663705949 1929944767878992873889731)
                      ·
                        rfl

theorem cell23_3758554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 4, 2, 2, 1, 3].length) (baseStart_3758554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3758554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3758554 prefixEnd_3758554 := by exact prefixLift 3758554
  have htrace : WordTrace (prefixWord ++ tailWord_3758554) baseStart_3758554 baseEnd_3758554 := by
    simpa [prefixWord, tailWord_3758554, baseEnd_3758554] using wordTrace_append hprefix tailTrace_3758554
  have hstable : (prefixWord ++ tailWord_3758554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3758554).length < 2 ^ (prefixWord ++ tailWord_3758554).sum := by decide
  have hdescent : baseEnd_3758554 < baseStart_3758554 := by decide
  rcases family_descends (prefixWord ++ tailWord_3758554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3758570 : List Nat := [3, 1, 3, 1, 3, 1, 1, 1, 1, 8]
def baseStart_3758570 : Nat := 118140960795 + 3758570 * 2 ^ 59
def prefixEnd_3758570 : Nat := 4983230072969 + 3 ^ 40 * 3758570 * 2
def baseEnd_3758570 : Nat := 643317661189821603763219

theorem tailTrace_3758570 : CollatzResearch.WordTrace tailWord_3758570 prefixEnd_3758570 643317661189821603763219 := by
  unfold tailWord_3758570
  simp only [CollatzResearch.WordTrace]
  refine ⟨34271577498337569373958291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91390873328900184997222109 34271577498337569373958291)
  ·
    refine ⟨51407366247506354060937437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34271577498337569373958291 51407366247506354060937437)
    ·
      refine ⟨19277762342814882772851539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51407366247506354060937437 19277762342814882772851539)
      ·
        refine ⟨28916643514222324159277309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19277762342814882772851539 28916643514222324159277309)
        ·
          refine ⟨10843741317833371559728991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28916643514222324159277309 10843741317833371559728991)
          ·
            refine ⟨16265611976750057339593487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10843741317833371559728991 16265611976750057339593487)
            ·
              refine ⟨24398417965125086009390231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16265611976750057339593487 24398417965125086009390231)
              ·
                refine ⟨36597626947687629014085347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24398417965125086009390231 36597626947687629014085347)
                ·
                  refine ⟨54896440421531443521128021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36597626947687629014085347 54896440421531443521128021)
                  ·
                    refine ⟨643317661189821603763219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 54896440421531443521128021 643317661189821603763219)
                    ·
                      rfl

theorem cell23_3758570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 1, 8].length) (baseStart_3758570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3758570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3758570 prefixEnd_3758570 := by exact prefixLift 3758570
  have htrace : WordTrace (prefixWord ++ tailWord_3758570) baseStart_3758570 baseEnd_3758570 := by
    simpa [prefixWord, tailWord_3758570, baseEnd_3758570] using wordTrace_append hprefix tailTrace_3758570
  have hstable : (prefixWord ++ tailWord_3758570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3758570).length < 2 ^ (prefixWord ++ tailWord_3758570).sum := by decide
  have hdescent : baseEnd_3758570 < baseStart_3758570 := by decide
  rcases family_descends (prefixWord ++ tailWord_3758570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3758605 : List Nat := [1, 7, 1, 1, 1, 3, 1, 2, 2, 1, 3]
def baseStart_3758605 : Nat := 118140960795 + 3758605 * 2 ^ 59
def prefixEnd_3758605 : Nat := 4983230072969 + 3 ^ 40 * 3758605 * 2
def baseEnd_3758605 : Nat := 1929970955392372174351997

theorem tailTrace_3758605 : CollatzResearch.WordTrace tailWord_3758605 prefixEnd_3758605 1929970955392372174351997 := by
  unfold tailWord_3758605
  simp only [CollatzResearch.WordTrace]
  refine ⟨137087586548223478473357269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91391724365482318982238179 137087586548223478473357269)
  ·
    refine ⟨3212990309723987776719311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 137087586548223478473357269 3212990309723987776719311)
    ·
      refine ⟨4819485464585981665078967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3212990309723987776719311 4819485464585981665078967)
      ·
        refine ⟨7229228196878972497618451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4819485464585981665078967 7229228196878972497618451)
        ·
          refine ⟨10843842295318458746427677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7229228196878972497618451 10843842295318458746427677)
          ·
            refine ⟨4066440860744422029910379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10843842295318458746427677 4066440860744422029910379)
            ·
              refine ⟨6099661291116633044865569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4066440860744422029910379 6099661291116633044865569)
              ·
                refine ⟨4574745968337474783649177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6099661291116633044865569 4574745968337474783649177)
                ·
                  refine ⟨3431059476253106087736883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4574745968337474783649177 3431059476253106087736883)
                  ·
                    refine ⟨5146589214379659131605325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3431059476253106087736883 5146589214379659131605325)
                    ·
                      refine ⟨1929970955392372174351997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5146589214379659131605325 1929970955392372174351997)
                      ·
                        rfl

theorem cell23_3758605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_3758605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3758605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3758605 prefixEnd_3758605 := by exact prefixLift 3758605
  have htrace : WordTrace (prefixWord ++ tailWord_3758605) baseStart_3758605 baseEnd_3758605 := by
    simpa [prefixWord, tailWord_3758605, baseEnd_3758605] using wordTrace_append hprefix tailTrace_3758605
  have hstable : (prefixWord ++ tailWord_3758605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3758605).length < 2 ^ (prefixWord ++ tailWord_3758605).sum := by decide
  have hdescent : baseEnd_3758605 < baseStart_3758605 := by decide
  rcases family_descends (prefixWord ++ tailWord_3758605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3758627 : List Nat := [1, 1, 1, 4, 4, 1, 2, 1, 2, 3, 3]
def baseStart_3758627 : Nat := 118140960795 + 3758627 * 2 ^ 59
def prefixEnd_3758627 : Nat := 4983230072969 + 3 ^ 40 * 3758627 * 2
def baseEnd_3758627 : Nat := 1929982251966771088276895

theorem tailTrace_3758627 : CollatzResearch.WordTrace tailWord_3758627 prefixEnd_3758627 1929982251966771088276895 := by
  unfold tailWord_3758627
  simp only [CollatzResearch.WordTrace]
  refine ⟨137088388954143776230658135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91392259302762517487105423 137088388954143776230658135)
  ·
    refine ⟨205632583431215664345987203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137088388954143776230658135 205632583431215664345987203)
    ·
      refine ⟨308448875146823496518980805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205632583431215664345987203 308448875146823496518980805)
      ·
        refine ⟨57834164090029405597308901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 308448875146823496518980805 57834164090029405597308901)
        ·
          refine ⟨10843905766880513549495419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57834164090029405597308901 10843905766880513549495419)
          ·
            refine ⟨16265858650320770324243129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10843905766880513549495419 16265858650320770324243129)
            ·
              refine ⟨12199393987740577743182347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16265858650320770324243129 12199393987740577743182347)
              ·
                refine ⟨18299090981610866614773521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12199393987740577743182347 18299090981610866614773521)
                ·
                  refine ⟨13724318236208149961080141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18299090981610866614773521 13724318236208149961080141)
                  ·
                    refine ⟨5146619338578056235405053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13724318236208149961080141 5146619338578056235405053)
                    ·
                      refine ⟨1929982251966771088276895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5146619338578056235405053 1929982251966771088276895)
                      ·
                        rfl

theorem cell23_3758627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 1, 2, 3, 3].length) (baseStart_3758627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3758627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3758627 prefixEnd_3758627 := by exact prefixLift 3758627
  have htrace : WordTrace (prefixWord ++ tailWord_3758627) baseStart_3758627 baseEnd_3758627 := by
    simpa [prefixWord, tailWord_3758627, baseEnd_3758627] using wordTrace_append hprefix tailTrace_3758627
  have hstable : (prefixWord ++ tailWord_3758627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3758627).length < 2 ^ (prefixWord ++ tailWord_3758627).sum := by decide
  have hdescent : baseEnd_3758627 < baseStart_3758627 := by decide
  rcases family_descends (prefixWord ++ tailWord_3758627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3758628 : List Nat := [2, 3, 1, 5, 1, 2, 1, 1, 1, 4, 2]
def baseStart_3758628 : Nat := 118140960795 + 3758628 * 2 ^ 59
def prefixEnd_3758628 : Nat := 4983230072969 + 3 ^ 40 * 3758628 * 2
def baseEnd_3758628 : Nat := 1929982765447425584364391

theorem tailTrace_3758628 : CollatzResearch.WordTrace tailWord_3758628 prefixEnd_3758628 1929982765447425584364391 := by
  unfold tailWord_3758628
  simp only [CollatzResearch.WordTrace]
  refine ⟨68544212713570076700722269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91392283618093435600963025 68544212713570076700722269)
  ·
    refine ⟨25704079767588778762770851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68544212713570076700722269 25704079767588778762770851)
    ·
      refine ⟨38556119651383168144156277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25704079767588778762770851 38556119651383168144156277)
      ·
        refine ⟨3614636217317172013514651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38556119651383168144156277 3614636217317172013514651)
        ·
          refine ⟨5421954325975758020271977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3614636217317172013514651 5421954325975758020271977)
          ·
            refine ⟨4066465744481818515203983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5421954325975758020271977 4066465744481818515203983)
            ·
              refine ⟨6099698616722727772805975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4066465744481818515203983 6099698616722727772805975)
              ·
                refine ⟨9149547925084091659208963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6099698616722727772805975 9149547925084091659208963)
                ·
                  refine ⟨13724321887626137488813445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9149547925084091659208963 13724321887626137488813445)
                  ·
                    refine ⟨2573310353929900779152521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13724321887626137488813445 2573310353929900779152521)
                    ·
                      refine ⟨1929982765447425584364391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2573310353929900779152521 1929982765447425584364391)
                      ·
                        rfl

theorem cell23_3758628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_3758628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3758628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3758628 prefixEnd_3758628 := by exact prefixLift 3758628
  have htrace : WordTrace (prefixWord ++ tailWord_3758628) baseStart_3758628 baseEnd_3758628 := by
    simpa [prefixWord, tailWord_3758628, baseEnd_3758628] using wordTrace_append hprefix tailTrace_3758628
  have hstable : (prefixWord ++ tailWord_3758628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3758628).length < 2 ^ (prefixWord ++ tailWord_3758628).sum := by decide
  have hdescent : baseEnd_3758628 < baseStart_3758628 := by decide
  rcases family_descends (prefixWord ++ tailWord_3758628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3758667 : List Nat := [1, 1, 1, 1, 3, 1, 4, 1, 4, 4, 2]
def baseStart_3758667 : Nat := 118140960795 + 3758667 * 2 ^ 59
def prefixEnd_3758667 : Nat := 4983230072969 + 3 ^ 40 * 3758667 * 2
def baseEnd_3758667 : Nat := 1930002791192950931776711

theorem tailTrace_3758667 : CollatzResearch.WordTrace tailWord_3758667 prefixEnd_3758667 1930002791192950931776711 := by
  unfold tailWord_3758667
  simp only [CollatzResearch.WordTrace]
  refine ⟨137089847873998863062114255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91393231915999242041409503 137089847873998863062114255)
  ·
    refine ⟨205634771810998294593171383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137089847873998863062114255 205634771810998294593171383)
    ·
      refine ⟨308452157716497441889757075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205634771810998294593171383 308452157716497441889757075)
      ·
        refine ⟨462678236574746162834635613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308452157716497441889757075 462678236574746162834635613)
        ·
          refine ⟨173504338715529811062988355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 462678236574746162834635613 173504338715529811062988355)
          ·
            refine ⟨260256508073294716594482533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173504338715529811062988355 260256508073294716594482533)
            ·
              refine ⟨48798095263742759361465475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 260256508073294716594482533 48798095263742759361465475)
              ·
                refine ⟨73197142895614139042198213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48798095263742759361465475 73197142895614139042198213)
                ·
                  refine ⟨13724464292927651070412165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73197142895614139042198213 13724464292927651070412165)
                  ·
                    refine ⟨2573337054923934575702281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13724464292927651070412165 2573337054923934575702281)
                    ·
                      refine ⟨1930002791192950931776711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2573337054923934575702281 1930002791192950931776711)
                      ·
                        rfl

theorem cell23_3758667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 4, 4, 2].length) (baseStart_3758667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3758667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3758667 prefixEnd_3758667 := by exact prefixLift 3758667
  have htrace : WordTrace (prefixWord ++ tailWord_3758667) baseStart_3758667 baseEnd_3758667 := by
    simpa [prefixWord, tailWord_3758667, baseEnd_3758667] using wordTrace_append hprefix tailTrace_3758667
  have hstable : (prefixWord ++ tailWord_3758667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3758667).length < 2 ^ (prefixWord ++ tailWord_3758667).sum := by decide
  have hdescent : baseEnd_3758667 < baseStart_3758667 := by decide
  rcases family_descends (prefixWord ++ tailWord_3758667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3758680 : List Nat := [2, 1, 2, 2, 1, 2, 2, 2, 2, 1, 6]
def baseStart_3758680 : Nat := 118140960795 + 3758680 * 2 ^ 59
def prefixEnd_3758680 : Nat := 4983230072969 + 3 ^ 40 * 3758680 * 2
def baseEnd_3758680 : Nat := 1930009466441459380914151

theorem tailTrace_3758680 : CollatzResearch.WordTrace tailWord_3758680 prefixEnd_3758680 1930009466441459380914151 := by
  unfold tailWord_3758680
  simp only [CollatzResearch.WordTrace]
  refine ⟨68545161011475883141168747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91393548015301177521558329 68545161011475883141168747)
  ·
    refine ⟨102817741517213824711753121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68545161011475883141168747 102817741517213824711753121)
    ·
      refine ⟨77113306137910368533814841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102817741517213824711753121 77113306137910368533814841)
      ·
        refine ⟨57834979603432776400361131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77113306137910368533814841 57834979603432776400361131)
        ·
          refine ⟨86752469405149164600541697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57834979603432776400361131 86752469405149164600541697)
          ·
            refine ⟨65064352053861873450406273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86752469405149164600541697 65064352053861873450406273)
            ·
              refine ⟨48798264040396405087804705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65064352053861873450406273 48798264040396405087804705)
              ·
                refine ⟨36598698030297303815853529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48798264040396405087804705 36598698030297303815853529)
                ·
                  refine ⟨27449023522722977861890147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36598698030297303815853529 27449023522722977861890147)
                  ·
                    refine ⟨41173535284084466792835221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27449023522722977861890147 41173535284084466792835221)
                    ·
                      refine ⟨1930009466441459380914151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41173535284084466792835221 1930009466441459380914151)
                      ·
                        rfl

theorem cell23_3758680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 2, 2, 1, 6].length) (baseStart_3758680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3758680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3758680 prefixEnd_3758680 := by exact prefixLift 3758680
  have htrace : WordTrace (prefixWord ++ tailWord_3758680) baseStart_3758680 baseEnd_3758680 := by
    simpa [prefixWord, tailWord_3758680, baseEnd_3758680] using wordTrace_append hprefix tailTrace_3758680
  have hstable : (prefixWord ++ tailWord_3758680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3758680).length < 2 ^ (prefixWord ++ tailWord_3758680).sum := by decide
  have hdescent : baseEnd_3758680 < baseStart_3758680 := by decide
  rcases family_descends (prefixWord ++ tailWord_3758680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3758724 : List Nat := [2, 3, 2, 1, 3, 2, 2, 2, 6]
def baseStart_3758724 : Nat := 118140960795 + 3758724 * 2 ^ 59
def prefixEnd_3758724 : Nat := 4983230072969 + 3 ^ 40 * 3758724 * 2
def baseEnd_3758724 : Nat := 214448006621139689862661

theorem tailTrace_3758724 : CollatzResearch.WordTrace tailWord_3758724 prefixEnd_3758724 214448006621139689862661 := by
  unfold tailWord_3758724
  simp only [CollatzResearch.WordTrace]
  refine ⟨68545963417396180898469613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91394617889861574531292817 68545963417396180898469613)
  ·
    refine ⟨25704736281523567836926105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68545963417396180898469613 25704736281523567836926105)
    ·
      refine ⟨19278552211142675877694579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25704736281523567836926105 19278552211142675877694579)
      ·
        refine ⟨28917828316714013816541869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19278552211142675877694579 28917828316714013816541869)
        ·
          refine ⟨10844185618767755181203201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28917828316714013816541869 10844185618767755181203201)
          ·
            refine ⟨8133139214075816385902401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10844185618767755181203201 8133139214075816385902401)
            ·
              refine ⟨6099854410556862289426801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8133139214075816385902401 6099854410556862289426801)
              ·
                refine ⟨4574890807917646717070101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6099854410556862289426801 4574890807917646717070101)
                ·
                  refine ⟨214448006621139689862661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4574890807917646717070101 214448006621139689862661)
                  ·
                    rfl

theorem cell23_3758724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 2, 2, 6].length) (baseStart_3758724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3758724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3758724 prefixEnd_3758724 := by exact prefixLift 3758724
  have htrace : WordTrace (prefixWord ++ tailWord_3758724) baseStart_3758724 baseEnd_3758724 := by
    simpa [prefixWord, tailWord_3758724, baseEnd_3758724] using wordTrace_append hprefix tailTrace_3758724
  have hstable : (prefixWord ++ tailWord_3758724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3758724).length < 2 ^ (prefixWord ++ tailWord_3758724).sum := by decide
  have hdescent : baseEnd_3758724 < baseStart_3758724 := by decide
  rcases family_descends (prefixWord ++ tailWord_3758724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3758744 : List Nat := [2, 1, 2, 4, 1, 1, 2, 2, 1, 5, 2]
def baseStart_3758744 : Nat := 118140960795 + 3758744 * 2 ^ 59
def prefixEnd_3758744 : Nat := 4983230072969 + 3 ^ 40 * 3758744 * 2
def baseEnd_3758744 : Nat := 1930042329203347130513857

theorem tailTrace_3758744 : CollatzResearch.WordTrace tailWord_3758744 prefixEnd_3758744 1930042329203347130513857 := by
  unfold tailWord_3758744
  simp only [CollatzResearch.WordTrace]
  refine ⟨68546328147359952606333643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91395104196479936808444857 68546328147359952606333643)
  ·
    refine ⟨102819492221039928909500465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68546328147359952606333643 102819492221039928909500465)
    ·
      refine ⟨77114619165779946682125349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102819492221039928909500465 77114619165779946682125349)
      ·
        refine ⟨14458991093583740002898503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77114619165779946682125349 14458991093583740002898503)
        ·
          refine ⟨21688486640375610004347755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14458991093583740002898503 21688486640375610004347755)
          ·
            refine ⟨32532729960563415006521633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21688486640375610004347755 32532729960563415006521633)
            ·
              refine ⟨24399547470422561254891225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32532729960563415006521633 24399547470422561254891225)
              ·
                refine ⟨18299660602816920941168419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24399547470422561254891225 18299660602816920941168419)
                ·
                  refine ⟨27449490904225381411752629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18299660602816920941168419 27449490904225381411752629)
                  ·
                    refine ⟨2573389772271129507351809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27449490904225381411752629 2573389772271129507351809)
                    ·
                      refine ⟨1930042329203347130513857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2573389772271129507351809 1930042329203347130513857)
                      ·
                        rfl

theorem cell23_3758744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 2, 1, 5, 2].length) (baseStart_3758744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3758744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3758744 prefixEnd_3758744 := by exact prefixLift 3758744
  have htrace : WordTrace (prefixWord ++ tailWord_3758744) baseStart_3758744 baseEnd_3758744 := by
    simpa [prefixWord, tailWord_3758744, baseEnd_3758744] using wordTrace_append hprefix tailTrace_3758744
  have hstable : (prefixWord ++ tailWord_3758744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3758744).length < 2 ^ (prefixWord ++ tailWord_3758744).sum := by decide
  have hdescent : baseEnd_3758744 < baseStart_3758744 := by decide
  rcases family_descends (prefixWord ++ tailWord_3758744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3758767 : List Nat := [1, 1, 2, 1, 2, 5, 2, 2, 1, 6]
def baseStart_3758767 : Nat := 118140960795 + 3758767 * 2 ^ 59
def prefixEnd_3758767 : Nat := 4983230072969 + 3 ^ 40 * 3758767 * 2
def baseEnd_3758767 : Nat := 643351379752800180175417

theorem tailTrace_3758767 : CollatzResearch.WordTrace tailWord_3758767 prefixEnd_3758767 643351379752800180175417 := by
  unfold tailWord_3758767
  simp only [CollatzResearch.WordTrace]
  refine ⟨137093495173636580140754555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91395663449091053427169703 137093495173636580140754555)
  ·
    refine ⟨205640242760454870211131833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137093495173636580140754555 205640242760454870211131833)
    ·
      refine ⟨154230182070341152658348875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205640242760454870211131833 154230182070341152658348875)
      ·
        refine ⟨231345273105511728987523313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154230182070341152658348875 231345273105511728987523313)
        ·
          refine ⟨173508954829133796740642485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231345273105511728987523313 173508954829133796740642485)
          ·
            refine ⟨16266464515231293444435233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 173508954829133796740642485 16266464515231293444435233)
            ·
              refine ⟨12199848386423470083326425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16266464515231293444435233 12199848386423470083326425)
              ·
                refine ⟨9149886289817602562494819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12199848386423470083326425 9149886289817602562494819)
                ·
                  refine ⟨13724829434726403843742229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9149886289817602562494819 13724829434726403843742229)
                  ·
                    refine ⟨643351379752800180175417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13724829434726403843742229 643351379752800180175417)
                    ·
                      rfl

theorem cell23_3758767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 2, 1, 6].length) (baseStart_3758767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3758767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3758767 prefixEnd_3758767 := by exact prefixLift 3758767
  have htrace : WordTrace (prefixWord ++ tailWord_3758767) baseStart_3758767 baseEnd_3758767 := by
    simpa [prefixWord, tailWord_3758767, baseEnd_3758767] using wordTrace_append hprefix tailTrace_3758767
  have hstable : (prefixWord ++ tailWord_3758767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3758767).length < 2 ^ (prefixWord ++ tailWord_3758767).sum := by decide
  have hdescent : baseEnd_3758767 < baseStart_3758767 := by decide
  rcases family_descends (prefixWord ++ tailWord_3758767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3758771 : List Nat := [1, 1, 1, 2, 3, 6, 2, 1, 1, 5]
def baseStart_3758771 : Nat := 118140960795 + 3758771 * 2 ^ 59
def prefixEnd_3758771 : Nat := 4983230072969 + 3 ^ 40 * 3758771 * 2
def baseEnd_3758771 : Nat := 643352064393672841625411

theorem tailTrace_3758771 : CollatzResearch.WordTrace tailWord_3758771 prefixEnd_3758771 643352064393672841625411 := by
  unfold tailWord_3758771
  simp only [CollatzResearch.WordTrace]
  refine ⟨137093641065622088823900167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91395760710414725882600111 137093641065622088823900167)
  ·
    refine ⟨205640461598433133235850251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137093641065622088823900167 205640461598433133235850251)
    ·
      refine ⟨308460692397649699853775377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205640461598433133235850251 308460692397649699853775377)
      ·
        refine ⟨231345519298237274890331533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 308460692397649699853775377 231345519298237274890331533)
        ·
          refine ⟨86754569736838978083874325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 231345519298237274890331533 86754569736838978083874325)
          ·
            refine ⟨4066620456414327097681609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 86754569736838978083874325 4066620456414327097681609)
            ·
              refine ⟨3049965342310745323261207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4066620456414327097681609 3049965342310745323261207)
              ·
                refine ⟨4574948013466117984891811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3049965342310745323261207 4574948013466117984891811)
                ·
                  refine ⟨6862422020199176977337717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4574948013466117984891811 6862422020199176977337717)
                  ·
                    refine ⟨643352064393672841625411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6862422020199176977337717 643352064393672841625411)
                    ·
                      rfl

theorem cell23_3758771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 2, 1, 1, 5].length) (baseStart_3758771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3758771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3758771 prefixEnd_3758771 := by exact prefixLift 3758771
  have htrace : WordTrace (prefixWord ++ tailWord_3758771) baseStart_3758771 baseEnd_3758771 := by
    simpa [prefixWord, tailWord_3758771, baseEnd_3758771] using wordTrace_append hprefix tailTrace_3758771
  have hstable : (prefixWord ++ tailWord_3758771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3758771).length < 2 ^ (prefixWord ++ tailWord_3758771).sum := by decide
  have hdescent : baseEnd_3758771 < baseStart_3758771 := by decide
  rcases family_descends (prefixWord ++ tailWord_3758771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3758777 : List Nat := [1, 2, 1, 4, 1, 1, 1, 5, 1, 1, 5]
def baseStart_3758777 : Nat := 118140960795 + 3758777 * 2 ^ 59
def prefixEnd_3758777 : Nat := 4983230072969 + 3 ^ 40 * 3758777 * 2
def baseEnd_3758777 : Nat := 1930059274064945501401205

theorem tailTrace_3758777 : CollatzResearch.WordTrace tailWord_3758777 prefixEnd_3758777 1930059274064945501401205 := by
  unfold tailWord_3758777
  simp only [CollatzResearch.WordTrace]
  refine ⟨137093859903600351848618585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91395906602400234565745723 137093859903600351848618585)
  ·
    refine ⟨102820394927700263886463939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137093859903600351848618585 102820394927700263886463939)
    ·
      refine ⟨154230592391550395829695909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102820394927700263886463939 154230592391550395829695909)
      ·
        refine ⟨28918236073415699218067983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 154230592391550395829695909 28918236073415699218067983)
        ·
          refine ⟨43377354110123548827101975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28918236073415699218067983 43377354110123548827101975)
          ·
            refine ⟨65066031165185323240652963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43377354110123548827101975 65066031165185323240652963)
            ·
              refine ⟨97599046747777984860979445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65066031165185323240652963 97599046747777984860979445)
              ·
                refine ⟨9149910632604186080716823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 97599046747777984860979445 9149910632604186080716823)
                ·
                  refine ⟨13724865948906279121075235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9149910632604186080716823 13724865948906279121075235)
                  ·
                    refine ⟨20587298923359418681612853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13724865948906279121075235 20587298923359418681612853)
                    ·
                      refine ⟨1930059274064945501401205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20587298923359418681612853 1930059274064945501401205)
                      ·
                        rfl

theorem cell23_3758777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 5, 1, 1, 5].length) (baseStart_3758777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3758777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3758777 prefixEnd_3758777 := by exact prefixLift 3758777
  have htrace : WordTrace (prefixWord ++ tailWord_3758777) baseStart_3758777 baseEnd_3758777 := by
    simpa [prefixWord, tailWord_3758777, baseEnd_3758777] using wordTrace_append hprefix tailTrace_3758777
  have hstable : (prefixWord ++ tailWord_3758777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3758777).length < 2 ^ (prefixWord ++ tailWord_3758777).sum := by decide
  have hdescent : baseEnd_3758777 < baseStart_3758777 := by decide
  rcases family_descends (prefixWord ++ tailWord_3758777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3758784 : List Nat := [2, 1, 1, 2, 4, 3, 1, 1, 4, 4]
def baseStart_3758784 : Nat := 118140960795 + 3758784 * 2 ^ 59
def prefixEnd_3758784 : Nat := 4983230072969 + 3 ^ 40 * 3758784 * 2
def baseEnd_3758784 : Nat := 643354289476508991337891

theorem tailTrace_3758784 : CollatzResearch.WordTrace tailWord_3758784 prefixEnd_3758784 643354289476508991337891 := by
  unfold tailWord_3758784
  simp only [CollatzResearch.WordTrace]
  refine ⟨68547057607287496022061703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91396076809716661362748937 68547057607287496022061703)
  ·
    refine ⟨102820586410931244033092555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68547057607287496022061703 102820586410931244033092555)
    ·
      refine ⟨154230879616396866049638833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102820586410931244033092555 154230879616396866049638833)
      ·
        refine ⟨115673159712297649537229125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154230879616396866049638833 115673159712297649537229125)
        ·
          refine ⟨21688717446055809288230461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115673159712297649537229125 21688717446055809288230461)
          ·
            refine ⟨8133269042270928483086423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21688717446055809288230461 8133269042270928483086423)
            ·
              refine ⟨12199903563406392724629635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8133269042270928483086423 12199903563406392724629635)
              ·
                refine ⟨18299855345109589086944453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12199903563406392724629635 18299855345109589086944453)
                ·
                  refine ⟨3431222877208047953802085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18299855345109589086944453 3431222877208047953802085)
                  ·
                    refine ⟨643354289476508991337891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3431222877208047953802085 643354289476508991337891)
                    ·
                      rfl

theorem cell23_3758784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 1, 4, 4].length) (baseStart_3758784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3758784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3758784 prefixEnd_3758784 := by exact prefixLift 3758784
  have htrace : WordTrace (prefixWord ++ tailWord_3758784) baseStart_3758784 baseEnd_3758784 := by
    simpa [prefixWord, tailWord_3758784, baseEnd_3758784] using wordTrace_append hprefix tailTrace_3758784
  have hstable : (prefixWord ++ tailWord_3758784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3758784).length < 2 ^ (prefixWord ++ tailWord_3758784).sum := by decide
  have hdescent : baseEnd_3758784 < baseStart_3758784 := by decide
  rcases family_descends (prefixWord ++ tailWord_3758784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3758785 : List Nat := [1, 2, 6, 2, 1, 1, 2, 1, 3, 1, 3]
def baseStart_3758785 : Nat := 118140960795 + 3758785 * 2 ^ 59
def prefixEnd_3758785 : Nat := 4983230072969 + 3 ^ 40 * 3758785 * 2
def baseEnd_3758785 : Nat := 1930063381910181470101169

theorem tailTrace_3758785 : CollatzResearch.WordTrace tailWord_3758785 prefixEnd_3758785 1930063381910181470101169 := by
  unfold tailWord_3758785
  simp only [CollatzResearch.WordTrace]
  refine ⟨137094151687571369214909809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91396101125047579476606539 137094151687571369214909809)
  ·
    refine ⟨102820613765678526911182357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137094151687571369214909809 102820613765678526911182357)
    ·
      refine ⟨4819716270266180948961673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 102820613765678526911182357 4819716270266180948961673)
      ·
        refine ⟨3614787202699635711721255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4819716270266180948961673 3614787202699635711721255)
        ·
          refine ⟨5422180804049453567581883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3614787202699635711721255 5422180804049453567581883)
          ·
            refine ⟨8133271206074180351372825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5422180804049453567581883 8133271206074180351372825)
            ·
              refine ⟨6099953404555635263529619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8133271206074180351372825 6099953404555635263529619)
              ·
                refine ⟨9149930106833452895294429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6099953404555635263529619 9149930106833452895294429)
                ·
                  refine ⟨3431223790062544835735411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9149930106833452895294429 3431223790062544835735411)
                  ·
                    refine ⟨5146835685093817253603117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3431223790062544835735411 5146835685093817253603117)
                    ·
                      refine ⟨1930063381910181470101169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5146835685093817253603117 1930063381910181470101169)
                      ·
                        rfl

theorem cell23_3758785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_3758785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3758785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3758785 prefixEnd_3758785 := by exact prefixLift 3758785
  have htrace : WordTrace (prefixWord ++ tailWord_3758785) baseStart_3758785 baseEnd_3758785 := by
    simpa [prefixWord, tailWord_3758785, baseEnd_3758785] using wordTrace_append hprefix tailTrace_3758785
  have hstable : (prefixWord ++ tailWord_3758785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3758785).length < 2 ^ (prefixWord ++ tailWord_3758785).sum := by decide
  have hdescent : baseEnd_3758785 < baseStart_3758785 := by decide
  rcases family_descends (prefixWord ++ tailWord_3758785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3758794 : List Nat := [3, 1, 2, 1, 4, 2, 1, 2, 1, 1, 5]
def baseStart_3758794 : Nat := 118140960795 + 3758794 * 2 ^ 59
def prefixEnd_3758794 : Nat := 4983230072969 + 3 ^ 40 * 3758794 * 2
def baseEnd_3758794 : Nat := 1930068003236071934888627

theorem tailTrace_3758794 : CollatzResearch.WordTrace tailWord_3758794 prefixEnd_3758794 1930068003236071934888627 := by
  unfold tailWord_3758794
  simp only [CollatzResearch.WordTrace]
  refine ⟨34273619986134690937996859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91396319963025842501324957 34273619986134690937996859)
  ·
    refine ⟨51410429979202036406995289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34273619986134690937996859 51410429979202036406995289)
    ·
      refine ⟨38557822484401527305246467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51410429979202036406995289 38557822484401527305246467)
      ·
        refine ⟨57836733726602290957869701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38557822484401527305246467 57836733726602290957869701)
        ·
          refine ⟨10844387573737929554600569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57836733726602290957869701 10844387573737929554600569)
          ·
            refine ⟨8133290680303447165950427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10844387573737929554600569 8133290680303447165950427)
            ·
              refine ⟨12199936020455170748925641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8133290680303447165950427 12199936020455170748925641)
              ·
                refine ⟨9149952015341378061694231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12199936020455170748925641 9149952015341378061694231)
                ·
                  refine ⟨13724928023012067092541347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9149952015341378061694231 13724928023012067092541347)
                  ·
                    refine ⟨20587392034518100638812021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13724928023012067092541347 20587392034518100638812021)
                    ·
                      refine ⟨1930068003236071934888627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20587392034518100638812021 1930068003236071934888627)
                      ·
                        rfl

theorem cell23_3758794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 2, 1, 1, 5].length) (baseStart_3758794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3758794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3758794 prefixEnd_3758794 := by exact prefixLift 3758794
  have htrace : WordTrace (prefixWord ++ tailWord_3758794) baseStart_3758794 baseEnd_3758794 := by
    simpa [prefixWord, tailWord_3758794, baseEnd_3758794] using wordTrace_append hprefix tailTrace_3758794
  have hstable : (prefixWord ++ tailWord_3758794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3758794).length < 2 ^ (prefixWord ++ tailWord_3758794).sum := by decide
  have hdescent : baseEnd_3758794 < baseStart_3758794 := by decide
  rcases family_descends (prefixWord ++ tailWord_3758794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3758801 : List Nat := [1, 2, 2, 1, 2, 3, 5, 1, 2, 4]
def baseStart_3758801 : Nat := 118140960795 + 3758801 * 2 ^ 59
def prefixEnd_3758801 : Nat := 4983230072969 + 3 ^ 40 * 3758801 * 2
def baseEnd_3758801 : Nat := 643357199200217802500365

theorem tailTrace_3758801 : CollatzResearch.WordTrace tailWord_3758801 prefixEnd_3758801 643357199200217802500365 := by
  unfold tailWord_3758801
  simp only [CollatzResearch.WordTrace]
  refine ⟨137094735255513403947492257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91396490170342269298328171 137094735255513403947492257)
  ·
    refine ⟨102821051441635052960619193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137094735255513403947492257 102821051441635052960619193)
    ·
      refine ⟨77115788581226289720464395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102821051441635052960619193 77115788581226289720464395)
      ·
        refine ⟨115673682871839434580696593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77115788581226289720464395 115673682871839434580696593)
        ·
          refine ⟨86755262153879575935522445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115673682871839434580696593 86755262153879575935522445)
          ·
            refine ⟨32533223307704840975820917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86755262153879575935522445 32533223307704840975820917)
            ·
              refine ⟨3049989685097328841483211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32533223307704840975820917 3049989685097328841483211)
              ·
                refine ⟨4574984527645993262224817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3049989685097328841483211 4574984527645993262224817)
                ·
                  refine ⟨3431238395734494946668613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4574984527645993262224817 3431238395734494946668613)
                  ·
                    refine ⟨643357199200217802500365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3431238395734494946668613 643357199200217802500365)
                    ·
                      rfl

theorem cell23_3758801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 5, 1, 2, 4].length) (baseStart_3758801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3758801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3758801 prefixEnd_3758801 := by exact prefixLift 3758801
  have htrace : WordTrace (prefixWord ++ tailWord_3758801) baseStart_3758801 baseEnd_3758801 := by
    simpa [prefixWord, tailWord_3758801, baseEnd_3758801] using wordTrace_append hprefix tailTrace_3758801
  have hstable : (prefixWord ++ tailWord_3758801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3758801).length < 2 ^ (prefixWord ++ tailWord_3758801).sum := by decide
  have hdescent : baseEnd_3758801 < baseStart_3758801 := by decide
  rcases family_descends (prefixWord ++ tailWord_3758801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3758847 : List Nat := [1, 1, 2, 2, 1, 3, 1, 3, 2, 3, 4]
def baseStart_3758847 : Nat := 118140960795 + 3758847 * 2 ^ 59
def prefixEnd_3758847 : Nat := 4983230072969 + 3 ^ 40 * 3758847 * 2
def baseEnd_3758847 : Nat := 1930095217710760227525883

theorem tailTrace_3758847 : CollatzResearch.WordTrace tailWord_3758847 prefixEnd_3758847 1930095217710760227525883 := by
  unfold tailWord_3758847
  simp only [CollatzResearch.WordTrace]
  refine ⟨137096413013346753803666795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91397608675564502535777863 137096413013346753803666795)
  ·
    refine ⟨205644619520020130705500193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137096413013346753803666795 205644619520020130705500193)
    ·
      refine ⟨154233464640015098029125145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205644619520020130705500193 154233464640015098029125145)
      ·
        refine ⟨115675098480011323521843859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154233464640015098029125145 115675098480011323521843859)
        ·
          refine ⟨173512647720016985282765789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115675098480011323521843859 173512647720016985282765789)
          ·
            refine ⟨65067242895006369481037171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 173512647720016985282765789 65067242895006369481037171)
            ·
              refine ⟨97600864342509554221555757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65067242895006369481037171 97600864342509554221555757)
              ·
                refine ⟨36600324128441082833083409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97600864342509554221555757 36600324128441082833083409)
                ·
                  refine ⟨27450243096330812124812557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36600324128441082833083409 27450243096330812124812557)
                  ·
                    refine ⟨10293841161124054546804709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27450243096330812124812557 10293841161124054546804709)
                    ·
                      refine ⟨1930095217710760227525883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10293841161124054546804709 1930095217710760227525883)
                      ·
                        rfl

theorem cell23_3758847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 3, 2, 3, 4].length) (baseStart_3758847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3758847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3758847 prefixEnd_3758847 := by exact prefixLift 3758847
  have htrace : WordTrace (prefixWord ++ tailWord_3758847) baseStart_3758847 baseEnd_3758847 := by
    simpa [prefixWord, tailWord_3758847, baseEnd_3758847] using wordTrace_append hprefix tailTrace_3758847
  have hstable : (prefixWord ++ tailWord_3758847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3758847).length < 2 ^ (prefixWord ++ tailWord_3758847).sum := by decide
  have hdescent : baseEnd_3758847 < baseStart_3758847 := by decide
  rcases family_descends (prefixWord ++ tailWord_3758847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3758857 : List Nat := [1, 2, 1, 1, 3, 2, 2, 3, 2, 6]
def baseStart_3758857 : Nat := 118140960795 + 3758857 * 2 ^ 59
def prefixEnd_3758857 : Nat := 4983230072969 + 3 ^ 40 * 3758857 * 2
def baseEnd_3758857 : Nat := 643366784172435062800279

theorem tailTrace_3758857 : CollatzResearch.WordTrace tailWord_3758857 prefixEnd_3758857 643366784172435062800279 := by
  unfold tailWord_3758857
  simp only [CollatzResearch.WordTrace]
  refine ⟨137096777743310525511530825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91397851828873683674353883 137096777743310525511530825)
  ·
    refine ⟨102822583307482894133648119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137096777743310525511530825 102822583307482894133648119)
    ·
      refine ⟨154233874961224341200472179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102822583307482894133648119 154233874961224341200472179)
      ·
        refine ⟨231350812441836511800708269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154233874961224341200472179 231350812441836511800708269)
        ·
          refine ⟨86756554665688691925265601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 231350812441836511800708269 86756554665688691925265601)
          ·
            refine ⟨65067415999266518943949201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86756554665688691925265601 65067415999266518943949201)
            ·
              refine ⟨48800561999449889207961901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65067415999266518943949201 48800561999449889207961901)
              ·
                refine ⟨18300210749793708452985713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48800561999449889207961901 18300210749793708452985713)
                ·
                  refine ⟨13725158062345281339739285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18300210749793708452985713 13725158062345281339739285)
                  ·
                    refine ⟨643366784172435062800279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13725158062345281339739285 643366784172435062800279)
                    ·
                      rfl

theorem cell23_3758857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 3, 2, 6].length) (baseStart_3758857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3758857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3758857 prefixEnd_3758857 := by exact prefixLift 3758857
  have htrace : WordTrace (prefixWord ++ tailWord_3758857) baseStart_3758857 baseEnd_3758857 := by
    simpa [prefixWord, tailWord_3758857, baseEnd_3758857] using wordTrace_append hprefix tailTrace_3758857
  have hstable : (prefixWord ++ tailWord_3758857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3758857).length < 2 ^ (prefixWord ++ tailWord_3758857).sum := by decide
  have hdescent : baseEnd_3758857 < baseStart_3758857 := by decide
  rcases family_descends (prefixWord ++ tailWord_3758857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3758867 : List Nat := [1, 1, 1, 2, 1, 3, 3, 1, 4, 1, 5]
def baseStart_3758867 : Nat := 118140960795 + 3758867 * 2 ^ 59
def prefixEnd_3758867 : Nat := 4983230072969 + 3 ^ 40 * 3758867 * 2
def baseEnd_3758867 : Nat := 1930105487323850149275791

theorem tailTrace_3758867 : CollatzResearch.WordTrace tailWord_3758867 prefixEnd_3758867 1930105487323850149275791 := by
  unfold tailWord_3758867
  simp only [CollatzResearch.WordTrace]
  refine ⟨137097142473274297219394855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91398094982182864812929903 137097142473274297219394855)
  ·
    refine ⟨205645713709911445829092283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137097142473274297219394855 205645713709911445829092283)
    ·
      refine ⟨308468570564867168743638425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205645713709911445829092283 308468570564867168743638425)
      ·
        refine ⟨231351427923650376557728819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 308468570564867168743638425 231351427923650376557728819)
        ·
          refine ⟨347027141885475564836593229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231351427923650376557728819 347027141885475564836593229)
          ·
            refine ⟨130135178207053336813722461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 347027141885475564836593229 130135178207053336813722461)
            ·
              refine ⟨48800691827645001305145923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 130135178207053336813722461 48800691827645001305145923)
              ·
                refine ⟨73201037741467501957718885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48800691827645001305145923 73201037741467501957718885)
                ·
                  refine ⟨13725194576525156617072291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73201037741467501957718885 13725194576525156617072291)
                  ·
                    refine ⟨20587791864787734925608437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13725194576525156617072291 20587791864787734925608437)
                    ·
                      refine ⟨1930105487323850149275791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20587791864787734925608437 1930105487323850149275791)
                      ·
                        rfl

theorem cell23_3758867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 4, 1, 5].length) (baseStart_3758867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3758867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3758867 prefixEnd_3758867 := by exact prefixLift 3758867
  have htrace : WordTrace (prefixWord ++ tailWord_3758867) baseStart_3758867 baseEnd_3758867 := by
    simpa [prefixWord, tailWord_3758867, baseEnd_3758867] using wordTrace_append hprefix tailTrace_3758867
  have hstable : (prefixWord ++ tailWord_3758867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3758867).length < 2 ^ (prefixWord ++ tailWord_3758867).sum := by decide
  have hdescent : baseEnd_3758867 < baseStart_3758867 := by decide
  rcases family_descends (prefixWord ++ tailWord_3758867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3758881 : List Nat := [1, 2, 3, 2, 1, 2, 3, 2, 1, 4, 2]
def baseStart_3758881 : Nat := 118140960795 + 3758881 * 2 ^ 59
def prefixEnd_3758881 : Nat := 4983230072969 + 3 ^ 40 * 3758881 * 2
def baseEnd_3758881 : Nat := 1930112676053013094500727

theorem tailTrace_3758881 : CollatzResearch.WordTrace tailWord_3758881 prefixEnd_3758881 1930112676053013094500727 := by
  unfold tailWord_3758881
  simp only [CollatzResearch.WordTrace]
  refine ⟨137097653095223577610404497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91398435396815718406936331 137097653095223577610404497)
  ·
    refine ⟨102823239821417683207803373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137097653095223577610404497 102823239821417683207803373)
    ·
      refine ⟨38558714933031631202926265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102823239821417683207803373 38558714933031631202926265)
      ·
        refine ⟨28919036199773723402194699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38558714933031631202926265 28919036199773723402194699)
        ·
          refine ⟨43378554299660585103292049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28919036199773723402194699 43378554299660585103292049)
          ·
            refine ⟨32533915724745438827469037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43378554299660585103292049 32533915724745438827469037)
            ·
              refine ⟨12200218396779539560300889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32533915724745438827469037 12200218396779539560300889)
              ·
                refine ⟨9150163797584654670225667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12200218396779539560300889 9150163797584654670225667)
                ·
                  refine ⟨13725245696376982005338501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9150163797584654670225667 13725245696376982005338501)
                  ·
                    refine ⟨2573483568070684126000969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13725245696376982005338501 2573483568070684126000969)
                    ·
                      refine ⟨1930112676053013094500727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2573483568070684126000969 1930112676053013094500727)
                      ·
                        rfl

theorem cell23_3758881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 2, 1, 4, 2].length) (baseStart_3758881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3758881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3758881 prefixEnd_3758881 := by exact prefixLift 3758881
  have htrace : WordTrace (prefixWord ++ tailWord_3758881) baseStart_3758881 baseEnd_3758881 := by
    simpa [prefixWord, tailWord_3758881, baseEnd_3758881] using wordTrace_append hprefix tailTrace_3758881
  have hstable : (prefixWord ++ tailWord_3758881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3758881).length < 2 ^ (prefixWord ++ tailWord_3758881).sum := by decide
  have hdescent : baseEnd_3758881 < baseStart_3758881 := by decide
  rcases family_descends (prefixWord ++ tailWord_3758881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3758893 : List Nat := [1, 5, 3, 2, 2, 1, 2, 2, 1, 2, 2]
def baseStart_3758893 : Nat := 118140960795 + 3758893 * 2 ^ 59
def prefixEnd_3758893 : Nat := 4983230072969 + 3 ^ 40 * 3758893 * 2
def baseEnd_3758893 : Nat := 1930118837820867047550673

theorem tailTrace_3758893 : CollatzResearch.WordTrace tailWord_3758893 prefixEnd_3758893 1930118837820867047550673 := by
  unfold tailWord_3758893
  simp only [CollatzResearch.WordTrace]
  refine ⟨137098090771180103659841333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91398727180786735773227555 137098090771180103659841333)
  ·
    refine ⟨12852946009798134718110125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 137098090771180103659841333 12852946009798134718110125)
    ·
      refine ⟨4819854753674300519291297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12852946009798134718110125 4819854753674300519291297)
      ·
        refine ⟨3614891065255725389468473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4819854753674300519291297 3614891065255725389468473)
        ·
          refine ⟨2711168298941794042101355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3614891065255725389468473 2711168298941794042101355)
          ·
            refine ⟨4066752448412691063152033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2711168298941794042101355 4066752448412691063152033)
            ·
              refine ⟨3050064336309518297364025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4066752448412691063152033 3050064336309518297364025)
              ·
                refine ⟨2287548252232138723023019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3050064336309518297364025 2287548252232138723023019)
                ·
                  refine ⟨3431322378348208084534529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2287548252232138723023019 3431322378348208084534529)
                  ·
                    refine ⟨2573491783761156063400897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3431322378348208084534529 2573491783761156063400897)
                    ·
                      refine ⟨1930118837820867047550673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2573491783761156063400897 1930118837820867047550673)
                      ·
                        rfl

theorem cell23_3758893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_3758893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3758893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3758893 prefixEnd_3758893 := by exact prefixLift 3758893
  have htrace : WordTrace (prefixWord ++ tailWord_3758893) baseStart_3758893 baseEnd_3758893 := by
    simpa [prefixWord, tailWord_3758893, baseEnd_3758893] using wordTrace_append hprefix tailTrace_3758893
  have hstable : (prefixWord ++ tailWord_3758893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3758893).length < 2 ^ (prefixWord ++ tailWord_3758893).sum := by decide
  have hdescent : baseEnd_3758893 < baseStart_3758893 := by decide
  rcases family_descends (prefixWord ++ tailWord_3758893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3758927 : List Nat := [1, 1, 2, 1, 1, 2, 1, 1, 2, 6, 5]
def baseStart_3758927 : Nat := 118140960795 + 3758927 * 2 ^ 59
def prefixEnd_3758927 : Nat := 4983230072969 + 3 ^ 40 * 3758927 * 2
def baseEnd_3758927 : Nat := 1930136296163119914525515

theorem tailTrace_3758927 : CollatzResearch.WordTrace tailWord_3758927 prefixEnd_3758927 1930136296163119914525515 := by
  unfold tailWord_3758927
  simp only [CollatzResearch.WordTrace]
  refine ⟨137099330853056927466579035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91399553902037951644386023 137099330853056927466579035)
  ·
    refine ⟨205648996279585391199868553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137099330853056927466579035 205648996279585391199868553)
    ·
      refine ⟨154236747209689043399901415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205648996279585391199868553 154236747209689043399901415)
      ·
        refine ⟨231355120814533565099852123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154236747209689043399901415 231355120814533565099852123)
        ·
          refine ⟨347032681221800347649778185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231355120814533565099852123 347032681221800347649778185)
          ·
            refine ⟨260274510916350260737333639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 347032681221800347649778185 260274510916350260737333639)
            ·
              refine ⟨390411766374525391106000459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 260274510916350260737333639 390411766374525391106000459)
              ·
                refine ⟨585617649561788086659000689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 390411766374525391106000459 585617649561788086659000689)
                ·
                  refine ⟨439213237171341064994250517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 585617649561788086659000689 439213237171341064994250517)
                  ·
                    refine ⟨20588120492406612421605493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 439213237171341064994250517 20588120492406612421605493)
                    ·
                      refine ⟨1930136296163119914525515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20588120492406612421605493 1930136296163119914525515)
                      ·
                        rfl

theorem cell23_3758927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 6, 5].length) (baseStart_3758927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3758927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3758927 prefixEnd_3758927 := by exact prefixLift 3758927
  have htrace : WordTrace (prefixWord ++ tailWord_3758927) baseStart_3758927 baseEnd_3758927 := by
    simpa [prefixWord, tailWord_3758927, baseEnd_3758927] using wordTrace_append hprefix tailTrace_3758927
  have hstable : (prefixWord ++ tailWord_3758927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3758927).length < 2 ^ (prefixWord ++ tailWord_3758927).sum := by decide
  have hdescent : baseEnd_3758927 < baseStart_3758927 := by decide
  rcases family_descends (prefixWord ++ tailWord_3758927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3758971 : List Nat := [1, 1, 1, 1, 1, 5, 4, 1, 2, 4, 2]
def baseStart_3758971 : Nat := 118140960795 + 3758971 * 2 ^ 59
def prefixEnd_3758971 : Nat := 4983230072969 + 3 ^ 40 * 3758971 * 2
def baseEnd_3758971 : Nat := 1930158889311917742375313

theorem tailTrace_3758971 : CollatzResearch.WordTrace tailWord_3758971 prefixEnd_3758971 1930158889311917742375313 := by
  unfold tailWord_3758971
  simp only [CollatzResearch.WordTrace]
  refine ⟨137100935664897522981180767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91400623776598348654120511 137100935664897522981180767)
  ·
    refine ⟨205651403497346284471771151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137100935664897522981180767 205651403497346284471771151)
    ·
      refine ⟨308477105246019426707656727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205651403497346284471771151 308477105246019426707656727)
      ·
        refine ⟨462715657869029140061485091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308477105246019426707656727 462715657869029140061485091)
        ·
          refine ⟨694073486803543710092227637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 462715657869029140061485091 694073486803543710092227637)
          ·
            refine ⟨65069389387832222821146341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 694073486803543710092227637 65069389387832222821146341)
            ·
              refine ⟨12200510510218541778964939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65069389387832222821146341 12200510510218541778964939)
              ·
                refine ⟨18300765765327812668447409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12200510510218541778964939 18300765765327812668447409)
                ·
                  refine ⟨13725574323995859501335557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18300765765327812668447409 13725574323995859501335557)
                  ·
                    refine ⟨2573545185749223656500417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13725574323995859501335557 2573545185749223656500417)
                    ·
                      refine ⟨1930158889311917742375313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2573545185749223656500417 1930158889311917742375313)
                      ·
                        rfl

theorem cell23_3758971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 1, 2, 4, 2].length) (baseStart_3758971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3758971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3758971 prefixEnd_3758971 := by exact prefixLift 3758971
  have htrace : WordTrace (prefixWord ++ tailWord_3758971) baseStart_3758971 baseEnd_3758971 := by
    simpa [prefixWord, tailWord_3758971, baseEnd_3758971] using wordTrace_append hprefix tailTrace_3758971
  have hstable : (prefixWord ++ tailWord_3758971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3758971).length < 2 ^ (prefixWord ++ tailWord_3758971).sum := by decide
  have hdescent : baseEnd_3758971 < baseStart_3758971 := by decide
  rcases family_descends (prefixWord ++ tailWord_3758971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3758981 : List Nat := [1, 3, 1, 1, 3, 3, 2, 2, 3, 4]
def baseStart_3758981 : Nat := 118140960795 + 3758981 * 2 ^ 59
def prefixEnd_3758981 : Nat := 4983230072969 + 3 ^ 40 * 3758981 * 2
def baseEnd_3758981 : Nat := 643388008039487567750089

theorem tailTrace_3758981 : CollatzResearch.WordTrace tailWord_3758981 prefixEnd_3758981 643388008039487567750089 := by
  unfold tailWord_3758981
  simp only [CollatzResearch.WordTrace]
  refine ⟨137101300394861294689044797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91400866929907529792696531 137101300394861294689044797)
  ·
    refine ⟨51412987648072985508391799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137101300394861294689044797 51412987648072985508391799)
    ·
      refine ⟨77119481472109478262587699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51412987648072985508391799 77119481472109478262587699)
      ·
        refine ⟨115679222208164217393881549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77119481472109478262587699 115679222208164217393881549)
        ·
          refine ⟨43379708328061581522705581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115679222208164217393881549 43379708328061581522705581)
          ·
            refine ⟨16267390623023093071014593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43379708328061581522705581 16267390623023093071014593)
            ·
              refine ⟨12200542967267319803260945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16267390623023093071014593 12200542967267319803260945)
              ·
                refine ⟨9150407225450489852445709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12200542967267319803260945 9150407225450489852445709)
                ·
                  refine ⟨3431402709543933694667141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9150407225450489852445709 3431402709543933694667141)
                  ·
                    refine ⟨643388008039487567750089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3431402709543933694667141 643388008039487567750089)
                    ·
                      rfl

theorem cell23_3758981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 2, 3, 4].length) (baseStart_3758981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3758981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3758981 prefixEnd_3758981 := by exact prefixLift 3758981
  have htrace : WordTrace (prefixWord ++ tailWord_3758981) baseStart_3758981 baseEnd_3758981 := by
    simpa [prefixWord, tailWord_3758981, baseEnd_3758981] using wordTrace_append hprefix tailTrace_3758981
  have hstable : (prefixWord ++ tailWord_3758981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3758981).length < 2 ^ (prefixWord ++ tailWord_3758981).sum := by decide
  have hdescent : baseEnd_3758981 < baseStart_3758981 := by decide
  rcases family_descends (prefixWord ++ tailWord_3758981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3759015 : List Nat := [1, 1, 6, 1, 3, 2, 1, 1, 3, 4]
def baseStart_3759015 : Nat := 118140960795 + 3759015 * 2 ^ 59
def prefixEnd_3759015 : Nat := 4983230072969 + 3 ^ 40 * 3759015 * 2
def baseEnd_3759015 : Nat := 643393827486905190075037

theorem tailTrace_3759015 : CollatzResearch.WordTrace tailWord_3759015 prefixEnd_3759015 643393827486905190075037 := by
  unfold tailWord_3759015
  simp only [CollatzResearch.WordTrace]
  refine ⟨137102540476738118495782499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91401693651158745663854999 137102540476738118495782499)
  ·
    refine ⟨205653810715107177743673749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137102540476738118495782499 205653810715107177743673749)
    ·
      refine ⟨9640022377270648956734707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 205653810715107177743673749 9640022377270648956734707)
      ·
        refine ⟨14460033565905973435102061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9640022377270648956734707 14460033565905973435102061)
        ·
          refine ⟨5422512587214740038163273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14460033565905973435102061 5422512587214740038163273)
          ·
            refine ⟨4066884440411055028622455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5422512587214740038163273 4066884440411055028622455)
            ·
              refine ⟨6100326660616582542933683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4066884440411055028622455 6100326660616582542933683)
              ·
                refine ⟨9150489990924873814400525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6100326660616582542933683 9150489990924873814400525)
                ·
                  refine ⟨3431433746596827680400197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9150489990924873814400525 3431433746596827680400197)
                  ·
                    refine ⟨643393827486905190075037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3431433746596827680400197 643393827486905190075037)
                    ·
                      rfl

theorem cell23_3759015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 1, 1, 3, 4].length) (baseStart_3759015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3759015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3759015 prefixEnd_3759015 := by exact prefixLift 3759015
  have htrace : WordTrace (prefixWord ++ tailWord_3759015) baseStart_3759015 baseEnd_3759015 := by
    simpa [prefixWord, tailWord_3759015, baseEnd_3759015] using wordTrace_append hprefix tailTrace_3759015
  have hstable : (prefixWord ++ tailWord_3759015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3759015).length < 2 ^ (prefixWord ++ tailWord_3759015).sum := by decide
  have hdescent : baseEnd_3759015 < baseStart_3759015 := by decide
  rcases family_descends (prefixWord ++ tailWord_3759015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3759031 : List Nat := [1, 1, 3, 1, 3, 1, 2, 1, 3, 5, 2]
def baseStart_3759031 : Nat := 118140960795 + 3759031 * 2 ^ 59
def prefixEnd_3759031 : Nat := 4983230072969 + 3 ^ 40 * 3759031 * 2
def baseEnd_3759031 : Nat := 1930189698151187507625037

theorem tailTrace_3759031 : CollatzResearch.WordTrace tailWord_3759031 prefixEnd_3759031 1930189698151187507625037 := by
  unfold tailWord_3759031
  simp only [CollatzResearch.WordTrace]
  refine ⟨137103124044680153228364947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91402082696453435485576631 137103124044680153228364947)
  ·
    refine ⟨205654686067020229842547421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137103124044680153228364947 205654686067020229842547421)
    ·
      refine ⟨77120507275132586190955283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205654686067020229842547421 77120507275132586190955283)
      ·
        refine ⟨115680760912698879286432925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77120507275132586190955283 115680760912698879286432925)
        ·
          refine ⟨43380285342262079732412347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115680760912698879286432925 43380285342262079732412347)
          ·
            refine ⟨65070428013393119598618521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43380285342262079732412347 65070428013393119598618521)
            ·
              refine ⟨48802821010044839698963891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65070428013393119598618521 48802821010044839698963891)
              ·
                refine ⟨73204231515067259548445837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48802821010044839698963891 73204231515067259548445837)
                ·
                  refine ⟨27451586818150222330667189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73204231515067259548445837 27451586818150222330667189)
                  ·
                    refine ⟨2573586264201583343500049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27451586818150222330667189 2573586264201583343500049)
                    ·
                      refine ⟨1930189698151187507625037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2573586264201583343500049 1930189698151187507625037)
                      ·
                        rfl

theorem cell23_3759031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 3, 5, 2].length) (baseStart_3759031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3759031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3759031 prefixEnd_3759031 := by exact prefixLift 3759031
  have htrace : WordTrace (prefixWord ++ tailWord_3759031) baseStart_3759031 baseEnd_3759031 := by
    simpa [prefixWord, tailWord_3759031, baseEnd_3759031] using wordTrace_append hprefix tailTrace_3759031
  have hstable : (prefixWord ++ tailWord_3759031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3759031).length < 2 ^ (prefixWord ++ tailWord_3759031).sum := by decide
  have hdescent : baseEnd_3759031 < baseStart_3759031 := by decide
  rcases family_descends (prefixWord ++ tailWord_3759031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3759038 : List Nat := [4, 2, 1, 1, 1, 2, 2, 1, 5, 1, 3]
def baseStart_3759038 : Nat := 118140960795 + 3759038 * 2 ^ 59
def prefixEnd_3759038 : Nat := 4983230072969 + 3 ^ 40 * 3759038 * 2
def baseEnd_3759038 : Nat := 1930193292515768980237505

theorem tailTrace_3759038 : CollatzResearch.WordTrace tailWord_3759038 prefixEnd_3759038 1930193292515768980237505 := by
  unfold tailWord_3759038
  simp only [CollatzResearch.WordTrace]
  refine ⟨17137922419456849177983721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91402252903769862282579845 17137922419456849177983721)
  ·
    refine ⟨12853441814592636883487791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17137922419456849177983721 12853441814592636883487791)
    ·
      refine ⟨19280162721888955325231687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12853441814592636883487791 19280162721888955325231687)
      ·
        refine ⟨28920244082833432987847531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19280162721888955325231687 28920244082833432987847531)
        ·
          refine ⟨43380366124250149481771297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28920244082833432987847531 43380366124250149481771297)
          ·
            refine ⟨32535274593187612111328473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43380366124250149481771297 32535274593187612111328473)
            ·
              refine ⟨24401455944890709083496355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32535274593187612111328473 24401455944890709083496355)
              ·
                refine ⟨36602183917336063625244533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24401455944890709083496355 36602183917336063625244533)
                ·
                  refine ⟨3431454742250255964866675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36602183917336063625244533 3431454742250255964866675)
                  ·
                    refine ⟨5147182113375383947300013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3431454742250255964866675 5147182113375383947300013)
                    ·
                      refine ⟨1930193292515768980237505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5147182113375383947300013 1930193292515768980237505)
                      ·
                        rfl

theorem cell23_3759038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 1, 5, 1, 3].length) (baseStart_3759038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3759038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3759038 prefixEnd_3759038 := by exact prefixLift 3759038
  have htrace : WordTrace (prefixWord ++ tailWord_3759038) baseStart_3759038 baseEnd_3759038 := by
    simpa [prefixWord, tailWord_3759038, baseEnd_3759038] using wordTrace_append hprefix tailTrace_3759038
  have hstable : (prefixWord ++ tailWord_3759038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3759038).length < 2 ^ (prefixWord ++ tailWord_3759038).sum := by decide
  have hdescent : baseEnd_3759038 < baseStart_3759038 := by decide
  rcases family_descends (prefixWord ++ tailWord_3759038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3759104 : List Nat := [2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 6]
def baseStart_3759104 : Nat := 118140960795 + 3759104 * 2 ^ 59
def prefixEnd_3759104 : Nat := 4983230072969 + 3 ^ 40 * 3759104 * 2
def baseEnd_3759104 : Nat := 1930227182238965722012201

theorem tailTrace_3759104 : CollatzResearch.WordTrace tailWord_3759104 prefixEnd_3759104 1930227182238965722012201 := by
  unfold tailWord_3759104
  simp only [CollatzResearch.WordTrace]
  refine ⟨68552893286707843347886183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91403857715610457797181577 68552893286707843347886183)
  ·
    refine ⟨102829339930061765021829275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68552893286707843347886183 102829339930061765021829275)
    ·
      refine ⟨154244009895092647532743913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102829339930061765021829275 154244009895092647532743913)
      ·
        refine ⟨115683007421319485649557935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154244009895092647532743913 115683007421319485649557935)
        ·
          refine ⟨173524511131979228474336903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115683007421319485649557935 173524511131979228474336903)
          ·
            refine ⟨260286766697968842711505355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173524511131979228474336903 260286766697968842711505355)
            ·
              refine ⟨390430150046953264067258033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 260286766697968842711505355 390430150046953264067258033)
              ·
                refine ⟨292822612535214948050443525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 390430150046953264067258033 292822612535214948050443525)
                ·
                  refine ⟨54904239850352802759458161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 292822612535214948050443525 54904239850352802759458161)
                  ·
                    refine ⟨41178179887764602069593621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54904239850352802759458161 41178179887764602069593621)
                    ·
                      refine ⟨1930227182238965722012201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41178179887764602069593621 1930227182238965722012201)
                      ·
                        rfl

theorem cell23_3759104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 6].length) (baseStart_3759104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3759104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3759104 prefixEnd_3759104 := by exact prefixLift 3759104
  have htrace : WordTrace (prefixWord ++ tailWord_3759104) baseStart_3759104 baseEnd_3759104 := by
    simpa [prefixWord, tailWord_3759104, baseEnd_3759104] using wordTrace_append hprefix tailTrace_3759104
  have hstable : (prefixWord ++ tailWord_3759104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3759104).length < 2 ^ (prefixWord ++ tailWord_3759104).sum := by decide
  have hdescent : baseEnd_3759104 < baseStart_3759104 := by decide
  rcases family_descends (prefixWord ++ tailWord_3759104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3759106 : List Nat := [3, 4, 1, 3, 1, 1, 2, 3, 1, 1, 3]
def baseStart_3759106 : Nat := 118140960795 + 3759106 * 2 ^ 59
def prefixEnd_3759106 : Nat := 4983230072969 + 3 ^ 40 * 3759106 * 2
def baseEnd_3759106 : Nat := 1930228209200274714187193

theorem tailTrace_3759106 : CollatzResearch.WordTrace tailWord_3759106 prefixEnd_3759106 1930228209200274714187193 := by
  unfold tailWord_3759106
  simp only [CollatzResearch.WordTrace]
  refine ⟨34276464879852110259336293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91403906346272294024896781 34276464879852110259336293)
  ·
    refine ⟨6426837164972270673625555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34276464879852110259336293 6426837164972270673625555)
    ·
      refine ⟨9640255747458406010438333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6426837164972270673625555 9640255747458406010438333)
      ·
        refine ⟨3615095905296902253914375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9640255747458406010438333 3615095905296902253914375)
        ·
          refine ⟨5422643857945353380871563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3615095905296902253914375 5422643857945353380871563)
          ·
            refine ⟨8133965786918030071307345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5422643857945353380871563 8133965786918030071307345)
            ·
              refine ⟨6100474340188522553480509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8133965786918030071307345 6100474340188522553480509)
              ·
                refine ⟨2287677877570695957555191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6100474340188522553480509 2287677877570695957555191)
                ·
                  refine ⟨3431516816356043936332787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2287677877570695957555191 3431516816356043936332787)
                  ·
                    refine ⟨5147275224534065904499181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3431516816356043936332787 5147275224534065904499181)
                    ·
                      refine ⟨1930228209200274714187193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5147275224534065904499181 1930228209200274714187193)
                      ·
                        rfl

theorem cell23_3759106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_3759106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3759106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3759106 prefixEnd_3759106 := by exact prefixLift 3759106
  have htrace : WordTrace (prefixWord ++ tailWord_3759106) baseStart_3759106 baseEnd_3759106 := by
    simpa [prefixWord, tailWord_3759106, baseEnd_3759106] using wordTrace_append hprefix tailTrace_3759106
  have hstable : (prefixWord ++ tailWord_3759106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3759106).length < 2 ^ (prefixWord ++ tailWord_3759106).sum := by decide
  have hdescent : baseEnd_3759106 < baseStart_3759106 := by decide
  rcases family_descends (prefixWord ++ tailWord_3759106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3759112 : List Nat := [2, 1, 3, 2, 1, 3, 1, 5, 1, 2, 2]
def baseStart_3759112 : Nat := 118140960795 + 3759112 * 2 ^ 59
def prefixEnd_3759112 : Nat := 4983230072969 + 3 ^ 40 * 3759112 * 2
def baseEnd_3759112 : Nat := 1930231290084201690712165

theorem tailTrace_3759112 : CollatzResearch.WordTrace tailWord_3759112 prefixEnd_3759112 1930231290084201690712165 := by
  unfold tailWord_3759112
  simp only [CollatzResearch.WordTrace]
  refine ⟨68553039178693352031031795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91404052238257802708042393 68553039178693352031031795)
  ·
    refine ⟨102829558768040028046547693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68553039178693352031031795 102829558768040028046547693)
    ·
      refine ⟨38561084538015010517455385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102829558768040028046547693 38561084538015010517455385)
      ·
        refine ⟨28920813403511257888091539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38561084538015010517455385 28920813403511257888091539)
        ·
          refine ⟨43381220105266886832137309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28920813403511257888091539 43381220105266886832137309)
          ·
            refine ⟨16267957539475082562051491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43381220105266886832137309 16267957539475082562051491)
            ·
              refine ⟨24401936309212623843077237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16267957539475082562051491 24401936309212623843077237)
              ·
                refine ⟨2287681528988683485288491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24401936309212623843077237 2287681528988683485288491)
                ·
                  refine ⟨3431522293483025227932737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2287681528988683485288491 3431522293483025227932737)
                  ·
                    refine ⟨2573641720112268920949553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3431522293483025227932737 2573641720112268920949553)
                    ·
                      refine ⟨1930231290084201690712165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2573641720112268920949553 1930231290084201690712165)
                      ·
                        rfl

theorem cell23_3759112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 5, 1, 2, 2].length) (baseStart_3759112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3759112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3759112 prefixEnd_3759112 := by exact prefixLift 3759112
  have htrace : WordTrace (prefixWord ++ tailWord_3759112) baseStart_3759112 baseEnd_3759112 := by
    simpa [prefixWord, tailWord_3759112, baseEnd_3759112] using wordTrace_append hprefix tailTrace_3759112
  have hstable : (prefixWord ++ tailWord_3759112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3759112).length < 2 ^ (prefixWord ++ tailWord_3759112).sum := by decide
  have hdescent : baseEnd_3759112 < baseStart_3759112 := by decide
  rcases family_descends (prefixWord ++ tailWord_3759112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3759115 : List Nat := [1, 1, 1, 1, 6, 2, 4, 1, 1, 2, 3]
def baseStart_3759115 : Nat := 118140960795 + 3759115 * 2 ^ 59
def prefixEnd_3759115 : Nat := 4983230072969 + 3 ^ 40 * 3759115 * 2
def baseEnd_3759115 : Nat := 1930232830526165178974651

theorem tailTrace_3759115 : CollatzResearch.WordTrace tailWord_3759115 prefixEnd_3759115 1930232830526165178974651 := by
  unfold tailWord_3759115
  simp only [CollatzResearch.WordTrace]
  refine ⟨137106187776375835574422799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91404125184250557049615199 137106187776375835574422799)
  ·
    refine ⟨205659281664563753361634199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137106187776375835574422799 205659281664563753361634199)
    ·
      refine ⟨308488922496845630042451299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205659281664563753361634199 308488922496845630042451299)
      ·
        refine ⟨462733383745268445063676949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308488922496845630042451299 462733383745268445063676949)
        ·
          refine ⟨21690627363059458362359857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 462733383745268445063676949 21690627363059458362359857)
          ·
            refine ⟨16267970522294593771769893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21690627363059458362359857 16267970522294593771769893)
            ·
              refine ⟨3050244472930236332206855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16267970522294593771769893 3050244472930236332206855)
              ·
                refine ⟨4575366709395354498310283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3050244472930236332206855 4575366709395354498310283)
                ·
                  refine ⟨6863050064093031747465425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4575366709395354498310283 6863050064093031747465425)
                  ·
                    refine ⟨5147287548069773810599069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6863050064093031747465425 5147287548069773810599069)
                    ·
                      refine ⟨1930232830526165178974651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5147287548069773810599069 1930232830526165178974651)
                      ·
                        rfl

theorem cell23_3759115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 4, 1, 1, 2, 3].length) (baseStart_3759115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3759115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3759115 prefixEnd_3759115 := by exact prefixLift 3759115
  have htrace : WordTrace (prefixWord ++ tailWord_3759115) baseStart_3759115 baseEnd_3759115 := by
    simpa [prefixWord, tailWord_3759115, baseEnd_3759115] using wordTrace_append hprefix tailTrace_3759115
  have hstable : (prefixWord ++ tailWord_3759115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3759115).length < 2 ^ (prefixWord ++ tailWord_3759115).sum := by decide
  have hdescent : baseEnd_3759115 < baseStart_3759115 := by decide
  rcases family_descends (prefixWord ++ tailWord_3759115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3759158 : List Nat := [5, 1, 2, 1, 1, 2, 1, 1, 2, 2, 5]
def baseStart_3759158 : Nat := 118140960795 + 3759158 * 2 ^ 59
def prefixEnd_3759158 : Nat := 4983230072969 + 3 ^ 40 * 3759158 * 2
def baseEnd_3759158 : Nat := 1930254910194308510736953

theorem tailTrace_3759158 : CollatzResearch.WordTrace tailWord_3759158 prefixEnd_3759158 1930254910194308510736953 := by
  unfold tailWord_3759158
  simp only [CollatzResearch.WordTrace]
  refine ⟨8569234757201253369889883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 91405170743480035945492085 8569234757201253369889883)
  ·
    refine ⟨12853852135801880054834825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8569234757201253369889883 12853852135801880054834825)
    ·
      refine ⟨9640389101851410041126119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12853852135801880054834825 9640389101851410041126119)
      ·
        refine ⟨14460583652777115061689179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9640389101851410041126119 14460583652777115061689179)
        ·
          refine ⟨21690875479165672592533769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14460583652777115061689179 21690875479165672592533769)
          ·
            refine ⟨16268156609374254444400327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21690875479165672592533769 16268156609374254444400327)
            ·
              refine ⟨24402234914061381666600491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16268156609374254444400327 24402234914061381666600491)
              ·
                refine ⟨36603352371092072499900737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24402234914061381666600491 36603352371092072499900737)
                ·
                  refine ⟨27452514278319054374925553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36603352371092072499900737 27452514278319054374925553)
                  ·
                    refine ⟨20589385708739290781194165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27452514278319054374925553 20589385708739290781194165)
                    ·
                      refine ⟨1930254910194308510736953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20589385708739290781194165 1930254910194308510736953)
                      ·
                        rfl

theorem cell23_3759158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_3759158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3759158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3759158 prefixEnd_3759158 := by exact prefixLift 3759158
  have htrace : WordTrace (prefixWord ++ tailWord_3759158) baseStart_3759158 baseEnd_3759158 := by
    simpa [prefixWord, tailWord_3759158, baseEnd_3759158] using wordTrace_append hprefix tailTrace_3759158
  have hstable : (prefixWord ++ tailWord_3759158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3759158).length < 2 ^ (prefixWord ++ tailWord_3759158).sum := by decide
  have hdescent : baseEnd_3759158 < baseStart_3759158 := by decide
  rcases family_descends (prefixWord ++ tailWord_3759158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3759168 : List Nat := [2, 1, 1, 2, 2, 3, 2, 1, 3, 4, 2]
def baseStart_3759168 : Nat := 118140960795 + 3759168 * 2 ^ 59
def prefixEnd_3759168 : Nat := 4983230072969 + 3 ^ 40 * 3759168 * 2
def baseEnd_3759168 : Nat := 1930260045000853471611907

theorem tailTrace_3759168 : CollatzResearch.WordTrace tailWord_3759168 prefixEnd_3759168 1930260045000853471611907 := by
  unfold tailWord_3759168
  simp only [CollatzResearch.WordTrace]
  refine ⟨68554060422591912813051079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91405413896789217084068105 68554060422591912813051079)
  ·
    refine ⟨102831090633887869219576619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68554060422591912813051079 102831090633887869219576619)
    ·
      refine ⟨154246635950831803829364929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102831090633887869219576619 154246635950831803829364929)
      ·
        refine ⟨115684976963123852872023697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154246635950831803829364929 115684976963123852872023697)
        ·
          refine ⟨86763732722342889654017773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115684976963123852872023697 86763732722342889654017773)
          ·
            refine ⟨32536399770878583620256665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86763732722342889654017773 32536399770878583620256665)
            ·
              refine ⟨24402299828158937715192499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32536399770878583620256665 24402299828158937715192499)
              ·
                refine ⟨36603449742238406572788749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24402299828158937715192499 36603449742238406572788749)
                ·
                  refine ⟨13726293653339402464795781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36603449742238406572788749 13726293653339402464795781)
                  ·
                    refine ⟨2573680060001137962149209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13726293653339402464795781 2573680060001137962149209)
                    ·
                      refine ⟨1930260045000853471611907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2573680060001137962149209 1930260045000853471611907)
                      ·
                        rfl

theorem cell23_3759168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 1, 3, 4, 2].length) (baseStart_3759168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3759168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3759168 prefixEnd_3759168 := by exact prefixLift 3759168
  have htrace : WordTrace (prefixWord ++ tailWord_3759168) baseStart_3759168 baseEnd_3759168 := by
    simpa [prefixWord, tailWord_3759168, baseEnd_3759168] using wordTrace_append hprefix tailTrace_3759168
  have hstable : (prefixWord ++ tailWord_3759168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3759168).length < 2 ^ (prefixWord ++ tailWord_3759168).sum := by decide
  have hdescent : baseEnd_3759168 < baseStart_3759168 := by decide
  rcases family_descends (prefixWord ++ tailWord_3759168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3759171 : List Nat := [1, 1, 1, 3, 1, 2, 5, 1, 2, 1, 5]
def baseStart_3759171 : Nat := 118140960795 + 3759171 * 2 ^ 59
def prefixEnd_3759171 : Nat := 4983230072969 + 3 ^ 40 * 3759171 * 2
def baseEnd_3759171 : Nat := 1930261585442816959874393

theorem tailTrace_3759171 : CollatzResearch.WordTrace tailWord_3759171 prefixEnd_3759171 1930261585442816959874393 := by
  unfold tailWord_3759171
  simp only [CollatzResearch.WordTrace]
  refine ⟨137108230264172957138461367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91405486842781971425640911 137108230264172957138461367)
  ·
    refine ⟨205662345396259435707692051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137108230264172957138461367 205662345396259435707692051)
    ·
      refine ⟨308493518094389153561538077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205662345396259435707692051 308493518094389153561538077)
      ·
        refine ⟨115685069285395932585576779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 308493518094389153561538077 115685069285395932585576779)
        ·
          refine ⟨173527603928093898878365169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115685069285395932585576779 173527603928093898878365169)
          ·
            refine ⟨130145702946070424158773877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173527603928093898878365169 130145702946070424158773877)
            ·
              refine ⟨12201159651194102264885051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 130145702946070424158773877 12201159651194102264885051)
              ·
                refine ⟨18301739476791153397327577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12201159651194102264885051 18301739476791153397327577)
                ·
                  refine ⟨13726304607593365047995683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18301739476791153397327577 13726304607593365047995683)
                  ·
                    refine ⟨20589456911390047571993525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13726304607593365047995683 20589456911390047571993525)
                    ·
                      refine ⟨1930261585442816959874393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20589456911390047571993525 1930261585442816959874393)
                      ·
                        rfl

theorem cell23_3759171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 1, 2, 1, 5].length) (baseStart_3759171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3759171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3759171 prefixEnd_3759171 := by exact prefixLift 3759171
  have htrace : WordTrace (prefixWord ++ tailWord_3759171) baseStart_3759171 baseEnd_3759171 := by
    simpa [prefixWord, tailWord_3759171, baseEnd_3759171] using wordTrace_append hprefix tailTrace_3759171
  have hstable : (prefixWord ++ tailWord_3759171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3759171).length < 2 ^ (prefixWord ++ tailWord_3759171).sum := by decide
  have hdescent : baseEnd_3759171 < baseStart_3759171 := by decide
  rcases family_descends (prefixWord ++ tailWord_3759171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3759185 : List Nat := [1, 2, 2, 1, 3, 1, 4, 1, 4, 2, 2]
def baseStart_3759185 : Nat := 118140960795 + 3759185 * 2 ^ 59
def prefixEnd_3759185 : Nat := 4983230072969 + 3 ^ 40 * 3759185 * 2
def baseEnd_3759185 : Nat := 1930268774171979905099329

theorem tailTrace_3759185 : CollatzResearch.WordTrace tailWord_3759185 prefixEnd_3759185 1930268774171979905099329 := by
  unfold tailWord_3759185
  simp only [CollatzResearch.WordTrace]
  refine ⟨137108740886122237529471009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91405827257414825019647339 137108740886122237529471009)
  ·
    refine ⟨102831555664591678147103257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137108740886122237529471009 102831555664591678147103257)
    ·
      refine ⟨77123666748443758610327443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102831555664591678147103257 77123666748443758610327443)
      ·
        refine ⟨115685500122665637915491165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77123666748443758610327443 115685500122665637915491165)
        ·
          refine ⟨43382062545999614218309187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115685500122665637915491165 43382062545999614218309187)
          ·
            refine ⟨65073093818999421327463781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43382062545999614218309187 65073093818999421327463781)
            ·
              refine ⟨12201205091062391498899459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65073093818999421327463781 12201205091062391498899459)
              ·
                refine ⟨18301807636593587248349189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12201205091062391498899459 18301807636593587248349189)
                ·
                  refine ⟨3431588931861297609065473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18301807636593587248349189 3431588931861297609065473)
                  ·
                    refine ⟨2573691698895973206799105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3431588931861297609065473 2573691698895973206799105)
                    ·
                      refine ⟨1930268774171979905099329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2573691698895973206799105 1930268774171979905099329)
                      ·
                        rfl

theorem cell23_3759185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 1, 4, 2, 2].length) (baseStart_3759185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3759185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3759185 prefixEnd_3759185 := by exact prefixLift 3759185
  have htrace : WordTrace (prefixWord ++ tailWord_3759185) baseStart_3759185 baseEnd_3759185 := by
    simpa [prefixWord, tailWord_3759185, baseEnd_3759185] using wordTrace_append hprefix tailTrace_3759185
  have hstable : (prefixWord ++ tailWord_3759185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3759185).length < 2 ^ (prefixWord ++ tailWord_3759185).sum := by decide
  have hdescent : baseEnd_3759185 < baseStart_3759185 := by decide
  rcases family_descends (prefixWord ++ tailWord_3759185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3759311 : List Nat := [1, 1, 2, 1, 1, 3, 2, 1, 2, 9]
def baseStart_3759311 : Nat := 118140960795 + 3759311 * 2 ^ 59
def prefixEnd_3759311 : Nat := 4983230072969 + 3 ^ 40 * 3759311 * 2
def baseEnd_3759311 : Nat := 643444490911482137374583

theorem tailTrace_3759311 : CollatzResearch.WordTrace tailWord_3759311 prefixEnd_3759311 643444490911482137374583 := by
  unfold tailWord_3759311
  simp only [CollatzResearch.WordTrace]
  refine ⟨137113336483665761048557787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91408890989110507365705191 137113336483665761048557787)
  ·
    refine ⟨205670004725498641572836681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137113336483665761048557787 205670004725498641572836681)
    ·
      refine ⟨154252503544123981179627511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205670004725498641572836681 154252503544123981179627511)
      ·
        refine ⟨231378755316185971769441267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154252503544123981179627511 231378755316185971769441267)
        ·
          refine ⟨347068132974278957654161901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231378755316185971769441267 347068132974278957654161901)
          ·
            refine ⟨130150549865354609120310713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 347068132974278957654161901 130150549865354609120310713)
            ·
              refine ⟨97612912399015956840233035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130150549865354609120310713 97612912399015956840233035)
              ·
                refine ⟨146419368598523935260349553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97612912399015956840233035 146419368598523935260349553)
                ·
                  refine ⟨109814526448892951445262165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 146419368598523935260349553 109814526448892951445262165)
                  ·
                    refine ⟨643444490911482137374583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 109814526448892951445262165 643444490911482137374583)
                    ·
                      rfl

theorem cell23_3759311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 9].length) (baseStart_3759311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3759311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3759311 prefixEnd_3759311 := by exact prefixLift 3759311
  have htrace : WordTrace (prefixWord ++ tailWord_3759311) baseStart_3759311 baseEnd_3759311 := by
    simpa [prefixWord, tailWord_3759311, baseEnd_3759311] using wordTrace_append hprefix tailTrace_3759311
  have hstable : (prefixWord ++ tailWord_3759311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3759311).length < 2 ^ (prefixWord ++ tailWord_3759311).sum := by decide
  have hdescent : baseEnd_3759311 < baseStart_3759311 := by decide
  rcases family_descends (prefixWord ++ tailWord_3759311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3759388 : List Nat := [2, 2, 3, 1, 1, 1, 4, 9]
def baseStart_3759388 : Nat := 118140960795 + 3759388 * 2 ^ 59
def prefixEnd_3759388 : Nat := 4983230072969 + 3 ^ 40 * 3759388 * 2
def baseEnd_3759388 : Nat := 71495296694253430031885

theorem tailTrace_3759388 : CollatzResearch.WordTrace tailWord_3759388 prefixEnd_3759388 71495296694253430031885 := by
  unfold tailWord_3759388
  simp only [CollatzResearch.WordTrace]
  refine ⟨68558072452193401599555409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91410763269591202132740545 68558072452193401599555409)
  ·
    refine ⟨51418554339145051199666557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68558072452193401599555409 51418554339145051199666557)
    ·
      refine ⟨19281957877179394199874959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51418554339145051199666557 19281957877179394199874959)
      ·
        refine ⟨28922936815769091299812439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19281957877179394199874959 28922936815769091299812439)
        ·
          refine ⟨43384405223653636949718659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28922936815769091299812439 43384405223653636949718659)
          ·
            refine ⟨65076607835480455424577989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43384405223653636949718659 65076607835480455424577989)
            ·
              refine ⟨12201863969152585392108373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65076607835480455424577989 12201863969152585392108373)
              ·
                refine ⟨71495296694253430031885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12201863969152585392108373 71495296694253430031885)
                ·
                  rfl

theorem cell23_3759388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 9].length) (baseStart_3759388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3759388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3759388 prefixEnd_3759388 := by exact prefixLift 3759388
  have htrace : WordTrace (prefixWord ++ tailWord_3759388) baseStart_3759388 baseEnd_3759388 := by
    simpa [prefixWord, tailWord_3759388, baseEnd_3759388] using wordTrace_append hprefix tailTrace_3759388
  have hstable : (prefixWord ++ tailWord_3759388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3759388).length < 2 ^ (prefixWord ++ tailWord_3759388).sum := by decide
  have hdescent : baseEnd_3759388 < baseStart_3759388 := by decide
  rcases family_descends (prefixWord ++ tailWord_3759388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3759395 : List Nat := [1, 1, 1, 4, 2, 4, 1, 2, 1, 2, 4]
def baseStart_3759395 : Nat := 118140960795 + 3759395 * 2 ^ 59
def prefixEnd_3759395 : Nat := 4983230072969 + 3 ^ 40 * 3759395 * 2
def baseEnd_3759395 : Nat := 1930376605109424083473363

theorem tailTrace_3759395 : CollatzResearch.WordTrace tailWord_3759395 prefixEnd_3759395 1930376605109424083473363 := by
  unfold tailWord_3759395
  simp only [CollatzResearch.WordTrace]
  refine ⟨137116400215361443394615639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91410933476907628929743759 137116400215361443394615639)
  ·
    refine ⟨205674600323042165091923459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137116400215361443394615639 205674600323042165091923459)
    ·
      refine ⟨308511900484563247637885189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205674600323042165091923459 308511900484563247637885189)
      ·
        refine ⟨57845981340855608932103473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 308511900484563247637885189 57845981340855608932103473)
        ·
          refine ⟨43384486005641706699077605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57845981340855608932103473 43384486005641706699077605)
          ·
            refine ⟨8134591126057820006077051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43384486005641706699077605 8134591126057820006077051)
            ·
              refine ⟨12201886689086730009115577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8134591126057820006077051 12201886689086730009115577)
              ·
                refine ⟨9151415016815047506836683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12201886689086730009115577 9151415016815047506836683)
                ·
                  refine ⟨13727122525222571260255025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9151415016815047506836683 13727122525222571260255025)
                  ·
                    refine ⟨10295341893916928445191269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13727122525222571260255025 10295341893916928445191269)
                    ·
                      refine ⟨1930376605109424083473363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10295341893916928445191269 1930376605109424083473363)
                      ·
                        rfl

theorem cell23_3759395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 2, 1, 2, 4].length) (baseStart_3759395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3759395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3759395 prefixEnd_3759395 := by exact prefixLift 3759395
  have htrace : WordTrace (prefixWord ++ tailWord_3759395) baseStart_3759395 baseEnd_3759395 := by
    simpa [prefixWord, tailWord_3759395, baseEnd_3759395] using wordTrace_append hprefix tailTrace_3759395
  have hstable : (prefixWord ++ tailWord_3759395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3759395).length < 2 ^ (prefixWord ++ tailWord_3759395).sum := by decide
  have hdescent : baseEnd_3759395 < baseStart_3759395 := by decide
  rcases family_descends (prefixWord ++ tailWord_3759395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3759402 : List Nat := [3, 1, 4, 2, 1, 1, 3, 1, 1, 1, 5]
def baseStart_3759402 : Nat := 118140960795 + 3759402 * 2 ^ 59
def prefixEnd_3759402 : Nat := 4983230072969 + 3 ^ 40 * 3759402 * 2
def baseEnd_3759402 : Nat := 1930380199474005556085831

theorem tailTrace_3759402 : CollatzResearch.WordTrace tailWord_3759402 prefixEnd_3759402 1930380199474005556085831 := by
  unfold tailWord_3759402
  simp only [CollatzResearch.WordTrace]
  refine ⟨34279163881584020897530115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91411103684224055726746973 34279163881584020897530115)
  ·
    refine ⟨51418745822376031346295173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34279163881584020897530115 51418745822376031346295173)
    ·
      refine ⟨9641014841695505877430345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51418745822376031346295173 9641014841695505877430345)
      ·
        refine ⟨7230761131271629408072759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9641014841695505877430345 7230761131271629408072759)
        ·
          refine ⟨10846141696907444112109139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7230761131271629408072759 10846141696907444112109139)
          ·
            refine ⟨16269212545361166168163709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10846141696907444112109139 16269212545361166168163709)
            ·
              refine ⟨6100954704510437313061391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16269212545361166168163709 6100954704510437313061391)
              ·
                refine ⟨9151432056765655969592087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6100954704510437313061391 9151432056765655969592087)
                ·
                  refine ⟨13727148085148483954388131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9151432056765655969592087 13727148085148483954388131)
                  ·
                    refine ⟨20590722127722725931582197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13727148085148483954388131 20590722127722725931582197)
                    ·
                      refine ⟨1930380199474005556085831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20590722127722725931582197 1930380199474005556085831)
                      ·
                        rfl

theorem cell23_3759402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_3759402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3759402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3759402 prefixEnd_3759402 := by exact prefixLift 3759402
  have htrace : WordTrace (prefixWord ++ tailWord_3759402) baseStart_3759402 baseEnd_3759402 := by
    simpa [prefixWord, tailWord_3759402, baseEnd_3759402] using wordTrace_append hprefix tailTrace_3759402
  have hstable : (prefixWord ++ tailWord_3759402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3759402).length < 2 ^ (prefixWord ++ tailWord_3759402).sum := by decide
  have hdescent : baseEnd_3759402 < baseStart_3759402 := by decide
  rcases family_descends (prefixWord ++ tailWord_3759402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3759405 : List Nat := [1, 5, 3, 1, 1, 12]
def baseStart_3759405 : Nat := 118140960795 + 3759405 * 2 ^ 59
def prefixEnd_3759405 : Nat := 4983230072969 + 3 ^ 40 * 3759405 * 2
def baseEnd_3759405 : Nat := 7943957777431971375919

theorem tailTrace_3759405 : CollatzResearch.WordTrace tailWord_3759405 prefixEnd_3759405 7943957777431971375919 := by
  unfold tailWord_3759405
  simp only [CollatzResearch.WordTrace]
  refine ⟨137116764945325215102479669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91411176630216810068319779 137116764945325215102479669)
  ·
    refine ⟨12854696713624238915857469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 137116764945325215102479669 12854696713624238915857469)
    ·
      refine ⟨4820511267609089593446551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12854696713624238915857469 4820511267609089593446551)
      ·
        refine ⟨7230766901413634390169827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4820511267609089593446551 7230766901413634390169827)
        ·
          refine ⟨10846150352120451585254741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7230766901413634390169827 10846150352120451585254741)
          ·
            refine ⟨7943957777431971375919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 10846150352120451585254741 7943957777431971375919)
            ·
              rfl

theorem cell23_3759405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 12].length) (baseStart_3759405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3759405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3759405 prefixEnd_3759405 := by exact prefixLift 3759405
  have htrace : WordTrace (prefixWord ++ tailWord_3759405) baseStart_3759405 baseEnd_3759405 := by
    simpa [prefixWord, tailWord_3759405, baseEnd_3759405] using wordTrace_append hprefix tailTrace_3759405
  have hstable : (prefixWord ++ tailWord_3759405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3759405).length < 2 ^ (prefixWord ++ tailWord_3759405).sum := by decide
  have hdescent : baseEnd_3759405 < baseStart_3759405 := by decide
  rcases family_descends (prefixWord ++ tailWord_3759405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3759418 : List Nat := [3, 1, 1, 1, 4, 1, 1, 1, 1, 9]
def baseStart_3759418 : Nat := 118140960795 + 3759418 * 2 ^ 59
def prefixEnd_3759418 : Nat := 4983230072969 + 3 ^ 40 * 3759418 * 2
def baseEnd_3759418 : Nat := 643462805054825831161919

theorem tailTrace_3759418 : CollatzResearch.WordTrace tailWord_3759418 prefixEnd_3759418 643462805054825831161919 := by
  unfold tailWord_3759418
  simp only [CollatzResearch.WordTrace]
  refine ⟨34279309773569529580675727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91411492729518745548468605 34279309773569529580675727)
  ·
    refine ⟨51418964660354294371013591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34279309773569529580675727 51418964660354294371013591)
    ·
      refine ⟨77128446990531441556520387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51418964660354294371013591 77128446990531441556520387)
      ·
        refine ⟨115692670485797162334780581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77128446990531441556520387 115692670485797162334780581)
        ·
          refine ⟨21692375716086967937771359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115692670485797162334780581 21692375716086967937771359)
          ·
            refine ⟨32538563574130451906657039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21692375716086967937771359 32538563574130451906657039)
            ·
              refine ⟨48807845361195677859985559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32538563574130451906657039 48807845361195677859985559)
              ·
                refine ⟨73211768041793516789978339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48807845361195677859985559 73211768041793516789978339)
                ·
                  refine ⟨109817652062690275184967509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73211768041793516789978339 109817652062690275184967509)
                  ·
                    refine ⟨643462805054825831161919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 109817652062690275184967509 643462805054825831161919)
                    ·
                      rfl

theorem cell23_3759418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 1, 9].length) (baseStart_3759418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3759418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3759418 prefixEnd_3759418 := by exact prefixLift 3759418
  have htrace : WordTrace (prefixWord ++ tailWord_3759418) baseStart_3759418 baseEnd_3759418 := by
    simpa [prefixWord, tailWord_3759418, baseEnd_3759418] using wordTrace_append hprefix tailTrace_3759418
  have hstable : (prefixWord ++ tailWord_3759418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3759418).length < 2 ^ (prefixWord ++ tailWord_3759418).sum := by decide
  have hdescent : baseEnd_3759418 < baseStart_3759418 := by decide
  rcases family_descends (prefixWord ++ tailWord_3759418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3759448 : List Nat := [2, 1, 2, 2, 1, 1, 3, 2, 1, 8]
def baseStart_3759448 : Nat := 118140960795 + 3759448 * 2 ^ 59
def prefixEnd_3759448 : Nat := 4983230072969 + 3 ^ 40 * 3759448 * 2
def baseEnd_3759448 : Nat := 643467939861370792036873

theorem tailTrace_3759448 : CollatzResearch.WordTrace tailWord_3759448 prefixEnd_3759448 643467939861370792036873 := by
  unfold tailWord_3759448
  simp only [CollatzResearch.WordTrace]
  refine ⟨68559166642084716723147499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91412222189446288964196665 68559166642084716723147499)
  ·
    refine ⟨102838749963127075084721249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68559166642084716723147499 102838749963127075084721249)
    ·
      refine ⟨77129062472345306313540937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102838749963127075084721249 77129062472345306313540937)
      ·
        refine ⟨57846796854258979735155703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77129062472345306313540937 57846796854258979735155703)
        ·
          refine ⟨86770195281388469602733555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57846796854258979735155703 86770195281388469602733555)
          ·
            refine ⟨130155292922082704404100333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86770195281388469602733555 130155292922082704404100333)
            ·
              refine ⟨48808234845781014151537625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 130155292922082704404100333 48808234845781014151537625)
              ·
                refine ⟨36606176134335760613653219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48808234845781014151537625 36606176134335760613653219)
                ·
                  refine ⟨54909264201503640920479829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36606176134335760613653219 54909264201503640920479829)
                  ·
                    refine ⟨643467939861370792036873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 54909264201503640920479829 643467939861370792036873)
                    ·
                      rfl

theorem cell23_3759448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 2, 1, 8].length) (baseStart_3759448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3759448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3759448 prefixEnd_3759448 := by exact prefixLift 3759448
  have htrace : WordTrace (prefixWord ++ tailWord_3759448) baseStart_3759448 baseEnd_3759448 := by
    simpa [prefixWord, tailWord_3759448, baseEnd_3759448] using wordTrace_append hprefix tailTrace_3759448
  have hstable : (prefixWord ++ tailWord_3759448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3759448).length < 2 ^ (prefixWord ++ tailWord_3759448).sum := by decide
  have hdescent : baseEnd_3759448 < baseStart_3759448 := by decide
  rcases family_descends (prefixWord ++ tailWord_3759448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3759453 : List Nat := [1, 4, 5, 1, 1, 1, 1, 3, 1, 2, 3]
def baseStart_3759453 : Nat := 118140960795 + 3759453 * 2 ^ 59
def prefixEnd_3759453 : Nat := 4983230072969 + 3 ^ 40 * 3759453 * 2
def baseEnd_3759453 : Nat := 1930406386987384856548097

theorem tailTrace_3759453 : CollatzResearch.WordTrace tailWord_3759453 prefixEnd_3759453 1930406386987384856548097 := by
  unfold tailWord_3759453
  simp only [CollatzResearch.WordTrace]
  refine ⟨137118515649151319300227013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91412343766100879533484675 137118515649151319300227013)
  ·
    refine ⟨25709721684215872368792565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137118515649151319300227013 25709721684215872368792565)
    ·
      refine ⟨2410286407895238034574303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25709721684215872368792565 2410286407895238034574303)
      ·
        refine ⟨3615429611842857051861455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2410286407895238034574303 3615429611842857051861455)
        ·
          refine ⟨5423144417764285577792183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3615429611842857051861455 5423144417764285577792183)
          ·
            refine ⟨8134716626646428366688275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5423144417764285577792183 8134716626646428366688275)
            ·
              refine ⟨12202074939969642550032413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8134716626646428366688275 12202074939969642550032413)
              ·
                refine ⟨4575778102488615956262155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12202074939969642550032413 4575778102488615956262155)
                ·
                  refine ⟨6863667153732923934393233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4575778102488615956262155 6863667153732923934393233)
                  ·
                    refine ⟨5147750365299692950794925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6863667153732923934393233 5147750365299692950794925)
                    ·
                      refine ⟨1930406386987384856548097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5147750365299692950794925 1930406386987384856548097)
                      ·
                        rfl

theorem cell23_3759453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_3759453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3759453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3759453 prefixEnd_3759453 := by exact prefixLift 3759453
  have htrace : WordTrace (prefixWord ++ tailWord_3759453) baseStart_3759453 baseEnd_3759453 := by
    simpa [prefixWord, tailWord_3759453, baseEnd_3759453] using wordTrace_append hprefix tailTrace_3759453
  have hstable : (prefixWord ++ tailWord_3759453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3759453).length < 2 ^ (prefixWord ++ tailWord_3759453).sum := by decide
  have hdescent : baseEnd_3759453 < baseStart_3759453 := by decide
  rcases family_descends (prefixWord ++ tailWord_3759453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3759459 : List Nat := [1, 1, 1, 5, 2, 3, 1, 3, 1, 3, 2]
def baseStart_3759459 : Nat := 118140960795 + 3759459 * 2 ^ 59
def prefixEnd_3759459 : Nat := 4983230072969 + 3 ^ 40 * 3759459 * 2
def baseEnd_3759459 : Nat := 1930409467871311833073069

theorem tailTrace_3759459 : CollatzResearch.WordTrace tailWord_3759459 prefixEnd_3759459 1930409467871311833073069 := by
  unfold tailWord_3759459
  simp only [CollatzResearch.WordTrace]
  refine ⟨137118734487129582324945431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91412489658086388216630287 137118734487129582324945431)
  ·
    refine ⟨205678101730694373487418147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137118734487129582324945431 205678101730694373487418147)
    ·
      refine ⟨308517152596041560231127221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205678101730694373487418147 308517152596041560231127221)
      ·
        refine ⟨28923483055878896271668177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 308517152596041560231127221 28923483055878896271668177)
        ·
          refine ⟨21692612291909172203751133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28923483055878896271668177 21692612291909172203751133)
          ·
            refine ⟨8134729609465939576406675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21692612291909172203751133 8134729609465939576406675)
            ·
              refine ⟨12202094414198909364610013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8134729609465939576406675 12202094414198909364610013)
              ·
                refine ⟨4575785405324591011728755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12202094414198909364610013 4575785405324591011728755)
                ·
                  refine ⟨6863678107986886517593133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4575785405324591011728755 6863678107986886517593133)
                  ·
                    refine ⟨2573879290495082444097425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6863678107986886517593133 2573879290495082444097425)
                    ·
                      refine ⟨1930409467871311833073069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2573879290495082444097425 1930409467871311833073069)
                      ·
                        rfl

theorem cell23_3759459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 3, 1, 3, 2].length) (baseStart_3759459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3759459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3759459 prefixEnd_3759459 := by exact prefixLift 3759459
  have htrace : WordTrace (prefixWord ++ tailWord_3759459) baseStart_3759459 baseEnd_3759459 := by
    simpa [prefixWord, tailWord_3759459, baseEnd_3759459] using wordTrace_append hprefix tailTrace_3759459
  have hstable : (prefixWord ++ tailWord_3759459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3759459).length < 2 ^ (prefixWord ++ tailWord_3759459).sum := by decide
  have hdescent : baseEnd_3759459 < baseStart_3759459 := by decide
  rcases family_descends (prefixWord ++ tailWord_3759459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3759485 : List Nat := [1, 4, 1, 1, 2, 2, 1, 3, 2, 2, 4]
def baseStart_3759485 : Nat := 118140960795 + 3759485 * 2 ^ 59
def prefixEnd_3759485 : Nat := 4983230072969 + 3 ^ 40 * 3759485 * 2
def baseEnd_3759485 : Nat := 1930422818368328731347949

theorem tailTrace_3759485 : CollatzResearch.WordTrace tailWord_3759485 prefixEnd_3759485 1930422818368328731347949 := by
  unfold tailWord_3759485
  simp only [CollatzResearch.WordTrace]
  refine ⟨137119682785035388765391909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91413121856690259176927939 137119682785035388765391909)
  ·
    refine ⟨25709940522194135393510983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137119682785035388765391909 25709940522194135393510983)
    ·
      refine ⟨38564910783291203090266475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25709940522194135393510983 38564910783291203090266475)
      ·
        refine ⟨57847366174936804635399713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38564910783291203090266475 57847366174936804635399713)
        ·
          refine ⟨43385524631202603476549785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57847366174936804635399713 43385524631202603476549785)
          ·
            refine ⟨32539143473401952607412339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43385524631202603476549785 32539143473401952607412339)
            ·
              refine ⟨48808715210102928911118509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32539143473401952607412339 48808715210102928911118509)
              ·
                refine ⟨18303268203788598341669441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48808715210102928911118509 18303268203788598341669441)
                ·
                  refine ⟨13727451152841448756252081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18303268203788598341669441 13727451152841448756252081)
                  ·
                    refine ⟨10295588364631086567189061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13727451152841448756252081 10295588364631086567189061)
                    ·
                      refine ⟨1930422818368328731347949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10295588364631086567189061 1930422818368328731347949)
                      ·
                        rfl

theorem cell23_3759485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 3, 2, 2, 4].length) (baseStart_3759485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3759485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3759485 prefixEnd_3759485 := by exact prefixLift 3759485
  have htrace : WordTrace (prefixWord ++ tailWord_3759485) baseStart_3759485 baseEnd_3759485 := by
    simpa [prefixWord, tailWord_3759485, baseEnd_3759485] using wordTrace_append hprefix tailTrace_3759485
  have hstable : (prefixWord ++ tailWord_3759485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3759485).length < 2 ^ (prefixWord ++ tailWord_3759485).sum := by decide
  have hdescent : baseEnd_3759485 < baseStart_3759485 := by decide
  rcases family_descends (prefixWord ++ tailWord_3759485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3759488 : List Nat := [2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 9]
def baseStart_3759488 : Nat := 118140960795 + 3759488 * 2 ^ 59
def prefixEnd_3759488 : Nat := 4983230072969 + 3 ^ 40 * 3759488 * 2
def baseEnd_3759488 : Nat := 1930424358810292219610435

theorem tailTrace_3759488 : CollatzResearch.WordTrace tailWord_3759488 prefixEnd_3759488 1930424358810292219610435 := by
  unfold tailWord_3759488
  simp only [CollatzResearch.WordTrace]
  refine ⟨68559896102012260138875559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91413194802683013518500745 68559896102012260138875559)
  ·
    refine ⟨102839844153018390208313339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68559896102012260138875559 102839844153018390208313339)
    ·
      refine ⟨154259766229527585312470009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102839844153018390208313339 154259766229527585312470009)
      ·
        refine ⟨115694824672145688984352507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154259766229527585312470009 115694824672145688984352507)
        ·
          refine ⟨173542237008218533476528761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115694824672145688984352507 173542237008218533476528761)
          ·
            refine ⟨130156677756163900107396571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173542237008218533476528761 130156677756163900107396571)
            ·
              refine ⟨195235016634245850161094857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130156677756163900107396571 195235016634245850161094857)
              ·
                refine ⟨146426262475684387620821143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 195235016634245850161094857 146426262475684387620821143)
                ·
                  refine ⟨219639393713526581431231715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 146426262475684387620821143 219639393713526581431231715)
                  ·
                    refine ⟨329459090570289872146847573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 219639393713526581431231715 329459090570289872146847573)
                    ·
                      refine ⟨1930424358810292219610435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 329459090570289872146847573 1930424358810292219610435)
                      ·
                        rfl

theorem cell23_3759488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 9].length) (baseStart_3759488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3759488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3759488 prefixEnd_3759488 := by exact prefixLift 3759488
  have htrace : WordTrace (prefixWord ++ tailWord_3759488) baseStart_3759488 baseEnd_3759488 := by
    simpa [prefixWord, tailWord_3759488, baseEnd_3759488] using wordTrace_append hprefix tailTrace_3759488
  have hstable : (prefixWord ++ tailWord_3759488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3759488).length < 2 ^ (prefixWord ++ tailWord_3759488).sum := by decide
  have hdescent : baseEnd_3759488 < baseStart_3759488 := by decide
  rcases family_descends (prefixWord ++ tailWord_3759488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3759495 : List Nat := [1, 1, 4, 2, 2, 2, 2, 2, 7]
def baseStart_3759495 : Nat := 118140960795 + 3759495 * 2 ^ 59
def prefixEnd_3759495 : Nat := 4983230072969 + 3 ^ 40 * 3759495 * 2
def baseEnd_3759495 : Nat := 214491994797208188024767

theorem tailTrace_3759495 : CollatzResearch.WordTrace tailWord_3759495 prefixEnd_3759495 214491994797208188024767 := by
  unfold tailWord_3759495
  simp only [CollatzResearch.WordTrace]
  refine ⟨137120047514999160473255939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91413365009999440315503959 137120047514999160473255939)
  ·
    refine ⟨205680071272498740709883909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137120047514999160473255939 205680071272498740709883909)
    ·
      refine ⟨38565013363593513883103233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 205680071272498740709883909 38565013363593513883103233)
      ·
        refine ⟨28923760022695135412327425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38565013363593513883103233 28923760022695135412327425)
        ·
          refine ⟨21692820017021351559245569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28923760022695135412327425 21692820017021351559245569)
          ·
            refine ⟨16269615012766013669434177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21692820017021351559245569 16269615012766013669434177)
            ·
              refine ⟨12202211259574510252075633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16269615012766013669434177 12202211259574510252075633)
              ·
                refine ⟨9151658444680882689056725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12202211259574510252075633 9151658444680882689056725)
                ·
                  refine ⟨214491994797208188024767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9151658444680882689056725 214491994797208188024767)
                  ·
                    rfl

theorem cell23_3759495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 2, 7].length) (baseStart_3759495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3759495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3759495 prefixEnd_3759495 := by exact prefixLift 3759495
  have htrace : WordTrace (prefixWord ++ tailWord_3759495) baseStart_3759495 baseEnd_3759495 := by
    simpa [prefixWord, tailWord_3759495, baseEnd_3759495] using wordTrace_append hprefix tailTrace_3759495
  have hstable : (prefixWord ++ tailWord_3759495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3759495).length < 2 ^ (prefixWord ++ tailWord_3759495).sum := by decide
  have hdescent : baseEnd_3759495 < baseStart_3759495 := by decide
  rcases family_descends (prefixWord ++ tailWord_3759495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3759562 : List Nat := [3, 1, 2, 1, 2, 3, 1, 3, 2, 1, 4]
def baseStart_3759562 : Nat := 118140960795 + 3759562 * 2 ^ 59
def prefixEnd_3759562 : Nat := 4983230072969 + 3 ^ 40 * 3759562 * 2
def baseEnd_3759562 : Nat := 1930462356378724930085095

theorem tailTrace_3759562 : CollatzResearch.WordTrace tailWord_3759562 prefixEnd_3759562 1930462356378724930085095 := by
  unfold tailWord_3759562
  simp only [CollatzResearch.WordTrace]
  refine ⟨34280622801439107728986235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91414994137170953943963293 34280622801439107728986235)
  ·
    refine ⟨51420934202158661593479353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34280622801439107728986235 51420934202158661593479353)
    ·
      refine ⟨38565700651618996195109515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51420934202158661593479353 38565700651618996195109515)
      ·
        refine ⟨57848550977428494292664273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38565700651618996195109515 57848550977428494292664273)
        ·
          refine ⟨43386413233071370719498205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57848550977428494292664273 43386413233071370719498205)
          ·
            refine ⟨16269904962401764019811827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43386413233071370719498205 16269904962401764019811827)
            ·
              refine ⟨24404857443602646029717741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16269904962401764019811827 24404857443602646029717741)
              ·
                refine ⟨9151821541350992261144153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24404857443602646029717741 9151821541350992261144153)
                ·
                  refine ⟨6863866156013244195858115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9151821541350992261144153 6863866156013244195858115)
                  ·
                    refine ⟨10295799234019866293787173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6863866156013244195858115 10295799234019866293787173)
                    ·
                      refine ⟨1930462356378724930085095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10295799234019866293787173 1930462356378724930085095)
                      ·
                        rfl

theorem cell23_3759562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 3, 2, 1, 4].length) (baseStart_3759562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3759562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3759562 prefixEnd_3759562 := by exact prefixLift 3759562
  have htrace : WordTrace (prefixWord ++ tailWord_3759562) baseStart_3759562 baseEnd_3759562 := by
    simpa [prefixWord, tailWord_3759562, baseEnd_3759562] using wordTrace_append hprefix tailTrace_3759562
  have hstable : (prefixWord ++ tailWord_3759562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3759562).length < 2 ^ (prefixWord ++ tailWord_3759562).sum := by decide
  have hdescent : baseEnd_3759562 < baseStart_3759562 := by decide
  rcases family_descends (prefixWord ++ tailWord_3759562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3759669 : List Nat := [1, 3, 3, 1, 1, 3, 1, 4, 1, 1, 4]
def baseStart_3759669 : Nat := 118140960795 + 3759669 * 2 ^ 59
def prefixEnd_3759669 : Nat := 4983230072969 + 3 ^ 40 * 3759669 * 2
def baseEnd_3759669 : Nat := 1930517298808756011447103

theorem tailTrace_3759669 : CollatzResearch.WordTrace tailWord_3759669 prefixEnd_3759669 1930517298808756011447103 := by
  unfold tailWord_3759669
  simp only [CollatzResearch.WordTrace]
  refine ⟨137126393816368788190090061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91417595877579192126726707 137126393816368788190090061)
  ·
    refine ⟨51422397681138295571283773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137126393816368788190090061 51422397681138295571283773)
    ·
      refine ⟨19283399130426860839231415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51422397681138295571283773 19283399130426860839231415)
      ·
        refine ⟨28925098695640291258847123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19283399130426860839231415 28925098695640291258847123)
        ·
          refine ⟨43387648043460436888270685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28925098695640291258847123 43387648043460436888270685)
          ·
            refine ⟨16270368016297663833101507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43387648043460436888270685 16270368016297663833101507)
            ·
              refine ⟨24405552024446495749652261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16270368016297663833101507 24405552024446495749652261)
              ·
                refine ⟨4576041004583717953059799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24405552024446495749652261 4576041004583717953059799)
                ·
                  refine ⟨6864061506875576929589699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4576041004583717953059799 6864061506875576929589699)
                  ·
                    refine ⟨10296092260313365394384549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6864061506875576929589699 10296092260313365394384549)
                    ·
                      refine ⟨1930517298808756011447103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10296092260313365394384549 1930517298808756011447103)
                      ·
                        rfl

theorem cell23_3759669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 4, 1, 1, 4].length) (baseStart_3759669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3759669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3759669 prefixEnd_3759669 := by exact prefixLift 3759669
  have htrace : WordTrace (prefixWord ++ tailWord_3759669) baseStart_3759669 baseEnd_3759669 := by
    simpa [prefixWord, tailWord_3759669, baseEnd_3759669] using wordTrace_append hprefix tailTrace_3759669
  have hstable : (prefixWord ++ tailWord_3759669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3759669).length < 2 ^ (prefixWord ++ tailWord_3759669).sum := by decide
  have hdescent : baseEnd_3759669 < baseStart_3759669 := by decide
  rcases family_descends (prefixWord ++ tailWord_3759669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3759692 : List Nat := [2, 2, 1, 3, 1, 5, 9]
def baseStart_3759692 : Nat := 118140960795 + 3759692 * 2 ^ 59
def prefixEnd_3759692 : Nat := 4983230072969 + 3 ^ 40 * 3759692 * 2
def baseEnd_3759692 : Nat := 23833692702022338536537

theorem tailTrace_3759692 : CollatzResearch.WordTrace tailWord_3759692 prefixEnd_3759692 23833692702022338536537 := by
  unfold tailWord_3759692
  simp only [CollatzResearch.WordTrace]
  refine ⟨68563616347642731559088665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91418155130190308745451553 68563616347642731559088665)
  ·
    refine ⟨51422712260732048669316499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68563616347642731559088665 51422712260732048669316499)
    ·
      refine ⟨77134068391098073003974749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51422712260732048669316499 77134068391098073003974749)
      ·
        refine ⟨28925275646661777376490531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77134068391098073003974749 28925275646661777376490531)
        ·
          refine ⟨43387913469992666064735797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28925275646661777376490531 43387913469992666064735797)
          ·
            refine ⟨4067616887811812443568981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43387913469992666064735797 4067616887811812443568981)
            ·
              refine ⟨23833692702022338536537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4067616887811812443568981 23833692702022338536537)
              ·
                rfl

theorem cell23_3759692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 9].length) (baseStart_3759692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3759692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3759692 prefixEnd_3759692 := by exact prefixLift 3759692
  have htrace : WordTrace (prefixWord ++ tailWord_3759692) baseStart_3759692 baseEnd_3759692 := by
    simpa [prefixWord, tailWord_3759692, baseEnd_3759692] using wordTrace_append hprefix tailTrace_3759692
  have hstable : (prefixWord ++ tailWord_3759692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3759692).length < 2 ^ (prefixWord ++ tailWord_3759692).sum := by decide
  have hdescent : baseEnd_3759692 < baseStart_3759692 := by decide
  rcases family_descends (prefixWord ++ tailWord_3759692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3759703 : List Nat := [1, 1, 3, 2, 2, 5, 1, 1, 3, 2, 2]
def baseStart_3759703 : Nat := 118140960795 + 3759703 * 2 ^ 59
def prefixEnd_3759703 : Nat := 4983230072969 + 3 ^ 40 * 3759703 * 2
def baseEnd_3759703 : Nat := 1930534757151008878421947

theorem tailTrace_3759703 : CollatzResearch.WordTrace tailWord_3759703 prefixEnd_3759703 1930534757151008878421947 := by
  unfold tailWord_3759703
  simp only [CollatzResearch.WordTrace]
  refine ⟨137127633898245611996827763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91418422598830407997885175 137127633898245611996827763)
  ·
    refine ⟨205691450847368417995241645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137127633898245611996827763 205691450847368417995241645)
    ·
      refine ⟨77134294067763156748215617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205691450847368417995241645 77134294067763156748215617)
      ·
        refine ⟨57850720550822367561161713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77134294067763156748215617 57850720550822367561161713)
        ·
          refine ⟨43388040413116775670871285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57850720550822367561161713 43388040413116775670871285)
          ·
            refine ⟨4067628788729697719144183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43388040413116775670871285 4067628788729697719144183)
            ·
              refine ⟨6101443183094546578716275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4067628788729697719144183 6101443183094546578716275)
              ·
                refine ⟨9152164774641819868074413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6101443183094546578716275 9152164774641819868074413)
                ·
                  refine ⟨3432061790490682450527905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9152164774641819868074413 3432061790490682450527905)
                  ·
                    refine ⟨2574046342868011837895929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3432061790490682450527905 2574046342868011837895929)
                    ·
                      refine ⟨1930534757151008878421947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2574046342868011837895929 1930534757151008878421947)
                      ·
                        rfl

theorem cell23_3759703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 1, 1, 3, 2, 2].length) (baseStart_3759703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3759703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3759703 prefixEnd_3759703 := by exact prefixLift 3759703
  have htrace : WordTrace (prefixWord ++ tailWord_3759703) baseStart_3759703 baseEnd_3759703 := by
    simpa [prefixWord, tailWord_3759703, baseEnd_3759703] using wordTrace_append hprefix tailTrace_3759703
  have hstable : (prefixWord ++ tailWord_3759703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3759703).length < 2 ^ (prefixWord ++ tailWord_3759703).sum := by decide
  have hdescent : baseEnd_3759703 < baseStart_3759703 := by decide
  rcases family_descends (prefixWord ++ tailWord_3759703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3759776 : List Nat := [2, 1, 1, 4, 3, 1, 1, 3, 1, 4, 2]
def baseStart_3759776 : Nat := 118140960795 + 3759776 * 2 ^ 59
def prefixEnd_3759776 : Nat := 4983230072969 + 3 ^ 40 * 3759776 * 2
def baseEnd_3759776 : Nat := 1930572241238787092809111

theorem tailTrace_3759776 : CollatzResearch.WordTrace tailWord_3759776 prefixEnd_3759776 1930572241238787092809111 := by
  unfold tailWord_3759776
  simp only [CollatzResearch.WordTrace]
  refine ⟨68565148213490572732117591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91420197617987430309490121 68565148213490572732117591)
  ·
    refine ⟨102847722320235859098176387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68565148213490572732117591 102847722320235859098176387)
    ·
      refine ⟨154271583480353788647264581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102847722320235859098176387 154271583480353788647264581)
      ·
        refine ⟨28925921902566335371362109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 154271583480353788647264581 28925921902566335371362109)
        ·
          refine ⟨10847220713462375764260791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28925921902566335371362109 10847220713462375764260791)
          ·
            refine ⟨16270831070193563646391187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10847220713462375764260791 16270831070193563646391187)
            ·
              refine ⟨24406246605290345469586781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16270831070193563646391187 24406246605290345469586781)
              ·
                refine ⟨9152342476983879551095043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24406246605290345469586781 9152342476983879551095043)
                ·
                  refine ⟨13728513715475819326642565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9152342476983879551095043 13728513715475819326642565)
                  ·
                    refine ⟨2574096321651716123745481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13728513715475819326642565 2574096321651716123745481)
                    ·
                      refine ⟨1930572241238787092809111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2574096321651716123745481 1930572241238787092809111)
                      ·
                        rfl

theorem cell23_3759776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 3, 1, 4, 2].length) (baseStart_3759776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3759776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3759776 prefixEnd_3759776 := by exact prefixLift 3759776
  have htrace : WordTrace (prefixWord ++ tailWord_3759776) baseStart_3759776 baseEnd_3759776 := by
    simpa [prefixWord, tailWord_3759776, baseEnd_3759776] using wordTrace_append hprefix tailTrace_3759776
  have hstable : (prefixWord ++ tailWord_3759776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3759776).length < 2 ^ (prefixWord ++ tailWord_3759776).sum := by decide
  have hdescent : baseEnd_3759776 < baseStart_3759776 := by decide
  rcases family_descends (prefixWord ++ tailWord_3759776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3759789 : List Nat := [1, 5, 2, 1, 1, 1, 1, 2, 1, 4, 4]
def baseStart_3759789 : Nat := 118140960795 + 3759789 * 2 ^ 59
def prefixEnd_3759789 : Nat := 4983230072969 + 3 ^ 40 * 3759789 * 2
def baseEnd_3759789 : Nat := 1930578916487295541946551

theorem tailTrace_3759789 : CollatzResearch.WordTrace tailWord_3759789 prefixEnd_3759789 1930578916487295541946551 := by
  unfold tailWord_3759789
  simp only [CollatzResearch.WordTrace]
  refine ⟨137130770575934048684458421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91420513717289365789638947 137130770575934048684458421)
  ·
    refine ⟨12856009741493817064167977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 137130770575934048684458421 12856009741493817064167977)
    ·
      refine ⟨9642007306120362798125983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12856009741493817064167977 9642007306120362798125983)
      ·
        refine ⟨14463010959180544197188975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9642007306120362798125983 14463010959180544197188975)
        ·
          refine ⟨21694516438770816295783463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14463010959180544197188975 21694516438770816295783463)
          ·
            refine ⟨32541774658156224443675195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21694516438770816295783463 32541774658156224443675195)
            ·
              refine ⟨48812661987234336665512793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32541774658156224443675195 48812661987234336665512793)
              ·
                refine ⟨36609496490425752499134595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48812661987234336665512793 36609496490425752499134595)
                ·
                  refine ⟨54914244735638628748701893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36609496490425752499134595 54914244735638628748701893)
                  ·
                    refine ⟨10296420887932242890381605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54914244735638628748701893 10296420887932242890381605)
                    ·
                      refine ⟨1930578916487295541946551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10296420887932242890381605 1930578916487295541946551)
                      ·
                        rfl

theorem cell23_3759789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_3759789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3759789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3759789 prefixEnd_3759789 := by exact prefixLift 3759789
  have htrace : WordTrace (prefixWord ++ tailWord_3759789) baseStart_3759789 baseEnd_3759789 := by
    simpa [prefixWord, tailWord_3759789, baseEnd_3759789] using wordTrace_append hprefix tailTrace_3759789
  have hstable : (prefixWord ++ tailWord_3759789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3759789).length < 2 ^ (prefixWord ++ tailWord_3759789).sum := by decide
  have hdescent : baseEnd_3759789 < baseStart_3759789 := by decide
  rcases family_descends (prefixWord ++ tailWord_3759789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3759797 : List Nat := [1, 3, 3, 3, 2, 2, 2, 1, 1, 3, 2]
def baseStart_3759797 : Nat := 118140960795 + 3759797 * 2 ^ 59
def prefixEnd_3759797 : Nat := 4983230072969 + 3 ^ 40 * 3759797 * 2
def baseEnd_3759797 : Nat := 1930583024332531510646515

theorem tailTrace_3759797 : CollatzResearch.WordTrace tailWord_3759797 prefixEnd_3759797 1930583024332531510646515 := by
  unfold tailWord_3759797
  simp only [CollatzResearch.WordTrace]
  refine ⟨137131062359905066050749645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91420708239936710700499763 137131062359905066050749645)
  ·
    refine ⟨51424148384964399769031117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137131062359905066050749645 51424148384964399769031117)
    ·
      refine ⟨19284055644361649913386669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51424148384964399769031117 19284055644361649913386669)
      ·
        refine ⟨7231520866635618717520001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19284055644361649913386669 7231520866635618717520001)
        ·
          refine ⟨5423640649976714038140001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7231520866635618717520001 5423640649976714038140001)
          ·
            refine ⟨4067730487482535528605001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5423640649976714038140001 4067730487482535528605001)
            ·
              refine ⟨3050797865611901646453751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4067730487482535528605001 3050797865611901646453751)
              ·
                refine ⟨4576196798417852469680627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3050797865611901646453751 4576196798417852469680627)
                ·
                  refine ⟨6864295197626778704520941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4576196798417852469680627 6864295197626778704520941)
                  ·
                    refine ⟨2574110699110042014195353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6864295197626778704520941 2574110699110042014195353)
                    ·
                      refine ⟨1930583024332531510646515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2574110699110042014195353 1930583024332531510646515)
                      ·
                        rfl

theorem cell23_3759797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 2, 1, 1, 3, 2].length) (baseStart_3759797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3759797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3759797 prefixEnd_3759797 := by exact prefixLift 3759797
  have htrace : WordTrace (prefixWord ++ tailWord_3759797) baseStart_3759797 baseEnd_3759797 := by
    simpa [prefixWord, tailWord_3759797, baseEnd_3759797] using wordTrace_append hprefix tailTrace_3759797
  have hstable : (prefixWord ++ tailWord_3759797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3759797).length < 2 ^ (prefixWord ++ tailWord_3759797).sum := by decide
  have hdescent : baseEnd_3759797 < baseStart_3759797 := by decide
  rcases family_descends (prefixWord ++ tailWord_3759797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3759819 : List Nat := [1, 1, 1, 1, 3, 2, 1, 3, 1, 7, 2]
def baseStart_3759819 : Nat := 118140960795 + 3759819 * 2 ^ 59
def prefixEnd_3759819 : Nat := 4983230072969 + 3 ^ 40 * 3759819 * 2
def baseEnd_3759819 : Nat := 1930594320906930424571413

theorem tailTrace_3759819 : CollatzResearch.WordTrace tailWord_3759819 prefixEnd_3759819 1930594320906930424571413 := by
  unfold tailWord_3759819
  simp only [CollatzResearch.WordTrace]
  refine ⟨137131864765825363808050511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91421243177216909205367007 137131864765825363808050511)
  ·
    refine ⟨205697797148738045712075767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137131864765825363808050511 205697797148738045712075767)
    ·
      refine ⟨308546695723107068568113651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205697797148738045712075767 308546695723107068568113651)
      ·
        refine ⟨462820043584660602852170477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308546695723107068568113651 462820043584660602852170477)
        ·
          refine ⟨173557516344247726069563929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 462820043584660602852170477 173557516344247726069563929)
          ·
            refine ⟨130168137258185794552172947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173557516344247726069563929 130168137258185794552172947)
            ·
              refine ⟨195252205887278691828259421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130168137258185794552172947 195252205887278691828259421)
              ·
                refine ⟨73219577207729509435597283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 195252205887278691828259421 73219577207729509435597283)
                ·
                  refine ⟨109829365811594264153395925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73219577207729509435597283 109829365811594264153395925)
                  ·
                    refine ⟨2574125761209240566095217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 109829365811594264153395925 2574125761209240566095217)
                    ·
                      refine ⟨1930594320906930424571413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2574125761209240566095217 1930594320906930424571413)
                      ·
                        rfl

theorem cell23_3759819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 7, 2].length) (baseStart_3759819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3759819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3759819 prefixEnd_3759819 := by exact prefixLift 3759819
  have htrace : WordTrace (prefixWord ++ tailWord_3759819) baseStart_3759819 baseEnd_3759819 := by
    simpa [prefixWord, tailWord_3759819, baseEnd_3759819] using wordTrace_append hprefix tailTrace_3759819
  have hstable : (prefixWord ++ tailWord_3759819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3759819).length < 2 ^ (prefixWord ++ tailWord_3759819).sum := by decide
  have hdescent : baseEnd_3759819 < baseStart_3759819 := by decide
  rcases family_descends (prefixWord ++ tailWord_3759819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3759826 : List Nat := [3, 2, 2, 2, 2, 1, 2, 1, 2, 3, 3]
def baseStart_3759826 : Nat := 118140960795 + 3759826 * 2 ^ 59
def prefixEnd_3759826 : Nat := 4983230072969 + 3 ^ 40 * 3759826 * 2
def baseEnd_3759826 : Nat := 1930597915271511897183881

theorem tailTrace_3759826 : CollatzResearch.WordTrace tailWord_3759826 prefixEnd_3759826 1930597915271511897183881 := by
  unfold tailWord_3759826
  simp only [CollatzResearch.WordTrace]
  refine ⟨34283030019200001000888833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91421413384533336002370221 34283030019200001000888833)
  ·
    refine ⟨25712272514400000750666625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34283030019200001000888833 25712272514400000750666625)
    ·
      refine ⟨19284204385800000562999969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25712272514400000750666625 19284204385800000562999969)
      ·
        refine ⟨14463153289350000422249977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19284204385800000562999969 14463153289350000422249977)
        ·
          refine ⟨10847364967012500316687483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14463153289350000422249977 10847364967012500316687483)
          ·
            refine ⟨16271047450518750475031225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10847364967012500316687483 16271047450518750475031225)
            ·
              refine ⟨12203285587889062856273419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16271047450518750475031225 12203285587889062856273419)
              ·
                refine ⟨18304928381833594284410129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12203285587889062856273419 18304928381833594284410129)
                ·
                  refine ⟨13728696286375195713307597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18304928381833594284410129 13728696286375195713307597)
                  ·
                    refine ⟨5148261107390698392490349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13728696286375195713307597 5148261107390698392490349)
                    ·
                      refine ⟨1930597915271511897183881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5148261107390698392490349 1930597915271511897183881)
                      ·
                        rfl

theorem cell23_3759826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 1, 2, 3, 3].length) (baseStart_3759826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3759826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3759826 prefixEnd_3759826 := by exact prefixLift 3759826
  have htrace : WordTrace (prefixWord ++ tailWord_3759826) baseStart_3759826 baseEnd_3759826 := by
    simpa [prefixWord, tailWord_3759826, baseEnd_3759826] using wordTrace_append hprefix tailTrace_3759826
  have hstable : (prefixWord ++ tailWord_3759826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3759826).length < 2 ^ (prefixWord ++ tailWord_3759826).sum := by decide
  have hdescent : baseEnd_3759826 < baseStart_3759826 := by decide
  rcases family_descends (prefixWord ++ tailWord_3759826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3759849 : List Nat := [1, 2, 1, 1, 1, 2, 3, 5, 2, 1, 4]
def baseStart_3759849 : Nat := 118140960795 + 3759849 * 2 ^ 59
def prefixEnd_3759849 : Nat := 4983230072969 + 3 ^ 40 * 3759849 * 2
def baseEnd_3759849 : Nat := 1930609725326565307196275

theorem tailTrace_3759849 : CollatzResearch.WordTrace tailWord_3759849 prefixEnd_3759849 1930609725326565307196275 := by
  unfold tailWord_3759849
  simp only [CollatzResearch.WordTrace]
  refine ⟨137132958955716678931642601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91421972637144452621095067 137132958955716678931642601)
  ·
    refine ⟨102849719216787509198731951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137132958955716678931642601 102849719216787509198731951)
    ·
      refine ⟨154274578825181263798097927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102849719216787509198731951 154274578825181263798097927)
      ·
        refine ⟨231411868237771895697146891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154274578825181263798097927 231411868237771895697146891)
        ·
          refine ⟨347117802356657843545720337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231411868237771895697146891 347117802356657843545720337)
          ·
            refine ⟨260338351767493382659290253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 347117802356657843545720337 260338351767493382659290253)
            ·
              refine ⟨97626881912810018497233845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 260338351767493382659290253 97626881912810018497233845)
              ·
                refine ⟨9152520179325939234115673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 97626881912810018497233845 9152520179325939234115673)
                ·
                  refine ⟨6864390134494454425586755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9152520179325939234115673 6864390134494454425586755)
                  ·
                    refine ⟨10296585201741681638380133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6864390134494454425586755 10296585201741681638380133)
                    ·
                      refine ⟨1930609725326565307196275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10296585201741681638380133 1930609725326565307196275)
                      ·
                        rfl

theorem cell23_3759849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 5, 2, 1, 4].length) (baseStart_3759849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3759849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3759849 prefixEnd_3759849 := by exact prefixLift 3759849
  have htrace : WordTrace (prefixWord ++ tailWord_3759849) baseStart_3759849 baseEnd_3759849 := by
    simpa [prefixWord, tailWord_3759849, baseEnd_3759849] using wordTrace_append hprefix tailTrace_3759849
  have hstable : (prefixWord ++ tailWord_3759849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3759849).length < 2 ^ (prefixWord ++ tailWord_3759849).sum := by decide
  have hdescent : baseEnd_3759849 < baseStart_3759849 := by decide
  rcases family_descends (prefixWord ++ tailWord_3759849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3759859 : List Nat := [1, 1, 1, 2, 2, 3, 2, 2, 5, 4]
def baseStart_3759859 : Nat := 118140960795 + 3759859 * 2 ^ 59
def prefixEnd_3759859 : Nat := 4983230072969 + 3 ^ 40 * 3759859 * 2
def baseEnd_3759859 : Nat := 643538286711036756023743

theorem tailTrace_3759859 : CollatzResearch.WordTrace tailWord_3759859 prefixEnd_3759859 643538286711036756023743 := by
  unfold tailWord_3759859
  simp only [CollatzResearch.WordTrace]
  refine ⟨137133323685680450639506631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91422215790453633759671087 137133323685680450639506631)
  ·
    refine ⟨205699985528520675959259947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137133323685680450639506631 205699985528520675959259947)
    ·
      refine ⟨308549978292781013938889921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205699985528520675959259947 308549978292781013938889921)
      ·
        refine ⟨231412483719585760454167441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 308549978292781013938889921 231412483719585760454167441)
        ·
          refine ⟨173559362789689320340625581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231412483719585760454167441 173559362789689320340625581)
          ·
            refine ⟨65084761046133495127734593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 173559362789689320340625581 65084761046133495127734593)
            ·
              refine ⟨48813570784600121345800945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65084761046133495127734593 48813570784600121345800945)
              ·
                refine ⟨36610178088450091009350709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48813570784600121345800945 36610178088450091009350709)
                ·
                  refine ⟨3432204195792196032126629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36610178088450091009350709 3432204195792196032126629)
                  ·
                    refine ⟨643538286711036756023743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3432204195792196032126629 643538286711036756023743)
                    ·
                      rfl

theorem cell23_3759859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 2, 5, 4].length) (baseStart_3759859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3759859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3759859 prefixEnd_3759859 := by exact prefixLift 3759859
  have htrace : WordTrace (prefixWord ++ tailWord_3759859) baseStart_3759859 baseEnd_3759859 := by
    simpa [prefixWord, tailWord_3759859, baseEnd_3759859] using wordTrace_append hprefix tailTrace_3759859
  have hstable : (prefixWord ++ tailWord_3759859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3759859).length < 2 ^ (prefixWord ++ tailWord_3759859).sum := by decide
  have hdescent : baseEnd_3759859 < baseStart_3759859 := by decide
  rcases family_descends (prefixWord ++ tailWord_3759859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3759869 : List Nat := [1, 4, 1, 1, 1, 1, 2, 2, 3, 4, 3]
def baseStart_3759869 : Nat := 118140960795 + 3759869 * 2 ^ 59
def prefixEnd_3759869 : Nat := 4983230072969 + 3 ^ 40 * 3759869 * 2
def baseEnd_3759869 : Nat := 1930619994939655228946183

theorem tailTrace_3759869 : CollatzResearch.WordTrace tailWord_3759869 prefixEnd_3759869 1930619994939655228946183 := by
  unfold tailWord_3759869
  simp only [CollatzResearch.WordTrace]
  refine ⟨137133688415644222347370661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91422458943762814898247107 137133688415644222347370661)
  ·
    refine ⟨25712566577933291690131999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137133688415644222347370661 25712566577933291690131999)
    ·
      refine ⟨38568849866899937535197999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25712566577933291690131999 38568849866899937535197999)
      ·
        refine ⟨57853274800349906302796999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38568849866899937535197999 57853274800349906302796999)
        ·
          refine ⟨86779912200524859454195499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57853274800349906302796999 86779912200524859454195499)
          ·
            refine ⟨130169868300787289181293249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86779912200524859454195499 130169868300787289181293249)
            ·
              refine ⟨97627401225590466885969937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130169868300787289181293249 97627401225590466885969937)
              ·
                refine ⟨73220550919192850164477453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97627401225590466885969937 73220550919192850164477453)
                ·
                  refine ⟨27457706594697318811679045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73220550919192850164477453 27457706594697318811679045)
                  ·
                    refine ⟨5148319986505747277189821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27457706594697318811679045 5148319986505747277189821)
                    ·
                      refine ⟨1930619994939655228946183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5148319986505747277189821 1930619994939655228946183)
                      ·
                        rfl

theorem cell23_3759869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 3, 4, 3].length) (baseStart_3759869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3759869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3759869 prefixEnd_3759869 := by exact prefixLift 3759869
  have htrace : WordTrace (prefixWord ++ tailWord_3759869) baseStart_3759869 baseEnd_3759869 := by
    simpa [prefixWord, tailWord_3759869, baseEnd_3759869] using wordTrace_append hprefix tailTrace_3759869
  have hstable : (prefixWord ++ tailWord_3759869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3759869).length < 2 ^ (prefixWord ++ tailWord_3759869).sum := by decide
  have hdescent : baseEnd_3759869 < baseStart_3759869 := by decide
  rcases family_descends (prefixWord ++ tailWord_3759869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3759878 : List Nat := [6, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2]
def baseStart_3759878 : Nat := 118140960795 + 3759878 * 2 ^ 59
def prefixEnd_3759878 : Nat := 4983230072969 + 3 ^ 40 * 3759878 * 2
def baseEnd_3759878 : Nat := 1930624616265545693733643

theorem tailTrace_3759878 : CollatzResearch.WordTrace tailWord_3759878 prefixEnd_3759878 1930624616265545693733643 := by
  unfold tailWord_3759878
  simp only [CollatzResearch.WordTrace]
  refine ⟨4285438021019113027639009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 91422677781741077922965525 4285438021019113027639009)
  ·
    refine ⟨3214078515764334770729257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4285438021019113027639009 3214078515764334770729257)
    ·
      refine ⟨2410558886823251078046943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3214078515764334770729257 2410558886823251078046943)
      ·
        refine ⟨3615838330234876617070415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2410558886823251078046943 3615838330234876617070415)
        ·
          refine ⟨5423757495352314925605623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3615838330234876617070415 5423757495352314925605623)
          ·
            refine ⟨8135636243028472388408435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5423757495352314925605623 8135636243028472388408435)
            ·
              refine ⟨12203454364542708582612653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8135636243028472388408435 12203454364542708582612653)
              ·
                refine ⟨4576295386703515718479745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12203454364542708582612653 4576295386703515718479745)
                ·
                  refine ⟨3432221540027636788859809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4576295386703515718479745 3432221540027636788859809)
                  ·
                    refine ⟨2574166155020727591644857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3432221540027636788859809 2574166155020727591644857)
                    ·
                      refine ⟨1930624616265545693733643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2574166155020727591644857 1930624616265545693733643)
                      ·
                        rfl

theorem cell23_3759878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_3759878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3759878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3759878 prefixEnd_3759878 := by exact prefixLift 3759878
  have htrace : WordTrace (prefixWord ++ tailWord_3759878) baseStart_3759878 baseEnd_3759878 := by
    simpa [prefixWord, tailWord_3759878, baseEnd_3759878] using wordTrace_append hprefix tailTrace_3759878
  have hstable : (prefixWord ++ tailWord_3759878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3759878).length < 2 ^ (prefixWord ++ tailWord_3759878).sum := by decide
  have hdescent : baseEnd_3759878 < baseStart_3759878 := by decide
  rcases family_descends (prefixWord ++ tailWord_3759878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3759970 : List Nat := [3, 3, 2, 1, 2, 1, 4, 1, 1, 5]
def baseStart_3759970 : Nat := 118140960795 + 3759970 * 2 ^ 59
def prefixEnd_3759970 : Nat := 4983230072969 + 3 ^ 40 * 3759970 * 2
def baseEnd_3759970 : Nat := 643557285495253111261073

theorem tailTrace_3759970 : CollatzResearch.WordTrace tailWord_3759970 prefixEnd_3759970 643557285495253111261073 := by
  unfold tailWord_3759970
  simp only [CollatzResearch.WordTrace]
  refine ⟨34284343047069579149199341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91424914792185544397864909 34284343047069579149199341)
  ·
    refine ⟨12856628642651092180949753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34284343047069579149199341 12856628642651092180949753)
    ·
      refine ⟨9642471481988319135712315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12856628642651092180949753 9642471481988319135712315)
      ·
        refine ⟨14463707222982478703568473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9642471481988319135712315 14463707222982478703568473)
        ·
          refine ⟨10847780417236859027676355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14463707222982478703568473 10847780417236859027676355)
          ·
            refine ⟨16271670625855288541514533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10847780417236859027676355 16271670625855288541514533)
            ·
              refine ⟨3050938242347866601533975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16271670625855288541514533 3050938242347866601533975)
              ·
                refine ⟨4576407363521799902300963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3050938242347866601533975 4576407363521799902300963)
                ·
                  refine ⟨6864611045282699853451445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4576407363521799902300963 6864611045282699853451445)
                  ·
                    refine ⟨643557285495253111261073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6864611045282699853451445 643557285495253111261073)
                    ·
                      rfl

theorem cell23_3759970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 4, 1, 1, 5].length) (baseStart_3759970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3759970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3759970 prefixEnd_3759970 := by exact prefixLift 3759970
  have htrace : WordTrace (prefixWord ++ tailWord_3759970) baseStart_3759970 baseEnd_3759970 := by
    simpa [prefixWord, tailWord_3759970, baseEnd_3759970] using wordTrace_append hprefix tailTrace_3759970
  have hstable : (prefixWord ++ tailWord_3759970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3759970).length < 2 ^ (prefixWord ++ tailWord_3759970).sum := by decide
  have hdescent : baseEnd_3759970 < baseStart_3759970 := by decide
  rcases family_descends (prefixWord ++ tailWord_3759970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3759973 : List Nat := [1, 3, 1, 3, 1, 1, 1, 1, 7, 2, 2]
def baseStart_3759973 : Nat := 118140960795 + 3759973 * 2 ^ 59
def prefixEnd_3759973 : Nat := 4983230072969 + 3 ^ 40 * 3759973 * 2
def baseEnd_3759973 : Nat := 1930673396927722822045705

theorem tailTrace_3759973 : CollatzResearch.WordTrace tailWord_3759973 prefixEnd_3759973 1930673396927722822045705 := by
  unfold tailWord_3759973
  simp only [CollatzResearch.WordTrace]
  refine ⟨137137481607267448109156573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91424987738178298739437715 137137481607267448109156573)
  ·
    refine ⟨51426555602725293040933715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137137481607267448109156573 51426555602725293040933715)
    ·
      refine ⟨77139833404087939561400573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51426555602725293040933715 77139833404087939561400573)
      ·
        refine ⟨28927437526532977335525215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77139833404087939561400573 28927437526532977335525215)
        ·
          refine ⟨43391156289799466003287823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28927437526532977335525215 43391156289799466003287823)
          ·
            refine ⟨65086734434699199004931735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43391156289799466003287823 65086734434699199004931735)
            ·
              refine ⟨97630101652048798507397603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65086734434699199004931735 97630101652048798507397603)
              ·
                refine ⟨146445152478073197761096405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97630101652048798507397603 146445152478073197761096405)
                ·
                  refine ⟨3432308261204840572525697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 146445152478073197761096405 3432308261204840572525697)
                  ·
                    refine ⟨2574231195903630429394273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3432308261204840572525697 2574231195903630429394273)
                    ·
                      refine ⟨1930673396927722822045705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2574231195903630429394273 1930673396927722822045705)
                      ·
                        rfl

theorem cell23_3759973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 7, 2, 2].length) (baseStart_3759973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3759973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3759973 prefixEnd_3759973 := by exact prefixLift 3759973
  have htrace : WordTrace (prefixWord ++ tailWord_3759973) baseStart_3759973 baseEnd_3759973 := by
    simpa [prefixWord, tailWord_3759973, baseEnd_3759973] using wordTrace_append hprefix tailTrace_3759973
  have hstable : (prefixWord ++ tailWord_3759973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3759973).length < 2 ^ (prefixWord ++ tailWord_3759973).sum := by decide
  have hdescent : baseEnd_3759973 < baseStart_3759973 := by decide
  rcases family_descends (prefixWord ++ tailWord_3759973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3759976 : List Nat := [2, 1, 4, 2, 1, 1, 2, 3, 1, 1, 5]
def baseStart_3759976 : Nat := 118140960795 + 3759976 * 2 ^ 59
def prefixEnd_3759976 : Nat := 4983230072969 + 3 ^ 40 * 3759976 * 2
def baseEnd_3759976 : Nat := 1930674937369686310308191

theorem tailTrace_3759976 : CollatzResearch.WordTrace tailWord_3759976 prefixEnd_3759976 1930674937369686310308191 := by
  unfold tailWord_3759976
  simp only [CollatzResearch.WordTrace]
  refine ⟨68568795513128289810757891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91425060684171053081010521 68568795513128289810757891)
  ·
    refine ⟨102853193269692434716136837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68568795513128289810757891 102853193269692434716136837)
    ·
      refine ⟨19284973738067331509275657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102853193269692434716136837 19284973738067331509275657)
      ·
        refine ⟨14463730303550498631956743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19284973738067331509275657 14463730303550498631956743)
        ·
          refine ⟨21695595455325747947935115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14463730303550498631956743 21695595455325747947935115)
          ·
            refine ⟨32543393182988621921902673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21695595455325747947935115 32543393182988621921902673)
            ·
              refine ⟨24407544887241466441427005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32543393182988621921902673 24407544887241466441427005)
              ·
                refine ⟨9152829332715549915535127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24407544887241466441427005 9152829332715549915535127)
                ·
                  refine ⟨13729243999073324873302691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9152829332715549915535127 13729243999073324873302691)
                  ·
                    refine ⟨20593865998609987309954037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13729243999073324873302691 20593865998609987309954037)
                    ·
                      refine ⟨1930674937369686310308191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20593865998609987309954037 1930674937369686310308191)
                      ·
                        rfl

theorem cell23_3759976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_3759976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3759976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3759976 prefixEnd_3759976 := by exact prefixLift 3759976
  have htrace : WordTrace (prefixWord ++ tailWord_3759976) baseStart_3759976 baseEnd_3759976 := by
    simpa [prefixWord, tailWord_3759976, baseEnd_3759976] using wordTrace_append hprefix tailTrace_3759976
  have hstable : (prefixWord ++ tailWord_3759976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3759976).length < 2 ^ (prefixWord ++ tailWord_3759976).sum := by decide
  have hdescent : baseEnd_3759976 < baseStart_3759976 := by decide
  rcases family_descends (prefixWord ++ tailWord_3759976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3760003 : List Nat := [1, 1, 1, 3, 4, 4, 1, 1, 1, 2, 4]
def baseStart_3760003 : Nat := 118140960795 + 3760003 * 2 ^ 59
def prefixEnd_3760003 : Nat := 4983230072969 + 3 ^ 40 * 3760003 * 2
def baseEnd_3760003 : Nat := 1930688801347357704670567

theorem tailTrace_3760003 : CollatzResearch.WordTrace tailWord_3760003 prefixEnd_3760003 1930688801347357704670567 := by
  unfold tailWord_3760003
  simp only [CollatzResearch.WordTrace]
  refine ⟨137138575797158763232748663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91425717198105842155165775 137138575797158763232748663)
  ·
    refine ⟨205707863695738144849122995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137138575797158763232748663 205707863695738144849122995)
    ·
      refine ⟨308561795543607217273684493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205707863695738144849122995 308561795543607217273684493)
      ·
        refine ⟨115710673328852706477631685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 308561795543607217273684493 115710673328852706477631685)
        ·
          refine ⟨21695751249159882464555941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115710673328852706477631685 21695751249159882464555941)
          ·
            refine ⟨4067953359217477962104239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21695751249159882464555941 4067953359217477962104239)
            ·
              refine ⟨6101930038826216943156359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4067953359217477962104239 6101930038826216943156359)
              ·
                refine ⟨9152895058239325414734539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6101930038826216943156359 9152895058239325414734539)
                ·
                  refine ⟨13729342587358988122101809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9152895058239325414734539 13729342587358988122101809)
                  ·
                    refine ⟨10297006940519241091576357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13729342587358988122101809 10297006940519241091576357)
                    ·
                      refine ⟨1930688801347357704670567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10297006940519241091576357 1930688801347357704670567)
                      ·
                        rfl

theorem cell23_3760003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 1, 1, 1, 2, 4].length) (baseStart_3760003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3760003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3760003 prefixEnd_3760003 := by exact prefixLift 3760003
  have htrace : WordTrace (prefixWord ++ tailWord_3760003) baseStart_3760003 baseEnd_3760003 := by
    simpa [prefixWord, tailWord_3760003, baseEnd_3760003] using wordTrace_append hprefix tailTrace_3760003
  have hstable : (prefixWord ++ tailWord_3760003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3760003).length < 2 ^ (prefixWord ++ tailWord_3760003).sum := by decide
  have hdescent : baseEnd_3760003 < baseStart_3760003 := by decide
  rcases family_descends (prefixWord ++ tailWord_3760003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3760023 : List Nat := [1, 1, 3, 3, 1, 3, 1, 2, 4, 1, 3]
def baseStart_3760023 : Nat := 118140960795 + 3760023 * 2 ^ 59
def prefixEnd_3760023 : Nat := 4983230072969 + 3 ^ 40 * 3760023 * 2
def baseEnd_3760023 : Nat := 1930699070960447626420475

theorem tailTrace_3760023 : CollatzResearch.WordTrace tailWord_3760023 prefixEnd_3760023 1930699070960447626420475 := by
  unfold tailWord_3760023
  simp only [CollatzResearch.WordTrace]
  refine ⟨137139305257086306648476723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91426203504724204432317815 137139305257086306648476723)
  ·
    refine ⟨205708957885629459972715085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137139305257086306648476723 205708957885629459972715085)
    ·
      refine ⟨77140859207111047489768157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205708957885629459972715085 77140859207111047489768157)
      ·
        refine ⟨28927822202666642808663059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77140859207111047489768157 28927822202666642808663059)
        ·
          refine ⟨43391733303999964212994589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28927822202666642808663059 43391733303999964212994589)
          ·
            refine ⟨16271899988999986579872971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43391733303999964212994589 16271899988999986579872971)
            ·
              refine ⟨24407849983499979869809457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16271899988999986579872971 24407849983499979869809457)
              ·
                refine ⟨18305887487624984902357093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24407849983499979869809457 18305887487624984902357093)
                ·
                  refine ⟨3432353903929684669191955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18305887487624984902357093 3432353903929684669191955)
                  ·
                    refine ⟨5148530855894527003787933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3432353903929684669191955 5148530855894527003787933)
                    ·
                      refine ⟨1930699070960447626420475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5148530855894527003787933 1930699070960447626420475)
                      ·
                        rfl

theorem cell23_3760023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 2, 4, 1, 3].length) (baseStart_3760023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3760023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3760023 prefixEnd_3760023 := by exact prefixLift 3760023
  have htrace : WordTrace (prefixWord ++ tailWord_3760023) baseStart_3760023 baseEnd_3760023 := by
    simpa [prefixWord, tailWord_3760023, baseEnd_3760023] using wordTrace_append hprefix tailTrace_3760023
  have hstable : (prefixWord ++ tailWord_3760023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3760023).length < 2 ^ (prefixWord ++ tailWord_3760023).sum := by decide
  have hdescent : baseEnd_3760023 < baseStart_3760023 := by decide
  rcases family_descends (prefixWord ++ tailWord_3760023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3760030 : List Nat := [4, 3, 1, 3, 1, 2, 9]
def baseStart_3760030 : Nat := 118140960795 + 3760030 * 2 ^ 59
def prefixEnd_3760030 : Nat := 4983230072969 + 3 ^ 40 * 3760030 * 2
def baseEnd_3760030 : Nat := 23835835374383075296703

theorem tailTrace_3760030 : CollatzResearch.WordTrace tailWord_3760030 prefixEnd_3760030 23835835374383075296703 := by
  unfold tailWord_3760030
  simp only [CollatzResearch.WordTrace]
  refine ⟨17142445071007618355497693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91426373712040631229321029 17142445071007618355497693)
  ·
    refine ⟨6428416901627856883311635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17142445071007618355497693 6428416901627856883311635)
    ·
      refine ⟨9642625352441785324967453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6428416901627856883311635 9642625352441785324967453)
      ·
        refine ⟨3615984507165669496862795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9642625352441785324967453 3615984507165669496862795)
        ·
          refine ⟨5423976760748504245294193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3615984507165669496862795 5423976760748504245294193)
          ·
            refine ⟨4067982570561378183970645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5423976760748504245294193 4067982570561378183970645)
            ·
              refine ⟨23835835374383075296703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4067982570561378183970645 23835835374383075296703)
              ·
                rfl

theorem cell23_3760030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 9].length) (baseStart_3760030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3760030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3760030 prefixEnd_3760030 := by exact prefixLift 3760030
  have htrace : WordTrace (prefixWord ++ tailWord_3760030) baseStart_3760030 baseEnd_3760030 := by
    simpa [prefixWord, tailWord_3760030, baseEnd_3760030] using wordTrace_append hprefix tailTrace_3760030
  have hstable : (prefixWord ++ tailWord_3760030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3760030).length < 2 ^ (prefixWord ++ tailWord_3760030).sum := by decide
  have hdescent : baseEnd_3760030 < baseStart_3760030 := by decide
  rcases family_descends (prefixWord ++ tailWord_3760030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3760063 : List Nat := [1, 1, 2, 2, 2, 1, 4, 3, 1, 4, 2]
def baseStart_3760063 : Nat := 118140960795 + 3760063 * 2 ^ 59
def prefixEnd_3760063 : Nat := 4983230072969 + 3 ^ 40 * 3760063 * 2
def baseEnd_3760063 : Nat := 1930719610186627469920291

theorem tailTrace_3760063 : CollatzResearch.WordTrace tailWord_3760063 prefixEnd_3760063 1930719610186627469920291 := by
  unfold tailWord_3760063
  simp only [CollatzResearch.WordTrace]
  refine ⟨137140764176941393479932843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91427176117960928986621895 137140764176941393479932843)
  ·
    refine ⟨205711146265412090219899265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137140764176941393479932843 205711146265412090219899265)
    ·
      refine ⟨154283359699059067664924449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205711146265412090219899265 154283359699059067664924449)
      ·
        refine ⟨115712519774294300748693337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154283359699059067664924449 115712519774294300748693337)
        ·
          refine ⟨86784389830720725561520003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115712519774294300748693337 86784389830720725561520003)
          ·
            refine ⟨130176584746081088342280005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86784389830720725561520003 130176584746081088342280005)
            ·
              refine ⟨24408109639890204064177501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 130176584746081088342280005 24408109639890204064177501)
              ·
                refine ⟨9153041114958826524066563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24408109639890204064177501 9153041114958826524066563)
                ·
                  refine ⟨13729561672438239786099845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9153041114958826524066563 13729561672438239786099845)
                  ·
                    refine ⟨2574292813582169959893721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13729561672438239786099845 2574292813582169959893721)
                    ·
                      refine ⟨1930719610186627469920291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2574292813582169959893721 1930719610186627469920291)
                      ·
                        rfl

theorem cell23_3760063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 3, 1, 4, 2].length) (baseStart_3760063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3760063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3760063 prefixEnd_3760063 := by exact prefixLift 3760063
  have htrace : WordTrace (prefixWord ++ tailWord_3760063) baseStart_3760063 baseEnd_3760063 := by
    simpa [prefixWord, tailWord_3760063, baseEnd_3760063] using wordTrace_append hprefix tailTrace_3760063
  have hstable : (prefixWord ++ tailWord_3760063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3760063).length < 2 ^ (prefixWord ++ tailWord_3760063).sum := by decide
  have hdescent : baseEnd_3760063 < baseStart_3760063 := by decide
  rcases family_descends (prefixWord ++ tailWord_3760063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3760092 : List Nat := [2, 2, 6, 1, 2, 1, 2, 2, 1, 2, 2]
def baseStart_3760092 : Nat := 118140960795 + 3760092 * 2 ^ 59
def prefixEnd_3760092 : Nat := 4983230072969 + 3 ^ 40 * 3760092 * 2
def baseEnd_3760092 : Nat := 1930734501125607856457659

theorem tailTrace_3760092 : CollatzResearch.WordTrace tailWord_3760092 prefixEnd_3760092 1930734501125607856457659 := by
  unfold tailWord_3760092
  simp only [CollatzResearch.WordTrace]
  refine ⟨68570910946918165716369265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91427881262557554288492353 68570910946918165716369265)
  ·
    refine ⟨51428183210188624287276949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68570910946918165716369265 51428183210188624287276949)
    ·
      refine ⟨2410696087977591763466107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 51428183210188624287276949 2410696087977591763466107)
      ·
        refine ⟨3616044131966387645199161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2410696087977591763466107 3616044131966387645199161)
        ·
          refine ⟨2712033098974790733899371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3616044131966387645199161 2712033098974790733899371)
          ·
            refine ⟨4068049648462186100849057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2712033098974790733899371 4068049648462186100849057)
            ·
              refine ⟨3051037236346639575636793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4068049648462186100849057 3051037236346639575636793)
              ·
                refine ⟨2288277927259979681727595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3051037236346639575636793 2288277927259979681727595)
                ·
                  refine ⟨3432416890889969522591393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2288277927259979681727595 3432416890889969522591393)
                  ·
                    refine ⟨2574312668167477141943545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3432416890889969522591393 2574312668167477141943545)
                    ·
                      refine ⟨1930734501125607856457659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2574312668167477141943545 1930734501125607856457659)
                      ·
                        rfl

theorem cell23_3760092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_3760092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3760092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3760092 prefixEnd_3760092 := by exact prefixLift 3760092
  have htrace : WordTrace (prefixWord ++ tailWord_3760092) baseStart_3760092 baseEnd_3760092 := by
    simpa [prefixWord, tailWord_3760092, baseEnd_3760092] using wordTrace_append hprefix tailTrace_3760092
  have hstable : (prefixWord ++ tailWord_3760092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3760092).length < 2 ^ (prefixWord ++ tailWord_3760092).sum := by decide
  have hdescent : baseEnd_3760092 < baseStart_3760092 := by decide
  rcases family_descends (prefixWord ++ tailWord_3760092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3760096 : List Nat := [2, 1, 1, 3, 1, 1, 1, 2, 3, 5, 3]
def baseStart_3760096 : Nat := 118140960795 + 3760096 * 2 ^ 59
def prefixEnd_3760096 : Nat := 4983230072969 + 3 ^ 40 * 3760096 * 2
def baseEnd_3760096 : Nat := 1930736555048225840807639

theorem tailTrace_3760096 : CollatzResearch.WordTrace tailWord_3760096 prefixEnd_3760096 1930736555048225840807639 := by
  unfold tailWord_3760096
  simp only [CollatzResearch.WordTrace]
  refine ⟨68570983892910920057942071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91427978523881226743922761 68570983892910920057942071)
  ·
    refine ⟨102856475839366380086913107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68570983892910920057942071 102856475839366380086913107)
    ·
      refine ⟨154284713759049570130369661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102856475839366380086913107 154284713759049570130369661)
      ·
        refine ⟨57856767659643588798888623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154284713759049570130369661 57856767659643588798888623)
        ·
          refine ⟨86785151489465383198332935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57856767659643588798888623 86785151489465383198332935)
          ·
            refine ⟨130177727234198074797499403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86785151489465383198332935 130177727234198074797499403)
            ·
              refine ⟨195266590851297112196249105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130177727234198074797499403 195266590851297112196249105)
              ·
                refine ⟨146449943138472834147186829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 195266590851297112196249105 146449943138472834147186829)
                ·
                  refine ⟨54918728676927312805195061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 146449943138472834147186829 54918728676927312805195061)
                  ·
                    refine ⟨5148630813461935575487037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54918728676927312805195061 5148630813461935575487037)
                    ·
                      refine ⟨1930736555048225840807639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5148630813461935575487037 1930736555048225840807639)
                      ·
                        rfl

theorem cell23_3760096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 3, 5, 3].length) (baseStart_3760096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3760096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3760096 prefixEnd_3760096 := by exact prefixLift 3760096
  have htrace : WordTrace (prefixWord ++ tailWord_3760096) baseStart_3760096 baseEnd_3760096 := by
    simpa [prefixWord, tailWord_3760096, baseEnd_3760096] using wordTrace_append hprefix tailTrace_3760096
  have hstable : (prefixWord ++ tailWord_3760096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3760096).length < 2 ^ (prefixWord ++ tailWord_3760096).sum := by decide
  have hdescent : baseEnd_3760096 < baseStart_3760096 := by decide
  rcases family_descends (prefixWord ++ tailWord_3760096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3760133 : List Nat := [1, 3, 1, 1, 2, 4, 3, 1, 2, 5]
def baseStart_3760133 : Nat := 118140960795 + 3760133 * 2 ^ 59
def prefixEnd_3760133 : Nat := 4983230072969 + 3 ^ 40 * 3760133 * 2
def baseEnd_3760133 : Nat := 643585184610814065348323

theorem tailTrace_3760133 : CollatzResearch.WordTrace tailWord_3760133 prefixEnd_3760133 643585184610814065348323 := by
  unfold tailWord_3760133
  simp only [CollatzResearch.WordTrace]
  refine ⟨137143317286687795434981053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91428878191125196956654035 137143317286687795434981053)
  ·
    refine ⟨51428743982507923288117895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137143317286687795434981053 51428743982507923288117895)
    ·
      refine ⟨77143115973761884932176843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51428743982507923288117895 77143115973761884932176843)
      ·
        refine ⟨115714673960642827398265265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77143115973761884932176843 115714673960642827398265265)
        ·
          refine ⟨86786005470482120548698949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115714673960642827398265265 86786005470482120548698949)
          ·
            refine ⟨16272376025715397602881053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86786005470482120548698949 16272376025715397602881053)
            ·
              refine ⟨6102141009643274101080395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16272376025715397602881053 6102141009643274101080395)
              ·
                refine ⟨9153211514464911151620593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6102141009643274101080395 9153211514464911151620593)
                ·
                  refine ⟨6864908635848683363715445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9153211514464911151620593 6864908635848683363715445)
                  ·
                    refine ⟨643585184610814065348323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6864908635848683363715445 643585184610814065348323)
                    ·
                      rfl

theorem cell23_3760133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 2, 5].length) (baseStart_3760133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3760133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3760133 prefixEnd_3760133 := by exact prefixLift 3760133
  have htrace : WordTrace (prefixWord ++ tailWord_3760133) baseStart_3760133 baseEnd_3760133 := by
    simpa [prefixWord, tailWord_3760133, baseEnd_3760133] using wordTrace_append hprefix tailTrace_3760133
  have hstable : (prefixWord ++ tailWord_3760133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3760133).length < 2 ^ (prefixWord ++ tailWord_3760133).sum := by decide
  have hdescent : baseEnd_3760133 < baseStart_3760133 := by decide
  rcases family_descends (prefixWord ++ tailWord_3760133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3760148 : List Nat := [2, 4, 3, 2, 1, 2, 1, 2, 2, 2, 2]
def baseStart_3760148 : Nat := 118140960795 + 3760148 * 2 ^ 59
def prefixEnd_3760148 : Nat := 4983230072969 + 3 ^ 40 * 3760148 * 2
def baseEnd_3760148 : Nat := 1930763256042259637357401

theorem tailTrace_3760148 : CollatzResearch.WordTrace tailWord_3760148 prefixEnd_3760148 1930763256042259637357401 := by
  unfold tailWord_3760148
  simp only [CollatzResearch.WordTrace]
  refine ⟨68571932190816726498388549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91429242921088968664518065 68571932190816726498388549)
  ·
    refine ⟨12857237285778136218447853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68571932190816726498388549 12857237285778136218447853)
    ·
      refine ⟨4821463982166801081917945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12857237285778136218447853 4821463982166801081917945)
      ·
        refine ⟨3616097986625100811438459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4821463982166801081917945 3616097986625100811438459)
        ·
          refine ⟨5424146979937651217157689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3616097986625100811438459 5424146979937651217157689)
          ·
            refine ⟨4068110234953238412868267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5424146979937651217157689 4068110234953238412868267)
            ·
              refine ⟨6102165352429857619302401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4068110234953238412868267 6102165352429857619302401)
              ·
                refine ⟨4576624014322393214476801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6102165352429857619302401 4576624014322393214476801)
                ·
                  refine ⟨3432468010741794910857601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4576624014322393214476801 3432468010741794910857601)
                  ·
                    refine ⟨2574351008056346183143201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3432468010741794910857601 2574351008056346183143201)
                    ·
                      refine ⟨1930763256042259637357401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2574351008056346183143201 1930763256042259637357401)
                      ·
                        rfl

theorem cell23_3760148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_3760148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3760148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3760148 prefixEnd_3760148 := by exact prefixLift 3760148
  have htrace : WordTrace (prefixWord ++ tailWord_3760148) baseStart_3760148 baseEnd_3760148 := by
    simpa [prefixWord, tailWord_3760148, baseEnd_3760148] using wordTrace_append hprefix tailTrace_3760148
  have hstable : (prefixWord ++ tailWord_3760148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3760148).length < 2 ^ (prefixWord ++ tailWord_3760148).sum := by decide
  have hdescent : baseEnd_3760148 < baseStart_3760148 := by decide
  rcases family_descends (prefixWord ++ tailWord_3760148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3760193 : List Nat := [1, 2, 5, 1, 2, 1, 1, 2, 8]
def baseStart_3760193 : Nat := 118140960795 + 3760193 * 2 ^ 59
def prefixEnd_3760193 : Nat := 4983230072969 + 3 ^ 40 * 3760193 * 2
def baseEnd_3760193 : Nat := 214531818074634662366077

theorem tailTrace_3760193 : CollatzResearch.WordTrace tailWord_3760193 prefixEnd_3760193 214531818074634662366077 := by
  unfold tailWord_3760193
  simp only [CollatzResearch.WordTrace]
  refine ⟨137145505666470425682165233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91430337110980283788110155 137145505666470425682165233)
  ·
    refine ⟨102859129249852819261623925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137145505666470425682165233 102859129249852819261623925)
    ·
      refine ⟨9643043367173701805777243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 102859129249852819261623925 9643043367173701805777243)
      ·
        refine ⟨14464565050760552708665865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9643043367173701805777243 14464565050760552708665865)
        ·
          refine ⟨10848423788070414531499399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14464565050760552708665865 10848423788070414531499399)
          ·
            refine ⟨16272635682105621797249099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10848423788070414531499399 16272635682105621797249099)
            ·
              refine ⟨24408953523158432695873649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16272635682105621797249099 24408953523158432695873649)
              ·
                refine ⟨18306715142368824521905237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24408953523158432695873649 18306715142368824521905237)
                ·
                  refine ⟨214531818074634662366077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18306715142368824521905237 214531818074634662366077)
                  ·
                    rfl

theorem cell23_3760193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 2, 8].length) (baseStart_3760193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3760193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3760193 prefixEnd_3760193 := by exact prefixLift 3760193
  have htrace : WordTrace (prefixWord ++ tailWord_3760193) baseStart_3760193 baseEnd_3760193 := by
    simpa [prefixWord, tailWord_3760193, baseEnd_3760193] using wordTrace_append hprefix tailTrace_3760193
  have hstable : (prefixWord ++ tailWord_3760193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3760193).length < 2 ^ (prefixWord ++ tailWord_3760193).sum := by decide
  have hdescent : baseEnd_3760193 < baseStart_3760193 := by decide
  rcases family_descends (prefixWord ++ tailWord_3760193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3760214 : List Nat := [5, 2, 2, 1, 1, 1, 3, 1, 3, 4]
def baseStart_3760214 : Nat := 118140960795 + 3760214 * 2 ^ 59
def prefixEnd_3760214 : Nat := 4983230072969 + 3 ^ 40 * 3760214 * 2
def baseEnd_3760214 : Nat := 643599048588485459710699

theorem tailTrace_3760214 : CollatzResearch.WordTrace tailWord_3760214 prefixEnd_3760214 643599048588485459710699 := by
  unfold tailWord_3760214
  simp only [CollatzResearch.WordTrace]
  refine ⟨8571641974962146641792481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 91430847732929564179119797 8571641974962146641792481)
  ·
    refine ⟨6428731481221609981344361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8571641974962146641792481 6428731481221609981344361)
    ·
      refine ⟨4821548610916207486008271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6428731481221609981344361 4821548610916207486008271)
      ·
        refine ⟨7232322916374311229012407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4821548610916207486008271 7232322916374311229012407)
        ·
          refine ⟨10848484374561466843518611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7232322916374311229012407 10848484374561466843518611)
          ·
            refine ⟨16272726561842200265277917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10848484374561466843518611 16272726561842200265277917)
            ·
              refine ⟨6102272460690825099479219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16272726561842200265277917 6102272460690825099479219)
              ·
                refine ⟨9153408691036237649218829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6102272460690825099479219 9153408691036237649218829)
                ·
                  refine ⟨3432528259138589118457061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9153408691036237649218829 3432528259138589118457061)
                  ·
                    refine ⟨643599048588485459710699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3432528259138589118457061 643599048588485459710699)
                    ·
                      rfl

theorem cell23_3760214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_3760214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3760214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3760214 prefixEnd_3760214 := by exact prefixLift 3760214
  have htrace : WordTrace (prefixWord ++ tailWord_3760214) baseStart_3760214 baseEnd_3760214 := by
    simpa [prefixWord, tailWord_3760214, baseEnd_3760214] using wordTrace_append hprefix tailTrace_3760214
  have hstable : (prefixWord ++ tailWord_3760214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3760214).length < 2 ^ (prefixWord ++ tailWord_3760214).sum := by decide
  have hdescent : baseEnd_3760214 < baseStart_3760214 := by decide
  rcases family_descends (prefixWord ++ tailWord_3760214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3760240 : List Nat := [2, 1, 1, 1, 5, 2, 3, 2, 1, 5]
def baseStart_3760240 : Nat := 118140960795 + 3760240 * 2 ^ 59
def prefixEnd_3760240 : Nat := 4983230072969 + 3 ^ 40 * 3760240 * 2
def baseEnd_3760240 : Nat := 643603498754157759135659

theorem tailTrace_3760240 : CollatzResearch.WordTrace tailWord_3760240 prefixEnd_3760240 643603498754157759135659 := by
  unfold tailWord_3760240
  simp only [CollatzResearch.WordTrace]
  refine ⟨68573609948650076354563087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91431479931533435139417449 68573609948650076354563087)
  ·
    refine ⟨102860414922975114531844631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68573609948650076354563087 102860414922975114531844631)
    ·
      refine ⟨154290622384462671797766947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102860414922975114531844631 154290622384462671797766947)
      ·
        refine ⟨231435933576694007696650421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154290622384462671797766947 231435933576694007696650421)
        ·
          refine ⟨21697118772815063221560977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 231435933576694007696650421 21697118772815063221560977)
          ·
            refine ⟨16272839079611297416170733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21697118772815063221560977 16272839079611297416170733)
            ·
              refine ⟨6102314654854236531064025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16272839079611297416170733 6102314654854236531064025)
              ·
                refine ⟨4576735991140677398298019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6102314654854236531064025 4576735991140677398298019)
                ·
                  refine ⟨6865103986711016097447029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4576735991140677398298019 6865103986711016097447029)
                  ·
                    refine ⟨643603498754157759135659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6865103986711016097447029 643603498754157759135659)
                    ·
                      rfl

theorem cell23_3760240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 3, 2, 1, 5].length) (baseStart_3760240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3760240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3760240 prefixEnd_3760240 := by exact prefixLift 3760240
  have htrace : WordTrace (prefixWord ++ tailWord_3760240) baseStart_3760240 baseEnd_3760240 := by
    simpa [prefixWord, tailWord_3760240, baseEnd_3760240] using wordTrace_append hprefix tailTrace_3760240
  have hstable : (prefixWord ++ tailWord_3760240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3760240).length < 2 ^ (prefixWord ++ tailWord_3760240).sum := by decide
  have hdescent : baseEnd_3760240 < baseStart_3760240 := by decide
  rcases family_descends (prefixWord ++ tailWord_3760240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3760247 : List Nat := [1, 1, 3, 1, 1, 6, 2, 1, 2, 3, 2]
def baseStart_3760247 : Nat := 118140960795 + 3760247 * 2 ^ 59
def prefixEnd_3760247 : Nat := 4983230072969 + 3 ^ 40 * 3760247 * 2
def baseEnd_3760247 : Nat := 1930814090627054750019445

theorem tailTrace_3760247 : CollatzResearch.WordTrace tailWord_3760247 prefixEnd_3760247 1930814090627054750019445 := by
  unfold tailWord_3760247
  simp only [CollatzResearch.WordTrace]
  refine ⟨137147475208274792904630995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91431650138849861936420663 137147475208274792904630995)
  ·
    refine ⟨205721212812412189356946493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137147475208274792904630995 205721212812412189356946493)
    ·
      refine ⟨77145454804654571008854935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205721212812412189356946493 77145454804654571008854935)
      ·
        refine ⟨115718182206981856513282403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77145454804654571008854935 115718182206981856513282403)
        ·
          refine ⟨173577273310472784769923605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115718182206981856513282403 173577273310472784769923605)
          ·
            refine ⟨8136434686428411786090169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 173577273310472784769923605 8136434686428411786090169)
            ·
              refine ⟨6102326014821308839567627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8136434686428411786090169 6102326014821308839567627)
              ·
                refine ⟨9153489022231963259351441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6102326014821308839567627 9153489022231963259351441)
                ·
                  refine ⟨6865116766673972444513581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9153489022231963259351441 6865116766673972444513581)
                  ·
                    refine ⟨2574418787502739666692593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6865116766673972444513581 2574418787502739666692593)
                    ·
                      refine ⟨1930814090627054750019445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2574418787502739666692593 1930814090627054750019445)
                      ·
                        rfl

theorem cell23_3760247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 2, 1, 2, 3, 2].length) (baseStart_3760247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3760247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3760247 prefixEnd_3760247 := by exact prefixLift 3760247
  have htrace : WordTrace (prefixWord ++ tailWord_3760247) baseStart_3760247 baseEnd_3760247 := by
    simpa [prefixWord, tailWord_3760247, baseEnd_3760247] using wordTrace_append hprefix tailTrace_3760247
  have hstable : (prefixWord ++ tailWord_3760247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3760247).length < 2 ^ (prefixWord ++ tailWord_3760247).sum := by decide
  have hdescent : baseEnd_3760247 < baseStart_3760247 := by decide
  rcases family_descends (prefixWord ++ tailWord_3760247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3760253 : List Nat := [1, 4, 1, 1, 3, 2, 1, 1, 3, 6]
def baseStart_3760253 : Nat := 118140960795 + 3760253 * 2 ^ 59
def prefixEnd_3760253 : Nat := 4983230072969 + 3 ^ 40 * 3760253 * 2
def baseEnd_3760253 : Nat := 643605723836993908848139

theorem tailTrace_3760253 : CollatzResearch.WordTrace tailWord_3760253 prefixEnd_3760253 643605723836993908848139 := by
  unfold tailWord_3760253
  simp only [CollatzResearch.WordTrace]
  refine ⟨137147694046253055929349413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91431796030835370619566275 137147694046253055929349413)
  ·
    refine ⟨25715192633672447986753015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137147694046253055929349413 25715192633672447986753015)
    ·
      refine ⟨38572788950508671980129523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25715192633672447986753015 38572788950508671980129523)
      ·
        refine ⟨57859183425763007970194285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38572788950508671980129523 57859183425763007970194285)
        ·
          refine ⟨21697193784661127988822857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57859183425763007970194285 21697193784661127988822857)
          ·
            refine ⟨16272895338495845991617143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21697193784661127988822857 16272895338495845991617143)
            ·
              refine ⟨24409343007743768987425715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16272895338495845991617143 24409343007743768987425715)
              ·
                refine ⟨36614014511615653481138573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24409343007743768987425715 36614014511615653481138573)
                ·
                  refine ⟨13730255441855870055426965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36614014511615653481138573 13730255441855870055426965)
                  ·
                    refine ⟨643605723836993908848139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13730255441855870055426965 643605723836993908848139)
                    ·
                      rfl

theorem cell23_3760253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 1, 3, 6].length) (baseStart_3760253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3760253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3760253 prefixEnd_3760253 := by exact prefixLift 3760253
  have htrace : WordTrace (prefixWord ++ tailWord_3760253) baseStart_3760253 baseEnd_3760253 := by
    simpa [prefixWord, tailWord_3760253, baseEnd_3760253] using wordTrace_append hprefix tailTrace_3760253
  have hstable : (prefixWord ++ tailWord_3760253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3760253).length < 2 ^ (prefixWord ++ tailWord_3760253).sum := by decide
  have hdescent : baseEnd_3760253 < baseStart_3760253 := by decide
  rcases family_descends (prefixWord ++ tailWord_3760253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3760277 : List Nat := [1, 3, 2, 1, 1, 1, 4, 3, 3, 2, 2]
def baseStart_3760277 : Nat := 118140960795 + 3760277 * 2 ^ 59
def prefixEnd_3760277 : Nat := 4983230072969 + 3 ^ 40 * 3760277 * 2
def baseEnd_3760277 : Nat := 1930829495046689632644307

theorem tailTrace_3760277 : CollatzResearch.WordTrace tailWord_3760277 prefixEnd_3760277 1930829495046689632644307 := by
  unfold tailWord_3760277
  simp only [CollatzResearch.WordTrace]
  refine ⟨137148569398166108028223085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91432379598777405352148723 137148569398166108028223085)
  ·
    refine ⟨51430713524312290510583657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137148569398166108028223085 51430713524312290510583657)
    ·
      refine ⟨38573035143234217882937743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51430713524312290510583657 38573035143234217882937743)
      ·
        refine ⟨57859552714851326824406615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38573035143234217882937743 57859552714851326824406615)
        ·
          refine ⟨86789329072276990236609923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57859552714851326824406615 86789329072276990236609923)
          ·
            refine ⟨130183993608415485354914885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86789329072276990236609923 130183993608415485354914885)
            ·
              refine ⟨24409498801577903504046541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 130183993608415485354914885 24409498801577903504046541)
              ·
                refine ⟨9153562050591713814017453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24409498801577903504046541 9153562050591713814017453)
                ·
                  refine ⟨3432585768971892680256545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9153562050591713814017453 3432585768971892680256545)
                  ·
                    refine ⟨2574439326728919510192409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3432585768971892680256545 2574439326728919510192409)
                    ·
                      refine ⟨1930829495046689632644307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2574439326728919510192409 1930829495046689632644307)
                      ·
                        rfl

theorem cell23_3760277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 3, 3, 2, 2].length) (baseStart_3760277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3760277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3760277 prefixEnd_3760277 := by exact prefixLift 3760277
  have htrace : WordTrace (prefixWord ++ tailWord_3760277) baseStart_3760277 baseEnd_3760277 := by
    simpa [prefixWord, tailWord_3760277, baseEnd_3760277] using wordTrace_append hprefix tailTrace_3760277
  have hstable : (prefixWord ++ tailWord_3760277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3760277).length < 2 ^ (prefixWord ++ tailWord_3760277).sum := by decide
  have hdescent : baseEnd_3760277 < baseStart_3760277 := by decide
  rcases family_descends (prefixWord ++ tailWord_3760277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3760287 : List Nat := [1, 1, 2, 6, 1, 1, 2, 3, 2, 4]
def baseStart_3760287 : Nat := 118140960795 + 3760287 * 2 ^ 59
def prefixEnd_3760287 : Nat := 4983230072969 + 3 ^ 40 * 3760287 * 2
def baseEnd_3760287 : Nat := 643611543284411531173087

theorem tailTrace_3760287 : CollatzResearch.WordTrace tailWord_3760287 prefixEnd_3760287 643611543284411531173087 := by
  unfold tailWord_3760287
  simp only [CollatzResearch.WordTrace]
  refine ⟨137148934128129879736087115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91432622752086586490724743 137148934128129879736087115)
  ·
    refine ⟨205723401192194819604130673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137148934128129879736087115 205723401192194819604130673)
    ·
      refine ⟨154292550894146114703098005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205723401192194819604130673 154292550894146114703098005)
      ·
        refine ⟨7232463323163099126707719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 154292550894146114703098005 7232463323163099126707719)
        ·
          refine ⟨10848694984744648690061579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7232463323163099126707719 10848694984744648690061579)
          ·
            refine ⟨16273042477116973035092369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10848694984744648690061579 16273042477116973035092369)
            ·
              refine ⟨12204781857837729776319277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16273042477116973035092369 12204781857837729776319277)
              ·
                refine ⟨4576793196689148666119729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12204781857837729776319277 4576793196689148666119729)
                ·
                  refine ⟨3432594897516861499589797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4576793196689148666119729 3432594897516861499589797)
                  ·
                    refine ⟨643611543284411531173087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3432594897516861499589797 643611543284411531173087)
                    ·
                      rfl

theorem cell23_3760287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 3, 2, 4].length) (baseStart_3760287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3760287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3760287 prefixEnd_3760287 := by exact prefixLift 3760287
  have htrace : WordTrace (prefixWord ++ tailWord_3760287) baseStart_3760287 baseEnd_3760287 := by
    simpa [prefixWord, tailWord_3760287, baseEnd_3760287] using wordTrace_append hprefix tailTrace_3760287
  have hstable : (prefixWord ++ tailWord_3760287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3760287).length < 2 ^ (prefixWord ++ tailWord_3760287).sum := by decide
  have hdescent : baseEnd_3760287 < baseStart_3760287 := by decide
  rcases family_descends (prefixWord ++ tailWord_3760287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3760298 : List Nat := [3, 1, 5, 1, 3, 1, 1, 1, 2, 3, 2]
def baseStart_3760298 : Nat := 118140960795 + 3760298 * 2 ^ 59
def prefixEnd_3760298 : Nat := 4983230072969 + 3 ^ 40 * 3760298 * 2
def baseEnd_3760298 : Nat := 1930840278140434050481711

theorem tailTrace_3760298 : CollatzResearch.WordTrace tailWord_3760298 prefixEnd_3760298 1930840278140434050481711 := by
  unfold tailWord_3760298
  simp only [CollatzResearch.WordTrace]
  refine ⟨34287333832772507153684387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91432890220726685743158365 34287333832772507153684387)
  ·
    refine ⟨51431000749158760730526581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34287333832772507153684387 51431000749158760730526581)
    ·
      refine ⟨4821656320233633818486867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51431000749158760730526581 4821656320233633818486867)
      ·
        refine ⟨7232484480350450727730301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4821656320233633818486867 7232484480350450727730301)
        ·
          refine ⟨2712181680131419022898863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7232484480350450727730301 2712181680131419022898863)
          ·
            refine ⟨4068272520197128534348295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2712181680131419022898863 4068272520197128534348295)
            ·
              refine ⟨6102408780295692801522443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4068272520197128534348295 6102408780295692801522443)
              ·
                refine ⟨9153613170443539202283665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6102408780295692801522443 9153613170443539202283665)
                ·
                  refine ⟨6865209877832654401712749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9153613170443539202283665 6865209877832654401712749)
                  ·
                    refine ⟨2574453704187245400642281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6865209877832654401712749 2574453704187245400642281)
                    ·
                      refine ⟨1930840278140434050481711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2574453704187245400642281 1930840278140434050481711)
                      ·
                        rfl

theorem cell23_3760298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 1, 1, 2, 3, 2].length) (baseStart_3760298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3760298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3760298 prefixEnd_3760298 := by exact prefixLift 3760298
  have htrace : WordTrace (prefixWord ++ tailWord_3760298) baseStart_3760298 baseEnd_3760298 := by
    simpa [prefixWord, tailWord_3760298, baseEnd_3760298] using wordTrace_append hprefix tailTrace_3760298
  have hstable : (prefixWord ++ tailWord_3760298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3760298).length < 2 ^ (prefixWord ++ tailWord_3760298).sum := by decide
  have hdescent : baseEnd_3760298 < baseStart_3760298 := by decide
  rcases family_descends (prefixWord ++ tailWord_3760298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
