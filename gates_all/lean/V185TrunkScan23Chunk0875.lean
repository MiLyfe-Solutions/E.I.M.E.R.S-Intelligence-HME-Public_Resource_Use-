import V185TrunkScan23Chunk0874

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5178839 : List Nat := [1, 1, 3, 2, 1, 1, 1, 2, 7, 2, 2]
def baseStart_5178839 : Nat := 118140960795 + 5178839 * 2 ^ 59
def prefixEnd_5178839 : Nat := 4983230072969 + 3 ^ 40 * 5178839 * 2
def baseEnd_5178839 : Nat := 2659233639249968502295459

theorem tailTrace_5178839 : CollatzResearch.WordTrace tailWord_5178839 prefixEnd_5178839 2659233639249968502295459 := by
  unfold tailWord_5178839
  simp only [CollatzResearch.WordTrace]
  refine ⟨188887776084958253129635571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125925184056638835419757047 188887776084958253129635571)
  ·
    refine ⟨283331664127437379694453357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188887776084958253129635571 283331664127437379694453357)
    ·
      refine ⟨106249374047789017385420009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 283331664127437379694453357 106249374047789017385420009)
      ·
        refine ⟨79687030535841763039065007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106249374047789017385420009 79687030535841763039065007)
        ·
          refine ⟨119530545803762644558597511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79687030535841763039065007 119530545803762644558597511)
          ·
            refine ⟨179295818705643966837896267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119530545803762644558597511 179295818705643966837896267)
            ·
              refine ⟨268943728058465950256844401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 179295818705643966837896267 268943728058465950256844401)
              ·
                refine ⟨201707796043849462692633301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 268943728058465950256844401 201707796043849462692633301)
                ·
                  refine ⟨4727526469777721781858593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 201707796043849462692633301 4727526469777721781858593)
                  ·
                    refine ⟨3545644852333291336393945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4727526469777721781858593 3545644852333291336393945)
                    ·
                      refine ⟨2659233639249968502295459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3545644852333291336393945 2659233639249968502295459)
                      ·
                        rfl

theorem cell23_5178839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 7, 2, 2].length) (baseStart_5178839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5178839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5178839 prefixEnd_5178839 := by exact prefixLift 5178839
  have htrace : WordTrace (prefixWord ++ tailWord_5178839) baseStart_5178839 baseEnd_5178839 := by
    simpa [prefixWord, tailWord_5178839, baseEnd_5178839] using wordTrace_append hprefix tailTrace_5178839
  have hstable : (prefixWord ++ tailWord_5178839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5178839).length < 2 ^ (prefixWord ++ tailWord_5178839).sum := by decide
  have hdescent : baseEnd_5178839 < baseStart_5178839 := by decide
  rcases family_descends (prefixWord ++ tailWord_5178839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5178849 : List Nat := [1, 2, 3, 1, 2, 3, 2, 3, 2, 4]
def baseStart_5178849 : Nat := 118140960795 + 5178849 * 2 ^ 59
def prefixEnd_5178849 : Nat := 4983230072969 + 3 ^ 40 * 5178849 * 2
def baseEnd_5178849 : Nat := 886412924685504487723471

theorem tailTrace_5178849 : CollatzResearch.WordTrace tailWord_5178849 prefixEnd_5178849 886412924685504487723471 := by
  unfold tailWord_5178849
  simp only [CollatzResearch.WordTrace]
  refine ⟨188888140814922024837499601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125925427209948016558333067 188888140814922024837499601)
  ·
    refine ⟨141666105611191518628124701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188888140814922024837499601 141666105611191518628124701)
    ·
      refine ⟨53124789604196819485546763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141666105611191518628124701 53124789604196819485546763)
      ·
        refine ⟨79687184406295229228320145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53124789604196819485546763 79687184406295229228320145)
        ·
          refine ⟨59765388304721421921240109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79687184406295229228320145 59765388304721421921240109)
          ·
            refine ⟨22412020614270533220465041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59765388304721421921240109 22412020614270533220465041)
            ·
              refine ⟨16809015460702899915348781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22412020614270533220465041 16809015460702899915348781)
              ·
                refine ⟨6303380797763587468255793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16809015460702899915348781 6303380797763587468255793)
                ·
                  refine ⟨4727535598322690601191845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6303380797763587468255793 4727535598322690601191845)
                  ·
                    refine ⟨886412924685504487723471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4727535598322690601191845 886412924685504487723471)
                    ·
                      rfl

theorem cell23_5178849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 3, 2, 4].length) (baseStart_5178849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5178849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5178849 prefixEnd_5178849 := by exact prefixLift 5178849
  have htrace : WordTrace (prefixWord ++ tailWord_5178849) baseStart_5178849 baseEnd_5178849 := by
    simpa [prefixWord, tailWord_5178849, baseEnd_5178849] using wordTrace_append hprefix tailTrace_5178849
  have hstable : (prefixWord ++ tailWord_5178849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5178849).length < 2 ^ (prefixWord ++ tailWord_5178849).sum := by decide
  have hdescent : baseEnd_5178849 < baseStart_5178849 := by decide
  rcases family_descends (prefixWord ++ tailWord_5178849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5178856 : List Nat := [2, 1, 4, 1, 1, 2, 3, 2, 3, 2, 2]
def baseStart_5178856 : Nat := 118140960795 + 5178856 * 2 ^ 59
def prefixEnd_5178856 : Nat := 4983230072969 + 3 ^ 40 * 5178856 * 2
def baseEnd_5178856 : Nat := 2659242368421094935782881

theorem tailTrace_5178856 : CollatzResearch.WordTrace tailWord_5178856 prefixEnd_5178856 2659242368421094935782881 := by
  unfold tailWord_5178856
  simp only [CollatzResearch.WordTrace]
  refine ⟨94444198062948332516502211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125925597417264443355336281 94444198062948332516502211)
  ·
    refine ⟨141666297094422498774753317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94444198062948332516502211 141666297094422498774753317)
    ·
      refine ⟨26562430705204218520266247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 141666297094422498774753317 26562430705204218520266247)
      ·
        refine ⟨39843646057806327780399371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26562430705204218520266247 39843646057806327780399371)
        ·
          refine ⟨59765469086709491670599057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39843646057806327780399371 59765469086709491670599057)
          ·
            refine ⟨44824101815032118752949293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59765469086709491670599057 44824101815032118752949293)
            ·
              refine ⟨16809038180637044532355985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44824101815032118752949293 16809038180637044532355985)
              ·
                refine ⟨12606778635477783399266989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16809038180637044532355985 12606778635477783399266989)
                ·
                  refine ⟨4727541988304168774725121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12606778635477783399266989 4727541988304168774725121)
                  ·
                    refine ⟨3545656491228126581043841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4727541988304168774725121 3545656491228126581043841)
                    ·
                      refine ⟨2659242368421094935782881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3545656491228126581043841 2659242368421094935782881)
                      ·
                        rfl

theorem cell23_5178856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 2, 3, 2, 2].length) (baseStart_5178856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5178856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5178856 prefixEnd_5178856 := by exact prefixLift 5178856
  have htrace : WordTrace (prefixWord ++ tailWord_5178856) baseStart_5178856 baseEnd_5178856 := by
    simpa [prefixWord, tailWord_5178856, baseEnd_5178856] using wordTrace_append hprefix tailTrace_5178856
  have hstable : (prefixWord ++ tailWord_5178856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5178856).length < 2 ^ (prefixWord ++ tailWord_5178856).sum := by decide
  have hdescent : baseEnd_5178856 < baseStart_5178856 := by decide
  rcases family_descends (prefixWord ++ tailWord_5178856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5178875 : List Nat := [1, 1, 1, 1, 1, 3, 2, 2, 4, 7]
def baseStart_5178875 : Nat := 118140960795 + 5178875 * 2 ^ 59
def prefixEnd_5178875 : Nat := 4983230072969 + 3 ^ 40 * 5178875 * 2
def baseEnd_5178875 : Nat := 886417374851176787148431

theorem tailTrace_5178875 : CollatzResearch.WordTrace tailWord_5178875 prefixEnd_5178875 886417374851176787148431 := by
  unfold tailWord_5178875
  simp only [CollatzResearch.WordTrace]
  refine ⟨188889089112827831277946079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125926059408551887518630719 188889089112827831277946079)
  ·
    refine ⟨283333633669241746916919119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188889089112827831277946079 283333633669241746916919119)
    ·
      refine ⟨425000450503862620375378679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 283333633669241746916919119 425000450503862620375378679)
      ·
        refine ⟨637500675755793930563068019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 425000450503862620375378679 637500675755793930563068019)
        ·
          refine ⟨956251013633690895844602029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 637500675755793930563068019 956251013633690895844602029)
          ·
            refine ⟨358594130112634085941725761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 956251013633690895844602029 358594130112634085941725761)
            ·
              refine ⟨268945597584475564456294321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 358594130112634085941725761 268945597584475564456294321)
              ·
                refine ⟨201709198188356673342220741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 268945597584475564456294321 201709198188356673342220741)
                ·
                  refine ⟨37820474660316876251666389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 201709198188356673342220741 37820474660316876251666389)
                  ·
                    refine ⟨886417374851176787148431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37820474660316876251666389 886417374851176787148431)
                    ·
                      rfl

theorem cell23_5178875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 4, 7].length) (baseStart_5178875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5178875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5178875 prefixEnd_5178875 := by exact prefixLift 5178875
  have htrace : WordTrace (prefixWord ++ tailWord_5178875) baseStart_5178875 baseEnd_5178875 := by
    simpa [prefixWord, tailWord_5178875, baseEnd_5178875] using wordTrace_append hprefix tailTrace_5178875
  have hstable : (prefixWord ++ tailWord_5178875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5178875).length < 2 ^ (prefixWord ++ tailWord_5178875).sum := by decide
  have hdescent : baseEnd_5178875 < baseStart_5178875 := by decide
  rcases family_descends (prefixWord ++ tailWord_5178875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5178876 : List Nat := [2, 2, 2, 1, 2, 1, 6, 1, 1, 2, 3]
def baseStart_5178876 : Nat := 118140960795 + 5178876 * 2 ^ 59
def prefixEnd_5178876 : Nat := 4983230072969 + 3 ^ 40 * 5178876 * 2
def baseEnd_5178876 : Nat := 2659252638034184857532789

theorem tailTrace_5178876 : CollatzResearch.WordTrace tailWord_5178876 prefixEnd_5178876 2659252638034184857532789 := by
  unfold tailWord_5178876
  simp only [CollatzResearch.WordTrace]
  refine ⟨94444562792912104224366241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125926083723882805632488321 94444562792912104224366241)
  ·
    refine ⟨70833422094684078168274681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94444562792912104224366241 70833422094684078168274681)
    ·
      refine ⟨53125066571013058626206011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70833422094684078168274681 53125066571013058626206011)
      ·
        refine ⟨79687599856519587939309017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53125066571013058626206011 79687599856519587939309017)
        ·
          refine ⟨59765699892389690954481763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79687599856519587939309017 59765699892389690954481763)
          ·
            refine ⟨89648549838584536431722645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59765699892389690954481763 89648549838584536431722645)
            ·
              refine ⟨4202275773683650145236999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 89648549838584536431722645 4202275773683650145236999)
              ·
                refine ⟨6303413660525475217855499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4202275773683650145236999 6303413660525475217855499)
                ·
                  refine ⟨9455120490788212826783249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6303413660525475217855499 9455120490788212826783249)
                  ·
                    refine ⟨7091340368091159620087437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9455120490788212826783249 7091340368091159620087437)
                    ·
                      refine ⟨2659252638034184857532789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7091340368091159620087437 2659252638034184857532789)
                      ·
                        rfl

theorem cell23_5178876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 6, 1, 1, 2, 3].length) (baseStart_5178876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5178876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5178876 prefixEnd_5178876 := by exact prefixLift 5178876
  have htrace : WordTrace (prefixWord ++ tailWord_5178876) baseStart_5178876 baseEnd_5178876 := by
    simpa [prefixWord, tailWord_5178876, baseEnd_5178876] using wordTrace_append hprefix tailTrace_5178876
  have hstable : (prefixWord ++ tailWord_5178876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5178876).length < 2 ^ (prefixWord ++ tailWord_5178876).sum := by decide
  have hdescent : baseEnd_5178876 < baseStart_5178876 := by decide
  rcases family_descends (prefixWord ++ tailWord_5178876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5178889 : List Nat := [1, 2, 1, 1, 3, 1, 5, 1, 4, 1, 3]
def baseStart_5178889 : Nat := 118140960795 + 5178889 * 2 ^ 59
def prefixEnd_5178889 : Nat := 4983230072969 + 3 ^ 40 * 5178889 * 2
def baseEnd_5178889 : Nat := 2659259313282693306670229

theorem tailTrace_5178889 : CollatzResearch.WordTrace tailWord_5178889 prefixEnd_5178889 2659259313282693306670229 := by
  unfold tailWord_5178889
  simp only [CollatzResearch.WordTrace]
  refine ⟨188889599734777111668955721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125926399823184741112637147 188889599734777111668955721)
  ·
    refine ⟨141667199801082833751716791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188889599734777111668955721 141667199801082833751716791)
    ·
      refine ⟨212500799701624250627575187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141667199801082833751716791 212500799701624250627575187)
      ·
        refine ⟨318751199552436375941362781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212500799701624250627575187 318751199552436375941362781)
        ·
          refine ⟨119531699832163640978011043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 318751199552436375941362781 119531699832163640978011043)
          ·
            refine ⟨179297549748245461467016565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119531699832163640978011043 179297549748245461467016565)
            ·
              refine ⟨16809145288898012012532803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 179297549748245461467016565 16809145288898012012532803)
              ·
                refine ⟨25213717933347018018799205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16809145288898012012532803 25213717933347018018799205)
                ·
                  refine ⟨4727572112502565878524851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25213717933347018018799205 4727572112502565878524851)
                  ·
                    refine ⟨7091358168753848817787277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4727572112502565878524851 7091358168753848817787277)
                    ·
                      refine ⟨2659259313282693306670229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7091358168753848817787277 2659259313282693306670229)
                      ·
                        rfl

theorem cell23_5178889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 1, 4, 1, 3].length) (baseStart_5178889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5178889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5178889 prefixEnd_5178889 := by exact prefixLift 5178889
  have htrace : WordTrace (prefixWord ++ tailWord_5178889) baseStart_5178889 baseEnd_5178889 := by
    simpa [prefixWord, tailWord_5178889, baseEnd_5178889] using wordTrace_append hprefix tailTrace_5178889
  have hstable : (prefixWord ++ tailWord_5178889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5178889).length < 2 ^ (prefixWord ++ tailWord_5178889).sum := by decide
  have hdescent : baseEnd_5178889 < baseStart_5178889 := by decide
  rcases family_descends (prefixWord ++ tailWord_5178889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5178893 : List Nat := [1, 7, 1, 1, 2, 1, 1, 2, 1, 1, 5]
def baseStart_5178893 : Nat := 118140960795 + 5178893 * 2 ^ 59
def prefixEnd_5178893 : Nat := 4983230072969 + 3 ^ 40 * 5178893 * 2
def baseEnd_5178893 : Nat := 2659261367205311291020211

theorem tailTrace_5178893 : CollatzResearch.WordTrace tailWord_5178893 prefixEnd_5178893 2659261367205311291020211 := by
  unfold tailWord_5178893
  simp only [CollatzResearch.WordTrace]
  refine ⟨188889745626762620352101333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125926497084508413568067555 188889745626762620352101333)
  ·
    refine ⟨4427103413127248914502375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 188889745626762620352101333 4427103413127248914502375)
    ·
      refine ⟨6640655119690873371753563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4427103413127248914502375 6640655119690873371753563)
      ·
        refine ⟨9960982679536310057630345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6640655119690873371753563 9960982679536310057630345)
        ·
          refine ⟨7470737009652232543222759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9960982679536310057630345 7470737009652232543222759)
          ·
            refine ⟨11206105514478348814834139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7470737009652232543222759 11206105514478348814834139)
            ·
              refine ⟨16809158271717523222251209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11206105514478348814834139 16809158271717523222251209)
              ·
                refine ⟨12606868703788142416688407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16809158271717523222251209 12606868703788142416688407)
                ·
                  refine ⟨18910303055682213625032611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12606868703788142416688407 18910303055682213625032611)
                  ·
                    refine ⟨28365454583523320437548917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18910303055682213625032611 28365454583523320437548917)
                    ·
                      refine ⟨2659261367205311291020211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28365454583523320437548917 2659261367205311291020211)
                      ·
                        rfl

theorem cell23_5178893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_5178893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5178893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5178893 prefixEnd_5178893 := by exact prefixLift 5178893
  have htrace : WordTrace (prefixWord ++ tailWord_5178893) baseStart_5178893 baseEnd_5178893 := by
    simpa [prefixWord, tailWord_5178893, baseEnd_5178893] using wordTrace_append hprefix tailTrace_5178893
  have hstable : (prefixWord ++ tailWord_5178893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5178893).length < 2 ^ (prefixWord ++ tailWord_5178893).sum := by decide
  have hdescent : baseEnd_5178893 < baseStart_5178893 := by decide
  rcases family_descends (prefixWord ++ tailWord_5178893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5178895 : List Nat := [1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 10]
def baseStart_5178895 : Nat := 118140960795 + 5178895 * 2 ^ 59
def prefixEnd_5178895 : Nat := 4983230072969 + 3 ^ 40 * 5178895 * 2
def baseEnd_5178895 : Nat := 2659262394166620283195201

theorem tailTrace_5178895 : CollatzResearch.WordTrace tailWord_5178895 prefixEnd_5178895 2659262394166620283195201 := by
  unfold tailWord_5178895
  simp only [CollatzResearch.WordTrace]
  refine ⟨188889818572755374693674139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125926545715170249795782759 188889818572755374693674139)
  ·
    refine ⟨283334727859133062040511209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188889818572755374693674139 283334727859133062040511209)
    ·
      refine ⟨212501045894349796530383407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 283334727859133062040511209 212501045894349796530383407)
      ·
        refine ⟨318751568841524694795575111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212501045894349796530383407 318751568841524694795575111)
        ·
          refine ⟨478127353262287042193362667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 318751568841524694795575111 478127353262287042193362667)
          ·
            refine ⟨717191029893430563290044001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 478127353262287042193362667 717191029893430563290044001)
            ·
              refine ⟨537893272420072922467533001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 717191029893430563290044001 537893272420072922467533001)
              ·
                refine ⟨403419954315054691850649751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 537893272420072922467533001 403419954315054691850649751)
                ·
                  refine ⟨605129931472582037775974627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 403419954315054691850649751 605129931472582037775974627)
                  ·
                    refine ⟨907694897208873056663961941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 605129931472582037775974627 907694897208873056663961941)
                    ·
                      refine ⟨2659262394166620283195201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 907694897208873056663961941 2659262394166620283195201)
                      ·
                        rfl

theorem cell23_5178895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 10].length) (baseStart_5178895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5178895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5178895 prefixEnd_5178895 := by exact prefixLift 5178895
  have htrace : WordTrace (prefixWord ++ tailWord_5178895) baseStart_5178895 baseEnd_5178895 := by
    simpa [prefixWord, tailWord_5178895, baseEnd_5178895] using wordTrace_append hprefix tailTrace_5178895
  have hstable : (prefixWord ++ tailWord_5178895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5178895).length < 2 ^ (prefixWord ++ tailWord_5178895).sum := by decide
  have hdescent : baseEnd_5178895 < baseStart_5178895 := by decide
  rcases family_descends (prefixWord ++ tailWord_5178895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5178900 : List Nat := [2, 4, 3, 1, 2, 1, 3, 1, 2, 4]
def baseStart_5178900 : Nat := 118140960795 + 5178900 * 2 ^ 59
def prefixEnd_5178900 : Nat := 4983230072969 + 3 ^ 40 * 5178900 * 2
def baseEnd_5178900 : Nat := 886421653856630921210893

theorem tailTrace_5178900 : CollatzResearch.WordTrace tailWord_5178900 prefixEnd_5178900 886421653856630921210893 := by
  unfold tailWord_5178900
  simp only [CollatzResearch.WordTrace]
  refine ⟨94445000468868630273803077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125926667291824840365070769 94445000468868630273803077)
  ·
    refine ⟨17708437587912868176338077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94445000468868630273803077 17708437587912868176338077)
    ·
      refine ⟨6640664095467325566126779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17708437587912868176338077 6640664095467325566126779)
      ·
        refine ⟨9960996143200988349190169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6640664095467325566126779 9960996143200988349190169)
        ·
          refine ⟨7470747107400741261892627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9960996143200988349190169 7470747107400741261892627)
          ·
            refine ⟨11206120661101111892838941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7470747107400741261892627 11206120661101111892838941)
            ·
              refine ⟨4202295247912916959814603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11206120661101111892838941 4202295247912916959814603)
              ·
                refine ⟨6303442871869375439721905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4202295247912916959814603 6303442871869375439721905)
                ·
                  refine ⟨4727582153902031579791429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6303442871869375439721905 4727582153902031579791429)
                  ·
                    refine ⟨886421653856630921210893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4727582153902031579791429 886421653856630921210893)
                    ·
                      rfl

theorem cell23_5178900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_5178900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5178900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5178900 prefixEnd_5178900 := by exact prefixLift 5178900
  have htrace : WordTrace (prefixWord ++ tailWord_5178900) baseStart_5178900 baseEnd_5178900 := by
    simpa [prefixWord, tailWord_5178900, baseEnd_5178900] using wordTrace_append hprefix tailTrace_5178900
  have hstable : (prefixWord ++ tailWord_5178900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5178900).length < 2 ^ (prefixWord ++ tailWord_5178900).sum := by decide
  have hdescent : baseEnd_5178900 < baseStart_5178900 := by decide
  rcases family_descends (prefixWord ++ tailWord_5178900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5178929 : List Nat := [1, 2, 2, 3, 1, 1, 1, 3, 3, 4, 2]
def baseStart_5178929 : Nat := 118140960795 + 5178929 * 2 ^ 59
def prefixEnd_5178929 : Nat := 4983230072969 + 3 ^ 40 * 5178929 * 2
def baseEnd_5178929 : Nat := 2659279852508873150170045

theorem tailTrace_5178929 : CollatzResearch.WordTrace tailWord_5178929 prefixEnd_5178929 2659279852508873150170045 := by
  unfold tailWord_5178929
  simp only [CollatzResearch.WordTrace]
  refine ⟨188891058654632198500411841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125927372436421465666941227 188891058654632198500411841)
  ·
    refine ⟨141668293990974148875308881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188891058654632198500411841 141668293990974148875308881)
    ·
      refine ⟨106251220493230611656481661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141668293990974148875308881 106251220493230611656481661)
      ·
        refine ⟨39844207684961479371180623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106251220493230611656481661 39844207684961479371180623)
        ·
          refine ⟨59766311527442219056770935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39844207684961479371180623 59766311527442219056770935)
          ·
            refine ⟨89649467291163328585156403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59766311527442219056770935 89649467291163328585156403)
            ·
              refine ⟨134474200936744992877734605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89649467291163328585156403 134474200936744992877734605)
              ·
                refine ⟨50427825351279372329150477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 134474200936744992877734605 50427825351279372329150477)
                ·
                  refine ⟨18910434506729764623431429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50427825351279372329150477 18910434506729764623431429)
                  ·
                    refine ⟨3545706470011830866893393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18910434506729764623431429 3545706470011830866893393)
                    ·
                      refine ⟨2659279852508873150170045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3545706470011830866893393 2659279852508873150170045)
                      ·
                        rfl

theorem cell23_5178929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 3, 3, 4, 2].length) (baseStart_5178929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5178929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5178929 prefixEnd_5178929 := by exact prefixLift 5178929
  have htrace : WordTrace (prefixWord ++ tailWord_5178929) baseStart_5178929 baseEnd_5178929 := by
    simpa [prefixWord, tailWord_5178929, baseEnd_5178929] using wordTrace_append hprefix tailTrace_5178929
  have hstable : (prefixWord ++ tailWord_5178929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5178929).length < 2 ^ (prefixWord ++ tailWord_5178929).sum := by decide
  have hdescent : baseEnd_5178929 < baseStart_5178929 := by decide
  rcases family_descends (prefixWord ++ tailWord_5178929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5178957 : List Nat := [1, 6, 1, 1, 3, 2, 2, 1, 2, 1, 3]
def baseStart_5178957 : Nat := 118140960795 + 5178957 * 2 ^ 59
def prefixEnd_5178957 : Nat := 4983230072969 + 3 ^ 40 * 5178957 * 2
def baseEnd_5178957 : Nat := 2659294229967199040619917

theorem tailTrace_5178957 : CollatzResearch.WordTrace tailWord_5178957 prefixEnd_5178957 2659294229967199040619917 := by
  unfold tailWord_5178957
  simp only [CollatzResearch.WordTrace]
  refine ⟨188892079898530759282431125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125928053265687172854954083 188892079898530759282431125)
  ·
    refine ⟨8854316245243629341363959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 188892079898530759282431125 8854316245243629341363959)
    ·
      refine ⟨13281474367865444012045939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8854316245243629341363959 13281474367865444012045939)
      ·
        refine ⟨19922211551798166018068909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13281474367865444012045939 19922211551798166018068909)
        ·
          refine ⟨7470829331924312256775841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19922211551798166018068909 7470829331924312256775841)
          ·
            refine ⟨5603121998943234192581881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7470829331924312256775841 5603121998943234192581881)
            ·
              refine ⟨4202341499207425644436411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5603121998943234192581881 4202341499207425644436411)
              ·
                refine ⟨6303512248811138466654617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4202341499207425644436411 6303512248811138466654617)
                ·
                  refine ⟨4727634186608353849990963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6303512248811138466654617 4727634186608353849990963)
                  ·
                    refine ⟨7091451279912530774986445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4727634186608353849990963 7091451279912530774986445)
                    ·
                      refine ⟨2659294229967199040619917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7091451279912530774986445 2659294229967199040619917)
                      ·
                        rfl

theorem cell23_5178957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 2, 1, 2, 1, 3].length) (baseStart_5178957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5178957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5178957 prefixEnd_5178957 := by exact prefixLift 5178957
  have htrace : WordTrace (prefixWord ++ tailWord_5178957) baseStart_5178957 baseEnd_5178957 := by
    simpa [prefixWord, tailWord_5178957, baseEnd_5178957] using wordTrace_append hprefix tailTrace_5178957
  have hstable : (prefixWord ++ tailWord_5178957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5178957).length < 2 ^ (prefixWord ++ tailWord_5178957).sum := by decide
  have hdescent : baseEnd_5178957 < baseStart_5178957 := by decide
  rcases family_descends (prefixWord ++ tailWord_5178957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5179009 : List Nat := [1, 2, 4, 2, 1, 2, 2, 1, 1, 2, 5]
def baseStart_5179009 : Nat := 118140960795 + 5179009 * 2 ^ 59
def prefixEnd_5179009 : Nat := 4983230072969 + 3 ^ 40 * 5179009 * 2
def baseEnd_5179009 : Nat := 2659320930961232837169677

theorem tailTrace_5179009 : CollatzResearch.WordTrace tailWord_5179009 prefixEnd_5179009 2659320930961232837169677 := by
  unfold tailWord_5179009
  simp only [CollatzResearch.WordTrace]
  refine ⟨188893976494342372163324081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125929317662894914775549387 188893976494342372163324081)
  ·
    refine ⟨141670482370756779122493061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188893976494342372163324081 141670482370756779122493061)
    ·
      refine ⟨26563215444516896085467449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 141670482370756779122493061 26563215444516896085467449)
      ·
        refine ⟨19922411583387672064100587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26563215444516896085467449 19922411583387672064100587)
        ·
          refine ⟨29883617375081508096150881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19922411583387672064100587 29883617375081508096150881)
          ·
            refine ⟨22412713031311131072113161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29883617375081508096150881 22412713031311131072113161)
            ·
              refine ⟨16809534773483348304084871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22412713031311131072113161 16809534773483348304084871)
              ·
                refine ⟨25214302160225022456127307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16809534773483348304084871 25214302160225022456127307)
                ·
                  refine ⟨37821453240337533684190961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25214302160225022456127307 37821453240337533684190961)
                  ·
                    refine ⟨28366089930253150263143221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37821453240337533684190961 28366089930253150263143221)
                    ·
                      refine ⟨2659320930961232837169677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28366089930253150263143221 2659320930961232837169677)
                      ·
                        rfl

theorem cell23_5179009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_5179009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5179009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5179009 prefixEnd_5179009 := by exact prefixLift 5179009
  have htrace : WordTrace (prefixWord ++ tailWord_5179009) baseStart_5179009 baseEnd_5179009 := by
    simpa [prefixWord, tailWord_5179009, baseEnd_5179009] using wordTrace_append hprefix tailTrace_5179009
  have hstable : (prefixWord ++ tailWord_5179009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5179009).length < 2 ^ (prefixWord ++ tailWord_5179009).sum := by decide
  have hdescent : baseEnd_5179009 < baseStart_5179009 := by decide
  rcases family_descends (prefixWord ++ tailWord_5179009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5179036 : List Nat := [2, 2, 3, 2, 3, 1, 1, 1, 1, 3, 4]
def baseStart_5179036 : Nat := 118140960795 + 5179036 * 2 ^ 59
def prefixEnd_5179036 : Nat := 4983230072969 + 3 ^ 40 * 5179036 * 2
def baseEnd_5179036 : Nat := 2659334794938904231532053

theorem tailTrace_5179036 : CollatzResearch.WordTrace tailWord_5179036 prefixEnd_5179036 2659334794938904231532053 := by
  unfold tailWord_5179036
  simp only [CollatzResearch.WordTrace]
  refine ⟨94447480632622277887278481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125929974176829703849704641 94447480632622277887278481)
  ·
    refine ⟨70835610474466708415458861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94447480632622277887278481 70835610474466708415458861)
    ·
      refine ⟨26563353927925015655797073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70835610474466708415458861 26563353927925015655797073)
      ·
        refine ⟨19922515445943761741847805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26563353927925015655797073 19922515445943761741847805)
        ·
          refine ⟨7470943292228910653192927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19922515445943761741847805 7470943292228910653192927)
          ·
            refine ⟨11206414938343365979789391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7470943292228910653192927 11206414938343365979789391)
            ·
              refine ⟨16809622407515048969684087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11206414938343365979789391 16809622407515048969684087)
              ·
                refine ⟨25214433611272573454526131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16809622407515048969684087 25214433611272573454526131)
                ·
                  refine ⟨37821650416908860181789197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25214433611272573454526131 37821650416908860181789197)
                  ·
                    refine ⟨14183118906340822568170949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37821650416908860181789197 14183118906340822568170949)
                    ·
                      refine ⟨2659334794938904231532053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14183118906340822568170949 2659334794938904231532053)
                      ·
                        rfl

theorem cell23_5179036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 1, 1, 3, 4].length) (baseStart_5179036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5179036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5179036 prefixEnd_5179036 := by exact prefixLift 5179036
  have htrace : WordTrace (prefixWord ++ tailWord_5179036) baseStart_5179036 baseEnd_5179036 := by
    simpa [prefixWord, tailWord_5179036, baseEnd_5179036] using wordTrace_append hprefix tailTrace_5179036
  have hstable : (prefixWord ++ tailWord_5179036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5179036).length < 2 ^ (prefixWord ++ tailWord_5179036).sum := by decide
  have hdescent : baseEnd_5179036 < baseStart_5179036 := by decide
  rcases family_descends (prefixWord ++ tailWord_5179036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5179052 : List Nat := [2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 7]
def baseStart_5179052 : Nat := 118140960795 + 5179052 * 2 ^ 59
def prefixEnd_5179052 : Nat := 4983230072969 + 3 ^ 40 * 5179052 * 2
def baseEnd_5179052 : Nat := 2659343010629376168931979

theorem tailTrace_5179052 : CollatzResearch.WordTrace tailWord_5179052 prefixEnd_5179052 2659343010629376168931979 := by
  unfold tailWord_5179052
  simp only [CollatzResearch.WordTrace]
  refine ⟨94447772416593295253569705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125930363222124393671426273 94447772416593295253569705)
  ·
    refine ⟨70835829312444971440177279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94447772416593295253569705 70835829312444971440177279)
    ·
      refine ⟨106253743968667457160265919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70835829312444971440177279 106253743968667457160265919)
      ·
        refine ⟨159380615953001185740398879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106253743968667457160265919 159380615953001185740398879)
        ·
          refine ⟨239070923929501778610598319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159380615953001185740398879 239070923929501778610598319)
          ·
            refine ⟨358606385894252667915897479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 239070923929501778610598319 358606385894252667915897479)
            ·
              refine ⟨537909578841379001873846219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 358606385894252667915897479 537909578841379001873846219)
              ·
                refine ⟨806864368262068502810769329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 537909578841379001873846219 806864368262068502810769329)
                ·
                  refine ⟨605148276196551377108076997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 806864368262068502810769329 605148276196551377108076997)
                  ·
                    refine ⟨113465301786853383207764437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 605148276196551377108076997 113465301786853383207764437)
                    ·
                      refine ⟨2659343010629376168931979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 113465301786853383207764437 2659343010629376168931979)
                      ·
                        rfl

theorem cell23_5179052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 7].length) (baseStart_5179052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5179052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5179052 prefixEnd_5179052 := by exact prefixLift 5179052
  have htrace : WordTrace (prefixWord ++ tailWord_5179052) baseStart_5179052 baseEnd_5179052 := by
    simpa [prefixWord, tailWord_5179052, baseEnd_5179052] using wordTrace_append hprefix tailTrace_5179052
  have hstable : (prefixWord ++ tailWord_5179052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5179052).length < 2 ^ (prefixWord ++ tailWord_5179052).sum := by decide
  have hdescent : baseEnd_5179052 < baseStart_5179052 := by decide
  rcases family_descends (prefixWord ++ tailWord_5179052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5179063 : List Nat := [1, 1, 3, 1, 5, 1, 2, 4, 1, 4]
def baseStart_5179063 : Nat := 118140960795 + 5179063 * 2 ^ 59
def prefixEnd_5179063 : Nat := 4983230072969 + 3 ^ 40 * 5179063 * 2
def baseEnd_5179063 : Nat := 886449552972191875298143

theorem tailTrace_5179063 : CollatzResearch.WordTrace tailWord_5179063 prefixEnd_5179063 886449552972191875298143 := by
  unfold tailWord_5179063
  simp only [CollatzResearch.WordTrace]
  refine ⟨188895946036146739385789843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125930630690764492923859895 188895946036146739385789843)
  ·
    refine ⟨283343919054220109078684765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188895946036146739385789843 283343919054220109078684765)
    ·
      refine ⟨106253969645332540904506787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 283343919054220109078684765 106253969645332540904506787)
      ·
        refine ⟨159380954467998811356760181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106253969645332540904506787 159380954467998811356760181)
        ·
          refine ⟨14941964481374888564696267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 159380954467998811356760181 14941964481374888564696267)
          ·
            refine ⟨22412946722062332847044401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14941964481374888564696267 22412946722062332847044401)
            ·
              refine ⟨16809710041546749635283301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22412946722062332847044401 16809710041546749635283301)
              ·
                refine ⟨3151820632790015556615619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16809710041546749635283301 3151820632790015556615619)
                ·
                  refine ⟨4727730949185023334923429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3151820632790015556615619 4727730949185023334923429)
                  ·
                    refine ⟨886449552972191875298143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4727730949185023334923429 886449552972191875298143)
                    ·
                      rfl

theorem cell23_5179063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 4, 1, 4].length) (baseStart_5179063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5179063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5179063 prefixEnd_5179063 := by exact prefixLift 5179063
  have htrace : WordTrace (prefixWord ++ tailWord_5179063) baseStart_5179063 baseEnd_5179063 := by
    simpa [prefixWord, tailWord_5179063, baseEnd_5179063] using wordTrace_append hprefix tailTrace_5179063
  have hstable : (prefixWord ++ tailWord_5179063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5179063).length < 2 ^ (prefixWord ++ tailWord_5179063).sum := by decide
  have hdescent : baseEnd_5179063 < baseStart_5179063 := by decide
  rcases family_descends (prefixWord ++ tailWord_5179063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5179096 : List Nat := [2, 1, 2, 2, 3, 1, 1, 3, 1, 5, 2]
def baseStart_5179096 : Nat := 118140960795 + 5179096 * 2 ^ 59
def prefixEnd_5179096 : Nat := 4983230072969 + 3 ^ 40 * 5179096 * 2
def baseEnd_5179096 : Nat := 2659365603778173996781777

theorem tailTrace_5179096 : CollatzResearch.WordTrace tailWord_5179096 prefixEnd_5179096 2659365603778173996781777 := by
  unfold tailWord_5179096
  simp only [CollatzResearch.WordTrace]
  refine ⟨94448574822513593010870571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125931433096684790681160761 94448574822513593010870571)
  ·
    refine ⟨141672862233770389516305857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94448574822513593010870571 141672862233770389516305857)
    ·
      refine ⟨106254646675327792137229393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141672862233770389516305857 106254646675327792137229393)
      ·
        refine ⟨79690985006495844102922045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106254646675327792137229393 79690985006495844102922045)
        ·
          refine ⟨29884119377435941538595767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79690985006495844102922045 29884119377435941538595767)
          ·
            refine ⟨44826179066153912307893651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29884119377435941538595767 44826179066153912307893651)
            ·
              refine ⟨67239268599230868461840477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44826179066153912307893651 67239268599230868461840477)
              ·
                refine ⟨25214725724711575673190179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67239268599230868461840477 25214725724711575673190179)
                ·
                  refine ⟨37822088587067363509785269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25214725724711575673190179 37822088587067363509785269)
                  ·
                    refine ⟨3545820805037565329042369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37822088587067363509785269 3545820805037565329042369)
                    ·
                      refine ⟨2659365603778173996781777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3545820805037565329042369 2659365603778173996781777)
                      ·
                        rfl

theorem cell23_5179096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 3, 1, 5, 2].length) (baseStart_5179096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5179096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5179096 prefixEnd_5179096 := by exact prefixLift 5179096
  have htrace : WordTrace (prefixWord ++ tailWord_5179096) baseStart_5179096 baseEnd_5179096 := by
    simpa [prefixWord, tailWord_5179096, baseEnd_5179096] using wordTrace_append hprefix tailTrace_5179096
  have hstable : (prefixWord ++ tailWord_5179096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5179096).length < 2 ^ (prefixWord ++ tailWord_5179096).sum := by decide
  have hdescent : baseEnd_5179096 < baseStart_5179096 := by decide
  rcases family_descends (prefixWord ++ tailWord_5179096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5179129 : List Nat := [1, 2, 1, 3, 1, 1, 1, 1, 1, 8, 3]
def baseStart_5179129 : Nat := 118140960795 + 5179129 * 2 ^ 59
def prefixEnd_5179129 : Nat := 4983230072969 + 3 ^ 40 * 5179129 * 2
def baseEnd_5179129 : Nat := 2659382548639772367669125

theorem tailTrace_5179129 : CollatzResearch.WordTrace tailWord_5179129 prefixEnd_5179129 2659382548639772367669125 := by
  unfold tailWord_5179129
  simp only [CollatzResearch.WordTrace]
  refine ⟨188898353253907632657692441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125932235502605088438461627 188898353253907632657692441)
  ·
    refine ⟨141673764940430724493269331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188898353253907632657692441 141673764940430724493269331)
    ·
      refine ⟨212510647410646086739903997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141673764940430724493269331 212510647410646086739903997)
      ·
        refine ⟨79691492778992282527463999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 212510647410646086739903997 79691492778992282527463999)
        ·
          refine ⟨119537239168488423791195999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79691492778992282527463999 119537239168488423791195999)
          ·
            refine ⟨179305858752732635686793999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119537239168488423791195999 179305858752732635686793999)
            ·
              refine ⟨268958788129098953530190999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 179305858752732635686793999 268958788129098953530190999)
              ·
                refine ⟨403438182193648430295286499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 268958788129098953530190999 403438182193648430295286499)
                ·
                  refine ⟨605157273290472645442929749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 403438182193648430295286499 605157273290472645442929749)
                  ·
                    refine ⟨7091686796372726313784333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 605157273290472645442929749 7091686796372726313784333)
                    ·
                      refine ⟨2659382548639772367669125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7091686796372726313784333 2659382548639772367669125)
                      ·
                        rfl

theorem cell23_5179129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 8, 3].length) (baseStart_5179129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5179129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5179129 prefixEnd_5179129 := by exact prefixLift 5179129
  have htrace : WordTrace (prefixWord ++ tailWord_5179129) baseStart_5179129 baseEnd_5179129 := by
    simpa [prefixWord, tailWord_5179129, baseEnd_5179129] using wordTrace_append hprefix tailTrace_5179129
  have hstable : (prefixWord ++ tailWord_5179129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5179129).length < 2 ^ (prefixWord ++ tailWord_5179129).sum := by decide
  have hdescent : baseEnd_5179129 < baseStart_5179129 := by decide
  rcases family_descends (prefixWord ++ tailWord_5179129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5179136 : List Nat := [2, 1, 1, 2, 1, 1, 2, 7, 2, 4]
def baseStart_5179136 : Nat := 118140960795 + 5179136 * 2 ^ 59
def prefixEnd_5179136 : Nat := 4983230072969 + 3 ^ 40 * 5179136 * 2
def baseEnd_5179136 : Nat := 886462047668117946760531

theorem tailTrace_5179136 : CollatzResearch.WordTrace tailWord_5179136 prefixEnd_5179136 886462047668117946760531 := by
  unfold tailWord_5179136
  simp only [CollatzResearch.WordTrace]
  refine ⟨94449304282441136426598631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125932405709921515235464841 94449304282441136426598631)
  ·
    refine ⟨141673956423661704639897947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94449304282441136426598631 141673956423661704639897947)
    ·
      refine ⟨212510934635492556959846921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141673956423661704639897947 212510934635492556959846921)
      ·
        refine ⟨159383200976619417719885191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 212510934635492556959846921 159383200976619417719885191)
        ·
          refine ⟨239074801464929126579827787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159383200976619417719885191 239074801464929126579827787)
          ·
            refine ⟨358612202197393689869741681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 239074801464929126579827787 358612202197393689869741681)
            ·
              refine ⟨268959151648045267402306261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 358612202197393689869741681 268959151648045267402306261)
              ·
                refine ⟨6303730116751060954741553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 268959151648045267402306261 6303730116751060954741553)
                ·
                  refine ⟨4727797587563295716056165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6303730116751060954741553 4727797587563295716056165)
                  ·
                    refine ⟨886462047668117946760531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4727797587563295716056165 886462047668117946760531)
                    ·
                      rfl

theorem cell23_5179136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 7, 2, 4].length) (baseStart_5179136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5179136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5179136 prefixEnd_5179136 := by exact prefixLift 5179136
  have htrace : WordTrace (prefixWord ++ tailWord_5179136) baseStart_5179136 baseEnd_5179136 := by
    simpa [prefixWord, tailWord_5179136, baseEnd_5179136] using wordTrace_append hprefix tailTrace_5179136
  have hstable : (prefixWord ++ tailWord_5179136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5179136).length < 2 ^ (prefixWord ++ tailWord_5179136).sum := by decide
  have hdescent : baseEnd_5179136 < baseStart_5179136 := by decide
  rcases family_descends (prefixWord ++ tailWord_5179136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5179139 : List Nat := [1, 1, 1, 3, 2, 2, 4, 1, 1, 1, 6]
def baseStart_5179139 : Nat := 118140960795 + 5179139 * 2 ^ 59
def prefixEnd_5179139 : Nat := 4983230072969 + 3 ^ 40 * 5179139 * 2
def baseEnd_5179139 : Nat := 2659387683446317328544079

theorem tailTrace_5179139 : CollatzResearch.WordTrace tailWord_5179139 prefixEnd_5179139 2659387683446317328544079 := by
  unfold tailWord_5179139
  simp only [CollatzResearch.WordTrace]
  refine ⟨188898717983871404365556471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125932478655914269577037647 188898717983871404365556471)
  ·
    refine ⟨283348076975807106548334707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188898717983871404365556471 283348076975807106548334707)
    ·
      refine ⟨425022115463710659822502061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 283348076975807106548334707 425022115463710659822502061)
      ·
        refine ⟨159383293298891497433438273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 425022115463710659822502061 159383293298891497433438273)
        ·
          refine ⟨119537469974168623075078705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 159383293298891497433438273 119537469974168623075078705)
          ·
            refine ⟨89653102480626467306309029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119537469974168623075078705 89653102480626467306309029)
            ·
              refine ⟨16809956715117462619932943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 89653102480626467306309029 16809956715117462619932943)
              ·
                refine ⟨25214935072676193929899415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16809956715117462619932943 25214935072676193929899415)
                ·
                  refine ⟨37822402609014290894849123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25214935072676193929899415 37822402609014290894849123)
                  ·
                    refine ⟨56733603913521436342273685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37822402609014290894849123 56733603913521436342273685)
                    ·
                      refine ⟨2659387683446317328544079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56733603913521436342273685 2659387683446317328544079)
                      ·
                        rfl

theorem cell23_5179139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 1, 1, 1, 6].length) (baseStart_5179139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5179139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5179139 prefixEnd_5179139 := by exact prefixLift 5179139
  have htrace : WordTrace (prefixWord ++ tailWord_5179139) baseStart_5179139 baseEnd_5179139 := by
    simpa [prefixWord, tailWord_5179139, baseEnd_5179139] using wordTrace_append hprefix tailTrace_5179139
  have hstable : (prefixWord ++ tailWord_5179139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5179139).length < 2 ^ (prefixWord ++ tailWord_5179139).sum := by decide
  have hdescent : baseEnd_5179139 < baseStart_5179139 := by decide
  rcases family_descends (prefixWord ++ tailWord_5179139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5179143 : List Nat := [1, 1, 4, 4, 2, 1, 1, 1, 3, 1, 4]
def baseStart_5179143 : Nat := 118140960795 + 5179143 * 2 ^ 59
def prefixEnd_5179143 : Nat := 4983230072969 + 3 ^ 40 * 5179143 * 2
def baseEnd_5179143 : Nat := 2659389737368935312894061

theorem tailTrace_5179143 : CollatzResearch.WordTrace tailWord_5179143 prefixEnd_5179143 2659389737368935312894061 := by
  unfold tailWord_5179143
  simp only [CollatzResearch.WordTrace]
  refine ⟨188898863875856913048702083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125932575917237942032468055 188898863875856913048702083)
  ·
    refine ⟨283348295813785369573053125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188898863875856913048702083 283348295813785369573053125)
    ·
      refine ⟨53127805465084756794947461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 283348295813785369573053125 53127805465084756794947461)
      ·
        refine ⟨9961463524703391899052649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53127805465084756794947461 9961463524703391899052649)
        ·
          refine ⟨7471097643527543924289487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9961463524703391899052649 7471097643527543924289487)
          ·
            refine ⟨11206646465291315886434231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7471097643527543924289487 11206646465291315886434231)
            ·
              refine ⟨16809969697936973829651347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11206646465291315886434231 16809969697936973829651347)
              ·
                refine ⟨25214954546905460744477021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16809969697936973829651347 25214954546905460744477021)
                ·
                  refine ⟨9455607955089547779178883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25214954546905460744477021 9455607955089547779178883)
                  ·
                    refine ⟨14183411932634321668768325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9455607955089547779178883 14183411932634321668768325)
                    ·
                      refine ⟨2659389737368935312894061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14183411932634321668768325 2659389737368935312894061)
                      ·
                        rfl

theorem cell23_5179143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_5179143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5179143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5179143 prefixEnd_5179143 := by exact prefixLift 5179143
  have htrace : WordTrace (prefixWord ++ tailWord_5179143) baseStart_5179143 baseEnd_5179143 := by
    simpa [prefixWord, tailWord_5179143, baseEnd_5179143] using wordTrace_append hprefix tailTrace_5179143
  have hstable : (prefixWord ++ tailWord_5179143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5179143).length < 2 ^ (prefixWord ++ tailWord_5179143).sum := by decide
  have hdescent : baseEnd_5179143 < baseStart_5179143 := by decide
  rcases family_descends (prefixWord ++ tailWord_5179143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5179190 : List Nat := [5, 1, 2, 2, 1, 2, 2, 1, 1, 2, 4]
def baseStart_5179190 : Nat := 118140960795 + 5179190 * 2 ^ 59
def prefixEnd_5179190 : Nat := 4983230072969 + 3 ^ 40 * 5179190 * 2
def baseEnd_5179190 : Nat := 2659413870959696629006345

theorem tailTrace_5179190 : CollatzResearch.WordTrace tailWord_5179190 prefixEnd_5179190 2659413870959696629006345 := by
  unfold tailWord_5179190
  simp only [CollatzResearch.WordTrace]
  refine ⟨11806286131667915004728939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 125933718737791093383775349 11806286131667915004728939)
  ·
    refine ⟨17709429197501872507093409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11806286131667915004728939 17709429197501872507093409)
    ·
      refine ⟨13282071898126404380320057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17709429197501872507093409 13282071898126404380320057)
      ·
        refine ⟨9961553923594803285240043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13282071898126404380320057 9961553923594803285240043)
        ·
          refine ⟨14942330885392204927860065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9961553923594803285240043 14942330885392204927860065)
          ·
            refine ⟨11206748164044153695895049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14942330885392204927860065 11206748164044153695895049)
            ·
              refine ⟨8405061123033115271921287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11206748164044153695895049 8405061123033115271921287)
              ·
                refine ⟨12607591684549672907881931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8405061123033115271921287 12607591684549672907881931)
                ·
                  refine ⟨18911387526824509361822897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12607591684549672907881931 18911387526824509361822897)
                  ·
                    refine ⟨14183540645118382021367173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18911387526824509361822897 14183540645118382021367173)
                    ·
                      refine ⟨2659413870959696629006345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14183540645118382021367173 2659413870959696629006345)
                      ·
                        rfl

theorem cell23_5179190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_5179190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5179190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5179190 prefixEnd_5179190 := by exact prefixLift 5179190
  have htrace : WordTrace (prefixWord ++ tailWord_5179190) baseStart_5179190 baseEnd_5179190 := by
    simpa [prefixWord, tailWord_5179190, baseEnd_5179190] using wordTrace_append hprefix tailTrace_5179190
  have hstable : (prefixWord ++ tailWord_5179190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5179190).length < 2 ^ (prefixWord ++ tailWord_5179190).sum := by decide
  have hdescent : baseEnd_5179190 < baseStart_5179190 := by decide
  rcases family_descends (prefixWord ++ tailWord_5179190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5179203 : List Nat := [1, 1, 1, 3, 1, 5, 2, 1, 3, 3, 2]
def baseStart_5179203 : Nat := 118140960795 + 5179203 * 2 ^ 59
def prefixEnd_5179203 : Nat := 4983230072969 + 3 ^ 40 * 5179203 * 2
def baseEnd_5179203 : Nat := 2659420546208205078143785

theorem tailTrace_5179203 : CollatzResearch.WordTrace tailWord_5179203 prefixEnd_5179203 2659420546208205078143785 := by
  unfold tailWord_5179203
  simp only [CollatzResearch.WordTrace]
  refine ⟨188901052255639543295886263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125934034837093028863924175 188901052255639543295886263)
  ·
    refine ⟨283351578383459314943829395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188901052255639543295886263 283351578383459314943829395)
    ·
      refine ⟨425027367575188972415744093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 283351578383459314943829395 425027367575188972415744093)
      ·
        refine ⟨159385262840695864655904035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 425027367575188972415744093 159385262840695864655904035)
        ·
          refine ⟨239077894261043796983856053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159385262840695864655904035 239077894261043796983856053)
          ·
            refine ⟨22413552586972855967236505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 239077894261043796983856053 22413552586972855967236505)
            ·
              refine ⟨16810164440229641975427379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22413552586972855967236505 16810164440229641975427379)
              ·
                refine ⟨25215246660344462963141069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16810164440229641975427379 25215246660344462963141069)
                ·
                  refine ⟨9455717497629173611177901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25215246660344462963141069 9455717497629173611177901)
                  ·
                    refine ⟨3545894061610940104191713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9455717497629173611177901 3545894061610940104191713)
                    ·
                      refine ⟨2659420546208205078143785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3545894061610940104191713 2659420546208205078143785)
                      ·
                        rfl

theorem cell23_5179203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 1, 3, 3, 2].length) (baseStart_5179203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5179203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5179203 prefixEnd_5179203 := by exact prefixLift 5179203
  have htrace : WordTrace (prefixWord ++ tailWord_5179203) baseStart_5179203 baseEnd_5179203 := by
    simpa [prefixWord, tailWord_5179203, baseEnd_5179203] using wordTrace_append hprefix tailTrace_5179203
  have hstable : (prefixWord ++ tailWord_5179203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5179203).length < 2 ^ (prefixWord ++ tailWord_5179203).sum := by decide
  have hdescent : baseEnd_5179203 < baseStart_5179203 := by decide
  rcases family_descends (prefixWord ++ tailWord_5179203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5179209 : List Nat := [1, 2, 1, 1, 2, 4, 1, 2, 1, 8]
def baseStart_5179209 : Nat := 118140960795 + 5179209 * 2 ^ 59
def prefixEnd_5179209 : Nat := 4983230072969 + 3 ^ 40 * 5179209 * 2
def baseEnd_5179209 : Nat := 886474542364044018222919

theorem tailTrace_5179209 : CollatzResearch.WordTrace tailWord_5179209 prefixEnd_5179209 886474542364044018222919 := by
  unfold tailWord_5179209
  simp only [CollatzResearch.WordTrace]
  refine ⟨188901271093617806320604681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125934180729078537547069787 188901271093617806320604681)
  ·
    refine ⟨141675953320213354740453511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188901271093617806320604681 141675953320213354740453511)
    ·
      refine ⟨212513929980320032110680267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141675953320213354740453511 212513929980320032110680267)
      ·
        refine ⟨318770894970480048166020401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212513929980320032110680267 318770894970480048166020401)
        ·
          refine ⟨239078171227860036124515301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 318770894970480048166020401 239078171227860036124515301)
          ·
            refine ⟨44827157105223756773346619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 239078171227860036124515301 44827157105223756773346619)
            ·
              refine ⟨67240735657835635160019929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44827157105223756773346619 67240735657835635160019929)
              ·
                refine ⟨50430551743376726370014947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67240735657835635160019929 50430551743376726370014947)
                ·
                  refine ⟨75645827615065089555022421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50430551743376726370014947 75645827615065089555022421)
                  ·
                    refine ⟨886474542364044018222919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 75645827615065089555022421 886474542364044018222919)
                    ·
                      rfl

theorem cell23_5179209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 8].length) (baseStart_5179209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5179209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5179209 prefixEnd_5179209 := by exact prefixLift 5179209
  have htrace : WordTrace (prefixWord ++ tailWord_5179209) baseStart_5179209 baseEnd_5179209 := by
    simpa [prefixWord, tailWord_5179209, baseEnd_5179209] using wordTrace_append hprefix tailTrace_5179209
  have hstable : (prefixWord ++ tailWord_5179209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5179209).length < 2 ^ (prefixWord ++ tailWord_5179209).sum := by decide
  have hdescent : baseEnd_5179209 < baseStart_5179209 := by decide
  rcases family_descends (prefixWord ++ tailWord_5179209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5179254 : List Nat := [5, 1, 1, 3, 2, 1, 2, 2, 1, 3, 2]
def baseStart_5179254 : Nat := 118140960795 + 5179254 * 2 ^ 59
def prefixEnd_5179254 : Nat := 4983230072969 + 3 ^ 40 * 5179254 * 2
def baseEnd_5179254 : Nat := 2659446733721584378606051

theorem tailTrace_5179254 : CollatzResearch.WordTrace tailWord_5179254 prefixEnd_5179254 2659446733721584378606051 := by
  unfold tailWord_5179254
  simp only [CollatzResearch.WordTrace]
  refine ⟨11806432023653423687874551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 125935274918969852670661877 11806432023653423687874551)
  ·
    refine ⟨17709648035480135531811827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11806432023653423687874551 17709648035480135531811827)
    ·
      refine ⟨26564472053220203297717741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17709648035480135531811827 26564472053220203297717741)
      ·
        refine ⟨9961677019957576236644153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26564472053220203297717741 9961677019957576236644153)
        ·
          refine ⟨7471257764968182177483115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9961677019957576236644153 7471257764968182177483115)
          ·
            refine ⟨11206886647452273266224673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7471257764968182177483115 11206886647452273266224673)
            ·
              refine ⟨8405164985589204949668505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11206886647452273266224673 8405164985589204949668505)
              ·
                refine ⟨6303873739191903712251379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8405164985589204949668505 6303873739191903712251379)
                ·
                  refine ⟨9455810608787855568377069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6303873739191903712251379 9455810608787855568377069)
                  ·
                    refine ⟨3545928978295445838141401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9455810608787855568377069 3545928978295445838141401)
                    ·
                      refine ⟨2659446733721584378606051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3545928978295445838141401 2659446733721584378606051)
                      ·
                        rfl

theorem cell23_5179254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 2, 2, 1, 3, 2].length) (baseStart_5179254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5179254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5179254 prefixEnd_5179254 := by exact prefixLift 5179254
  have htrace : WordTrace (prefixWord ++ tailWord_5179254) baseStart_5179254 baseEnd_5179254 := by
    simpa [prefixWord, tailWord_5179254, baseEnd_5179254] using wordTrace_append hprefix tailTrace_5179254
  have hstable : (prefixWord ++ tailWord_5179254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5179254).length < 2 ^ (prefixWord ++ tailWord_5179254).sum := by decide
  have hdescent : baseEnd_5179254 < baseStart_5179254 := by decide
  rcases family_descends (prefixWord ++ tailWord_5179254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5179343 : List Nat := [1, 1, 2, 1, 1, 5, 1, 4, 2, 2, 3]
def baseStart_5179343 : Nat := 118140960795 + 5179343 * 2 ^ 59
def prefixEnd_5179343 : Nat := 4983230072969 + 3 ^ 40 * 5179343 * 2
def baseEnd_5179343 : Nat := 2659492433499834530393141

theorem tailTrace_5179343 : CollatzResearch.WordTrace tailWord_5179343 prefixEnd_5179343 2659492433499834530393141 := by
  unfold tailWord_5179343
  simp only [CollatzResearch.WordTrace]
  refine ⟨188906158475132347205982683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125937438983421564803988455 188906158475132347205982683)
  ·
    refine ⟨283359237712698520808974025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188906158475132347205982683 283359237712698520808974025)
    ·
      refine ⟨212519428284523890606730519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 283359237712698520808974025 212519428284523890606730519)
      ·
        refine ⟨318779142426785835910095779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212519428284523890606730519 318779142426785835910095779)
        ·
          refine ⟨478168713640178753865143669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 318779142426785835910095779 478168713640178753865143669)
          ·
            refine ⟨44828316903766758174857219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 478168713640178753865143669 44828316903766758174857219)
            ·
              refine ⟨67242475355650137262285829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44828316903766758174857219 67242475355650137262285829)
              ·
                refine ⟨12607964129184400736678593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 67242475355650137262285829 12607964129184400736678593)
                ·
                  refine ⟨9455973096888300552508945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12607964129184400736678593 9455973096888300552508945)
                  ·
                    refine ⟨7091979822666225414381709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9455973096888300552508945 7091979822666225414381709)
                    ·
                      refine ⟨2659492433499834530393141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7091979822666225414381709 2659492433499834530393141)
                      ·
                        rfl

theorem cell23_5179343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 4, 2, 2, 3].length) (baseStart_5179343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5179343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5179343 prefixEnd_5179343 := by exact prefixLift 5179343
  have htrace : WordTrace (prefixWord ++ tailWord_5179343) baseStart_5179343 baseEnd_5179343 := by
    simpa [prefixWord, tailWord_5179343, baseEnd_5179343] using wordTrace_append hprefix tailTrace_5179343
  have hstable : (prefixWord ++ tailWord_5179343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5179343).length < 2 ^ (prefixWord ++ tailWord_5179343).sum := by decide
  have hdescent : baseEnd_5179343 < baseStart_5179343 := by decide
  rcases family_descends (prefixWord ++ tailWord_5179343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5179357 : List Nat := [1, 4, 3, 1, 3, 1, 1, 1, 2, 4, 2]
def baseStart_5179357 : Nat := 118140960795 + 5179357 * 2 ^ 59
def prefixEnd_5179357 : Nat := 4983230072969 + 3 ^ 40 * 5179357 * 2
def baseEnd_5179357 : Nat := 2659499622228997475618077

theorem tailTrace_5179357 : CollatzResearch.WordTrace tailWord_5179357 prefixEnd_5179357 2659499622228997475618077 := by
  unfold tailWord_5179357
  simp only [CollatzResearch.WordTrace]
  refine ⟨188906669097081627596992325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125937779398054418397994883 188906669097081627596992325)
  ·
    refine ⟨35420000455702805174436061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 188906669097081627596992325 35420000455702805174436061)
    ·
      refine ⟨13282500170888551940413523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35420000455702805174436061 13282500170888551940413523)
      ·
        refine ⟨19923750256332827910620285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13282500170888551940413523 19923750256332827910620285)
        ·
          refine ⟨7471406346124810466482607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19923750256332827910620285 7471406346124810466482607)
          ·
            refine ⟨11207109519187215699723911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7471406346124810466482607 11207109519187215699723911)
            ·
              refine ⟨16810664278780823549585867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11207109519187215699723911 16810664278780823549585867)
              ·
                refine ⟨25215996418171235324378801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16810664278780823549585867 25215996418171235324378801)
                ·
                  refine ⟨18911997313628426493284101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25215996418171235324378801 18911997313628426493284101)
                  ·
                    refine ⟨3545999496305329967490769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18911997313628426493284101 3545999496305329967490769)
                    ·
                      refine ⟨2659499622228997475618077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3545999496305329967490769 2659499622228997475618077)
                      ·
                        rfl

theorem cell23_5179357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 1, 2, 4, 2].length) (baseStart_5179357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5179357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5179357 prefixEnd_5179357 := by exact prefixLift 5179357
  have htrace : WordTrace (prefixWord ++ tailWord_5179357) baseStart_5179357 baseEnd_5179357 := by
    simpa [prefixWord, tailWord_5179357, baseEnd_5179357] using wordTrace_append hprefix tailTrace_5179357
  have hstable : (prefixWord ++ tailWord_5179357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5179357).length < 2 ^ (prefixWord ++ tailWord_5179357).sum := by decide
  have hdescent : baseEnd_5179357 < baseStart_5179357 := by decide
  rcases family_descends (prefixWord ++ tailWord_5179357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5179363 : List Nat := [1, 1, 1, 6, 1, 2, 2, 3, 6]
def baseStart_5179363 : Nat := 118140960795 + 5179363 * 2 ^ 59
def prefixEnd_5179363 : Nat := 4983230072969 + 3 ^ 40 * 5179363 * 2
def baseEnd_5179363 : Nat := 295500300345880494682561

theorem tailTrace_5179363 : CollatzResearch.WordTrace tailWord_5179363 prefixEnd_5179363 295500300345880494682561 := by
  unfold tailWord_5179363
  simp only [CollatzResearch.WordTrace]
  refine ⟨188906887935059890621710743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125937925290039927081140495 188906887935059890621710743)
  ·
    refine ⟨283360331902589835932566115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188906887935059890621710743 283360331902589835932566115)
    ·
      refine ⟨425040497853884753898849173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 283360331902589835932566115 425040497853884753898849173)
      ·
        refine ⟨19923773336900847839008555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 425040497853884753898849173 19923773336900847839008555)
        ·
          refine ⟨29885660005351271758512833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19923773336900847839008555 29885660005351271758512833)
          ·
            refine ⟨22414245004013453818884625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29885660005351271758512833 22414245004013453818884625)
            ·
              refine ⟨16810683753010090364163469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22414245004013453818884625 16810683753010090364163469)
              ·
                refine ⟨6304006407378783886561301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16810683753010090364163469 6304006407378783886561301)
                ·
                  refine ⟨295500300345880494682561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6304006407378783886561301 295500300345880494682561)
                  ·
                    rfl

theorem cell23_5179363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 3, 6].length) (baseStart_5179363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5179363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5179363 prefixEnd_5179363 := by exact prefixLift 5179363
  have htrace : WordTrace (prefixWord ++ tailWord_5179363) baseStart_5179363 baseEnd_5179363 := by
    simpa [prefixWord, tailWord_5179363, baseEnd_5179363] using wordTrace_append hprefix tailTrace_5179363
  have hstable : (prefixWord ++ tailWord_5179363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5179363).length < 2 ^ (prefixWord ++ tailWord_5179363).sum := by decide
  have hdescent : baseEnd_5179363 < baseStart_5179363 := by decide
  rcases family_descends (prefixWord ++ tailWord_5179363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5179377 : List Nat := [1, 2, 2, 2, 5, 2, 1, 1, 2, 2, 3]
def baseStart_5179377 : Nat := 118140960795 + 5179377 * 2 ^ 59
def prefixEnd_5179377 : Nat := 4983230072969 + 3 ^ 40 * 5179377 * 2
def baseEnd_5179377 : Nat := 2659509891842087397367985

theorem tailTrace_5179377 : CollatzResearch.WordTrace tailWord_5179377 prefixEnd_5179377 2659509891842087397367985 := by
  unfold tailWord_5179377
  simp only [CollatzResearch.WordTrace]
  refine ⟨188907398557009171012720385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125938265704672780675146923 188907398557009171012720385)
  ·
    refine ⟨141680548917756878259540289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188907398557009171012720385 141680548917756878259540289)
    ·
      refine ⟨106260411688317658694655217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141680548917756878259540289 106260411688317658694655217)
      ·
        refine ⟨79695308766238244020991413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106260411688317658694655217 79695308766238244020991413)
        ·
          refine ⟨7471435196834835376967945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 79695308766238244020991413 7471435196834835376967945)
          ·
            refine ⟨5603576397626126532725959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7471435196834835376967945 5603576397626126532725959)
            ·
              refine ⟨8405364596439189799088939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5603576397626126532725959 8405364596439189799088939)
              ·
                refine ⟨12608046894658784698633409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8405364596439189799088939 12608046894658784698633409)
                ·
                  refine ⟨9456035170994088523975057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12608046894658784698633409 9456035170994088523975057)
                  ·
                    refine ⟨7092026378245566392981293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9456035170994088523975057 7092026378245566392981293)
                    ·
                      refine ⟨2659509891842087397367985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7092026378245566392981293 2659509891842087397367985)
                      ·
                        rfl

theorem cell23_5179377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 1, 1, 2, 2, 3].length) (baseStart_5179377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5179377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5179377 prefixEnd_5179377 := by exact prefixLift 5179377
  have htrace : WordTrace (prefixWord ++ tailWord_5179377) baseStart_5179377 baseEnd_5179377 := by
    simpa [prefixWord, tailWord_5179377, baseEnd_5179377] using wordTrace_append hprefix tailTrace_5179377
  have hstable : (prefixWord ++ tailWord_5179377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5179377).length < 2 ^ (prefixWord ++ tailWord_5179377).sum := by decide
  have hdescent : baseEnd_5179377 < baseStart_5179377 := by decide
  rcases family_descends (prefixWord ++ tailWord_5179377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5179386 : List Nat := [3, 1, 1, 1, 1, 2, 1, 1, 1, 6, 5]
def baseStart_5179386 : Nat := 118140960795 + 5179386 * 2 ^ 59
def prefixEnd_5179386 : Nat := 4983230072969 + 3 ^ 40 * 5179386 * 2
def baseEnd_5179386 : Nat := 2659514513167977862155443

theorem tailTrace_5179386 : CollatzResearch.WordTrace tailWord_5179386 prefixEnd_5179386 2659514513167977862155443 := by
  unfold tailWord_5179386
  simp only [CollatzResearch.WordTrace]
  refine ⟨47226931703494141387449503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125938484542651043699865341 47226931703494141387449503)
  ·
    refine ⟨70840397555241212081174255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47226931703494141387449503 70840397555241212081174255)
    ·
      refine ⟨106260596332861818121761383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70840397555241212081174255 106260596332861818121761383)
      ·
        refine ⟨159390894499292727182642075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106260596332861818121761383 159390894499292727182642075)
        ·
          refine ⟨239086341748939090773963113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159390894499292727182642075 239086341748939090773963113)
          ·
            refine ⟨179314756311704318080472335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 239086341748939090773963113 179314756311704318080472335)
            ·
              refine ⟨268972134467556477120708503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 179314756311704318080472335 268972134467556477120708503)
              ·
                refine ⟨403458201701334715681062755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 268972134467556477120708503 403458201701334715681062755)
                ·
                  refine ⟨605187302552002073521594133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 403458201701334715681062755 605187302552002073521594133)
                  ·
                    refine ⟨28368154807125097196324725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 605187302552002073521594133 28368154807125097196324725)
                    ·
                      refine ⟨2659514513167977862155443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28368154807125097196324725 2659514513167977862155443)
                      ·
                        rfl

theorem cell23_5179386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 1, 6, 5].length) (baseStart_5179386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5179386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5179386 prefixEnd_5179386 := by exact prefixLift 5179386
  have htrace : WordTrace (prefixWord ++ tailWord_5179386) baseStart_5179386 baseEnd_5179386 := by
    simpa [prefixWord, tailWord_5179386, baseEnd_5179386] using wordTrace_append hprefix tailTrace_5179386
  have hstable : (prefixWord ++ tailWord_5179386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5179386).length < 2 ^ (prefixWord ++ tailWord_5179386).sum := by decide
  have hdescent : baseEnd_5179386 < baseStart_5179386 := by decide
  rcases family_descends (prefixWord ++ tailWord_5179386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5179400 : List Nat := [2, 1, 3, 2, 1, 2, 2, 1, 4, 3, 2]
def baseStart_5179400 : Nat := 118140960795 + 5179400 * 2 ^ 59
def prefixEnd_5179400 : Nat := 4983230072969 + 3 ^ 40 * 5179400 * 2
def baseEnd_5179400 : Nat := 2659521701897140807380379

theorem tailTrace_5179400 : CollatzResearch.WordTrace tailWord_5179400 prefixEnd_5179400 2659521701897140807380379 := by
  unfold tailWord_5179400
  simp only [CollatzResearch.WordTrace]
  refine ⟨94454118717962922970403827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125938824957283897293871769 94454118717962922970403827)
  ·
    refine ⟨141681178076944384455605741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94454118717962922970403827 141681178076944384455605741)
    ·
      refine ⟨53130441778854144170852153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141681178076944384455605741 53130441778854144170852153)
      ·
        refine ⟨39847831334140608128139115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53130441778854144170852153 39847831334140608128139115)
        ·
          refine ⟨59771747001210912192208673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39847831334140608128139115 59771747001210912192208673)
          ·
            refine ⟨44828810250908184144156505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59771747001210912192208673 44828810250908184144156505)
            ·
              refine ⟨33621607688181138108117379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44828810250908184144156505 33621607688181138108117379)
              ·
                refine ⟨50432411532271707162176069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33621607688181138108117379 50432411532271707162176069)
                ·
                  refine ⟨9456077162300945092908013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50432411532271707162176069 9456077162300945092908013)
                  ·
                    refine ⟨3546028935862854409840505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9456077162300945092908013 3546028935862854409840505)
                    ·
                      refine ⟨2659521701897140807380379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3546028935862854409840505 2659521701897140807380379)
                      ·
                        rfl

theorem cell23_5179400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 1, 4, 3, 2].length) (baseStart_5179400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5179400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5179400 prefixEnd_5179400 := by exact prefixLift 5179400
  have htrace : WordTrace (prefixWord ++ tailWord_5179400) baseStart_5179400 baseEnd_5179400 := by
    simpa [prefixWord, tailWord_5179400, baseEnd_5179400] using wordTrace_append hprefix tailTrace_5179400
  have hstable : (prefixWord ++ tailWord_5179400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5179400).length < 2 ^ (prefixWord ++ tailWord_5179400).sum := by decide
  have hdescent : baseEnd_5179400 < baseStart_5179400 := by decide
  rcases family_descends (prefixWord ++ tailWord_5179400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5179433 : List Nat := [1, 2, 1, 1, 1, 1, 1, 1, 9, 2, 3]
def baseStart_5179433 : Nat := 118140960795 + 5179433 * 2 ^ 59
def prefixEnd_5179433 : Nat := 4983230072969 + 3 ^ 40 * 5179433 * 2
def baseEnd_5179433 : Nat := 2659538646758739178267727

theorem tailTrace_5179433 : CollatzResearch.WordTrace tailWord_5179433 prefixEnd_5179433 2659538646758739178267727 := by
  unfold tailWord_5179433
  simp only [CollatzResearch.WordTrace]
  refine ⟨188909441044806292576758953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125939627363204195051172635 188909441044806292576758953)
  ·
    refine ⟨141682080783604719432569215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188909441044806292576758953 141682080783604719432569215)
    ·
      refine ⟨212523121175407079148853823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141682080783604719432569215 212523121175407079148853823)
      ·
        refine ⟨318784681763110618723280735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212523121175407079148853823 318784681763110618723280735)
        ·
          refine ⟨478177022644665928084921103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 318784681763110618723280735 478177022644665928084921103)
          ·
            refine ⟨717265533966998892127381655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 478177022644665928084921103 717265533966998892127381655)
            ·
              refine ⟨1075898300950498338191072483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 717265533966998892127381655 1075898300950498338191072483)
              ·
                refine ⟨1613847451425747507286608725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1075898300950498338191072483 1613847451425747507286608725)
                ·
                  refine ⟨9456137410697739300507473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 1613847451425747507286608725 9456137410697739300507473)
                  ·
                    refine ⟨7092103058023304475380605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9456137410697739300507473 7092103058023304475380605)
                    ·
                      refine ⟨2659538646758739178267727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7092103058023304475380605 2659538646758739178267727)
                      ·
                        rfl

theorem cell23_5179433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 9, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 9, 2, 3].length) (baseStart_5179433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5179433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5179433 prefixEnd_5179433 := by exact prefixLift 5179433
  have htrace : WordTrace (prefixWord ++ tailWord_5179433) baseStart_5179433 baseEnd_5179433 := by
    simpa [prefixWord, tailWord_5179433, baseEnd_5179433] using wordTrace_append hprefix tailTrace_5179433
  have hstable : (prefixWord ++ tailWord_5179433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5179433).length < 2 ^ (prefixWord ++ tailWord_5179433).sum := by decide
  have hdescent : baseEnd_5179433 < baseStart_5179433 := by decide
  rcases family_descends (prefixWord ++ tailWord_5179433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5179443 : List Nat := [1, 1, 1, 2, 4, 1, 2, 4, 1, 2, 4]
def baseStart_5179443 : Nat := 118140960795 + 5179443 * 2 ^ 59
def prefixEnd_5179443 : Nat := 4983230072969 + 3 ^ 40 * 5179443 * 2
def baseEnd_5179443 : Nat := 2659543781565284139142681

theorem tailTrace_5179443 : CollatzResearch.WordTrace tailWord_5179443 prefixEnd_5179443 2659543781565284139142681 := by
  unfold tailWord_5179443
  simp only [CollatzResearch.WordTrace]
  refine ⟨188909805774770064284622983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125939870516513376189748655 188909805774770064284622983)
  ·
    refine ⟨283364708662155096426934475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188909805774770064284622983 283364708662155096426934475)
    ·
      refine ⟨425047062993232644640401713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 283364708662155096426934475 425047062993232644640401713)
      ·
        refine ⟨318785297244924483480301285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 425047062993232644640401713 318785297244924483480301285)
        ·
          refine ⟨59772243233423340652556491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 318785297244924483480301285 59772243233423340652556491)
          ·
            refine ⟨89658364850135010978834737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59772243233423340652556491 89658364850135010978834737)
            ·
              refine ⟨67243773637601258234126053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89658364850135010978834737 67243773637601258234126053)
              ·
                refine ⟨12608207557050235918898635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 67243773637601258234126053 12608207557050235918898635)
                ·
                  refine ⟨18912311335575353878347953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12608207557050235918898635 18912311335575353878347953)
                  ·
                    refine ⟨14184233501681515408760965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18912311335575353878347953 14184233501681515408760965)
                    ·
                      refine ⟨2659543781565284139142681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14184233501681515408760965 2659543781565284139142681)
                      ·
                        rfl

theorem cell23_5179443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 4, 1, 2, 4].length) (baseStart_5179443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5179443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5179443 prefixEnd_5179443 := by exact prefixLift 5179443
  have htrace : WordTrace (prefixWord ++ tailWord_5179443) baseStart_5179443 baseEnd_5179443 := by
    simpa [prefixWord, tailWord_5179443, baseEnd_5179443] using wordTrace_append hprefix tailTrace_5179443
  have hstable : (prefixWord ++ tailWord_5179443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5179443).length < 2 ^ (prefixWord ++ tailWord_5179443).sum := by decide
  have hdescent : baseEnd_5179443 < baseStart_5179443 := by decide
  rcases family_descends (prefixWord ++ tailWord_5179443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5179484 : List Nat := [2, 2, 4, 1, 1, 4, 1, 2, 1, 2, 3]
def baseStart_5179484 : Nat := 118140960795 + 5179484 * 2 ^ 59
def prefixEnd_5179484 : Nat := 4983230072969 + 3 ^ 40 * 5179484 * 2
def baseEnd_5179484 : Nat := 2659564834272118478729993

theorem tailTrace_5179484 : CollatzResearch.WordTrace tailWord_5179484 prefixEnd_5179484 2659564834272118478729993 := by
  unfold tailWord_5179484
  simp only [CollatzResearch.WordTrace]
  refine ⟨94455650583810764143432753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125940867445081018857910337 94455650583810764143432753)
  ·
    refine ⟨70841737937858073107574565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94455650583810764143432753 70841737937858073107574565)
    ·
      refine ⟨13282825863348388707670231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70841737937858073107574565 13282825863348388707670231)
      ·
        refine ⟨19924238795022583061505347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13282825863348388707670231 19924238795022583061505347)
        ·
          refine ⟨29886358192533874592258021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19924238795022583061505347 29886358192533874592258021)
          ·
            refine ⟨5603692161100101486048379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29886358192533874592258021 5603692161100101486048379)
            ·
              refine ⟨8405538241650152229072569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5603692161100101486048379 8405538241650152229072569)
              ·
                refine ⟨6304153681237614171804427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8405538241650152229072569 6304153681237614171804427)
                ·
                  refine ⟨9456230521856421257706641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6304153681237614171804427 9456230521856421257706641)
                  ·
                    refine ⟨7092172891392315943279981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9456230521856421257706641 7092172891392315943279981)
                    ·
                      refine ⟨2659564834272118478729993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7092172891392315943279981 2659564834272118478729993)
                      ·
                        rfl

theorem cell23_5179484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 1, 2, 1, 2, 3].length) (baseStart_5179484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5179484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5179484 prefixEnd_5179484 := by exact prefixLift 5179484
  have htrace : WordTrace (prefixWord ++ tailWord_5179484) baseStart_5179484 baseEnd_5179484 := by
    simpa [prefixWord, tailWord_5179484, baseEnd_5179484] using wordTrace_append hprefix tailTrace_5179484
  have hstable : (prefixWord ++ tailWord_5179484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5179484).length < 2 ^ (prefixWord ++ tailWord_5179484).sum := by decide
  have hdescent : baseEnd_5179484 < baseStart_5179484 := by decide
  rcases family_descends (prefixWord ++ tailWord_5179484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5179520 : List Nat := [2, 1, 1, 2, 1, 3, 1, 1, 5, 4, 2]
def baseStart_5179520 : Nat := 118140960795 + 5179520 * 2 ^ 59
def prefixEnd_5179520 : Nat := 4983230072969 + 3 ^ 40 * 5179520 * 2
def baseEnd_5179520 : Nat := 2659583319575680337879827

theorem tailTrace_5179520 : CollatzResearch.WordTrace tailWord_5179520 prefixEnd_5179520 2659583319575680337879827 := by
  unfold tailWord_5179520
  simp only [CollatzResearch.WordTrace]
  refine ⟨94456307097745553217588007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125941742796994070956784009 94456307097745553217588007)
  ·
    refine ⟨141684460646618329826382011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94456307097745553217588007 141684460646618329826382011)
    ·
      refine ⟨212526690969927494739573017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141684460646618329826382011 212526690969927494739573017)
      ·
        refine ⟨159395018227445621054679763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 212526690969927494739573017 159395018227445621054679763)
        ·
          refine ⟨239092527341168431582019645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159395018227445621054679763 239092527341168431582019645)
          ·
            refine ⟨89659697752938161843257367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 239092527341168431582019645 89659697752938161843257367)
            ·
              refine ⟨134489546629407242764886051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89659697752938161843257367 134489546629407242764886051)
              ·
                refine ⟨201734319944110864147329077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 134489546629407242764886051 201734319944110864147329077)
                ·
                  refine ⟨18912592494760393513812101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 201734319944110864147329077 18912592494760393513812101)
                  ·
                    refine ⟨3546111092767573783839769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18912592494760393513812101 3546111092767573783839769)
                    ·
                      refine ⟨2659583319575680337879827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3546111092767573783839769 2659583319575680337879827)
                      ·
                        rfl

theorem cell23_5179520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 5, 4, 2].length) (baseStart_5179520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5179520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5179520 prefixEnd_5179520 := by exact prefixLift 5179520
  have htrace : WordTrace (prefixWord ++ tailWord_5179520) baseStart_5179520 baseEnd_5179520 := by
    simpa [prefixWord, tailWord_5179520, baseEnd_5179520] using wordTrace_append hprefix tailTrace_5179520
  have hstable : (prefixWord ++ tailWord_5179520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5179520).length < 2 ^ (prefixWord ++ tailWord_5179520).sum := by decide
  have hdescent : baseEnd_5179520 < baseStart_5179520 := by decide
  rcases family_descends (prefixWord ++ tailWord_5179520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5179530 : List Nat := [3, 1, 2, 3, 1, 3, 1, 1, 2, 6]
def baseStart_5179530 : Nat := 118140960795 + 5179530 * 2 ^ 59
def prefixEnd_5179530 : Nat := 4983230072969 + 3 ^ 40 * 5179530 * 2
def baseEnd_5179530 : Nat := 886529484794075099584927

theorem tailTrace_5179530 : CollatzResearch.WordTrace tailWord_5179530 prefixEnd_5179530 886529484794075099584927 := by
  unfold tailWord_5179530
  simp only [CollatzResearch.WordTrace]
  refine ⟨47228244731363719535760011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125941985950303252095360029 47228244731363719535760011)
  ·
    refine ⟨70842367097045579303640017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47228244731363719535760011 70842367097045579303640017)
    ·
      refine ⟨53131775322784184477730013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70842367097045579303640017 53131775322784184477730013)
      ·
        refine ⟨19924415746044069179148755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53131775322784184477730013 19924415746044069179148755)
        ·
          refine ⟨29886623619066103768723133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19924415746044069179148755 29886623619066103768723133)
          ·
            refine ⟨11207483857149788913271175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29886623619066103768723133 11207483857149788913271175)
            ·
              refine ⟨16811225785724683369906763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11207483857149788913271175 16811225785724683369906763)
              ·
                refine ⟨25216838678587025054860145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16811225785724683369906763 25216838678587025054860145)
                ·
                  refine ⟨18912629008940268791145109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25216838678587025054860145 18912629008940268791145109)
                  ·
                    refine ⟨886529484794075099584927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18912629008940268791145109 886529484794075099584927)
                    ·
                      rfl

theorem cell23_5179530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 1, 2, 6].length) (baseStart_5179530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5179530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5179530 prefixEnd_5179530 := by exact prefixLift 5179530
  have htrace : WordTrace (prefixWord ++ tailWord_5179530) baseStart_5179530 baseEnd_5179530 := by
    simpa [prefixWord, tailWord_5179530, baseEnd_5179530] using wordTrace_append hprefix tailTrace_5179530
  have hstable : (prefixWord ++ tailWord_5179530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5179530).length < 2 ^ (prefixWord ++ tailWord_5179530).sum := by decide
  have hdescent : baseEnd_5179530 < baseStart_5179530 := by decide
  rcases family_descends (prefixWord ++ tailWord_5179530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5179554 : List Nat := [3, 3, 1, 3, 1, 1, 2, 2, 1, 4, 2]
def baseStart_5179554 : Nat := 118140960795 + 5179554 * 2 ^ 59
def prefixEnd_5179554 : Nat := 4983230072969 + 3 ^ 40 * 5179554 * 2
def baseEnd_5179554 : Nat := 2659600777917933204854671

theorem tailTrace_5179554 : CollatzResearch.WordTrace tailWord_5179554 prefixEnd_5179554 2659600777917933204854671 := by
  unfold tailWord_5179554
  simp only [CollatzResearch.WordTrace]
  refine ⟨47228463569341982560478429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125942569518245286827942477 47228463569341982560478429)
  ·
    refine ⟨17710673838503243460179411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47228463569341982560478429 17710673838503243460179411)
    ·
      refine ⟨26566010757754865190269117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17710673838503243460179411 26566010757754865190269117)
      ·
        refine ⟨9962254034158074446350919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26566010757754865190269117 9962254034158074446350919)
        ·
          refine ⟨14943381051237111669526379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9962254034158074446350919 14943381051237111669526379)
          ·
            refine ⟨22415071576855667504289569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14943381051237111669526379 22415071576855667504289569)
            ·
              refine ⟨16811303682641750628217177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22415071576855667504289569 16811303682641750628217177)
              ·
                refine ⟨12608477761981312971162883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16811303682641750628217177 12608477761981312971162883)
                ·
                  refine ⟨18912716642971969456744325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12608477761981312971162883 18912716642971969456744325)
                  ·
                    refine ⟨3546134370557244273139561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18912716642971969456744325 3546134370557244273139561)
                    ·
                      refine ⟨2659600777917933204854671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3546134370557244273139561 2659600777917933204854671)
                      ·
                        rfl

theorem cell23_5179554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 2, 1, 4, 2].length) (baseStart_5179554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5179554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5179554 prefixEnd_5179554 := by exact prefixLift 5179554
  have htrace : WordTrace (prefixWord ++ tailWord_5179554) baseStart_5179554 baseEnd_5179554 := by
    simpa [prefixWord, tailWord_5179554, baseEnd_5179554] using wordTrace_append hprefix tailTrace_5179554
  have hstable : (prefixWord ++ tailWord_5179554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5179554).length < 2 ^ (prefixWord ++ tailWord_5179554).sum := by decide
  have hdescent : baseEnd_5179554 < baseStart_5179554 := by decide
  rcases family_descends (prefixWord ++ tailWord_5179554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5179570 : List Nat := [3, 2, 1, 1, 1, 3, 1, 1, 4, 3, 3]
def baseStart_5179570 : Nat := 118140960795 + 5179570 * 2 ^ 59
def prefixEnd_5179570 : Nat := 4983230072969 + 3 ^ 40 * 5179570 * 2
def baseEnd_5179570 : Nat := 2659608993608405142254597

theorem tailTrace_5179570 : CollatzResearch.WordTrace tailWord_5179570 prefixEnd_5179570 2659608993608405142254597 := by
  unfold tailWord_5179570
  simp only [CollatzResearch.WordTrace]
  refine ⟨47228609461327491243624041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125942958563539976649664109 47228609461327491243624041)
  ·
    refine ⟨35421457095995618432718031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47228609461327491243624041 35421457095995618432718031)
    ·
      refine ⟨53132185643993427649077047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35421457095995618432718031 53132185643993427649077047)
      ·
        refine ⟨79698278465990141473615571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53132185643993427649077047 79698278465990141473615571)
        ·
          refine ⟨119547417698985212210423357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79698278465990141473615571 119547417698985212210423357)
          ·
            refine ⟨44830281637119454578908759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 119547417698985212210423357 44830281637119454578908759)
            ·
              refine ⟨67245422455679181868363139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44830281637119454578908759 67245422455679181868363139)
              ·
                refine ⟨100868133683518772802544709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67245422455679181868363139 100868133683518772802544709)
                ·
                  refine ⟨18912775065659769900477133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 100868133683518772802544709 18912775065659769900477133)
                  ·
                    refine ⟨7092290649622413712678925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18912775065659769900477133 7092290649622413712678925)
                    ·
                      refine ⟨2659608993608405142254597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7092290649622413712678925 2659608993608405142254597)
                      ·
                        rfl

theorem cell23_5179570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 4, 3, 3].length) (baseStart_5179570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5179570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5179570 prefixEnd_5179570 := by exact prefixLift 5179570
  have htrace : WordTrace (prefixWord ++ tailWord_5179570) baseStart_5179570 baseEnd_5179570 := by
    simpa [prefixWord, tailWord_5179570, baseEnd_5179570] using wordTrace_append hprefix tailTrace_5179570
  have hstable : (prefixWord ++ tailWord_5179570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5179570).length < 2 ^ (prefixWord ++ tailWord_5179570).sum := by decide
  have hdescent : baseEnd_5179570 < baseStart_5179570 := by decide
  rcases family_descends (prefixWord ++ tailWord_5179570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5179583 : List Nat := [1, 1, 2, 2, 2, 2, 1, 3, 1, 1, 7]
def baseStart_5179583 : Nat := 118140960795 + 5179583 * 2 ^ 59
def prefixEnd_5179583 : Nat := 4983230072969 + 3 ^ 40 * 5179583 * 2
def baseEnd_5179583 : Nat := 2659615668856913591392037

theorem tailTrace_5179583 : CollatzResearch.WordTrace tailWord_5179583 prefixEnd_5179583 2659615668856913591392037 := by
  unfold tailWord_5179583
  simp only [CollatzResearch.WordTrace]
  refine ⟨188914911994262868194719403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125943274662841912129812935 188914911994262868194719403)
  ·
    refine ⟨283372367991394302292079105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188914911994262868194719403 283372367991394302292079105)
    ·
      refine ⟨212529275993545726719059329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 283372367991394302292079105 212529275993545726719059329)
      ·
        refine ⟨159396956995159295039294497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 212529275993545726719059329 159396956995159295039294497)
        ·
          refine ⟨119547717746369471279470873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 159396956995159295039294497 119547717746369471279470873)
          ·
            refine ⟨89660788309777103459603155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119547717746369471279470873 89660788309777103459603155)
            ·
              refine ⟨134491182464665655189404733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89660788309777103459603155 134491182464665655189404733)
              ·
                refine ⟨50434193424249620696026775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 134491182464665655189404733 50434193424249620696026775)
                ·
                  refine ⟨75651290136374431044040163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50434193424249620696026775 75651290136374431044040163)
                  ·
                    refine ⟨113476935204561646566060245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 75651290136374431044040163 113476935204561646566060245)
                    ·
                      refine ⟨2659615668856913591392037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 113476935204561646566060245 2659615668856913591392037)
                      ·
                        rfl

theorem cell23_5179583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 3, 1, 1, 7].length) (baseStart_5179583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5179583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5179583 prefixEnd_5179583 := by exact prefixLift 5179583
  have htrace : WordTrace (prefixWord ++ tailWord_5179583) baseStart_5179583 baseEnd_5179583 := by
    simpa [prefixWord, tailWord_5179583, baseEnd_5179583] using wordTrace_append hprefix tailTrace_5179583
  have hstable : (prefixWord ++ tailWord_5179583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5179583).length < 2 ^ (prefixWord ++ tailWord_5179583).sum := by decide
  have hdescent : baseEnd_5179583 < baseStart_5179583 := by decide
  rcases family_descends (prefixWord ++ tailWord_5179583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5179588 : List Nat := [2, 3, 3, 1, 2, 2, 3, 1, 2, 2, 2]
def baseStart_5179588 : Nat := 118140960795 + 5179588 * 2 ^ 59
def prefixEnd_5179588 : Nat := 4983230072969 + 3 ^ 40 * 5179588 * 2
def baseEnd_5179588 : Nat := 2659618236260186071829515

theorem tailTrace_5179588 : CollatzResearch.WordTrace tailWord_5179588 prefixEnd_5179588 2659618236260186071829515 := by
  unfold tailWord_5179588
  simp only [CollatzResearch.WordTrace]
  refine ⟨94457547179622377024325709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125943396239496502699100945 94457547179622377024325709)
  ·
    refine ⟨35421580192358391384122141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94457547179622377024325709 35421580192358391384122141)
    ·
      refine ⟨13283092572134396769045803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35421580192358391384122141 13283092572134396769045803)
      ·
        refine ⟨19924638858201595153568705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13283092572134396769045803 19924638858201595153568705)
        ·
          refine ⟨14943479143651196365176529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19924638858201595153568705 14943479143651196365176529)
          ·
            refine ⟨11207609357738397273882397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14943479143651196365176529 11207609357738397273882397)
            ·
              refine ⟨4202853509151898977705899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11207609357738397273882397 4202853509151898977705899)
              ·
                refine ⟨6304280263727848466558849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4202853509151898977705899 6304280263727848466558849)
                ·
                  refine ⟨4728210197795886349919137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6304280263727848466558849 4728210197795886349919137)
                  ·
                    refine ⟨3546157648346914762439353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4728210197795886349919137 3546157648346914762439353)
                    ·
                      refine ⟨2659618236260186071829515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3546157648346914762439353 2659618236260186071829515)
                      ·
                        rfl

theorem cell23_5179588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 3, 1, 2, 2, 2].length) (baseStart_5179588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5179588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5179588 prefixEnd_5179588 := by exact prefixLift 5179588
  have htrace : WordTrace (prefixWord ++ tailWord_5179588) baseStart_5179588 baseEnd_5179588 := by
    simpa [prefixWord, tailWord_5179588, baseEnd_5179588] using wordTrace_append hprefix tailTrace_5179588
  have hstable : (prefixWord ++ tailWord_5179588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5179588).length < 2 ^ (prefixWord ++ tailWord_5179588).sum := by decide
  have hdescent : baseEnd_5179588 < baseStart_5179588 := by decide
  rcases family_descends (prefixWord ++ tailWord_5179588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5179610 : List Nat := [3, 1, 1, 2, 2, 1, 4, 1, 1, 3, 4]
def baseStart_5179610 : Nat := 118140960795 + 5179610 * 2 ^ 59
def prefixEnd_5179610 : Nat := 4983230072969 + 3 ^ 40 * 5179610 * 2
def baseEnd_5179610 : Nat := 2659629532834584985754413

theorem tailTrace_5179610 : CollatzResearch.WordTrace tailWord_5179610 prefixEnd_5179610 2659629532834584985754413 := by
  unfold tailWord_5179610
  simp only [CollatzResearch.WordTrace]
  refine ⟨47228974191291262951488071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125943931176776701203968189 47228974191291262951488071)
  ·
    refine ⟨70843461286936894427232107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47228974191291262951488071 70843461286936894427232107)
    ·
      refine ⟨106265191930405341640848161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70843461286936894427232107 106265191930405341640848161)
      ·
        refine ⟨79698893947804006230636121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106265191930405341640848161 79698893947804006230636121)
        ·
          refine ⟨59774170460853004672977091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79698893947804006230636121 59774170460853004672977091)
          ·
            refine ⟨89661255691279507009465637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59774170460853004672977091 89661255691279507009465637)
            ·
              refine ⟨16811485442114907564274807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 89661255691279507009465637 16811485442114907564274807)
              ·
                refine ⟨25217228163172361346412211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16811485442114907564274807 25217228163172361346412211)
                ·
                  refine ⟨37825842244758542019618317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25217228163172361346412211 37825842244758542019618317)
                  ·
                    refine ⟨14184690841784453257356869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37825842244758542019618317 14184690841784453257356869)
                    ·
                      refine ⟨2659629532834584985754413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14184690841784453257356869 2659629532834584985754413)
                      ·
                        rfl

theorem cell23_5179610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 1, 1, 3, 4].length) (baseStart_5179610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5179610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5179610 prefixEnd_5179610 := by exact prefixLift 5179610
  have htrace : WordTrace (prefixWord ++ tailWord_5179610) baseStart_5179610 baseEnd_5179610 := by
    simpa [prefixWord, tailWord_5179610, baseEnd_5179610] using wordTrace_append hprefix tailTrace_5179610
  have hstable : (prefixWord ++ tailWord_5179610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5179610).length < 2 ^ (prefixWord ++ tailWord_5179610).sum := by decide
  have hdescent : baseEnd_5179610 < baseStart_5179610 := by decide
  rcases family_descends (prefixWord ++ tailWord_5179610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5179744 : List Nat := [2, 1, 1, 3, 5, 1, 1, 1, 4, 4]
def baseStart_5179744 : Nat := 118140960795 + 5179744 * 2 ^ 59
def prefixEnd_5179744 : Nat := 4983230072969 + 3 ^ 40 * 5179744 * 2
def baseEnd_5179744 : Nat := 886566113080762487159599

theorem tailTrace_5179744 : CollatzResearch.WordTrace tailWord_5179744 prefixEnd_5179744 886566113080762487159599 := by
  unfold tailWord_5179744
  simp only [CollatzResearch.WordTrace]
  refine ⟨94460392073339796345665143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125947189431119728460886857 94460392073339796345665143)
  ·
    refine ⟨141690588110009694518497715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94460392073339796345665143 141690588110009694518497715)
    ·
      refine ⟨212535882165014541777746573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141690588110009694518497715 212535882165014541777746573)
      ·
        refine ⟨79700955811880453166654965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 212535882165014541777746573 79700955811880453166654965)
        ·
          refine ⟨7471964607363792484373903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 79700955811880453166654965 7471964607363792484373903)
          ·
            refine ⟨11207946911045688726560855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7471964607363792484373903 11207946911045688726560855)
            ·
              refine ⟨16811920366568533089841283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11207946911045688726560855 16811920366568533089841283)
              ·
                refine ⟨25217880549852799634761925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16811920366568533089841283 25217880549852799634761925)
                ·
                  refine ⟨4728352603097399931517861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25217880549852799634761925 4728352603097399931517861)
                  ·
                    refine ⟨886566113080762487159599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4728352603097399931517861 886566113080762487159599)
                    ·
                      rfl

theorem cell23_5179744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 1, 4, 4].length) (baseStart_5179744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5179744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5179744 prefixEnd_5179744 := by exact prefixLift 5179744
  have htrace : WordTrace (prefixWord ++ tailWord_5179744) baseStart_5179744 baseEnd_5179744 := by
    simpa [prefixWord, tailWord_5179744, baseEnd_5179744] using wordTrace_append hprefix tailTrace_5179744
  have hstable : (prefixWord ++ tailWord_5179744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5179744).length < 2 ^ (prefixWord ++ tailWord_5179744).sum := by decide
  have hdescent : baseEnd_5179744 < baseStart_5179744 := by decide
  rcases family_descends (prefixWord ++ tailWord_5179744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5179751 : List Nat := [1, 1, 5, 1, 3, 1, 1, 3, 3, 2, 2]
def baseStart_5179751 : Nat := 118140960795 + 5179751 * 2 ^ 59
def prefixEnd_5179751 : Nat := 4983230072969 + 3 ^ 40 * 5179751 * 2
def baseEnd_5179751 : Nat := 2659701933606868934091265

theorem tailTrace_5179751 : CollatzResearch.WordTrace tailWord_5179751 prefixEnd_5179751 2659701933606868934091265 := by
  unfold tailWord_5179751
  simp only [CollatzResearch.WordTrace]
  refine ⟨188921039457654232886835107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125947359638436155257890071 188921039457654232886835107)
  ·
    refine ⟨283381559186481349330252661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188921039457654232886835107 283381559186481349330252661)
    ·
      refine ⟨26567021173732626499711187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 283381559186481349330252661 26567021173732626499711187)
      ·
        refine ⟨39850531760598939749566781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26567021173732626499711187 39850531760598939749566781)
        ·
          refine ⟨14943949410224602406087543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39850531760598939749566781 14943949410224602406087543)
          ·
            refine ⟨22415924115336903609131315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14943949410224602406087543 22415924115336903609131315)
            ·
              refine ⟨33623886173005355413696973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22415924115336903609131315 33623886173005355413696973)
              ·
                refine ⟨12608957314877008280136365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33623886173005355413696973 12608957314877008280136365)
                ·
                  refine ⟨4728358993078878105051137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12608957314877008280136365 4728358993078878105051137)
                  ·
                    refine ⟨3546269244809158578788353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4728358993078878105051137 3546269244809158578788353)
                    ·
                      refine ⟨2659701933606868934091265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3546269244809158578788353 2659701933606868934091265)
                      ·
                        rfl

theorem cell23_5179751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 3, 3, 2, 2].length) (baseStart_5179751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5179751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5179751 prefixEnd_5179751 := by exact prefixLift 5179751
  have htrace : WordTrace (prefixWord ++ tailWord_5179751) baseStart_5179751 baseEnd_5179751 := by
    simpa [prefixWord, tailWord_5179751, baseEnd_5179751] using wordTrace_append hprefix tailTrace_5179751
  have hstable : (prefixWord ++ tailWord_5179751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5179751).length < 2 ^ (prefixWord ++ tailWord_5179751).sum := by decide
  have hdescent : baseEnd_5179751 < baseStart_5179751 := by decide
  rcases family_descends (prefixWord ++ tailWord_5179751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5179754 : List Nat := [3, 1, 3, 3, 1, 2, 1, 2, 1, 1, 5]
def baseStart_5179754 : Nat := 118140960795 + 5179754 * 2 ^ 59
def prefixEnd_5179754 : Nat := 4983230072969 + 3 ^ 40 * 5179754 * 2
def baseEnd_5179754 : Nat := 2659703474048832422353751

theorem tailTrace_5179754 : CollatzResearch.WordTrace tailWord_5179754 prefixEnd_5179754 2659703474048832422353751 := by
  unfold tailWord_5179754
  simp only [CollatzResearch.WordTrace]
  refine ⟨47230287219160841099798579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125947432584428909599462877 47230287219160841099798579)
  ·
    refine ⟨70845430828741261649697869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47230287219160841099798579 70845430828741261649697869)
    ·
      refine ⟨26567036560777973118636701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70845430828741261649697869 26567036560777973118636701)
      ·
        refine ⟨9962638710291739919488763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26567036560777973118636701 9962638710291739919488763)
        ·
          refine ⟨14943958065437609879233145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9962638710291739919488763 14943958065437609879233145)
          ·
            refine ⟨11207968549078207409424859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14943958065437609879233145 11207968549078207409424859)
            ·
              refine ⟨16811952823617311114137289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11207968549078207409424859 16811952823617311114137289)
              ·
                refine ⟨12608964617712983335602967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16811952823617311114137289 12608964617712983335602967)
                ·
                  refine ⟨18913446926569475003404451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12608964617712983335602967 18913446926569475003404451)
                  ·
                    refine ⟨28370170389854212505106677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18913446926569475003404451 28370170389854212505106677)
                    ·
                      refine ⟨2659703474048832422353751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28370170389854212505106677 2659703474048832422353751)
                      ·
                        rfl

theorem cell23_5179754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_5179754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5179754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5179754 prefixEnd_5179754 := by exact prefixLift 5179754
  have htrace : WordTrace (prefixWord ++ tailWord_5179754) baseStart_5179754 baseEnd_5179754 := by
    simpa [prefixWord, tailWord_5179754, baseEnd_5179754] using wordTrace_append hprefix tailTrace_5179754
  have hstable : (prefixWord ++ tailWord_5179754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5179754).length < 2 ^ (prefixWord ++ tailWord_5179754).sum := by decide
  have hdescent : baseEnd_5179754 < baseStart_5179754 := by decide
  rcases family_descends (prefixWord ++ tailWord_5179754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5179767 : List Nat := [1, 1, 3, 1, 1, 2, 2, 5, 1, 3, 3]
def baseStart_5179767 : Nat := 118140960795 + 5179767 * 2 ^ 59
def prefixEnd_5179767 : Nat := 4983230072969 + 3 ^ 40 * 5179767 * 2
def baseEnd_5179767 : Nat := 2659710149297340871491191

theorem tailTrace_5179767 : CollatzResearch.WordTrace tailWord_5179767 prefixEnd_5179767 2659710149297340871491191 := by
  unfold tailWord_5179767
  simp only [CollatzResearch.WordTrace]
  refine ⟨188921623025596267619417555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125947748683730845079611703 188921623025596267619417555)
  ·
    refine ⟨283382434538394401429126333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188921623025596267619417555 283382434538394401429126333)
    ·
      refine ⟨106268412951897900535922375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 283382434538394401429126333 106268412951897900535922375)
      ·
        refine ⟨159402619427846850803883563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106268412951897900535922375 159402619427846850803883563)
        ·
          refine ⟨239103929141770276205825345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159402619427846850803883563 239103929141770276205825345)
          ·
            refine ⟨179327946856327707154369009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 239103929141770276205825345 179327946856327707154369009)
            ·
              refine ⟨134495960142245780365776757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 179327946856327707154369009 134495960142245780365776757)
              ·
                refine ⟨12608996263335541909291571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 134495960142245780365776757 12608996263335541909291571)
                ·
                  refine ⟨18913494395003312863937357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12608996263335541909291571 18913494395003312863937357)
                  ·
                    refine ⟨7092560398126242323976509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18913494395003312863937357 7092560398126242323976509)
                    ·
                      refine ⟨2659710149297340871491191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7092560398126242323976509 2659710149297340871491191)
                      ·
                        rfl

theorem cell23_5179767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 5, 1, 3, 3].length) (baseStart_5179767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5179767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5179767 prefixEnd_5179767 := by exact prefixLift 5179767
  have htrace : WordTrace (prefixWord ++ tailWord_5179767) baseStart_5179767 baseEnd_5179767 := by
    simpa [prefixWord, tailWord_5179767, baseEnd_5179767] using wordTrace_append hprefix tailTrace_5179767
  have hstable : (prefixWord ++ tailWord_5179767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5179767).length < 2 ^ (prefixWord ++ tailWord_5179767).sum := by decide
  have hdescent : baseEnd_5179767 < baseStart_5179767 := by decide
  rcases family_descends (prefixWord ++ tailWord_5179767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5179784 : List Nat := [2, 1, 3, 3, 1, 1, 1, 1, 6, 1, 3]
def baseStart_5179784 : Nat := 118140960795 + 5179784 * 2 ^ 59
def prefixEnd_5179784 : Nat := 4983230072969 + 3 ^ 40 * 5179784 * 2
def baseEnd_5179784 : Nat := 2659718878468467304978613

theorem tailTrace_5179784 : CollatzResearch.WordTrace tailWord_5179784 prefixEnd_5179784 2659718878468467304978613 := by
  unfold tailWord_5179784
  simp only [CollatzResearch.WordTrace]
  refine ⟨94461121533267339761393203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125948162044356453015190937 94461121533267339761393203)
  ·
    refine ⟨141691682299901009642089805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94461121533267339761393203 141691682299901009642089805)
    ·
      refine ⟨53134380862462878615783677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141691682299901009642089805 53134380862462878615783677)
      ·
        refine ⟨19925392823423579480918879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53134380862462878615783677 19925392823423579480918879)
        ·
          refine ⟨29888089235135369221378319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19925392823423579480918879 29888089235135369221378319)
          ·
            refine ⟨44832133852703053832067479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29888089235135369221378319 44832133852703053832067479)
            ·
              refine ⟨67248200779054580748101219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44832133852703053832067479 67248200779054580748101219)
              ·
                refine ⟨100872301168581871122151829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67248200779054580748101219 100872301168581871122151829)
                ·
                  refine ⟨4728389117277275208850867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 100872301168581871122151829 4728389117277275208850867)
                  ·
                    refine ⟨7092583675915912813276301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4728389117277275208850867 7092583675915912813276301)
                    ·
                      refine ⟨2659718878468467304978613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7092583675915912813276301 2659718878468467304978613)
                      ·
                        rfl

theorem cell23_5179784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 6, 1, 3].length) (baseStart_5179784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5179784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5179784 prefixEnd_5179784 := by exact prefixLift 5179784
  have htrace : WordTrace (prefixWord ++ tailWord_5179784) baseStart_5179784 baseEnd_5179784 := by
    simpa [prefixWord, tailWord_5179784, baseEnd_5179784] using wordTrace_append hprefix tailTrace_5179784
  have hstable : (prefixWord ++ tailWord_5179784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5179784).length < 2 ^ (prefixWord ++ tailWord_5179784).sum := by decide
  have hdescent : baseEnd_5179784 < baseStart_5179784 := by decide
  rcases family_descends (prefixWord ++ tailWord_5179784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5179785 : List Nat := [1, 2, 1, 1, 6, 3, 1, 3, 1, 2, 2]
def baseStart_5179785 : Nat := 118140960795 + 5179785 * 2 ^ 59
def prefixEnd_5179785 : Nat := 4983230072969 + 3 ^ 40 * 5179785 * 2
def baseEnd_5179785 : Nat := 2659719391949121801066109

theorem tailTrace_5179785 : CollatzResearch.WordTrace tailWord_5179785 prefixEnd_5179785 2659719391949121801066109 := by
  unfold tailWord_5179785
  simp only [CollatzResearch.WordTrace]
  refine ⟨188922279539531056693572809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125948186359687371129048539 188922279539531056693572809)
  ·
    refine ⟨141691709654648292520179607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188922279539531056693572809 141691709654648292520179607)
    ·
      refine ⟨212537564481972438780269411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141691709654648292520179607 212537564481972438780269411)
      ·
        refine ⟨318806346722958658170404117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212537564481972438780269411 318806346722958658170404117)
        ·
          refine ⟨14944047502638687101737693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 318806346722958658170404117 14944047502638687101737693)
          ·
            refine ⟨5604017813489507663151635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14944047502638687101737693 5604017813489507663151635)
            ·
              refine ⟨8406026720234261494727453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5604017813489507663151635 8406026720234261494727453)
              ·
                refine ⟨3152260020087848060522795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8406026720234261494727453 3152260020087848060522795)
                ·
                  refine ⟨4728390030131772090784193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3152260020087848060522795 4728390030131772090784193)
                  ·
                    refine ⟨3546292522598829068088145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4728390030131772090784193 3546292522598829068088145)
                    ·
                      refine ⟨2659719391949121801066109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3546292522598829068088145 2659719391949121801066109)
                      ·
                        rfl

theorem cell23_5179785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 1, 3, 1, 2, 2].length) (baseStart_5179785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5179785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5179785 prefixEnd_5179785 := by exact prefixLift 5179785
  have htrace : WordTrace (prefixWord ++ tailWord_5179785) baseStart_5179785 baseEnd_5179785 := by
    simpa [prefixWord, tailWord_5179785, baseEnd_5179785] using wordTrace_append hprefix tailTrace_5179785
  have hstable : (prefixWord ++ tailWord_5179785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5179785).length < 2 ^ (prefixWord ++ tailWord_5179785).sum := by decide
  have hdescent : baseEnd_5179785 < baseStart_5179785 := by decide
  rcases family_descends (prefixWord ++ tailWord_5179785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5179807 : List Nat := [1, 1, 2, 5, 1, 1, 2, 1, 2, 3, 4]
def baseStart_5179807 : Nat := 118140960795 + 5179807 * 2 ^ 59
def prefixEnd_5179807 : Nat := 4983230072969 + 3 ^ 40 * 5179807 * 2
def baseEnd_5179807 : Nat := 2659730688523520714991007

theorem tailTrace_5179807 : CollatzResearch.WordTrace tailWord_5179807 prefixEnd_5179807 2659730688523520714991007 := by
  unfold tailWord_5179807
  simp only [CollatzResearch.WordTrace]
  refine ⟨188923081945451354450873675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125948721296967569633915783 188923081945451354450873675)
  ·
    refine ⟨283384622918177031676310513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188923081945451354450873675 283384622918177031676310513)
    ·
      refine ⟨212538467188632773757232885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 283384622918177031676310513 212538467188632773757232885)
      ·
        refine ⟨19925481298934322539740583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 212538467188632773757232885 19925481298934322539740583)
        ·
          refine ⟨29888221948401483809610875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19925481298934322539740583 29888221948401483809610875)
          ·
            refine ⟨44832332922602225714416313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29888221948401483809610875 44832332922602225714416313)
            ·
              refine ⟨33624249691951669285812235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44832332922602225714416313 33624249691951669285812235)
              ·
                refine ⟨50436374537927503928718353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33624249691951669285812235 50436374537927503928718353)
                ·
                  refine ⟨37827280903445627946538765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50436374537927503928718353 37827280903445627946538765)
                  ·
                    refine ⟨14185230338792110479952037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37827280903445627946538765 14185230338792110479952037)
                    ·
                      refine ⟨2659730688523520714991007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14185230338792110479952037 2659730688523520714991007)
                      ·
                        rfl

theorem cell23_5179807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_5179807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5179807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5179807 prefixEnd_5179807 := by exact prefixLift 5179807
  have htrace : WordTrace (prefixWord ++ tailWord_5179807) baseStart_5179807 baseEnd_5179807 := by
    simpa [prefixWord, tailWord_5179807, baseEnd_5179807] using wordTrace_append hprefix tailTrace_5179807
  have hstable : (prefixWord ++ tailWord_5179807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5179807).length < 2 ^ (prefixWord ++ tailWord_5179807).sum := by decide
  have hdescent : baseEnd_5179807 < baseStart_5179807 := by decide
  rcases family_descends (prefixWord ++ tailWord_5179807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5179857 : List Nat := [1, 2, 2, 1, 2, 1, 1, 2, 3, 5, 3]
def baseStart_5179857 : Nat := 118140960795 + 5179857 * 2 ^ 59
def prefixEnd_5179857 : Nat := 4983230072969 + 3 ^ 40 * 5179857 * 2
def baseEnd_5179857 : Nat := 2659756362556245519365777

theorem tailTrace_5179857 : CollatzResearch.WordTrace tailWord_5179857 prefixEnd_5179857 2659756362556245519365777 := by
  unfold tailWord_5179857
  simp only [CollatzResearch.WordTrace]
  refine ⟨188924905595270212990193825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125949937063513475326795883 188924905595270212990193825)
  ·
    refine ⟨141693679196452659742645369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188924905595270212990193825 141693679196452659742645369)
    ·
      refine ⟨106270259397339494806984027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141693679196452659742645369 106270259397339494806984027)
      ·
        refine ⟨159405389096009242210476041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106270259397339494806984027 159405389096009242210476041)
        ·
          refine ⟨119554041822006931657857031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 159405389096009242210476041 119554041822006931657857031)
          ·
            refine ⟨179331062733010397486785547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119554041822006931657857031 179331062733010397486785547)
            ·
              refine ⟨268996594099515596230178321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 179331062733010397486785547 268996594099515596230178321)
              ·
                refine ⟨201747445574636697172633741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 268996594099515596230178321 201747445574636697172633741)
                ·
                  refine ⟨75655292090488761439737653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 201747445574636697172633741 75655292090488761439737653)
                  ·
                    refine ⟨7092683633483321384975405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 75655292090488761439737653 7092683633483321384975405)
                    ·
                      refine ⟨2659756362556245519365777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7092683633483321384975405 2659756362556245519365777)
                      ·
                        rfl

theorem cell23_5179857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 5, 3].length) (baseStart_5179857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5179857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5179857 prefixEnd_5179857 := by exact prefixLift 5179857
  have htrace : WordTrace (prefixWord ++ tailWord_5179857) baseStart_5179857 baseEnd_5179857 := by
    simpa [prefixWord, tailWord_5179857, baseEnd_5179857] using wordTrace_append hprefix tailTrace_5179857
  have hstable : (prefixWord ++ tailWord_5179857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5179857).length < 2 ^ (prefixWord ++ tailWord_5179857).sum := by decide
  have hdescent : baseEnd_5179857 < baseStart_5179857 := by decide
  rcases family_descends (prefixWord ++ tailWord_5179857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5179884 : List Nat := [2, 2, 1, 1, 2, 1, 3, 2, 2, 5, 2]
def baseStart_5179884 : Nat := 118140960795 + 5179884 * 2 ^ 59
def prefixEnd_5179884 : Nat := 4983230072969 + 3 ^ 40 * 5179884 * 2
def baseEnd_5179884 : Nat := 2659770226533916913728153

theorem tailTrace_5179884 : CollatzResearch.WordTrace tailWord_5179884 prefixEnd_5179884 2659770226533916913728153 := by
  unfold tailWord_5179884
  simp only [CollatzResearch.WordTrace]
  refine ⟨94462945183086198300713353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125950593577448264400951137 94462945183086198300713353)
  ·
    refine ⟨70847208887314648725535015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94462945183086198300713353 70847208887314648725535015)
    ·
      refine ⟨106270813330971973088302523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70847208887314648725535015 106270813330971973088302523)
      ·
        refine ⟨159406219996457959632453785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106270813330971973088302523 159406219996457959632453785)
        ·
          refine ⟨119554664997343469724340339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 159406219996457959632453785 119554664997343469724340339)
          ·
            refine ⟨179331997496015204586510509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119554664997343469724340339 179331997496015204586510509)
            ·
              refine ⟨67249499061005701719941441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 179331997496015204586510509 67249499061005701719941441)
              ·
                refine ⟨50437124295754276289956081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67249499061005701719941441 50437124295754276289956081)
                ·
                  refine ⟨37827843221815707217467061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50437124295754276289956081 37827843221815707217467061)
                  ·
                    refine ⟨3546360302045222551637537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37827843221815707217467061 3546360302045222551637537)
                    ·
                      refine ⟨2659770226533916913728153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3546360302045222551637537 2659770226533916913728153)
                      ·
                        rfl

theorem cell23_5179884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 5, 2].length) (baseStart_5179884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5179884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5179884 prefixEnd_5179884 := by exact prefixLift 5179884
  have htrace : WordTrace (prefixWord ++ tailWord_5179884) baseStart_5179884 baseEnd_5179884 := by
    simpa [prefixWord, tailWord_5179884, baseEnd_5179884] using wordTrace_append hprefix tailTrace_5179884
  have hstable : (prefixWord ++ tailWord_5179884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5179884).length < 2 ^ (prefixWord ++ tailWord_5179884).sum := by decide
  have hdescent : baseEnd_5179884 < baseStart_5179884 := by decide
  rcases family_descends (prefixWord ++ tailWord_5179884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5179894 : List Nat := [5, 1, 1, 1, 2, 1, 3, 1, 1, 7]
def baseStart_5179894 : Nat := 118140960795 + 5179894 * 2 ^ 59
def prefixEnd_5179894 : Nat := 4983230072969 + 3 ^ 40 * 5179894 * 2
def baseEnd_5179894 : Nat := 886591787113487291534369

theorem tailTrace_5179894 : CollatzResearch.WordTrace tailWord_5179894 prefixEnd_5179894 886591787113487291534369 := by
  unfold tailWord_5179894
  simp only [CollatzResearch.WordTrace]
  refine ⟨11807890943508510519330671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 125950836730757445539527157 11807890943508510519330671)
  ·
    refine ⟨17711836415262765778996007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11807890943508510519330671 17711836415262765778996007)
    ·
      refine ⟨26567754622894148668494011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17711836415262765778996007 26567754622894148668494011)
      ·
        refine ⟨39851631934341223002741017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26567754622894148668494011 39851631934341223002741017)
        ·
          refine ⟨29888723950755917252055763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39851631934341223002741017 29888723950755917252055763)
          ·
            refine ⟨44833085926133875878083645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29888723950755917252055763 44833085926133875878083645)
            ·
              refine ⟨16812407222300203454281367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44833085926133875878083645 16812407222300203454281367)
              ·
                refine ⟨25218610833450305181422051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16812407222300203454281367 25218610833450305181422051)
                ·
                  refine ⟨37827916250175457772133077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25218610833450305181422051 37827916250175457772133077)
                  ·
                    refine ⟨886591787113487291534369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37827916250175457772133077 886591787113487291534369)
                    ·
                      rfl

theorem cell23_5179894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 1, 1, 7].length) (baseStart_5179894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5179894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5179894 prefixEnd_5179894 := by exact prefixLift 5179894
  have htrace : WordTrace (prefixWord ++ tailWord_5179894) baseStart_5179894 baseEnd_5179894 := by
    simpa [prefixWord, tailWord_5179894, baseEnd_5179894] using wordTrace_append hprefix tailTrace_5179894
  have hstable : (prefixWord ++ tailWord_5179894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5179894).length < 2 ^ (prefixWord ++ tailWord_5179894).sum := by decide
  have hdescent : baseEnd_5179894 < baseStart_5179894 := by decide
  rcases family_descends (prefixWord ++ tailWord_5179894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5179914 : List Nat := [3, 1, 2, 2, 2, 1, 2, 1, 4, 1, 4]
def baseStart_5179914 : Nat := 118140960795 + 5179914 * 2 ^ 59
def prefixEnd_5179914 : Nat := 4983230072969 + 3 ^ 40 * 5179914 * 2
def baseEnd_5179914 : Nat := 2659785630953551796353015

theorem tailTrace_5179914 : CollatzResearch.WordTrace tailWord_5179914 prefixEnd_5179914 2659785630953551796353015 := by
  unfold tailWord_5179914
  simp only [CollatzResearch.WordTrace]
  refine ⟨47231746139015927931254699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125951323037375807816679197 47231746139015927931254699)
  ·
    refine ⟨70847619208523891896882049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47231746139015927931254699 70847619208523891896882049)
    ·
      refine ⟨53135714406392918922661537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70847619208523891896882049 53135714406392918922661537)
      ·
        refine ⟨39851785804794689191996153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53135714406392918922661537 39851785804794689191996153)
        ·
          refine ⟨29888839353596016893997115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39851785804794689191996153 29888839353596016893997115)
          ·
            refine ⟨44833259030394025340995673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29888839353596016893997115 44833259030394025340995673)
            ·
              refine ⟨33624944272795519005746755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44833259030394025340995673 33624944272795519005746755)
              ·
                refine ⟨50437416409193278508620133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33624944272795519005746755 50437416409193278508620133)
                ·
                  refine ⟨9457015576723739720366275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50437416409193278508620133 9457015576723739720366275)
                  ·
                    refine ⟨14185523365085609580549413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9457015576723739720366275 14185523365085609580549413)
                    ·
                      refine ⟨2659785630953551796353015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14185523365085609580549413 2659785630953551796353015)
                      ·
                        rfl

theorem cell23_5179914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 1, 4, 1, 4].length) (baseStart_5179914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5179914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5179914 prefixEnd_5179914 := by exact prefixLift 5179914
  have htrace : WordTrace (prefixWord ++ tailWord_5179914) baseStart_5179914 baseEnd_5179914 := by
    simpa [prefixWord, tailWord_5179914, baseEnd_5179914] using wordTrace_append hprefix tailTrace_5179914
  have hstable : (prefixWord ++ tailWord_5179914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5179914).length < 2 ^ (prefixWord ++ tailWord_5179914).sum := by decide
  have hdescent : baseEnd_5179914 < baseStart_5179914 := by decide
  rcases family_descends (prefixWord ++ tailWord_5179914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5179949 : List Nat := [1, 5, 4, 1, 2, 1, 1, 3, 5]
def baseStart_5179949 : Nat := 118140960795 + 5179949 * 2 ^ 59
def prefixEnd_5179949 : Nat := 4983230072969 + 3 ^ 40 * 5179949 * 2
def baseEnd_5179949 : Nat := 295533733641828795490595

theorem tailTrace_5179949 : CollatzResearch.WordTrace tailWord_5179949 prefixEnd_5179949 295533733641828795490595 := by
  unfold tailWord_5179949
  simp only [CollatzResearch.WordTrace]
  refine ⟨188928261110936912702542901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125952174073957941801695267 188928261110936912702542901)
  ·
    refine ⟨17712024479150335565863397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 188928261110936912702542901 17712024479150335565863397)
    ·
      refine ⟨3321004589840687918599387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17712024479150335565863397 3321004589840687918599387)
      ·
        refine ⟨4981506884761031877899081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3321004589840687918599387 4981506884761031877899081)
        ·
          refine ⟨3736130163570773908424311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4981506884761031877899081 3736130163570773908424311)
          ·
            refine ⟨5604195245356160862636467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3736130163570773908424311 5604195245356160862636467)
            ·
              refine ⟨8406292868034241293954701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5604195245356160862636467 8406292868034241293954701)
              ·
                refine ⟨3152359825512840485233013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8406292868034241293954701 3152359825512840485233013)
                ·
                  refine ⟨295533733641828795490595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3152359825512840485233013 295533733641828795490595)
                  ·
                    rfl

theorem cell23_5179949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 1, 3, 5].length) (baseStart_5179949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5179949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5179949 prefixEnd_5179949 := by exact prefixLift 5179949
  have htrace : WordTrace (prefixWord ++ tailWord_5179949) baseStart_5179949 baseEnd_5179949 := by
    simpa [prefixWord, tailWord_5179949, baseEnd_5179949] using wordTrace_append hprefix tailTrace_5179949
  have hstable : (prefixWord ++ tailWord_5179949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5179949).length < 2 ^ (prefixWord ++ tailWord_5179949).sum := by decide
  have hdescent : baseEnd_5179949 < baseStart_5179949 := by decide
  rcases family_descends (prefixWord ++ tailWord_5179949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5179975 : List Nat := [1, 1, 4, 1, 4, 2, 3, 2, 1, 4]
def baseStart_5179975 : Nat := 118140960795 + 5179975 * 2 ^ 59
def prefixEnd_5179975 : Nat := 4983230072969 + 3 ^ 40 * 5179975 * 2
def baseEnd_5179975 : Nat := 886605651091158685896745

theorem tailTrace_5179975 : CollatzResearch.WordTrace tailWord_5179975 prefixEnd_5179975 886605651091158685896745 := by
  unfold tailWord_5179975
  simp only [CollatzResearch.WordTrace]
  refine ⟨188929209408842719142989379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125952806272561812761992919 188929209408842719142989379)
  ·
    refine ⟨283393814113264078714484069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188929209408842719142989379 283393814113264078714484069)
    ·
      refine ⟨53136340146237014758965763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 283393814113264078714484069 53136340146237014758965763)
      ·
        refine ⟨79704510219355522138448645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53136340146237014758965763 79704510219355522138448645)
        ·
          refine ⟨14944595666129160400959121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 79704510219355522138448645 14944595666129160400959121)
          ·
            refine ⟨11208446749596870300719341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14944595666129160400959121 11208446749596870300719341)
            ·
              refine ⟨4203167531098826362769753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11208446749596870300719341 4203167531098826362769753)
              ·
                refine ⟨3152375648324119772077315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4203167531098826362769753 3152375648324119772077315)
                ·
                  refine ⟨4728563472486179658115973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3152375648324119772077315 4728563472486179658115973)
                  ·
                    refine ⟨886605651091158685896745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4728563472486179658115973 886605651091158685896745)
                    ·
                      rfl

theorem cell23_5179975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 3, 2, 1, 4].length) (baseStart_5179975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5179975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5179975 prefixEnd_5179975 := by exact prefixLift 5179975
  have htrace : WordTrace (prefixWord ++ tailWord_5179975) baseStart_5179975 baseEnd_5179975 := by
    simpa [prefixWord, tailWord_5179975, baseEnd_5179975] using wordTrace_append hprefix tailTrace_5179975
  have hstable : (prefixWord ++ tailWord_5179975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5179975).length < 2 ^ (prefixWord ++ tailWord_5179975).sum := by decide
  have hdescent : baseEnd_5179975 < baseStart_5179975 := by decide
  rcases family_descends (prefixWord ++ tailWord_5179975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5179977 : List Nat := [1, 2, 1, 1, 2, 2, 1, 1, 4, 1, 7]
def baseStart_5179977 : Nat := 118140960795 + 5179977 * 2 ^ 59
def prefixEnd_5179977 : Nat := 4983230072969 + 3 ^ 40 * 5179977 * 2
def baseEnd_5179977 : Nat := 2659817980234785049865225

theorem tailTrace_5179977 : CollatzResearch.WordTrace tailWord_5179977 prefixEnd_5179977 2659817980234785049865225 := by
  unfold tailWord_5179977
  simp only [CollatzResearch.WordTrace]
  refine ⟨188929282354835473484562185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125952854903223648989708123 188929282354835473484562185)
  ·
    refine ⟨141696961766126605113421639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188929282354835473484562185 141696961766126605113421639)
    ·
      refine ⟨212545442649189907670132459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141696961766126605113421639 212545442649189907670132459)
      ·
        refine ⟨318818163973784861505198689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212545442649189907670132459 318818163973784861505198689)
        ·
          refine ⟨239113622980338646128899017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 318818163973784861505198689 239113622980338646128899017)
          ·
            refine ⟨179335217235253984596674263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 239113622980338646128899017 179335217235253984596674263)
            ·
              refine ⟨269002825852880976895011395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 179335217235253984596674263 269002825852880976895011395)
              ·
                refine ⟨403504238779321465342517093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 269002825852880976895011395 403504238779321465342517093)
                ·
                  refine ⟨75657044771122774751721955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 403504238779321465342517093 75657044771122774751721955)
                  ·
                    refine ⟨113485567156684162127582933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 75657044771122774751721955 113485567156684162127582933)
                    ·
                      refine ⟨2659817980234785049865225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 113485567156684162127582933 2659817980234785049865225)
                      ·
                        rfl

theorem cell23_5179977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 4, 1, 7].length) (baseStart_5179977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5179977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5179977 prefixEnd_5179977 := by exact prefixLift 5179977
  have htrace : WordTrace (prefixWord ++ tailWord_5179977) baseStart_5179977 baseEnd_5179977 := by
    simpa [prefixWord, tailWord_5179977, baseEnd_5179977] using wordTrace_append hprefix tailTrace_5179977
  have hstable : (prefixWord ++ tailWord_5179977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5179977).length < 2 ^ (prefixWord ++ tailWord_5179977).sum := by decide
  have hdescent : baseEnd_5179977 < baseStart_5179977 := by decide
  rcases family_descends (prefixWord ++ tailWord_5179977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5179988 : List Nat := [2, 4, 1, 1, 1, 5, 2, 1, 6]
def baseStart_5179988 : Nat := 118140960795 + 5179988 * 2 ^ 59
def prefixEnd_5179988 : Nat := 4983230072969 + 3 ^ 40 * 5179988 * 2
def baseEnd_5179988 : Nat := 295535958724664945203075

theorem tailTrace_5179988 : CollatzResearch.WordTrace tailWord_5179988 prefixEnd_5179988 295535958724664945203075 := by
  unfold tailWord_5179988
  simp only [CollatzResearch.WordTrace]
  refine ⟨94464841778897811181606309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125953122371863748242141745 94464841778897811181606309)
  ·
    refine ⟨17712157833543339596551183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94464841778897811181606309 17712157833543339596551183)
    ·
      refine ⟨26568236750315009394826775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17712157833543339596551183 26568236750315009394826775)
      ·
        refine ⟨39852355125472514092240163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26568236750315009394826775 39852355125472514092240163)
        ·
          refine ⟨59778532688208771138360245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39852355125472514092240163 59778532688208771138360245)
          ·
            refine ⟨5604237439519572294221273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 59778532688208771138360245 5604237439519572294221273)
            ·
              refine ⟨4203178079639679220665955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5604237439519572294221273 4203178079639679220665955)
              ·
                refine ⟨6304767119459518830998933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4203178079639679220665955 6304767119459518830998933)
                ·
                  refine ⟨295535958724664945203075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6304767119459518830998933 295535958724664945203075)
                  ·
                    rfl

theorem cell23_5179988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 2, 1, 6].length) (baseStart_5179988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5179988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5179988 prefixEnd_5179988 := by exact prefixLift 5179988
  have htrace : WordTrace (prefixWord ++ tailWord_5179988) baseStart_5179988 baseEnd_5179988 := by
    simpa [prefixWord, tailWord_5179988, baseEnd_5179988] using wordTrace_append hprefix tailTrace_5179988
  have hstable : (prefixWord ++ tailWord_5179988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5179988).length < 2 ^ (prefixWord ++ tailWord_5179988).sum := by decide
  have hdescent : baseEnd_5179988 < baseStart_5179988 := by decide
  rcases family_descends (prefixWord ++ tailWord_5179988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5179991 : List Nat := [1, 1, 3, 2, 2, 2, 1, 2, 4, 3, 2]
def baseStart_5179991 : Nat := 118140960795 + 5179991 * 2 ^ 59
def prefixEnd_5179991 : Nat := 4983230072969 + 3 ^ 40 * 5179991 * 2
def baseEnd_5179991 : Nat := 2659825168963947995090161

theorem tailTrace_5179991 : CollatzResearch.WordTrace tailWord_5179991 prefixEnd_5179991 2659825168963947995090161 := by
  unfold tailWord_5179991
  simp only [CollatzResearch.WordTrace]
  refine ⟨188929792976784753875571827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125953195317856502583714551 188929792976784753875571827)
  ·
    refine ⟨283394689465177130813357741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188929792976784753875571827 283394689465177130813357741)
    ·
      refine ⟨106273008549441424055009153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 283394689465177130813357741 106273008549441424055009153)
      ·
        refine ⟨79704756412081068041256865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106273008549441424055009153 79704756412081068041256865)
        ·
          refine ⟨59778567309060801030942649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79704756412081068041256865 59778567309060801030942649)
          ·
            refine ⟨44833925481795600773206987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59778567309060801030942649 44833925481795600773206987)
            ·
              refine ⟨67250888222693401159810481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44833925481795600773206987 67250888222693401159810481)
              ·
                refine ⟨50438166167020050869857861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67250888222693401159810481 50438166167020050869857861)
                ·
                  refine ⟨9457156156316259538098349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50438166167020050869857861 9457156156316259538098349)
                  ·
                    refine ⟨3546433558618597326786881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9457156156316259538098349 3546433558618597326786881)
                    ·
                      refine ⟨2659825168963947995090161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3546433558618597326786881 2659825168963947995090161)
                      ·
                        rfl

theorem cell23_5179991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 2, 4, 3, 2].length) (baseStart_5179991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5179991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5179991 prefixEnd_5179991 := by exact prefixLift 5179991
  have htrace : WordTrace (prefixWord ++ tailWord_5179991) baseStart_5179991 baseEnd_5179991 := by
    simpa [prefixWord, tailWord_5179991, baseEnd_5179991] using wordTrace_append hprefix tailTrace_5179991
  have hstable : (prefixWord ++ tailWord_5179991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5179991).length < 2 ^ (prefixWord ++ tailWord_5179991).sum := by decide
  have hdescent : baseEnd_5179991 < baseStart_5179991 := by decide
  rcases family_descends (prefixWord ++ tailWord_5179991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5180001 : List Nat := [1, 2, 3, 1, 1, 4, 3, 2, 1, 5]
def baseStart_5180001 : Nat := 118140960795 + 5180001 * 2 ^ 59
def prefixEnd_5180001 : Nat := 4983230072969 + 3 ^ 40 * 5180001 * 2
def baseEnd_5180001 : Nat := 886610101256830985321705

theorem tailTrace_5180001 : CollatzResearch.WordTrace tailWord_5180001 prefixEnd_5180001 886610101256830985321705 := by
  unfold tailWord_5180001
  simp only [CollatzResearch.WordTrace]
  refine ⟨188930157706748525583435857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125953438471165683722290571 188930157706748525583435857)
  ·
    refine ⟨141697618280061394187576893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188930157706748525583435857 141697618280061394187576893)
    ·
      refine ⟨53136606855023022820341335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141697618280061394187576893 53136606855023022820341335)
      ·
        refine ⟨79704910282534534230512003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53136606855023022820341335 79704910282534534230512003)
        ·
          refine ⟨119557365423801801345768005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79704910282534534230512003 119557365423801801345768005)
          ·
            refine ⟨22417006016962837752331501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 119557365423801801345768005 22417006016962837752331501)
            ·
              refine ⟨8406377256361064157124313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22417006016962837752331501 8406377256361064157124313)
              ·
                refine ⟨6304782942270798117843235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8406377256361064157124313 6304782942270798117843235)
                ·
                  refine ⟨9457174413406197176764853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6304782942270798117843235 9457174413406197176764853)
                  ·
                    refine ⟨886610101256830985321705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9457174413406197176764853 886610101256830985321705)
                    ·
                      rfl

theorem cell23_5180001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 3, 2, 1, 5].length) (baseStart_5180001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5180001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5180001 prefixEnd_5180001 := by exact prefixLift 5180001
  have htrace : WordTrace (prefixWord ++ tailWord_5180001) baseStart_5180001 baseEnd_5180001 := by
    simpa [prefixWord, tailWord_5180001, baseEnd_5180001] using wordTrace_append hprefix tailTrace_5180001
  have hstable : (prefixWord ++ tailWord_5180001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5180001).length < 2 ^ (prefixWord ++ tailWord_5180001).sum := by decide
  have hdescent : baseEnd_5180001 < baseStart_5180001 := by decide
  rcases family_descends (prefixWord ++ tailWord_5180001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5180032 : List Nat := [2, 1, 1, 2, 1, 7, 2, 2, 1, 1, 3]
def baseStart_5180032 : Nat := 118140960795 + 5180032 * 2 ^ 59
def prefixEnd_5180032 : Nat := 4983230072969 + 3 ^ 40 * 5180032 * 2
def baseEnd_5180032 : Nat := 2659846221670782334677473

theorem tailTrace_5180032 : CollatzResearch.WordTrace tailWord_5180032 prefixEnd_5180032 2659846221670782334677473 := by
  unfold tailWord_5180032
  simp only [CollatzResearch.WordTrace]
  refine ⟨94465644184818108938907175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125954192246424145251876233 94465644184818108938907175)
  ·
    refine ⟨141698466277227163408360763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94465644184818108938907175 141698466277227163408360763)
    ·
      refine ⟨212547699415840745112541145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141698466277227163408360763 212547699415840745112541145)
      ·
        refine ⟨159410774561880558834405859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 212547699415840745112541145 159410774561880558834405859)
        ·
          refine ⟨239116161842820838251608789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159410774561880558834405859 239116161842820838251608789)
          ·
            refine ⟨5604285043191113396522081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 239116161842820838251608789 5604285043191113396522081)
            ·
              refine ⟨4203213782393335047391561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5604285043191113396522081 4203213782393335047391561)
              ·
                refine ⟨3152410336795001285543671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4203213782393335047391561 3152410336795001285543671)
                ·
                  refine ⟨4728615505192501928315507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3152410336795001285543671 4728615505192501928315507)
                  ·
                    refine ⟨7092923257788752892473261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4728615505192501928315507 7092923257788752892473261)
                    ·
                      refine ⟨2659846221670782334677473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7092923257788752892473261 2659846221670782334677473)
                      ·
                        rfl

theorem cell23_5180032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 2, 2, 1, 1, 3].length) (baseStart_5180032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5180032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5180032 prefixEnd_5180032 := by exact prefixLift 5180032
  have htrace : WordTrace (prefixWord ++ tailWord_5180032) baseStart_5180032 baseEnd_5180032 := by
    simpa [prefixWord, tailWord_5180032, baseEnd_5180032] using wordTrace_append hprefix tailTrace_5180032
  have hstable : (prefixWord ++ tailWord_5180032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5180032).length < 2 ^ (prefixWord ++ tailWord_5180032).sum := by decide
  have hdescent : baseEnd_5180032 < baseStart_5180032 := by decide
  rcases family_descends (prefixWord ++ tailWord_5180032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5180131 : List Nat := [1, 1, 1, 7, 1, 1, 1, 1, 1, 3, 5]
def baseStart_5180131 : Nat := 118140960795 + 5180131 * 2 ^ 59
def prefixEnd_5180131 : Nat := 4983230072969 + 3 ^ 40 * 5180131 * 2
def baseEnd_5180131 : Nat := 2659897056255577447339517

theorem tailTrace_5180131 : CollatzResearch.WordTrace tailWord_5180131 prefixEnd_5180131 2659897056255577447339517 := by
  unfold tailWord_5180131
  simp only [CollatzResearch.WordTrace]
  refine ⟨188934899196277557785668247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125956599464185038523778831 188934899196277557785668247)
  ·
    refine ⟨283402348794416336678502371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188934899196277557785668247 283402348794416336678502371)
    ·
      refine ⟨425103523191624505017753557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 283402348794416336678502371 425103523191624505017753557)
      ·
        refine ⟨9963363824803699336353599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 425103523191624505017753557 9963363824803699336353599)
        ·
          refine ⟨14945045737205549004530399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9963363824803699336353599 14945045737205549004530399)
          ·
            refine ⟨22417568605808323506795599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14945045737205549004530399 22417568605808323506795599)
            ·
              refine ⟨33626352908712485260193399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22417568605808323506795599 33626352908712485260193399)
              ·
                refine ⟨50439529363068727890290099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33626352908712485260193399 50439529363068727890290099)
                ·
                  refine ⟨75659294044603091835435149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50439529363068727890290099 75659294044603091835435149)
                  ·
                    refine ⟨28372235266726159438288181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 75659294044603091835435149 28372235266726159438288181)
                    ·
                      refine ⟨2659897056255577447339517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28372235266726159438288181 2659897056255577447339517)
                      ·
                        rfl

theorem cell23_5180131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_5180131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5180131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5180131 prefixEnd_5180131 := by exact prefixLift 5180131
  have htrace : WordTrace (prefixWord ++ tailWord_5180131) baseStart_5180131 baseEnd_5180131 := by
    simpa [prefixWord, tailWord_5180131, baseEnd_5180131] using wordTrace_append hprefix tailTrace_5180131
  have hstable : (prefixWord ++ tailWord_5180131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5180131).length < 2 ^ (prefixWord ++ tailWord_5180131).sum := by decide
  have hdescent : baseEnd_5180131 < baseStart_5180131 := by decide
  rcases family_descends (prefixWord ++ tailWord_5180131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5180144 : List Nat := [2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 7]
def baseStart_5180144 : Nat := 118140960795 + 5180144 * 2 ^ 59
def prefixEnd_5180144 : Nat := 4983230072969 + 3 ^ 40 * 5180144 * 2
def baseEnd_5180144 : Nat := 2659903731504085896476957

theorem tailTrace_5180144 : CollatzResearch.WordTrace tailWord_5180144 prefixEnd_5180144 2659903731504085896476957 := by
  unfold tailWord_5180144
  simp only [CollatzResearch.WordTrace]
  refine ⟨94467686672615230502945743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125956915563486974003927657 94467686672615230502945743)
  ·
    refine ⟨141701530008922845754418615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94467686672615230502945743 141701530008922845754418615)
    ·
      refine ⟨212552295013384268631627923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141701530008922845754418615 212552295013384268631627923)
      ·
        refine ⟨318828442520076402947441885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212552295013384268631627923 318828442520076402947441885)
        ·
          refine ⟨119560665945028651105290707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 318828442520076402947441885 119560665945028651105290707)
          ·
            refine ⟨179340998917542976657936061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119560665945028651105290707 179340998917542976657936061)
            ·
              refine ⟨67252874594078616246726023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 179340998917542976657936061 67252874594078616246726023)
              ·
                refine ⟨100879311891117924370089035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67252874594078616246726023 100879311891117924370089035)
                ·
                  refine ⟨151318967836676886555133553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 100879311891117924370089035 151318967836676886555133553)
                  ·
                    refine ⟨113489225877507664916350165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 151318967836676886555133553 113489225877507664916350165)
                    ·
                      refine ⟨2659903731504085896476957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 113489225877507664916350165 2659903731504085896476957)
                      ·
                        rfl

theorem cell23_5180144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 7].length) (baseStart_5180144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5180144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5180144 prefixEnd_5180144 := by exact prefixLift 5180144
  have htrace : WordTrace (prefixWord ++ tailWord_5180144) baseStart_5180144 baseEnd_5180144 := by
    simpa [prefixWord, tailWord_5180144, baseEnd_5180144] using wordTrace_append hprefix tailTrace_5180144
  have hstable : (prefixWord ++ tailWord_5180144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5180144).length < 2 ^ (prefixWord ++ tailWord_5180144).sum := by decide
  have hdescent : baseEnd_5180144 < baseStart_5180144 := by decide
  rcases family_descends (prefixWord ++ tailWord_5180144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5180145 : List Nat := [1, 2, 2, 2, 2, 2, 2, 4, 2, 2, 2]
def baseStart_5180145 : Nat := 118140960795 + 5180145 * 2 ^ 59
def prefixEnd_5180145 : Nat := 4983230072969 + 3 ^ 40 * 5180145 * 2
def baseEnd_5180145 : Nat := 2659904244984740392564453

theorem tailTrace_5180145 : CollatzResearch.WordTrace tailWord_5180145 prefixEnd_5180145 2659904244984740392564453 := by
  unfold tailWord_5180145
  simp only [CollatzResearch.WordTrace]
  refine ⟨188935409818226838176677889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125956939878817892117785259 188935409818226838176677889)
  ·
    refine ⟨141701557363670128632508417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188935409818226838176677889 141701557363670128632508417)
    ·
      refine ⟨106276168022752596474381313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141701557363670128632508417 106276168022752596474381313)
      ·
        refine ⟨79707126017064447355785985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106276168022752596474381313 79707126017064447355785985)
        ·
          refine ⟨59780344512798335516839489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79707126017064447355785985 59780344512798335516839489)
          ·
            refine ⟨44835258384598751637629617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59780344512798335516839489 44835258384598751637629617)
            ·
              refine ⟨33626443788449063728222213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44835258384598751637629617 33626443788449063728222213)
              ·
                refine ⟨6304958210334199449041665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33626443788449063728222213 6304958210334199449041665)
                ·
                  refine ⟨4728718657750649586781249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6304958210334199449041665 4728718657750649586781249)
                  ·
                    refine ⟨3546538993312987190085937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4728718657750649586781249 3546538993312987190085937)
                    ·
                      refine ⟨2659904244984740392564453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3546538993312987190085937 2659904244984740392564453)
                      ·
                        rfl

theorem cell23_5180145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 4, 2, 2, 2].length) (baseStart_5180145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5180145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5180145 prefixEnd_5180145 := by exact prefixLift 5180145
  have htrace : WordTrace (prefixWord ++ tailWord_5180145) baseStart_5180145 baseEnd_5180145 := by
    simpa [prefixWord, tailWord_5180145, baseEnd_5180145] using wordTrace_append hprefix tailTrace_5180145
  have hstable : (prefixWord ++ tailWord_5180145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5180145).length < 2 ^ (prefixWord ++ tailWord_5180145).sum := by decide
  have hdescent : baseEnd_5180145 < baseStart_5180145 := by decide
  rcases family_descends (prefixWord ++ tailWord_5180145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5180161 : List Nat := [1, 2, 4, 1, 1, 1, 1, 3, 1, 5, 3]
def baseStart_5180161 : Nat := 118140960795 + 5180161 * 2 ^ 59
def prefixEnd_5180161 : Nat := 4983230072969 + 3 ^ 40 * 5180161 * 2
def baseEnd_5180161 : Nat := 2659912460675212329964379

theorem tailTrace_5180161 : CollatzResearch.WordTrace tailWord_5180161 prefixEnd_5180161 2659912460675212329964379 := by
  unfold tailWord_5180161
  simp only [CollatzResearch.WordTrace]
  refine ⟨188935993386168872909260337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125957328924112581939506891 188935993386168872909260337)
  ·
    refine ⟨141701995039626654681945253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188935993386168872909260337 141701995039626654681945253)
    ·
      refine ⟨26569124069929997752864735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 141701995039626654681945253 26569124069929997752864735)
      ·
        refine ⟨39853686104894996629297103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26569124069929997752864735 39853686104894996629297103)
        ·
          refine ⟨59780529157342494943945655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39853686104894996629297103 59780529157342494943945655)
          ·
            refine ⟨89670793736013742415918483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59780529157342494943945655 89670793736013742415918483)
            ·
              refine ⟨134506190604020613623877725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89670793736013742415918483 134506190604020613623877725)
              ·
                refine ⟨50439821476507730108954147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 134506190604020613623877725 50439821476507730108954147)
                ·
                  refine ⟨75659732214761595163431221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50439821476507730108954147 75659732214761595163431221)
                  ·
                    refine ⟨7093099895133899546571677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 75659732214761595163431221 7093099895133899546571677)
                    ·
                      refine ⟨2659912460675212329964379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7093099895133899546571677 2659912460675212329964379)
                      ·
                        rfl

theorem cell23_5180161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 3, 1, 5, 3].length) (baseStart_5180161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5180161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5180161 prefixEnd_5180161 := by exact prefixLift 5180161
  have htrace : WordTrace (prefixWord ++ tailWord_5180161) baseStart_5180161 baseEnd_5180161 := by
    simpa [prefixWord, tailWord_5180161, baseEnd_5180161] using wordTrace_append hprefix tailTrace_5180161
  have hstable : (prefixWord ++ tailWord_5180161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5180161).length < 2 ^ (prefixWord ++ tailWord_5180161).sum := by decide
  have hdescent : baseEnd_5180161 < baseStart_5180161 := by decide
  rcases family_descends (prefixWord ++ tailWord_5180161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5180191 : List Nat := [1, 1, 2, 4, 2, 2, 1, 2, 1, 2, 5]
def baseStart_5180191 : Nat := 118140960795 + 5180191 * 2 ^ 59
def prefixEnd_5180191 : Nat := 4983230072969 + 3 ^ 40 * 5180191 * 2
def baseEnd_5180191 : Nat := 2659927865094847212589241

theorem tailTrace_5180191 : CollatzResearch.WordTrace tailWord_5180191 prefixEnd_5180191 2659927865094847212589241 := by
  unfold tailWord_5180191
  simp only [CollatzResearch.WordTrace]
  refine ⟨188937087576060188032852427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125958058384040125355234951 188937087576060188032852427)
  ·
    refine ⟨283405631364090282049278641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188937087576060188032852427 283405631364090282049278641)
    ·
      refine ⟨212554223523067711536958981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 283405631364090282049278641 212554223523067711536958981)
      ·
        refine ⟨39853916910575195913179809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 212554223523067711536958981 39853916910575195913179809)
        ·
          refine ⟨29890437682931396934884857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39853916910575195913179809 29890437682931396934884857)
          ·
            refine ⟨22417828262198547701163643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29890437682931396934884857 22417828262198547701163643)
            ·
              refine ⟨33626742393297821551745465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22417828262198547701163643 33626742393297821551745465)
              ·
                refine ⟨25220056794973366163809099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33626742393297821551745465 25220056794973366163809099)
                ·
                  refine ⟨37830085192460049245713649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25220056794973366163809099 37830085192460049245713649)
                  ·
                    refine ⟨28372563894345036934285237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37830085192460049245713649 28372563894345036934285237)
                    ·
                      refine ⟨2659927865094847212589241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28372563894345036934285237 2659927865094847212589241)
                      ·
                        rfl

theorem cell23_5180191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 2, 1, 2, 5].length) (baseStart_5180191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5180191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5180191 prefixEnd_5180191 := by exact prefixLift 5180191
  have htrace : WordTrace (prefixWord ++ tailWord_5180191) baseStart_5180191 baseEnd_5180191 := by
    simpa [prefixWord, tailWord_5180191, baseEnd_5180191] using wordTrace_append hprefix tailTrace_5180191
  have hstable : (prefixWord ++ tailWord_5180191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5180191).length < 2 ^ (prefixWord ++ tailWord_5180191).sum := by decide
  have hdescent : baseEnd_5180191 < baseStart_5180191 := by decide
  rcases family_descends (prefixWord ++ tailWord_5180191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5180202 : List Nat := [3, 1, 4, 3, 1, 1, 1, 4, 5]
def baseStart_5180202 : Nat := 118140960795 + 5180202 * 2 ^ 59
def prefixEnd_5180202 : Nat := 4983230072969 + 3 ^ 40 * 5180202 * 2
def baseEnd_5180202 : Nat := 295548168153560741061299

theorem tailTrace_5180202 : CollatzResearch.WordTrace tailWord_5180202 prefixEnd_5180202 295548168153560741061299 := by
  unfold tailWord_5180202
  simp only [CollatzResearch.WordTrace]
  refine ⟨47234372194755084227875715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125958325852680224607668573 47234372194755084227875715)
  ·
    refine ⟨70851558292132626341813573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47234372194755084227875715 70851558292132626341813573)
    ·
      refine ⟨13284667179774867439090045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70851558292132626341813573 13284667179774867439090045)
      ·
        refine ⟨4981750192415575289658767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13284667179774867439090045 4981750192415575289658767)
        ·
          refine ⟨7472625288623362934488151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4981750192415575289658767 7472625288623362934488151)
          ·
            refine ⟨11208937932935044401732227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7472625288623362934488151 11208937932935044401732227)
            ·
              refine ⟨16813406899402566602598341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11208937932935044401732227 16813406899402566602598341)
              ·
                refine ⟨3152513793637981237987189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16813406899402566602598341 3152513793637981237987189)
                ·
                  refine ⟨295548168153560741061299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3152513793637981237987189 295548168153560741061299)
                  ·
                    rfl

theorem cell23_5180202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 4, 5].length) (baseStart_5180202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5180202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5180202 prefixEnd_5180202 := by exact prefixLift 5180202
  have htrace : WordTrace (prefixWord ++ tailWord_5180202) baseStart_5180202 baseEnd_5180202 := by
    simpa [prefixWord, tailWord_5180202, baseEnd_5180202] using wordTrace_append hprefix tailTrace_5180202
  have hstable : (prefixWord ++ tailWord_5180202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5180202).length < 2 ^ (prefixWord ++ tailWord_5180202).sum := by decide
  have hdescent : baseEnd_5180202 < baseStart_5180202 := by decide
  rcases family_descends (prefixWord ++ tailWord_5180202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5180261 : List Nat := [1, 3, 1, 3, 1, 1, 3, 1, 1, 2, 6]
def baseStart_5180261 : Nat := 118140960795 + 5180261 * 2 ^ 59
def prefixEnd_5180261 : Nat := 4983230072969 + 3 ^ 40 * 5180261 * 2
def baseEnd_5180261 : Nat := 2659963808740661938713919

theorem tailTrace_5180261 : CollatzResearch.WordTrace tailWord_5180261 prefixEnd_5180261 2659963808740661938713919 := by
  unfold tailWord_5180261
  simp only [CollatzResearch.WordTrace]
  refine ⟨188939640685806589987900637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125959760457204393325267091 188939640685806589987900637)
  ·
    refine ⟨70852365257177471245462739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 188939640685806589987900637 70852365257177471245462739)
    ·
      refine ⟨106278547885766206868194109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70852365257177471245462739 106278547885766206868194109)
      ·
        refine ⟨39854455457162327575572791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106278547885766206868194109 39854455457162327575572791)
        ·
          refine ⟨59781683185743491363359187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39854455457162327575572791 59781683185743491363359187)
          ·
            refine ⟨89672524778615237045038781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59781683185743491363359187 89672524778615237045038781)
            ·
              refine ⟨33627196791980713891889543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89672524778615237045038781 33627196791980713891889543)
              ·
                refine ⟨50440795187971070837834315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33627196791980713891889543 50440795187971070837834315)
                ·
                  refine ⟨75661192781956606256751473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50440795187971070837834315 75661192781956606256751473)
                  ·
                    refine ⟨56745894586467454692563605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 75661192781956606256751473 56745894586467454692563605)
                    ·
                      refine ⟨2659963808740661938713919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56745894586467454692563605 2659963808740661938713919)
                      ·
                        rfl

theorem cell23_5180261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 1, 1, 2, 6].length) (baseStart_5180261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5180261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5180261 prefixEnd_5180261 := by exact prefixLift 5180261
  have htrace : WordTrace (prefixWord ++ tailWord_5180261) baseStart_5180261 baseEnd_5180261 := by
    simpa [prefixWord, tailWord_5180261, baseEnd_5180261] using wordTrace_append hprefix tailTrace_5180261
  have hstable : (prefixWord ++ tailWord_5180261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5180261).length < 2 ^ (prefixWord ++ tailWord_5180261).sum := by decide
  have hdescent : baseEnd_5180261 < baseStart_5180261 := by decide
  rcases family_descends (prefixWord ++ tailWord_5180261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5180271 : List Nat := [1, 1, 2, 1, 3, 1, 1, 3, 5, 5]
def baseStart_5180271 : Nat := 118140960795 + 5180271 * 2 ^ 59
def prefixEnd_5180271 : Nat := 4983230072969 + 3 ^ 40 * 5180271 * 2
def baseEnd_5180271 : Nat := 886656314515735633196291

theorem tailTrace_5180271 : CollatzResearch.WordTrace tailWord_5180271 prefixEnd_5180271 886656314515735633196291 := by
  unfold tailWord_5180271
  simp only [CollatzResearch.WordTrace]
  refine ⟨188940005415770361695764667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125960003610513574463843111 188940005415770361695764667)
  ·
    refine ⟨283410008123655542543647001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188940005415770361695764667 283410008123655542543647001)
    ·
      refine ⟨212557506092741656907735251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 283410008123655542543647001 212557506092741656907735251)
      ·
        refine ⟨318836259139112485361602877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212557506092741656907735251 318836259139112485361602877)
        ·
          refine ⟨119563597177167182010601079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 318836259139112485361602877 119563597177167182010601079)
          ·
            refine ⟨179345395765750773015901619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119563597177167182010601079 179345395765750773015901619)
            ·
              refine ⟨269018093648626159523852429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 179345395765750773015901619 269018093648626159523852429)
              ·
                refine ⟨100881785118234809821444661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 269018093648626159523852429 100881785118234809821444661)
                ·
                  refine ⟨9457667354834513420760437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 100881785118234809821444661 9457667354834513420760437)
                  ·
                    refine ⟨886656314515735633196291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9457667354834513420760437 886656314515735633196291)
                    ·
                      rfl

theorem cell23_5180271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 5, 5].length) (baseStart_5180271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5180271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5180271 prefixEnd_5180271 := by exact prefixLift 5180271
  have htrace : WordTrace (prefixWord ++ tailWord_5180271) baseStart_5180271 baseEnd_5180271 := by
    simpa [prefixWord, tailWord_5180271, baseEnd_5180271] using wordTrace_append hprefix tailTrace_5180271
  have hstable : (prefixWord ++ tailWord_5180271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5180271).length < 2 ^ (prefixWord ++ tailWord_5180271).sum := by decide
  have hdescent : baseEnd_5180271 < baseStart_5180271 := by decide
  rcases family_descends (prefixWord ++ tailWord_5180271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5180285 : List Nat := [1, 4, 1, 1, 2, 1, 4, 2, 3, 1, 3]
def baseStart_5180285 : Nat := 118140960795 + 5180285 * 2 ^ 59
def prefixEnd_5180285 : Nat := 4983230072969 + 3 ^ 40 * 5180285 * 2
def baseEnd_5180285 : Nat := 2659976132276369844813809

theorem tailTrace_5180285 : CollatzResearch.WordTrace tailWord_5180285 prefixEnd_5180285 2659976132276369844813809 := by
  unfold tailWord_5180285
  simp only [CollatzResearch.WordTrace]
  refine ⟨188940516037719642086774309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125960344025146428057849539 188940516037719642086774309)
  ·
    refine ⟨35426346757072432891270183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 188940516037719642086774309 35426346757072432891270183)
    ·
      refine ⟨53139520135608649336905275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35426346757072432891270183 53139520135608649336905275)
      ·
        refine ⟨79709280203412974005357913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53139520135608649336905275 79709280203412974005357913)
        ·
          refine ⟨59781960152559730504018435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79709280203412974005357913 59781960152559730504018435)
          ·
            refine ⟨89672940228839595756027653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59781960152559730504018435 89672940228839595756027653)
            ·
              refine ⟨16813676292907424204255185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 89672940228839595756027653 16813676292907424204255185)
              ·
                refine ⟨12610257219680568153191389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16813676292907424204255185 12610257219680568153191389)
                ·
                  refine ⟨4728846457380213057446771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12610257219680568153191389 4728846457380213057446771)
                  ·
                    refine ⟨7093269686070319586170157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4728846457380213057446771 7093269686070319586170157)
                    ·
                      refine ⟨2659976132276369844813809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7093269686070319586170157 2659976132276369844813809)
                      ·
                        rfl

theorem cell23_5180285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 2, 3, 1, 3].length) (baseStart_5180285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5180285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5180285 prefixEnd_5180285 := by exact prefixLift 5180285
  have htrace : WordTrace (prefixWord ++ tailWord_5180285) baseStart_5180285 baseEnd_5180285 := by
    simpa [prefixWord, tailWord_5180285, baseEnd_5180285] using wordTrace_append hprefix tailTrace_5180285
  have hstable : (prefixWord ++ tailWord_5180285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5180285).length < 2 ^ (prefixWord ++ tailWord_5180285).sum := by decide
  have hdescent : baseEnd_5180285 < baseStart_5180285 := by decide
  rcases family_descends (prefixWord ++ tailWord_5180285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5180295 : List Nat := [1, 1, 4, 2, 3, 1, 2, 1, 1, 5, 2]
def baseStart_5180295 : Nat := 118140960795 + 5180295 * 2 ^ 59
def prefixEnd_5180295 : Nat := 4983230072969 + 3 ^ 40 * 5180295 * 2
def baseEnd_5180295 : Nat := 2659981267082914805688763

theorem tailTrace_5180295 : CollatzResearch.WordTrace tailWord_5180295 prefixEnd_5180295 2659981267082914805688763 := by
  unfold tailWord_5180295
  simp only [CollatzResearch.WordTrace]
  refine ⟨188940880767683413794638339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125960587178455609196425559 188940880767683413794638339)
  ·
    refine ⟨283411321151525120691957509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188940880767683413794638339 283411321151525120691957509)
    ·
      refine ⟨53139622715910960129742033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 283411321151525120691957509 53139622715910960129742033)
      ·
        refine ⟨39854717036933220097306525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53139622715910960129742033 39854717036933220097306525)
        ·
          refine ⟨14945518888849957536489947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39854717036933220097306525 14945518888849957536489947)
          ·
            refine ⟨22418278333274936304734921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14945518888849957536489947 22418278333274936304734921)
            ·
              refine ⟨16813708749956202228551191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22418278333274936304734921 16813708749956202228551191)
              ·
                refine ⟨25220563124934303342826787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16813708749956202228551191 25220563124934303342826787)
                ·
                  refine ⟨37830844687401455014240181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25220563124934303342826787 37830844687401455014240181)
                  ·
                    refine ⟨3546641689443886407585017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37830844687401455014240181 3546641689443886407585017)
                    ·
                      refine ⟨2659981267082914805688763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3546641689443886407585017 2659981267082914805688763)
                      ·
                        rfl

theorem cell23_5180295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 1, 1, 5, 2].length) (baseStart_5180295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5180295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5180295 prefixEnd_5180295 := by exact prefixLift 5180295
  have htrace : WordTrace (prefixWord ++ tailWord_5180295) baseStart_5180295 baseEnd_5180295 := by
    simpa [prefixWord, tailWord_5180295, baseEnd_5180295] using wordTrace_append hprefix tailTrace_5180295
  have hstable : (prefixWord ++ tailWord_5180295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5180295).length < 2 ^ (prefixWord ++ tailWord_5180295).sum := by decide
  have hdescent : baseEnd_5180295 < baseStart_5180295 := by decide
  rcases family_descends (prefixWord ++ tailWord_5180295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5180345 : List Nat := [1, 2, 1, 4, 2, 3, 1, 1, 3, 2, 3]
def baseStart_5180345 : Nat := 118140960795 + 5180345 * 2 ^ 59
def prefixEnd_5180345 : Nat := 4983230072969 + 3 ^ 40 * 5180345 * 2
def baseEnd_5180345 : Nat := 2660006941115639610063533

theorem tailTrace_5180345 : CollatzResearch.WordTrace tailWord_5180345 prefixEnd_5180345 2660006941115639610063533 := by
  unfold tailWord_5180345
  simp only [CollatzResearch.WordTrace]
  refine ⟨188942704417502272333958489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125961802945001514889305659 188942704417502272333958489)
  ·
    refine ⟨141707028313126704250468867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188942704417502272333958489 141707028313126704250468867)
    ·
      refine ⟨212560542469690056375703301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141707028313126704250468867 212560542469690056375703301)
      ·
        refine ⟨39855101713066885570444369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 212560542469690056375703301 39855101713066885570444369)
        ·
          refine ⟨29891326284800164177833277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39855101713066885570444369 29891326284800164177833277)
          ·
            refine ⟨11209247356800061566687479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29891326284800164177833277 11209247356800061566687479)
            ·
              refine ⟨16813871035200092350031219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11209247356800061566687479 16813871035200092350031219)
              ·
                refine ⟨25220806552800138525046829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16813871035200092350031219 25220806552800138525046829)
                ·
                  refine ⟨9457802457300051946892561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25220806552800138525046829 9457802457300051946892561)
                  ·
                    refine ⟨7093351842975038960169421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9457802457300051946892561 7093351842975038960169421)
                    ·
                      refine ⟨2660006941115639610063533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7093351842975038960169421 2660006941115639610063533)
                      ·
                        rfl

theorem cell23_5180345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 1, 3, 2, 3].length) (baseStart_5180345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5180345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5180345 prefixEnd_5180345 := by exact prefixLift 5180345
  have htrace : WordTrace (prefixWord ++ tailWord_5180345) baseStart_5180345 baseEnd_5180345 := by
    simpa [prefixWord, tailWord_5180345, baseEnd_5180345] using wordTrace_append hprefix tailTrace_5180345
  have hstable : (prefixWord ++ tailWord_5180345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5180345).length < 2 ^ (prefixWord ++ tailWord_5180345).sum := by decide
  have hdescent : baseEnd_5180345 < baseStart_5180345 := by decide
  rcases family_descends (prefixWord ++ tailWord_5180345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5180361 : List Nat := [1, 2, 1, 1, 2, 1, 2, 1, 3, 9]
def baseStart_5180361 : Nat := 118140960795 + 5180361 * 2 ^ 59
def prefixEnd_5180361 : Nat := 4983230072969 + 3 ^ 40 * 5180361 * 2
def baseEnd_5180361 : Nat := 886671718935370515821153

theorem tailTrace_5180361 : CollatzResearch.WordTrace tailWord_5180361 prefixEnd_5180361 886671718935370515821153 := by
  unfold tailWord_5180361
  simp only [CollatzResearch.WordTrace]
  refine ⟨188943287985444307066540937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125962191990296204711027291 188943287985444307066540937)
  ·
    refine ⟨141707465989083230299905703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188943287985444307066540937 141707465989083230299905703)
    ·
      refine ⟨212561198983624845449858555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141707465989083230299905703 212561198983624845449858555)
      ·
        refine ⟨318841798475437268174787833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212561198983624845449858555 318841798475437268174787833)
        ·
          refine ⟨239131348856577951131090875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 318841798475437268174787833 239131348856577951131090875)
          ·
            refine ⟨358697023284866926696636313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 239131348856577951131090875 358697023284866926696636313)
            ·
              refine ⟨269022767463650195022477235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 358697023284866926696636313 269022767463650195022477235)
              ·
                refine ⟨403534151195475292533715853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 269022767463650195022477235 403534151195475292533715853)
                ·
                  refine ⟨151325306698303234700143445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 403534151195475292533715853 151325306698303234700143445)
                  ·
                    refine ⟨886671718935370515821153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 151325306698303234700143445 886671718935370515821153)
                    ·
                      rfl

theorem cell23_5180361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 9].length) (baseStart_5180361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5180361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5180361 prefixEnd_5180361 := by exact prefixLift 5180361
  have htrace : WordTrace (prefixWord ++ tailWord_5180361) baseStart_5180361 baseEnd_5180361 := by
    simpa [prefixWord, tailWord_5180361, baseEnd_5180361] using wordTrace_append hprefix tailTrace_5180361
  have hstable : (prefixWord ++ tailWord_5180361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5180361).length < 2 ^ (prefixWord ++ tailWord_5180361).sum := by decide
  have hdescent : baseEnd_5180361 < baseStart_5180361 := by decide
  rcases family_descends (prefixWord ++ tailWord_5180361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5180376 : List Nat := [2, 1, 2, 2, 2, 3, 4, 2, 1, 2, 2]
def baseStart_5180376 : Nat := 118140960795 + 5180376 * 2 ^ 59
def prefixEnd_5180376 : Nat := 4983230072969 + 3 ^ 40 * 5180376 * 2
def baseEnd_5180376 : Nat := 2660022859015928988775891

theorem tailTrace_5180376 : CollatzResearch.WordTrace tailWord_5180376 prefixEnd_5180376 2660022859015928988775891 := by
  unfold tailWord_5180376
  simp only [CollatzResearch.WordTrace]
  refine ⟨94471917540194982314168491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125962556720259976418891321 94471917540194982314168491)
  ·
    refine ⟨141707876310292473471252737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94471917540194982314168491 141707876310292473471252737)
    ·
      refine ⟨106280907232719355103439553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141707876310292473471252737 106280907232719355103439553)
      ·
        refine ⟨79710680424539516327579665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106280907232719355103439553 79710680424539516327579665)
        ·
          refine ⟨59783010318404637245684749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79710680424539516327579665 59783010318404637245684749)
          ·
            refine ⟨22418628869401738967131781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59783010318404637245684749 22418628869401738967131781)
            ·
              refine ⟨4203492913012826056337209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22418628869401738967131781 4203492913012826056337209)
              ·
                refine ⟨3152619684759619542252907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4203492913012826056337209 3152619684759619542252907)
                ·
                  refine ⟨4728929527139429313379361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3152619684759619542252907 4728929527139429313379361)
                  ·
                    refine ⟨3546697145354571985034521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4728929527139429313379361 3546697145354571985034521)
                    ·
                      refine ⟨2660022859015928988775891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3546697145354571985034521 2660022859015928988775891)
                      ·
                        rfl

theorem cell23_5180376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 4, 2, 1, 2, 2].length) (baseStart_5180376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5180376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5180376 prefixEnd_5180376 := by exact prefixLift 5180376
  have htrace : WordTrace (prefixWord ++ tailWord_5180376) baseStart_5180376 baseEnd_5180376 := by
    simpa [prefixWord, tailWord_5180376, baseEnd_5180376] using wordTrace_append hprefix tailTrace_5180376
  have hstable : (prefixWord ++ tailWord_5180376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5180376).length < 2 ^ (prefixWord ++ tailWord_5180376).sum := by decide
  have hdescent : baseEnd_5180376 < baseStart_5180376 := by decide
  rcases family_descends (prefixWord ++ tailWord_5180376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5180378 : List Nat := [3, 1, 1, 2, 4, 1, 1, 1, 2, 7]
def baseStart_5180378 : Nat := 118140960795 + 5180378 * 2 ^ 59
def prefixEnd_5180378 : Nat := 4983230072969 + 3 ^ 40 * 5180378 * 2
def baseEnd_5180378 : Nat := 886674628659079326983627

theorem tailTrace_5180378 : CollatzResearch.WordTrace tailWord_5180378 prefixEnd_5180378 886674628659079326983627 := by
  unfold tailWord_5180378
  simp only [CollatzResearch.WordTrace]
  refine ⟨47235977006595679742477447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125962605350921812646606525 47235977006595679742477447)
  ·
    refine ⟨70853965509893519613716171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47235977006595679742477447 70853965509893519613716171)
    ·
      refine ⟨106280948264840279420574257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70853965509893519613716171 106280948264840279420574257)
      ·
        refine ⟨79710711198630209565430693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106280948264840279420574257 79710711198630209565430693)
        ·
          refine ⟨14945758349743164293518255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 79710711198630209565430693 14945758349743164293518255)
          ·
            refine ⟨22418637524614746440277383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14945758349743164293518255 22418637524614746440277383)
            ·
              refine ⟨33627956286922119660416075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22418637524614746440277383 33627956286922119660416075)
              ·
                refine ⟨50441934430383179490624113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33627956286922119660416075 50441934430383179490624113)
                ·
                  refine ⟨37831450822787384617968085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50441934430383179490624113 37831450822787384617968085)
                  ·
                    refine ⟨886674628659079326983627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37831450822787384617968085 886674628659079326983627)
                    ·
                      rfl

theorem cell23_5180378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 1, 2, 7].length) (baseStart_5180378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5180378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5180378 prefixEnd_5180378 := by exact prefixLift 5180378
  have htrace : WordTrace (prefixWord ++ tailWord_5180378) baseStart_5180378 baseEnd_5180378 := by
    simpa [prefixWord, tailWord_5180378, baseEnd_5180378] using wordTrace_append hprefix tailTrace_5180378
  have hstable : (prefixWord ++ tailWord_5180378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5180378).length < 2 ^ (prefixWord ++ tailWord_5180378).sum := by decide
  have hdescent : baseEnd_5180378 < baseStart_5180378 := by decide
  rcases family_descends (prefixWord ++ tailWord_5180378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5180392 : List Nat := [2, 1, 4, 1, 1, 1, 4, 3, 2, 1, 3]
def baseStart_5180392 : Nat := 118140960795 + 5180392 * 2 ^ 59
def prefixEnd_5180392 : Nat := 4983230072969 + 3 ^ 40 * 5180392 * 2
def baseEnd_5180392 : Nat := 2660031074706400926175817

theorem tailTrace_5180392 : CollatzResearch.WordTrace tailWord_5180392 prefixEnd_5180392 2660031074706400926175817 := by
  unfold tailWord_5180392
  simp only [CollatzResearch.WordTrace]
  refine ⟨94472209324165999680459715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125962945765554666240612953 94472209324165999680459715)
  ·
    refine ⟨141708313986248999520689573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94472209324165999680459715 141708313986248999520689573)
    ·
      refine ⟨26570308872421687410129295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 141708313986248999520689573 26570308872421687410129295)
      ·
        refine ⟨39855463308632531115193943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26570308872421687410129295 39855463308632531115193943)
        ·
          refine ⟨59783194962948796672790915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39855463308632531115193943 59783194962948796672790915)
          ·
            refine ⟨89674792444423195009186373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59783194962948796672790915 89674792444423195009186373)
            ·
              refine ⟨16814023583329349064222445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 89674792444423195009186373 16814023583329349064222445)
              ·
                refine ⟨6305258843748505899083417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16814023583329349064222445 6305258843748505899083417)
                ·
                  refine ⟨4728944132811379424312563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6305258843748505899083417 4728944132811379424312563)
                  ·
                    refine ⟨7093416199217069136468845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4728944132811379424312563 7093416199217069136468845)
                    ·
                      refine ⟨2660031074706400926175817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7093416199217069136468845 2660031074706400926175817)
                      ·
                        rfl

theorem cell23_5180392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 3, 2, 1, 3].length) (baseStart_5180392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5180392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5180392 prefixEnd_5180392 := by exact prefixLift 5180392
  have htrace : WordTrace (prefixWord ++ tailWord_5180392) baseStart_5180392 baseEnd_5180392 := by
    simpa [prefixWord, tailWord_5180392, baseEnd_5180392] using wordTrace_append hprefix tailTrace_5180392
  have hstable : (prefixWord ++ tailWord_5180392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5180392).length < 2 ^ (prefixWord ++ tailWord_5180392).sum := by decide
  have hdescent : baseEnd_5180392 < baseStart_5180392 := by decide
  rcases family_descends (prefixWord ++ tailWord_5180392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5180449 : List Nat := [1, 2, 3, 2, 3, 3, 1, 1, 1, 4, 2]
def baseStart_5180449 : Nat := 118140960795 + 5180449 * 2 ^ 59
def prefixEnd_5180449 : Nat := 4983230072969 + 3 ^ 40 * 5180449 * 2
def baseEnd_5180449 : Nat := 2660060343103707203163055

theorem tailTrace_5180449 : CollatzResearch.WordTrace tailWord_5180449 prefixEnd_5180449 2660060343103707203163055 := by
  unfold tailWord_5180449
  simp only [CollatzResearch.WordTrace]
  refine ⟨188946497609125498095744401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125964331739416998730496267 188946497609125498095744401)
  ·
    refine ⟨141709873206844123571808301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188946497609125498095744401 141709873206844123571808301)
    ·
      refine ⟨53141202452566546339428113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141709873206844123571808301 53141202452566546339428113)
      ·
        refine ⟨39855901839424909754571085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53141202452566546339428113 39855901839424909754571085)
        ·
          refine ⟨14945963189784341157964157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39855901839424909754571085 14945963189784341157964157)
          ·
            refine ⟨5604736196169127934236559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14945963189784341157964157 5604736196169127934236559)
            ·
              refine ⟨8407104294253691901354839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5604736196169127934236559 8407104294253691901354839)
              ·
                refine ⟨12610656441380537852032259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8407104294253691901354839 12610656441380537852032259)
                ·
                  refine ⟨18915984662070806778048389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12610656441380537852032259 18915984662070806778048389)
                  ·
                    refine ⟨3546747124138276270884073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18915984662070806778048389 3546747124138276270884073)
                    ·
                      refine ⟨2660060343103707203163055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3546747124138276270884073 2660060343103707203163055)
                      ·
                        rfl

theorem cell23_5180449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 1, 1, 1, 4, 2].length) (baseStart_5180449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5180449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5180449 prefixEnd_5180449 := by exact prefixLift 5180449
  have htrace : WordTrace (prefixWord ++ tailWord_5180449) baseStart_5180449 baseEnd_5180449 := by
    simpa [prefixWord, tailWord_5180449, baseEnd_5180449] using wordTrace_append hprefix tailTrace_5180449
  have hstable : (prefixWord ++ tailWord_5180449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5180449).length < 2 ^ (prefixWord ++ tailWord_5180449).sum := by decide
  have hdescent : baseEnd_5180449 < baseStart_5180449 := by decide
  rcases family_descends (prefixWord ++ tailWord_5180449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5180472 : List Nat := [2, 1, 2, 1, 5, 1, 3, 3, 5]
def baseStart_5180472 : Nat := 118140960795 + 5180472 * 2 ^ 59
def prefixEnd_5180472 : Nat := 4983230072969 + 3 ^ 40 * 5180472 * 2
def baseEnd_5180472 : Nat := 295563572573195623686161

theorem tailTrace_5180472 : CollatzResearch.WordTrace tailWord_5180472 prefixEnd_5180472 295563572573195623686161 := by
  unfold tailWord_5180472
  simp only [CollatzResearch.WordTrace]
  refine ⟨94473668244021086511915835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125964890992028115349221113 94473668244021086511915835)
  ·
    refine ⟨141710502366031629767873753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94473668244021086511915835 141710502366031629767873753)
    ·
      refine ⟨106282876774523722325905315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141710502366031629767873753 106282876774523722325905315)
      ·
        refine ⟨159424315161785583488857973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106282876774523722325905315 159424315161785583488857973)
        ·
          refine ⟨14946029546417398452080435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 159424315161785583488857973 14946029546417398452080435)
          ·
            refine ⟨22419044319626097678120653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14946029546417398452080435 22419044319626097678120653)
            ·
              refine ⟨8407141619859786629295245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22419044319626097678120653 8407141619859786629295245)
              ·
                refine ⟨3152678107447419985985717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8407141619859786629295245 3152678107447419985985717)
                ·
                  refine ⟨295563572573195623686161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3152678107447419985985717 295563572573195623686161)
                  ·
                    rfl

theorem cell23_5180472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 3, 3, 5].length) (baseStart_5180472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5180472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5180472 prefixEnd_5180472 := by exact prefixLift 5180472
  have htrace : WordTrace (prefixWord ++ tailWord_5180472) baseStart_5180472 baseEnd_5180472 := by
    simpa [prefixWord, tailWord_5180472, baseEnd_5180472] using wordTrace_append hprefix tailTrace_5180472
  have hstable : (prefixWord ++ tailWord_5180472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5180472).length < 2 ^ (prefixWord ++ tailWord_5180472).sum := by decide
  have hdescent : baseEnd_5180472 < baseStart_5180472 := by decide
  rcases family_descends (prefixWord ++ tailWord_5180472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5180515 : List Nat := [1, 1, 1, 5, 1, 1, 1, 3, 5, 4]
def baseStart_5180515 : Nat := 118140960795 + 5180515 * 2 ^ 59
def prefixEnd_5180515 : Nat := 4983230072969 + 3 ^ 40 * 5180515 * 2
def baseEnd_5180515 : Nat := 886698077608967981645917

theorem tailTrace_5180515 : CollatzResearch.WordTrace tailWord_5180515 prefixEnd_5180515 886698077608967981645917 := by
  unfold tailWord_5180515
  simp only [CollatzResearch.WordTrace]
  refine ⟨188948904826886391367646999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125965936551257594245097999 188948904826886391367646999)
  ·
    refine ⟨283423357240329587051470499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188948904826886391367646999 283423357240329587051470499)
    ·
      refine ⟨425135035860494380577205749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 283423357240329587051470499 425135035860494380577205749)
      ·
        refine ⟨39856409611921348179113039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 425135035860494380577205749 39856409611921348179113039)
        ·
          refine ⟨59784614417882022268669559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39856409611921348179113039 59784614417882022268669559)
          ·
            refine ⟨89676921626823033403004339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59784614417882022268669559 89676921626823033403004339)
            ·
              refine ⟨134515382440234550104506509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89676921626823033403004339 134515382440234550104506509)
              ·
                refine ⟨50443268415087956289189941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 134515382440234550104506509 50443268415087956289189941)
                ·
                  refine ⟨4729056413914495902111557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 50443268415087956289189941 4729056413914495902111557)
                  ·
                    refine ⟨886698077608967981645917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4729056413914495902111557 886698077608967981645917)
                    ·
                      rfl

theorem cell23_5180515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 3, 5, 4].length) (baseStart_5180515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5180515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5180515 prefixEnd_5180515 := by exact prefixLift 5180515
  have htrace : WordTrace (prefixWord ++ tailWord_5180515) baseStart_5180515 baseEnd_5180515 := by
    simpa [prefixWord, tailWord_5180515, baseEnd_5180515] using wordTrace_append hprefix tailTrace_5180515
  have hstable : (prefixWord ++ tailWord_5180515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5180515).length < 2 ^ (prefixWord ++ tailWord_5180515).sum := by decide
  have hdescent : baseEnd_5180515 < baseStart_5180515 := by decide
  rcases family_descends (prefixWord ++ tailWord_5180515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5180522 : List Nat := [3, 1, 3, 2, 2, 1, 1, 3, 2, 1, 4]
def baseStart_5180522 : Nat := 118140960795 + 5180522 * 2 ^ 59
def prefixEnd_5180522 : Nat := 4983230072969 + 3 ^ 40 * 5180522 * 2
def baseEnd_5180522 : Nat := 2660097827191485417550219

theorem tailTrace_5180522 : CollatzResearch.WordTrace tailWord_5180522 prefixEnd_5180522 2660097827191485417550219 := by
  unfold tailWord_5180522
  simp only [CollatzResearch.WordTrace]
  refine ⟨47237290034465257890787955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125966106758574021042101213 47237290034465257890787955)
  ·
    refine ⟨70855935051697886836181933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47237290034465257890787955 70855935051697886836181933)
    ·
      refine ⟨26570975644386707563568225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70855935051697886836181933 26570975644386707563568225)
      ·
        refine ⟨19928231733290030672676169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26570975644386707563568225 19928231733290030672676169)
        ·
          refine ⟨14946173799967523004507127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19928231733290030672676169 14946173799967523004507127)
          ·
            refine ⟨22419260699951284506760691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14946173799967523004507127 22419260699951284506760691)
            ·
              refine ⟨33628891049926926760141037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22419260699951284506760691 33628891049926926760141037)
              ·
                refine ⟨12610834143722597535052889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33628891049926926760141037 12610834143722597535052889)
                ·
                  refine ⟨9458125607791948151289667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12610834143722597535052889 9458125607791948151289667)
                  ·
                    refine ⟨14187188411687922226934501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9458125607791948151289667 14187188411687922226934501)
                    ·
                      refine ⟨2660097827191485417550219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14187188411687922226934501 2660097827191485417550219)
                      ·
                        rfl

theorem cell23_5180522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_5180522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5180522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5180522 prefixEnd_5180522 := by exact prefixLift 5180522
  have htrace : WordTrace (prefixWord ++ tailWord_5180522) baseStart_5180522 baseEnd_5180522 := by
    simpa [prefixWord, tailWord_5180522, baseEnd_5180522] using wordTrace_append hprefix tailTrace_5180522
  have hstable : (prefixWord ++ tailWord_5180522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5180522).length < 2 ^ (prefixWord ++ tailWord_5180522).sum := by decide
  have hdescent : baseEnd_5180522 < baseStart_5180522 := by decide
  rcases family_descends (prefixWord ++ tailWord_5180522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5180562 : List Nat := [3, 2, 3, 1, 1, 2, 2, 3, 6]
def baseStart_5180562 : Nat := 118140960795 + 5180562 * 2 ^ 59
def prefixEnd_5180562 : Nat := 4983230072969 + 3 ^ 40 * 5180562 * 2
def baseEnd_5180562 : Nat := 295568707379740584561115

theorem tailTrace_5180562 : CollatzResearch.WordTrace tailWord_5180562 prefixEnd_5180562 295568707379740584561115 := by
  unfold tailWord_5180562
  simp only [CollatzResearch.WordTrace]
  refine ⟨47237654764429029598651985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125967079371810745596405293 47237654764429029598651985)
  ·
    refine ⟨35428241073321772198988989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47237654764429029598651985 35428241073321772198988989)
    ·
      refine ⟨13285590402495664574620871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35428241073321772198988989 13285590402495664574620871)
      ·
        refine ⟨19928385603743496861931307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13285590402495664574620871 19928385603743496861931307)
        ·
          refine ⟨29892578405615245292896961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19928385603743496861931307 29892578405615245292896961)
          ·
            refine ⟨22419433804211433969672721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29892578405615245292896961 22419433804211433969672721)
            ·
              refine ⟨16814575353158575477254541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22419433804211433969672721 16814575353158575477254541)
              ·
                refine ⟨6305465757434465803970453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16814575353158575477254541 6305465757434465803970453)
                ·
                  refine ⟨295568707379740584561115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6305465757434465803970453 295568707379740584561115)
                  ·
                    rfl

theorem cell23_5180562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 3, 6].length) (baseStart_5180562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5180562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5180562 prefixEnd_5180562 := by exact prefixLift 5180562
  have htrace : WordTrace (prefixWord ++ tailWord_5180562) baseStart_5180562 baseEnd_5180562 := by
    simpa [prefixWord, tailWord_5180562, baseEnd_5180562] using wordTrace_append hprefix tailTrace_5180562
  have hstable : (prefixWord ++ tailWord_5180562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5180562).length < 2 ^ (prefixWord ++ tailWord_5180562).sum := by decide
  have hdescent : baseEnd_5180562 < baseStart_5180562 := by decide
  rcases family_descends (prefixWord ++ tailWord_5180562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5180605 : List Nat := [1, 4, 1, 2, 1, 1, 2, 2, 3, 6]
def baseStart_5180605 : Nat := 118140960795 + 5180605 * 2 ^ 59
def prefixEnd_5180605 : Nat := 4983230072969 + 3 ^ 40 * 5180605 * 2
def baseEnd_5180605 : Nat := 886713482028602864270779

theorem tailTrace_5180605 : CollatzResearch.WordTrace tailWord_5180605 prefixEnd_5180605 886713482028602864270779 := by
  unfold tailWord_5180605
  simp only [CollatzResearch.WordTrace]
  refine ⟨188952187396560336738423269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125968124931040224492282179 188952187396560336738423269)
  ·
    refine ⟨35428535136855063138454363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 188952187396560336738423269 35428535136855063138454363)
    ·
      refine ⟨53142802705282594707681545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35428535136855063138454363 53142802705282594707681545)
      ·
        refine ⟨39857102028961946030761159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53142802705282594707681545 39857102028961946030761159)
        ·
          refine ⟨59785653043442919046141739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39857102028961946030761159 59785653043442919046141739)
          ·
            refine ⟨89678479565164378569212609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59785653043442919046141739 89678479565164378569212609)
            ·
              refine ⟨67258859673873283926909457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89678479565164378569212609 67258859673873283926909457)
              ·
                refine ⟨50444144755404962945182093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67258859673873283926909457 50444144755404962945182093)
                ·
                  refine ⟨18916554283276861104443285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50444144755404962945182093 18916554283276861104443285)
                  ·
                    refine ⟨886713482028602864270779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18916554283276861104443285 886713482028602864270779)
                    ·
                      rfl

theorem cell23_5180605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 2, 3, 6].length) (baseStart_5180605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5180605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5180605 prefixEnd_5180605 := by exact prefixLift 5180605
  have htrace : WordTrace (prefixWord ++ tailWord_5180605) baseStart_5180605 baseEnd_5180605 := by
    simpa [prefixWord, tailWord_5180605, baseEnd_5180605] using wordTrace_append hprefix tailTrace_5180605
  have hstable : (prefixWord ++ tailWord_5180605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5180605).length < 2 ^ (prefixWord ++ tailWord_5180605).sum := by decide
  have hdescent : baseEnd_5180605 < baseStart_5180605 := by decide
  rcases family_descends (prefixWord ++ tailWord_5180605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5180606 : List Nat := [4, 2, 1, 1, 3, 2, 2, 1, 3, 1, 3]
def baseStart_5180606 : Nat := 118140960795 + 5180606 * 2 ^ 59
def prefixEnd_5180606 : Nat := 4983230072969 + 3 ^ 40 * 5180606 * 2
def baseEnd_5180606 : Nat := 2660140959566463088899833

theorem tailTrace_5180606 : CollatzResearch.WordTrace tailWord_5180606 prefixEnd_5180606 2660140959566463088899833 := by
  unfold tailWord_5180606
  simp only [CollatzResearch.WordTrace]
  refine ⟨23619027983694589238651209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125968149246371142606139781 23619027983694589238651209)
  ·
    refine ⟨17714270987770941928988407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23619027983694589238651209 17714270987770941928988407)
    ·
      refine ⟨26571406481656412893482611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17714270987770941928988407 26571406481656412893482611)
      ·
        refine ⟨39857109722484619340223917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26571406481656412893482611 39857109722484619340223917)
        ·
          refine ⟨14946416145931732252583969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39857109722484619340223917 14946416145931732252583969)
          ·
            refine ⟨11209812109448799189437977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14946416145931732252583969 11209812109448799189437977)
            ·
              refine ⟨8407359082086599392078483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11209812109448799189437977 8407359082086599392078483)
              ·
                refine ⟨12611038623129899088117725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8407359082086599392078483 12611038623129899088117725)
                ·
                  refine ⟨4729139483673712158044147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12611038623129899088117725 4729139483673712158044147)
                  ·
                    refine ⟨7093709225510568237066221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4729139483673712158044147 7093709225510568237066221)
                    ·
                      refine ⟨2660140959566463088899833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7093709225510568237066221 2660140959566463088899833)
                      ·
                        rfl

theorem cell23_5180606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 2, 1, 3, 1, 3].length) (baseStart_5180606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5180606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5180606 prefixEnd_5180606 := by exact prefixLift 5180606
  have htrace : WordTrace (prefixWord ++ tailWord_5180606) baseStart_5180606 baseEnd_5180606 := by
    simpa [prefixWord, tailWord_5180606, baseEnd_5180606] using wordTrace_append hprefix tailTrace_5180606
  have hstable : (prefixWord ++ tailWord_5180606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5180606).length < 2 ^ (prefixWord ++ tailWord_5180606).sum := by decide
  have hdescent : baseEnd_5180606 < baseStart_5180606 := by decide
  rcases family_descends (prefixWord ++ tailWord_5180606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5180629 : List Nat := [1, 3, 2, 4, 1, 1, 1, 4, 1, 1, 4]
def baseStart_5180629 : Nat := 118140960795 + 5180629 * 2 ^ 59
def prefixEnd_5180629 : Nat := 4983230072969 + 3 ^ 40 * 5180629 * 2
def baseEnd_5180629 : Nat := 2660152769621516498912227

theorem tailTrace_5180629 : CollatzResearch.WordTrace tailWord_5180629 prefixEnd_5180629 2660152769621516498912227 := by
  unfold tailWord_5180629
  simp only [CollatzResearch.WordTrace]
  refine ⟨188953062748473388837296941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125968708498982259224864627 188953062748473388837296941)
  ·
    refine ⟨70857398530677520813986353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 188953062748473388837296941 70857398530677520813986353)
    ·
      refine ⟨53143048898008140610489765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70857398530677520813986353 53143048898008140610489765)
      ·
        refine ⟨9964321668376526364466831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53143048898008140610489765 9964321668376526364466831)
        ·
          refine ⟨14946482502564789546700247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9964321668376526364466831 14946482502564789546700247)
          ·
            refine ⟨22419723753847184320050371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14946482502564789546700247 22419723753847184320050371)
            ·
              refine ⟨33629585630770776480075557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22419723753847184320050371 33629585630770776480075557)
              ·
                refine ⟨6305547305769520590014167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33629585630770776480075557 6305547305769520590014167)
                ·
                  refine ⟨9458320958654280885021251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6305547305769520590014167 9458320958654280885021251)
                  ·
                    refine ⟨14187481437981421327531877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9458320958654280885021251 14187481437981421327531877)
                    ·
                      refine ⟨2660152769621516498912227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14187481437981421327531877 2660152769621516498912227)
                      ·
                        rfl

theorem cell23_5180629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_5180629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5180629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5180629 prefixEnd_5180629 := by exact prefixLift 5180629
  have htrace : WordTrace (prefixWord ++ tailWord_5180629) baseStart_5180629 baseEnd_5180629 := by
    simpa [prefixWord, tailWord_5180629, baseEnd_5180629] using wordTrace_append hprefix tailTrace_5180629
  have hstable : (prefixWord ++ tailWord_5180629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5180629).length < 2 ^ (prefixWord ++ tailWord_5180629).sum := by decide
  have hdescent : baseEnd_5180629 < baseStart_5180629 := by decide
  rcases family_descends (prefixWord ++ tailWord_5180629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5180665 : List Nat := [1, 2, 1, 3, 1, 1, 4, 1, 2, 7]
def baseStart_5180665 : Nat := 118140960795 + 5180665 * 2 ^ 59
def prefixEnd_5180665 : Nat := 4983230072969 + 3 ^ 40 * 5180665 * 2
def baseEnd_5180665 : Nat := 886723751641692786020687

theorem tailTrace_5180665 : CollatzResearch.WordTrace tailWord_5180665 prefixEnd_5180665 886723751641692786020687 := by
  unfold tailWord_5180665
  simp only [CollatzResearch.WordTrace]
  refine ⟨188954375776342966985607449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125969583850895311323738299 188954375776342966985607449)
  ·
    refine ⟨141715781832257225239205587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188954375776342966985607449 141715781832257225239205587)
    ·
      refine ⟨212573672748385837858808381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141715781832257225239205587 212573672748385837858808381)
      ·
        refine ⟨79715127280644689197053143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 212573672748385837858808381 79715127280644689197053143)
        ·
          refine ⟨119572690920967033795579715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79715127280644689197053143 119572690920967033795579715)
          ·
            refine ⟨179359036381450550693369573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119572690920967033795579715 179359036381450550693369573)
            ·
              refine ⟨33629819321521978255006795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 179359036381450550693369573 33629819321521978255006795)
              ·
                refine ⟨50444728982282967382510193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33629819321521978255006795 50444728982282967382510193)
                ·
                  refine ⟨37833546736712225536882645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50444728982282967382510193 37833546736712225536882645)
                  ·
                    refine ⟨886723751641692786020687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37833546736712225536882645 886723751641692786020687)
                    ·
                      rfl

theorem cell23_5180665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 1, 2, 7].length) (baseStart_5180665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5180665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5180665 prefixEnd_5180665 := by exact prefixLift 5180665
  have htrace : WordTrace (prefixWord ++ tailWord_5180665) baseStart_5180665 baseEnd_5180665 := by
    simpa [prefixWord, tailWord_5180665, baseEnd_5180665] using wordTrace_append hprefix tailTrace_5180665
  have hstable : (prefixWord ++ tailWord_5180665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5180665).length < 2 ^ (prefixWord ++ tailWord_5180665).sum := by decide
  have hdescent : baseEnd_5180665 < baseStart_5180665 := by decide
  rcases family_descends (prefixWord ++ tailWord_5180665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5180672 : List Nat := [2, 1, 1, 2, 1, 1, 3, 1, 2, 7, 2]
def baseStart_5180672 : Nat := 118140960795 + 5180672 * 2 ^ 59
def prefixEnd_5180672 : Nat := 4983230072969 + 3 ^ 40 * 5180672 * 2
def baseEnd_5180672 : Nat := 2660174849289659830674529

theorem tailTrace_5180672 : CollatzResearch.WordTrace tailWord_5180672 prefixEnd_5180672 2660174849289659830674529 := by
  unfold tailWord_5180672
  simp only [CollatzResearch.WordTrace]
  refine ⟨94477315543658803590556135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125969754058211738120741513 94477315543658803590556135)
  ·
    refine ⟨141715973315488205385834203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94477315543658803590556135 141715973315488205385834203)
    ·
      refine ⟨212573959973232308078751305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141715973315488205385834203 212573959973232308078751305)
      ·
        refine ⟨159430469979924231059063479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 212573959973232308078751305 159430469979924231059063479)
        ·
          refine ⟨239145704969886346588595219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159430469979924231059063479 239145704969886346588595219)
          ·
            refine ⟨358718557454829519882892829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 239145704969886346588595219 358718557454829519882892829)
            ·
              refine ⟨134519459045561069956084811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 358718557454829519882892829 134519459045561069956084811)
              ·
                refine ⟨201779188568341604934127217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 134519459045561069956084811 201779188568341604934127217)
                ·
                  refine ⟨151334391426256203700595413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 201779188568341604934127217 151334391426256203700595413)
                  ·
                    refine ⟨3546899799052879774232705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 151334391426256203700595413 3546899799052879774232705)
                    ·
                      refine ⟨2660174849289659830674529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3546899799052879774232705 2660174849289659830674529)
                      ·
                        rfl

theorem cell23_5180672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 2, 7, 2].length) (baseStart_5180672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5180672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5180672 prefixEnd_5180672 := by exact prefixLift 5180672
  have htrace : WordTrace (prefixWord ++ tailWord_5180672) baseStart_5180672 baseEnd_5180672 := by
    simpa [prefixWord, tailWord_5180672, baseEnd_5180672] using wordTrace_append hprefix tailTrace_5180672
  have hstable : (prefixWord ++ tailWord_5180672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5180672).length < 2 ^ (prefixWord ++ tailWord_5180672).sum := by decide
  have hdescent : baseEnd_5180672 < baseStart_5180672 := by decide
  rcases family_descends (prefixWord ++ tailWord_5180672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5180689 : List Nat := [1, 2, 2, 1, 1, 4, 3, 1, 3, 3, 2]
def baseStart_5180689 : Nat := 118140960795 + 5180689 * 2 ^ 59
def prefixEnd_5180689 : Nat := 4983230072969 + 3 ^ 40 * 5180689 * 2
def baseEnd_5180689 : Nat := 2660183578460786264161951

theorem tailTrace_5180689 : CollatzResearch.WordTrace tailWord_5180689 prefixEnd_5180689 2660183578460786264161951 := by
  unfold tailWord_5180689
  simp only [CollatzResearch.WordTrace]
  refine ⟨188955251128256019084481121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125970167418837346056320747 188955251128256019084481121)
  ·
    refine ⟨141716438346192014313360841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188955251128256019084481121 141716438346192014313360841)
    ·
      refine ⟨106287328759644010735020631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141716438346192014313360841 106287328759644010735020631)
      ·
        refine ⟨159430993139466016102530947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106287328759644010735020631 159430993139466016102530947)
        ·
          refine ⟨239146489709199024153796421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159430993139466016102530947 239146489709199024153796421)
          ·
            refine ⟨44839966820474817028836829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 239146489709199024153796421 44839966820474817028836829)
            ·
              refine ⟨16814987557678056385813811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44839966820474817028836829 16814987557678056385813811)
              ·
                refine ⟨25222481336517084578720717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16814987557678056385813811 25222481336517084578720717)
                ·
                  refine ⟨9458430501193906717020269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25222481336517084578720717 9458430501193906717020269)
                  ·
                    refine ⟨3546911437947715018882601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9458430501193906717020269 3546911437947715018882601)
                    ·
                      refine ⟨2660183578460786264161951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3546911437947715018882601 2660183578460786264161951)
                      ·
                        rfl

theorem cell23_5180689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 3, 2].length) (baseStart_5180689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5180689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5180689 prefixEnd_5180689 := by exact prefixLift 5180689
  have htrace : WordTrace (prefixWord ++ tailWord_5180689) baseStart_5180689 baseEnd_5180689 := by
    simpa [prefixWord, tailWord_5180689, baseEnd_5180689] using wordTrace_append hprefix tailTrace_5180689
  have hstable : (prefixWord ++ tailWord_5180689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5180689).length < 2 ^ (prefixWord ++ tailWord_5180689).sum := by decide
  have hdescent : baseEnd_5180689 < baseStart_5180689 := by decide
  rcases family_descends (prefixWord ++ tailWord_5180689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5180729 : List Nat := [1, 2, 1, 6, 2, 1, 1, 1, 2, 6]
def baseStart_5180729 : Nat := 118140960795 + 5180729 * 2 ^ 59
def prefixEnd_5180729 : Nat := 4983230072969 + 3 ^ 40 * 5180729 * 2
def baseEnd_5180729 : Nat := 886734705895655369220589

theorem tailTrace_5180729 : CollatzResearch.WordTrace tailWord_5180729 prefixEnd_5180729 886734705895655369220589 := by
  unfold tailWord_5180729
  simp only [CollatzResearch.WordTrace]
  refine ⟨188956710048111105915937241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125971140032074070610624827 188956710048111105915937241)
  ·
    refine ⟨141717532536083329436952931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188956710048111105915937241 141717532536083329436952931)
    ·
      refine ⟨212576298804124994155429397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141717532536083329436952931 212576298804124994155429397)
      ·
        refine ⟨9964514006443359101035753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 212576298804124994155429397 9964514006443359101035753)
        ·
          refine ⟨7473385504832519325776815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9964514006443359101035753 7473385504832519325776815)
          ·
            refine ⟨11210078257248778988665223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7473385504832519325776815 11210078257248778988665223)
            ·
              refine ⟨16815117385873168482997835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11210078257248778988665223 16815117385873168482997835)
              ·
                refine ⟨25222676078809752724496753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16815117385873168482997835 25222676078809752724496753)
                ·
                  refine ⟨18917007059107314543372565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25222676078809752724496753 18917007059107314543372565)
                  ·
                    refine ⟨886734705895655369220589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18917007059107314543372565 886734705895655369220589)
                    ·
                      rfl

theorem cell23_5180729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 1, 2, 6].length) (baseStart_5180729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5180729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5180729 prefixEnd_5180729 := by exact prefixLift 5180729
  have htrace : WordTrace (prefixWord ++ tailWord_5180729) baseStart_5180729 baseEnd_5180729 := by
    simpa [prefixWord, tailWord_5180729, baseEnd_5180729] using wordTrace_append hprefix tailTrace_5180729
  have hstable : (prefixWord ++ tailWord_5180729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5180729).length < 2 ^ (prefixWord ++ tailWord_5180729).sum := by decide
  have hdescent : baseEnd_5180729 < baseStart_5180729 := by decide
  rcases family_descends (prefixWord ++ tailWord_5180729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5180732 : List Nat := [2, 2, 2, 2, 1, 3, 1, 1, 1, 4, 4]
def baseStart_5180732 : Nat := 118140960795 + 5180732 * 2 ^ 59
def prefixEnd_5180732 : Nat := 4983230072969 + 3 ^ 40 * 5180732 * 2
def baseEnd_5180732 : Nat := 2660205658128929595924253

theorem tailTrace_5180732 : CollatzResearch.WordTrace tailWord_5180732 prefixEnd_5180732 2660205658128929595924253 := by
  unfold tailWord_5180732
  simp only [CollatzResearch.WordTrace]
  refine ⟨94478409733550118714148225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125971212978066824952197633 94478409733550118714148225)
  ·
    refine ⟨70858807300162589035611169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94478409733550118714148225 70858807300162589035611169)
    ·
      refine ⟨53144105475121941776708377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70858807300162589035611169 53144105475121941776708377)
      ·
        refine ⟨39858079106341456332531283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53144105475121941776708377 39858079106341456332531283)
        ·
          refine ⟨59787118659512184498796925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39858079106341456332531283 59787118659512184498796925)
          ·
            refine ⟨22420169497317069187048847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59787118659512184498796925 22420169497317069187048847)
            ·
              refine ⟨33630254245975603780573271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22420169497317069187048847 33630254245975603780573271)
              ·
                refine ⟨50445381368963405670859907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33630254245975603780573271 50445381368963405670859907)
                ·
                  refine ⟨75668072053445108506289861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50445381368963405670859907 75668072053445108506289861)
                  ·
                    refine ⟨14187763510020957844929349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 75668072053445108506289861 14187763510020957844929349)
                    ·
                      refine ⟨2660205658128929595924253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14187763510020957844929349 2660205658128929595924253)
                      ·
                        rfl

theorem cell23_5180732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 1, 1, 4, 4].length) (baseStart_5180732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5180732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5180732 prefixEnd_5180732 := by exact prefixLift 5180732
  have htrace : WordTrace (prefixWord ++ tailWord_5180732) baseStart_5180732 baseEnd_5180732 := by
    simpa [prefixWord, tailWord_5180732, baseEnd_5180732] using wordTrace_append hprefix tailTrace_5180732
  have hstable : (prefixWord ++ tailWord_5180732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5180732).length < 2 ^ (prefixWord ++ tailWord_5180732).sum := by decide
  have hdescent : baseEnd_5180732 < baseStart_5180732 := by decide
  rcases family_descends (prefixWord ++ tailWord_5180732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5180736 : List Nat := [2, 1, 1, 2, 2, 1, 3, 5, 2, 2, 2]
def baseStart_5180736 : Nat := 118140960795 + 5180736 * 2 ^ 59
def prefixEnd_5180736 : Nat := 4983230072969 + 3 ^ 40 * 5180736 * 2
def baseEnd_5180736 : Nat := 2660207712051547580274235

theorem tailTrace_5180736 : CollatzResearch.WordTrace tailWord_5180736 prefixEnd_5180736 2660207712051547580274235 := by
  unfold tailWord_5180736
  simp only [CollatzResearch.WordTrace]
  refine ⟨94478482679542873055721031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125971310239390497407628041 94478482679542873055721031)
  ·
    refine ⟨141717724019314309583581547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94478482679542873055721031 141717724019314309583581547)
    ·
      refine ⟨212576586028971464375372321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141717724019314309583581547 212576586028971464375372321)
      ·
        refine ⟨159432439521728598281529241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 212576586028971464375372321 159432439521728598281529241)
        ·
          refine ⟨119574329641296448711146931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 159432439521728598281529241 119574329641296448711146931)
          ·
            refine ⟨179361494461944673066720397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119574329641296448711146931 179361494461944673066720397)
            ·
              refine ⟨67260560423229252400020149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 179361494461944673066720397 67260560423229252400020149)
              ·
                refine ⟨6305677539677742412501889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 67260560423229252400020149 6305677539677742412501889)
                ·
                  refine ⟨4729258154758306809376417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6305677539677742412501889 4729258154758306809376417)
                  ·
                    refine ⟨3546943616068730107032313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4729258154758306809376417 3546943616068730107032313)
                    ·
                      refine ⟨2660207712051547580274235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3546943616068730107032313 2660207712051547580274235)
                      ·
                        rfl

theorem cell23_5180736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 5, 2, 2, 2].length) (baseStart_5180736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5180736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5180736 prefixEnd_5180736 := by exact prefixLift 5180736
  have htrace : WordTrace (prefixWord ++ tailWord_5180736) baseStart_5180736 baseEnd_5180736 := by
    simpa [prefixWord, tailWord_5180736, baseEnd_5180736] using wordTrace_append hprefix tailTrace_5180736
  have hstable : (prefixWord ++ tailWord_5180736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5180736).length < 2 ^ (prefixWord ++ tailWord_5180736).sum := by decide
  have hdescent : baseEnd_5180736 < baseStart_5180736 := by decide
  rcases family_descends (prefixWord ++ tailWord_5180736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5180752 : List Nat := [2, 1, 1, 1, 1, 5, 1, 2, 1, 5, 3]
def baseStart_5180752 : Nat := 118140960795 + 5180752 * 2 ^ 59
def prefixEnd_5180752 : Nat := 4983230072969 + 3 ^ 40 * 5180752 * 2
def baseEnd_5180752 : Nat := 2660215927742019517674161

theorem tailTrace_5180752 : CollatzResearch.WordTrace tailWord_5180752 prefixEnd_5180752 2660215927742019517674161 := by
  unfold tailWord_5180752
  simp only [CollatzResearch.WordTrace]
  refine ⟨94478774463513890422012255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125971699284685187229349673 94478774463513890422012255)
  ·
    refine ⟨141718161695270835633018383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94478774463513890422012255 141718161695270835633018383)
    ·
      refine ⟨212577242542906253449527575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141718161695270835633018383 212577242542906253449527575)
      ·
        refine ⟨318865863814359380174291363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212577242542906253449527575 318865863814359380174291363)
        ·
          refine ⟨478298795721539070261437045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 318865863814359380174291363 478298795721539070261437045)
          ·
            refine ⟨44840512098894287837009723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 478298795721539070261437045 44840512098894287837009723)
            ·
              refine ⟨67260768148341431755514585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44840512098894287837009723 67260768148341431755514585)
              ·
                refine ⟨50445576111256073816635939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67260768148341431755514585 50445576111256073816635939)
                ·
                  refine ⟨75668364166884110724953909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50445576111256073816635939 75668364166884110724953909)
                  ·
                    refine ⟨7093909140645385380464429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 75668364166884110724953909 7093909140645385380464429)
                    ·
                      refine ⟨2660215927742019517674161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7093909140645385380464429 2660215927742019517674161)
                      ·
                        rfl

theorem cell23_5180752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 2, 1, 5, 3].length) (baseStart_5180752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5180752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5180752 prefixEnd_5180752 := by exact prefixLift 5180752
  have htrace : WordTrace (prefixWord ++ tailWord_5180752) baseStart_5180752 baseEnd_5180752 := by
    simpa [prefixWord, tailWord_5180752, baseEnd_5180752] using wordTrace_append hprefix tailTrace_5180752
  have hstable : (prefixWord ++ tailWord_5180752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5180752).length < 2 ^ (prefixWord ++ tailWord_5180752).sum := by decide
  have hdescent : baseEnd_5180752 < baseStart_5180752 := by decide
  rcases family_descends (prefixWord ++ tailWord_5180752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5180759 : List Nat := [1, 1, 3, 2, 3, 2, 1, 5, 5]
def baseStart_5180759 : Nat := 118140960795 + 5180759 * 2 ^ 59
def prefixEnd_5180759 : Nat := 4983230072969 + 3 ^ 40 * 5180759 * 2
def baseEnd_5180759 : Nat := 295579946900733443365181

theorem tailTrace_5180759 : CollatzResearch.WordTrace tailWord_5180759 prefixEnd_5180759 295579946900733443365181 := by
  unfold tailWord_5180759
  simp only [CollatzResearch.WordTrace]
  refine ⟨188957804238002421039529331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125971869492001614026352887 188957804238002421039529331)
  ·
    refine ⟨283436706357003631559293997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188957804238002421039529331 283436706357003631559293997)
    ·
      refine ⟨106288764883876361834735249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 283436706357003631559293997 106288764883876361834735249)
      ·
        refine ⟨79716573662907271376051437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106288764883876361834735249 79716573662907271376051437)
        ·
          refine ⟨29893715123590226766019289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79716573662907271376051437 29893715123590226766019289)
          ·
            refine ⟨22420286342692670074514467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29893715123590226766019289 22420286342692670074514467)
            ·
              refine ⟨33630429514039005111771701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22420286342692670074514467 33630429514039005111771701)
              ·
                refine ⟨3152852766941156729228597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33630429514039005111771701 3152852766941156729228597)
                ·
                  refine ⟨295579946900733443365181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3152852766941156729228597 295579946900733443365181)
                  ·
                    rfl

theorem cell23_5180759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 5, 5].length) (baseStart_5180759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5180759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5180759 prefixEnd_5180759 := by exact prefixLift 5180759
  have htrace : WordTrace (prefixWord ++ tailWord_5180759) baseStart_5180759 baseEnd_5180759 := by
    simpa [prefixWord, tailWord_5180759, baseEnd_5180759] using wordTrace_append hprefix tailTrace_5180759
  have hstable : (prefixWord ++ tailWord_5180759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5180759).length < 2 ^ (prefixWord ++ tailWord_5180759).sum := by decide
  have hdescent : baseEnd_5180759 < baseStart_5180759 := by decide
  rcases family_descends (prefixWord ++ tailWord_5180759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5180832 : List Nat := [2, 1, 1, 4, 1, 2, 1, 3, 8]
def baseStart_5180832 : Nat := 118140960795 + 5180832 * 2 ^ 59
def prefixEnd_5180832 : Nat := 4983230072969 + 3 ^ 40 * 5180832 * 2
def baseEnd_5180832 : Nat := 295584111799375467185977

theorem tailTrace_5180832 : CollatzResearch.WordTrace tailWord_5180832 prefixEnd_5180832 295584111799375467185977 := by
  unfold tailWord_5180832
  simp only [CollatzResearch.WordTrace]
  refine ⟨94480233383368977253468375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125973644511158636337957833 94480233383368977253468375)
  ·
    refine ⟨141720350075053465880202563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94480233383368977253468375 141720350075053465880202563)
    ·
      refine ⟨212580525112580198820303845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141720350075053465880202563 212580525112580198820303845)
      ·
        refine ⟨39858848458608787278806971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 212580525112580198820303845 39858848458608787278806971)
        ·
          refine ⟨59788272687913180918210457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39858848458608787278806971 59788272687913180918210457)
          ·
            refine ⟨44841204515934885688657843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59788272687913180918210457 44841204515934885688657843)
            ·
              refine ⟨67261806773902328532986765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44841204515934885688657843 67261806773902328532986765)
              ·
                refine ⟨25223177540213373199870037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67261806773902328532986765 25223177540213373199870037)
                ·
                  refine ⟨295584111799375467185977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25223177540213373199870037 295584111799375467185977)
                  ·
                    rfl

theorem cell23_5180832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 3, 8].length) (baseStart_5180832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5180832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5180832 prefixEnd_5180832 := by exact prefixLift 5180832
  have htrace : WordTrace (prefixWord ++ tailWord_5180832) baseStart_5180832 baseEnd_5180832 := by
    simpa [prefixWord, tailWord_5180832, baseEnd_5180832] using wordTrace_append hprefix tailTrace_5180832
  have hstable : (prefixWord ++ tailWord_5180832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5180832).length < 2 ^ (prefixWord ++ tailWord_5180832).sum := by decide
  have hdescent : baseEnd_5180832 < baseStart_5180832 := by decide
  rcases family_descends (prefixWord ++ tailWord_5180832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5180849 : List Nat := [1, 2, 2, 4, 1, 1, 3, 3, 6]
def baseStart_5180849 : Nat := 118140960795 + 5180849 * 2 ^ 59
def prefixEnd_5180849 : Nat := 4983230072969 + 3 ^ 40 * 5180849 * 2
def baseEnd_5180849 : Nat := 295585081707278404240135

theorem tailTrace_5180849 : CollatzResearch.WordTrace tailWord_5180849 prefixEnd_5180849 295585081707278404240135 := by
  unfold tailWord_5180849
  simp only [CollatzResearch.WordTrace]
  refine ⟨188961086807676366410305601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125974057871784244273537067 188961086807676366410305601)
  ·
    refine ⟨141720815105757274807729201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188961086807676366410305601 141720815105757274807729201)
    ·
      refine ⟨106290611329317956105796901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141720815105757274807729201 106290611329317956105796901)
      ·
        refine ⟨19929489624247116769836919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 106290611329317956105796901 19929489624247116769836919)
        ·
          refine ⟨29894234436370675154755379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19929489624247116769836919 29894234436370675154755379)
          ·
            refine ⟨44841351654556012732133069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29894234436370675154755379 44841351654556012732133069)
            ·
              refine ⟨16815506870458504774549901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44841351654556012732133069 16815506870458504774549901)
              ·
                refine ⟨6305815076421939290456213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16815506870458504774549901 6305815076421939290456213)
                ·
                  refine ⟨295585081707278404240135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6305815076421939290456213 295585081707278404240135)
                  ·
                    rfl

theorem cell23_5180849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 3, 6].length) (baseStart_5180849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5180849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5180849 prefixEnd_5180849 := by exact prefixLift 5180849
  have htrace : WordTrace (prefixWord ++ tailWord_5180849) baseStart_5180849 baseEnd_5180849 := by
    simpa [prefixWord, tailWord_5180849, baseEnd_5180849] using wordTrace_append hprefix tailTrace_5180849
  have hstable : (prefixWord ++ tailWord_5180849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5180849).length < 2 ^ (prefixWord ++ tailWord_5180849).sum := by decide
  have hdescent : baseEnd_5180849 < baseStart_5180849 := by decide
  rcases family_descends (prefixWord ++ tailWord_5180849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5180879 : List Nat := [1, 1, 2, 1, 1, 4, 2, 5, 1, 5]
def baseStart_5180879 : Nat := 118140960795 + 5180879 * 2 ^ 59
def prefixEnd_5180879 : Nat := 4983230072969 + 3 ^ 40 * 5180879 * 2
def baseEnd_5180879 : Nat := 886760379928380173595359

theorem tailTrace_5180879 : CollatzResearch.WordTrace tailWord_5180879 prefixEnd_5180879 886760379928380173595359 := by
  unfold tailWord_5180879
  simp only [CollatzResearch.WordTrace]
  refine ⟨188962180997567681533897691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125974787331711787689265127 188962180997567681533897691)
  ·
    refine ⟨283443271496351522300846537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188962180997567681533897691 283443271496351522300846537)
    ·
      refine ⟨212582453622263641725634903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 283443271496351522300846537 212582453622263641725634903)
      ·
        refine ⟨318873680433395462588452355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212582453622263641725634903 318873680433395462588452355)
        ·
          refine ⟨478310520650093193882678533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 318873680433395462588452355 478310520650093193882678533)
          ·
            refine ⟨89683222621892473853002225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 478310520650093193882678533 89683222621892473853002225)
            ·
              refine ⟨67262416966419355389751669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89683222621892473853002225 67262416966419355389751669)
              ·
                refine ⟨6305851590601814567789219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 67262416966419355389751669 6305851590601814567789219)
                ·
                  refine ⟨9458777385902721851683829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6305851590601814567789219 9458777385902721851683829)
                  ·
                    refine ⟨886760379928380173595359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9458777385902721851683829 886760379928380173595359)
                    ·
                      rfl

theorem cell23_5180879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 5, 1, 5].length) (baseStart_5180879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5180879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5180879 prefixEnd_5180879 := by exact prefixLift 5180879
  have htrace : WordTrace (prefixWord ++ tailWord_5180879) baseStart_5180879 baseEnd_5180879 := by
    simpa [prefixWord, tailWord_5180879, baseEnd_5180879] using wordTrace_append hprefix tailTrace_5180879
  have hstable : (prefixWord ++ tailWord_5180879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5180879).length < 2 ^ (prefixWord ++ tailWord_5180879).sum := by decide
  have hdescent : baseEnd_5180879 < baseStart_5180879 := by decide
  rcases family_descends (prefixWord ++ tailWord_5180879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5180930 : List Nat := [3, 4, 1, 2, 1, 1, 4, 1, 1, 5]
def baseStart_5180930 : Nat := 118140960795 + 5180930 * 2 ^ 59
def prefixEnd_5180930 : Nat := 4983230072969 + 3 ^ 40 * 5180930 * 2
def baseEnd_5180930 : Nat := 886769109099506607082781

theorem tailTrace_5180930 : CollatzResearch.WordTrace tailWord_5180930 prefixEnd_5180930 886769109099506607082781 := by
  unfold tailWord_5180930
  simp only [CollatzResearch.WordTrace]
  refine ⟨47241010280095729311001061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125976027413588611496002829 47241010280095729311001061)
  ·
    refine ⟨8857689427517949245812699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47241010280095729311001061 8857689427517949245812699)
    ·
      refine ⟨13286534141276923868719049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8857689427517949245812699 13286534141276923868719049)
      ·
        refine ⟨9964900605957692901539287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13286534141276923868719049 9964900605957692901539287)
        ·
          refine ⟨14947350908936539352308931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9964900605957692901539287 14947350908936539352308931)
          ·
            refine ⟨22421026363404809028463397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14947350908936539352308931 22421026363404809028463397)
            ·
              refine ⟨4203942443138401692836887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22421026363404809028463397 4203942443138401692836887)
              ·
                refine ⟨6305913664707602539255331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4203942443138401692836887 6305913664707602539255331)
                ·
                  refine ⟨9458870497061403808882997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6305913664707602539255331 9458870497061403808882997)
                  ·
                    refine ⟨886769109099506607082781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9458870497061403808882997 886769109099506607082781)
                    ·
                      rfl

theorem cell23_5180930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 4, 1, 1, 5].length) (baseStart_5180930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5180930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5180930 prefixEnd_5180930 := by exact prefixLift 5180930
  have htrace : WordTrace (prefixWord ++ tailWord_5180930) baseStart_5180930 baseEnd_5180930 := by
    simpa [prefixWord, tailWord_5180930, baseEnd_5180930] using wordTrace_append hprefix tailTrace_5180930
  have hstable : (prefixWord ++ tailWord_5180930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5180930).length < 2 ^ (prefixWord ++ tailWord_5180930).sum := by decide
  have hdescent : baseEnd_5180930 < baseStart_5180930 := by decide
  rcases family_descends (prefixWord ++ tailWord_5180930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5180934 : List Nat := [6, 2, 1, 1, 3, 1, 1, 2, 6]
def baseStart_5180934 : Nat := 118140960795 + 5180934 * 2 ^ 59
def prefixEnd_5180934 : Nat := 4983230072969 + 3 ^ 40 * 5180934 * 2
def baseEnd_5180934 : Nat := 295589931246793089510925

theorem tailTrace_5180934 : CollatzResearch.WordTrace tailWord_5180934 prefixEnd_5180934 295589931246793089510925 := by
  unfold tailWord_5180934
  simp only [CollatzResearch.WordTrace]
  refine ⟨5905130844136513310223433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 125976124674912283951433237 5905130844136513310223433)
  ·
    refine ⟨4428848133102384982667575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5905130844136513310223433 4428848133102384982667575)
    ·
      refine ⟨6643272199653577474001363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4428848133102384982667575 6643272199653577474001363)
      ·
        refine ⟨9964908299480366211002045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6643272199653577474001363 9964908299480366211002045)
        ·
          refine ⟨3736840612305137329125767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9964908299480366211002045 3736840612305137329125767)
          ·
            refine ⟨5605260918457705993688651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3736840612305137329125767 5605260918457705993688651)
            ·
              refine ⟨8407891377686558990532977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5605260918457705993688651 8407891377686558990532977)
              ·
                refine ⟨6305918533264919242899733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8407891377686558990532977 6305918533264919242899733)
                ·
                  refine ⟨295589931246793089510925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6305918533264919242899733 295589931246793089510925)
                  ·
                    rfl

theorem cell23_5180934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 1, 2, 6].length) (baseStart_5180934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5180934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5180934 prefixEnd_5180934 := by exact prefixLift 5180934
  have htrace : WordTrace (prefixWord ++ tailWord_5180934) baseStart_5180934 baseEnd_5180934 := by
    simpa [prefixWord, tailWord_5180934, baseEnd_5180934] using wordTrace_append hprefix tailTrace_5180934
  have hstable : (prefixWord ++ tailWord_5180934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5180934).length < 2 ^ (prefixWord ++ tailWord_5180934).sum := by decide
  have hdescent : baseEnd_5180934 < baseStart_5180934 := by decide
  rcases family_descends (prefixWord ++ tailWord_5180934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5180939 : List Nat := [1, 1, 1, 1, 8, 1, 10]
def baseStart_5180939 : Nat := 118140960795 + 5180939 * 2 ^ 59
def prefixEnd_5180939 : Nat := 4983230072969 + 3 ^ 40 * 5180939 * 2
def baseEnd_5180939 : Nat := 32843357390424818346121

theorem tailTrace_5180939 : CollatzResearch.WordTrace tailWord_5180939 prefixEnd_5180939 32843357390424818346121 := by
  unfold tailWord_5180939
  simp only [CollatzResearch.WordTrace]
  refine ⟨188964369377350311781081871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125976246251566874520721247 188964369377350311781081871)
  ·
    refine ⟨283446554066025467671622807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188964369377350311781081871 283446554066025467671622807)
    ·
      refine ⟨425169831099038201507434211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 283446554066025467671622807 425169831099038201507434211)
      ·
        refine ⟨637754746648557302261151317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 425169831099038201507434211 637754746648557302261151317)
        ·
          refine ⟨7473688437287780885872867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 637754746648557302261151317 7473688437287780885872867)
          ·
            refine ⟨11210532655931671328809301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7473688437287780885872867 11210532655931671328809301)
            ·
              refine ⟨32843357390424818346121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 11210532655931671328809301 32843357390424818346121)
              ·
                rfl

theorem cell23_5180939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 10].length) (baseStart_5180939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5180939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5180939 prefixEnd_5180939 := by exact prefixLift 5180939
  have htrace : WordTrace (prefixWord ++ tailWord_5180939) baseStart_5180939 baseEnd_5180939 := by
    simpa [prefixWord, tailWord_5180939, baseEnd_5180939] using wordTrace_append hprefix tailTrace_5180939
  have hstable : (prefixWord ++ tailWord_5180939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5180939).length < 2 ^ (prefixWord ++ tailWord_5180939).sum := by decide
  have hdescent : baseEnd_5180939 < baseStart_5180939 := by decide
  rcases family_descends (prefixWord ++ tailWord_5180939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5180960 : List Nat := [2, 1, 1, 6, 1, 2, 3, 1, 2, 4]
def baseStart_5180960 : Nat := 118140960795 + 5180960 * 2 ^ 59
def prefixEnd_5180960 : Nat := 4983230072969 + 3 ^ 40 * 5180960 * 2
def baseEnd_5180960 : Nat := 886774243906051567957735

theorem tailTrace_5180960 : CollatzResearch.WordTrace tailWord_5180960 prefixEnd_5180960 886774243906051567957735 := by
  unfold tailWord_5180960
  simp only [CollatzResearch.WordTrace]
  refine ⟨94482567655137116183798167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125976756873516154911730889 94482567655137116183798167)
  ·
    refine ⟨141723851482705674275697251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94482567655137116183798167 141723851482705674275697251)
    ·
      refine ⟨212585777224058511413545877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141723851482705674275697251 212585777224058511413545877)
      ·
        refine ⟨9964958307377742722509963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 212585777224058511413545877 9964958307377742722509963)
        ·
          refine ⟨14947437461066614083764945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9964958307377742722509963 14947437461066614083764945)
          ·
            refine ⟨11210578095799960562823709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14947437461066614083764945 11210578095799960562823709)
            ·
              refine ⟨4203966785924985211058891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11210578095799960562823709 4203966785924985211058891)
              ·
                refine ⟨6305950178887477816588337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4203966785924985211058891 6305950178887477816588337)
                ·
                  refine ⟨4729462634165608362441253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6305950178887477816588337 4729462634165608362441253)
                  ·
                    refine ⟨886774243906051567957735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4729462634165608362441253 886774243906051567957735)
                    ·
                      rfl

theorem cell23_5180960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 3, 1, 2, 4].length) (baseStart_5180960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5180960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5180960 prefixEnd_5180960 := by exact prefixLift 5180960
  have htrace : WordTrace (prefixWord ++ tailWord_5180960) baseStart_5180960 baseEnd_5180960 := by
    simpa [prefixWord, tailWord_5180960, baseEnd_5180960] using wordTrace_append hprefix tailTrace_5180960
  have hstable : (prefixWord ++ tailWord_5180960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5180960).length < 2 ^ (prefixWord ++ tailWord_5180960).sum := by decide
  have hdescent : baseEnd_5180960 < baseStart_5180960 := by decide
  rcases family_descends (prefixWord ++ tailWord_5180960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5180963 : List Nat := [1, 1, 1, 4, 5, 2, 1, 1, 1, 2, 4]
def baseStart_5180963 : Nat := 118140960795 + 5180963 * 2 ^ 59
def prefixEnd_5180963 : Nat := 4983230072969 + 3 ^ 40 * 5180963 * 2
def baseEnd_5180963 : Nat := 2660324272160118192135691

theorem tailTrace_5180963 : CollatzResearch.WordTrace tailWord_5180963 prefixEnd_5180963 2660324272160118192135691 := by
  unfold tailWord_5180963
  simp only [CollatzResearch.WordTrace]
  refine ⟨188965244729263363879955543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125976829819508909253303695 188965244729263363879955543)
  ·
    refine ⟨283447867093895045819933315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188965244729263363879955543 283447867093895045819933315)
    ·
      refine ⟨425171800640842568729899973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 283447867093895045819933315 425171800640842568729899973)
      ·
        refine ⟨79719712620157981636856245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 425171800640842568729899973 79719712620157981636856245)
        ·
          refine ⟨7473723058139810778455273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 79719712620157981636856245 7473723058139810778455273)
          ·
            refine ⟨5605292293604858083841455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7473723058139810778455273 5605292293604858083841455)
            ·
              refine ⟨8407938440407287125762183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5605292293604858083841455 8407938440407287125762183)
              ·
                refine ⟨12611907660610930688643275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8407938440407287125762183 12611907660610930688643275)
                ·
                  refine ⟨18917861490916396032964913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12611907660610930688643275 18917861490916396032964913)
                  ·
                    refine ⟨14188396118187297024723685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18917861490916396032964913 14188396118187297024723685)
                    ·
                      refine ⟨2660324272160118192135691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14188396118187297024723685 2660324272160118192135691)
                      ·
                        rfl

theorem cell23_5180963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 1, 1, 1, 2, 4].length) (baseStart_5180963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5180963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5180963 prefixEnd_5180963 := by exact prefixLift 5180963
  have htrace : WordTrace (prefixWord ++ tailWord_5180963) baseStart_5180963 baseEnd_5180963 := by
    simpa [prefixWord, tailWord_5180963, baseEnd_5180963] using wordTrace_append hprefix tailTrace_5180963
  have hstable : (prefixWord ++ tailWord_5180963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5180963).length < 2 ^ (prefixWord ++ tailWord_5180963).sum := by decide
  have hdescent : baseEnd_5180963 < baseStart_5180963 := by decide
  rcases family_descends (prefixWord ++ tailWord_5180963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5180979 : List Nat := [1, 1, 1, 2, 4, 3, 1, 1, 2, 2, 5]
def baseStart_5180979 : Nat := 118140960795 + 5180979 * 2 ^ 59
def prefixEnd_5180979 : Nat := 4983230072969 + 3 ^ 40 * 5180979 * 2
def baseEnd_5180979 : Nat := 2660332487850590129535617

theorem tailTrace_5180979 : CollatzResearch.WordTrace tailWord_5180979 prefixEnd_5180979 2660332487850590129535617 := by
  unfold tailWord_5180979
  simp only [CollatzResearch.WordTrace]
  refine ⟨188965828297205398612537991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125977218864803599075025327 188965828297205398612537991)
  ·
    refine ⟨283448742445808097918806987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188965828297205398612537991 283448742445808097918806987)
    ·
      refine ⟨425173113668712146878210481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 283448742445808097918806987 425173113668712146878210481)
      ·
        refine ⟨318879835251534110158657861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 425173113668712146878210481 318879835251534110158657861)
        ·
          refine ⟨59789969109662645654748349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 318879835251534110158657861 59789969109662645654748349)
          ·
            refine ⟨22421238416123492120530631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59789969109662645654748349 22421238416123492120530631)
            ·
              refine ⟨33631857624185238180795947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22421238416123492120530631 33631857624185238180795947)
              ·
                refine ⟨50447786436277857271193921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33631857624185238180795947 50447786436277857271193921)
                ·
                  refine ⟨37835839827208392953395441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50447786436277857271193921 37835839827208392953395441)
                  ·
                    refine ⟨28376879870406294715046581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37835839827208392953395441 28376879870406294715046581)
                    ·
                      refine ⟨2660332487850590129535617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28376879870406294715046581 2660332487850590129535617)
                      ·
                        rfl

theorem cell23_5180979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 1, 2, 2, 5].length) (baseStart_5180979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5180979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5180979 prefixEnd_5180979 := by exact prefixLift 5180979
  have htrace : WordTrace (prefixWord ++ tailWord_5180979) baseStart_5180979 baseEnd_5180979 := by
    simpa [prefixWord, tailWord_5180979, baseEnd_5180979] using wordTrace_append hprefix tailTrace_5180979
  have hstable : (prefixWord ++ tailWord_5180979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5180979).length < 2 ^ (prefixWord ++ tailWord_5180979).sum := by decide
  have hdescent : baseEnd_5180979 < baseStart_5180979 := by decide
  rcases family_descends (prefixWord ++ tailWord_5180979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5181009 : List Nat := [1, 2, 2, 1, 3, 2, 1, 2, 1, 3, 5]
def baseStart_5181009 : Nat := 118140960795 + 5181009 * 2 ^ 59
def prefixEnd_5181009 : Nat := 4983230072969 + 3 ^ 40 * 5181009 * 2
def baseEnd_5181009 : Nat := 2660347892270225012160479

theorem tailTrace_5181009 : CollatzResearch.WordTrace tailWord_5181009 prefixEnd_5181009 2660347892270225012160479 := by
  unfold tailWord_5181009
  simp only [CollatzResearch.WordTrace]
  refine ⟨188966922487096713736130081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125977948324731142490753387 188966922487096713736130081)
  ·
    refine ⟨141725191865322535302097561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188966922487096713736130081 141725191865322535302097561)
    ·
      refine ⟨106293893898991901476573171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141725191865322535302097561 106293893898991901476573171)
      ·
        refine ⟨159440840848487852214859757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106293893898991901476573171 159440840848487852214859757)
        ·
          refine ⟨59790315318182944580572409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 159440840848487852214859757 59790315318182944580572409)
          ·
            refine ⟨44842736488637208435429307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59790315318182944580572409 44842736488637208435429307)
            ·
              refine ⟨67264104732955812653143961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44842736488637208435429307 67264104732955812653143961)
              ·
                refine ⟨50448078549716859489857971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67264104732955812653143961 50448078549716859489857971)
                ·
                  refine ⟨75672117824575289234786957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50448078549716859489857971 75672117824575289234786957)
                  ·
                    refine ⟨28377044184215733463045109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 75672117824575289234786957 28377044184215733463045109)
                    ·
                      refine ⟨2660347892270225012160479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28377044184215733463045109 2660347892270225012160479)
                      ·
                        rfl

theorem cell23_5181009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 2, 1, 3, 5].length) (baseStart_5181009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5181009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5181009 prefixEnd_5181009 := by exact prefixLift 5181009
  have htrace : WordTrace (prefixWord ++ tailWord_5181009) baseStart_5181009 baseEnd_5181009 := by
    simpa [prefixWord, tailWord_5181009, baseEnd_5181009] using wordTrace_append hprefix tailTrace_5181009
  have hstable : (prefixWord ++ tailWord_5181009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5181009).length < 2 ^ (prefixWord ++ tailWord_5181009).sum := by decide
  have hdescent : baseEnd_5181009 < baseStart_5181009 := by decide
  rcases family_descends (prefixWord ++ tailWord_5181009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5181056 : List Nat := [2, 1, 1, 2, 1, 4, 2, 2, 2, 3, 3]
def baseStart_5181056 : Nat := 118140960795 + 5181056 * 2 ^ 59
def prefixEnd_5181056 : Nat := 4983230072969 + 3 ^ 40 * 5181056 * 2
def baseEnd_5181056 : Nat := 2660372025860986328272763

theorem tailTrace_5181056 : CollatzResearch.WordTrace tailWord_5181056 prefixEnd_5181056 2660372025860986328272763 := by
  unfold tailWord_5181056
  simp only [CollatzResearch.WordTrace]
  refine ⟨94484318358963220381545511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125979091145284293842060681 94484318358963220381545511)
  ·
    refine ⟨141726477538444830572318267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94484318358963220381545511 141726477538444830572318267)
    ·
      refine ⟨212589716307667245858477401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141726477538444830572318267 212589716307667245858477401)
      ·
        refine ⟨159442287230750434393858051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 212589716307667245858477401 159442287230750434393858051)
        ·
          refine ⟨239163430846125651590787077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159442287230750434393858051 239163430846125651590787077)
          ·
            refine ⟨44843143283648559673272577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 239163430846125651590787077 44843143283648559673272577)
            ·
              refine ⟨33632357462736419754954433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44843143283648559673272577 33632357462736419754954433)
              ·
                refine ⟨25224268097052314816215825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33632357462736419754954433 25224268097052314816215825)
                ·
                  refine ⟨18918201072789236112161869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25224268097052314816215825 18918201072789236112161869)
                  ·
                    refine ⟨7094325402295963542060701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18918201072789236112161869 7094325402295963542060701)
                    ·
                      refine ⟨2660372025860986328272763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7094325402295963542060701 2660372025860986328272763)
                      ·
                        rfl

theorem cell23_5181056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 2, 2, 3, 3].length) (baseStart_5181056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5181056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5181056 prefixEnd_5181056 := by exact prefixLift 5181056
  have htrace : WordTrace (prefixWord ++ tailWord_5181056) baseStart_5181056 baseEnd_5181056 := by
    simpa [prefixWord, tailWord_5181056, baseEnd_5181056] using wordTrace_append hprefix tailTrace_5181056
  have hstable : (prefixWord ++ tailWord_5181056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5181056).length < 2 ^ (prefixWord ++ tailWord_5181056).sum := by decide
  have hdescent : baseEnd_5181056 < baseStart_5181056 := by decide
  rcases family_descends (prefixWord ++ tailWord_5181056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5181057 : List Nat := [1, 2, 4, 2, 1, 3, 2, 2, 2, 2, 2]
def baseStart_5181057 : Nat := 118140960795 + 5181057 * 2 ^ 59
def prefixEnd_5181057 : Nat := 4983230072969 + 3 ^ 40 * 5181057 * 2
def baseEnd_5181057 : Nat := 2660372539341640824360259

theorem tailTrace_5181057 : CollatzResearch.WordTrace tailWord_5181057 prefixEnd_5181057 2660372539341640824360259 := by
  unfold tailWord_5181057
  simp only [CollatzResearch.WordTrace]
  refine ⟨188968673190922817933877425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125979115460615211955918283 188968673190922817933877425)
  ·
    refine ⟨141726504893192113450408069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188968673190922817933877425 141726504893192113450408069)
    ·
      refine ⟨26573719667473521271951513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 141726504893192113450408069 26573719667473521271951513)
      ·
        refine ⟨19930289750605140953963635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26573719667473521271951513 19930289750605140953963635)
        ·
          refine ⟨29895434625907711430945453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19930289750605140953963635 29895434625907711430945453)
          ·
            refine ⟨11210787984715391786604545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29895434625907711430945453 11210787984715391786604545)
            ·
              refine ⟨8408090988536543839953409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11210787984715391786604545 8408090988536543839953409)
              ·
                refine ⟨6306068241402407879965057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8408090988536543839953409 6306068241402407879965057)
                ·
                  refine ⟨4729551181051805909973793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6306068241402407879965057 4729551181051805909973793)
                  ·
                    refine ⟨3547163385788854432480345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4729551181051805909973793 3547163385788854432480345)
                    ·
                      refine ⟨2660372539341640824360259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3547163385788854432480345 2660372539341640824360259)
                      ·
                        rfl

theorem cell23_5181057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 2, 2, 2, 2, 2].length) (baseStart_5181057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5181057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5181057 prefixEnd_5181057 := by exact prefixLift 5181057
  have htrace : WordTrace (prefixWord ++ tailWord_5181057) baseStart_5181057 baseEnd_5181057 := by
    simpa [prefixWord, tailWord_5181057, baseEnd_5181057] using wordTrace_append hprefix tailTrace_5181057
  have hstable : (prefixWord ++ tailWord_5181057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5181057).length < 2 ^ (prefixWord ++ tailWord_5181057).sum := by decide
  have hdescent : baseEnd_5181057 < baseStart_5181057 := by decide
  rcases family_descends (prefixWord ++ tailWord_5181057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5181059 : List Nat := [1, 1, 1, 3, 3, 1, 1, 2, 3, 7]
def baseStart_5181059 : Nat := 118140960795 + 5181059 * 2 ^ 59
def prefixEnd_5181059 : Nat := 4983230072969 + 3 ^ 40 * 5181059 * 2
def baseEnd_5181059 : Nat := 886791188767649938845083

theorem tailTrace_5181059 : CollatzResearch.WordTrace tailWord_5181059 prefixEnd_5181059 886791188767649938845083 := by
  unfold tailWord_5181059
  simp only [CollatzResearch.WordTrace]
  refine ⟨188968746136915572275450231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125979164091277048183633487 188968746136915572275450231)
  ·
    refine ⟨283453119205373358413175347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188968746136915572275450231 283453119205373358413175347)
    ·
      refine ⟨425179678808060037619763021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 283453119205373358413175347 425179678808060037619763021)
      ·
        refine ⟨159442379553022514107411133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 425179678808060037619763021 159442379553022514107411133)
        ·
          refine ⟨59790892332383442790279175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 159442379553022514107411133 59790892332383442790279175)
          ·
            refine ⟨89686338498575164185418763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59790892332383442790279175 89686338498575164185418763)
            ·
              refine ⟨134529507747862746278128145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89686338498575164185418763 134529507747862746278128145)
              ·
                refine ⟨100897130810897059708596109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 134529507747862746278128145 100897130810897059708596109)
                ·
                  refine ⟨37836424054086397390723541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 100897130810897059708596109 37836424054086397390723541)
                  ·
                    refine ⟨886791188767649938845083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37836424054086397390723541 886791188767649938845083)
                    ·
                      rfl

theorem cell23_5181059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 3, 7].length) (baseStart_5181059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5181059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5181059 prefixEnd_5181059 := by exact prefixLift 5181059
  have htrace : WordTrace (prefixWord ++ tailWord_5181059) baseStart_5181059 baseEnd_5181059 := by
    simpa [prefixWord, tailWord_5181059, baseEnd_5181059] using wordTrace_append hprefix tailTrace_5181059
  have hstable : (prefixWord ++ tailWord_5181059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5181059).length < 2 ^ (prefixWord ++ tailWord_5181059).sum := by decide
  have hdescent : baseEnd_5181059 < baseStart_5181059 := by decide
  rcases family_descends (prefixWord ++ tailWord_5181059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5181063 : List Nat := [1, 1, 4, 2, 1, 4, 1, 4, 5]
def baseStart_5181063 : Nat := 118140960795 + 5181063 * 2 ^ 59
def prefixEnd_5181063 : Nat := 4983230072969 + 3 ^ 40 * 5181063 * 2
def baseEnd_5181063 : Nat := 295597291136174200098359

theorem tailTrace_5181063 : CollatzResearch.WordTrace tailWord_5181063 prefixEnd_5181063 295597291136174200098359 := by
  unfold tailWord_5181063
  simp only [CollatzResearch.WordTrace]
  refine ⟨188968892028901080958595843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125979261352600720639063895 188968892028901080958595843)
  ·
    refine ⟨283453338043351621437893765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188968892028901080958595843 283453338043351621437893765)
    ·
      refine ⟨53147500883128429019605081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 283453338043351621437893765 53147500883128429019605081)
      ·
        refine ⟨39860625662346321764703811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53147500883128429019605081 39860625662346321764703811)
        ·
          refine ⟨59790938493519482647055717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39860625662346321764703811 59790938493519482647055717)
          ·
            refine ⟨11210800967534902996322947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59790938493519482647055717 11210800967534902996322947)
            ·
              refine ⟨16816201451302354494484421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11210800967534902996322947 16816201451302354494484421)
              ·
                refine ⟨3153037772119191467715829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16816201451302354494484421 3153037772119191467715829)
                ·
                  refine ⟨295597291136174200098359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3153037772119191467715829 295597291136174200098359)
                  ·
                    rfl

theorem cell23_5181063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 4, 5].length) (baseStart_5181063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5181063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5181063 prefixEnd_5181063 := by exact prefixLift 5181063
  have htrace : WordTrace (prefixWord ++ tailWord_5181063) baseStart_5181063 baseEnd_5181063 := by
    simpa [prefixWord, tailWord_5181063, baseEnd_5181063] using wordTrace_append hprefix tailTrace_5181063
  have hstable : (prefixWord ++ tailWord_5181063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5181063).length < 2 ^ (prefixWord ++ tailWord_5181063).sum := by decide
  have hdescent : baseEnd_5181063 < baseStart_5181063 := by decide
  rcases family_descends (prefixWord ++ tailWord_5181063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5181113 : List Nat := [1, 2, 1, 4, 1, 1, 3, 2, 2, 4, 2]
def baseStart_5181113 : Nat := 118140960795 + 5181113 * 2 ^ 59
def prefixEnd_5181113 : Nat := 4983230072969 + 3 ^ 40 * 5181113 * 2
def baseEnd_5181113 : Nat := 2660401294258292605260001

theorem tailTrace_5181113 : CollatzResearch.WordTrace tailWord_5181113 prefixEnd_5181113 2660401294258292605260001 := by
  unfold tailWord_5181113
  simp only [CollatzResearch.WordTrace]
  refine ⟨188970715678719939497915993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125980477119146626331943995 188970715678719939497915993)
  ·
    refine ⟨141728036759039954623436995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188970715678719939497915993 141728036759039954623436995)
    ·
      refine ⟨212592055138559931935155493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141728036759039954623436995 212592055138559931935155493)
      ·
        refine ⟨39861010338479987237841655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 212592055138559931935155493 39861010338479987237841655)
        ·
          refine ⟨59791515507719980856762483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39861010338479987237841655 59791515507719980856762483)
          ·
            refine ⟨89687273261579971285143725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59791515507719980856762483 89687273261579971285143725)
            ·
              refine ⟨33632727473092489231928897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89687273261579971285143725 33632727473092489231928897)
              ·
                refine ⟨25224545604819366923946673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33632727473092489231928897 25224545604819366923946673)
                ·
                  refine ⟨18918409203614525192960005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25224545604819366923946673 18918409203614525192960005)
                  ·
                    refine ⟨3547201725677723473680001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18918409203614525192960005 3547201725677723473680001)
                    ·
                      refine ⟨2660401294258292605260001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3547201725677723473680001 2660401294258292605260001)
                      ·
                        rfl

theorem cell23_5181113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 2, 2, 4, 2].length) (baseStart_5181113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5181113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5181113 prefixEnd_5181113 := by exact prefixLift 5181113
  have htrace : WordTrace (prefixWord ++ tailWord_5181113) baseStart_5181113 baseEnd_5181113 := by
    simpa [prefixWord, tailWord_5181113, baseEnd_5181113] using wordTrace_append hprefix tailTrace_5181113
  have hstable : (prefixWord ++ tailWord_5181113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5181113).length < 2 ^ (prefixWord ++ tailWord_5181113).sum := by decide
  have hdescent : baseEnd_5181113 < baseStart_5181113 := by decide
  rcases family_descends (prefixWord ++ tailWord_5181113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5181140 : List Nat := [2, 4, 1, 3, 1, 1, 2, 2, 3, 4]
def baseStart_5181140 : Nat := 118140960795 + 5181140 * 2 ^ 59
def prefixEnd_5181140 : Nat := 4983230072969 + 3 ^ 40 * 5181140 * 2
def baseEnd_5181140 : Nat := 886805052745321333207459

theorem tailTrace_5181140 : CollatzResearch.WordTrace tailWord_5181140 prefixEnd_5181140 886805052745321333207459 := by
  unfold tailWord_5181140
  simp only [CollatzResearch.WordTrace]
  refine ⟨94485850224811061554574437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125981133633081415406099249 94485850224811061554574437)
  ·
    refine ⟨17716096917152074041482707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94485850224811061554574437 17716096917152074041482707)
    ·
      refine ⟨26574145375728111062224061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17716096917152074041482707 26574145375728111062224061)
      ·
        refine ⟨9965304515898041648334023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26574145375728111062224061 9965304515898041648334023)
        ·
          refine ⟨14947956773847062472501035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9965304515898041648334023 14947956773847062472501035)
          ·
            refine ⟨22421935160770593708751553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14947956773847062472501035 22421935160770593708751553)
            ·
              refine ⟨16816451370577945281563665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22421935160770593708751553 16816451370577945281563665)
              ·
                refine ⟨12612338527933458961172749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16816451370577945281563665 12612338527933458961172749)
                ·
                  refine ⟨4729626947975047110439781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12612338527933458961172749 4729626947975047110439781)
                  ·
                    refine ⟨886805052745321333207459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4729626947975047110439781 886805052745321333207459)
                    ·
                      rfl

theorem cell23_5181140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 2, 3, 4].length) (baseStart_5181140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5181140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5181140 prefixEnd_5181140 := by exact prefixLift 5181140
  have htrace : WordTrace (prefixWord ++ tailWord_5181140) baseStart_5181140 baseEnd_5181140 := by
    simpa [prefixWord, tailWord_5181140, baseEnd_5181140] using wordTrace_append hprefix tailTrace_5181140
  have hstable : (prefixWord ++ tailWord_5181140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5181140).length < 2 ^ (prefixWord ++ tailWord_5181140).sum := by decide
  have hdescent : baseEnd_5181140 < baseStart_5181140 := by decide
  rcases family_descends (prefixWord ++ tailWord_5181140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5181163 : List Nat := [1, 1, 1, 1, 2, 4, 2, 2, 5, 1, 3]
def baseStart_5181163 : Nat := 118140960795 + 5181163 * 2 ^ 59
def prefixEnd_5181163 : Nat := 4983230072969 + 3 ^ 40 * 5181163 * 2
def baseEnd_5181163 : Nat := 2660426968291017409634771

theorem tailTrace_5181163 : CollatzResearch.WordTrace tailWord_5181163 prefixEnd_5181163 2660426968291017409634771 := by
  unfold tailWord_5181163
  simp only [CollatzResearch.WordTrace]
  refine ⟨188972539328538798037236143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125981692885692532024824095 188972539328538798037236143)
  ·
    refine ⟨283458808992808197055854215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188972539328538798037236143 283458808992808197055854215)
    ·
      refine ⟨425188213489212295583781323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 283458808992808197055854215 425188213489212295583781323)
      ·
        refine ⟨637782320233818443375671985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 425188213489212295583781323 637782320233818443375671985)
        ·
          refine ⟨478336740175363832531753989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 637782320233818443375671985 478336740175363832531753989)
          ·
            refine ⟨89688138782880718599703873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 478336740175363832531753989 89688138782880718599703873)
            ·
              refine ⟨67266104087160538949777905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89688138782880718599703873 67266104087160538949777905)
              ·
                refine ⟨50449578065370404212333429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67266104087160538949777905 50449578065370404212333429)
                ·
                  refine ⟨4729647943628475394906259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 50449578065370404212333429 4729647943628475394906259)
                  ·
                    refine ⟨7094471915442713092359389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4729647943628475394906259 7094471915442713092359389)
                    ·
                      refine ⟨2660426968291017409634771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7094471915442713092359389 2660426968291017409634771)
                      ·
                        rfl

theorem cell23_5181163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 2, 5, 1, 3].length) (baseStart_5181163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5181163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5181163 prefixEnd_5181163 := by exact prefixLift 5181163
  have htrace : WordTrace (prefixWord ++ tailWord_5181163) baseStart_5181163 baseEnd_5181163 := by
    simpa [prefixWord, tailWord_5181163, baseEnd_5181163] using wordTrace_append hprefix tailTrace_5181163
  have hstable : (prefixWord ++ tailWord_5181163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5181163).length < 2 ^ (prefixWord ++ tailWord_5181163).sum := by decide
  have hdescent : baseEnd_5181163 < baseStart_5181163 := by decide
  rcases family_descends (prefixWord ++ tailWord_5181163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5181174 : List Nat := [5, 1, 1, 1, 1, 4, 3, 2, 1, 4]
def baseStart_5181174 : Nat := 118140960795 + 5181174 * 2 ^ 59
def prefixEnd_5181174 : Nat := 4983230072969 + 3 ^ 40 * 5181174 * 2
def baseEnd_5181174 : Nat := 886810872192738955532407

theorem tailTrace_5181174 : CollatzResearch.WordTrace tailWord_5181174 prefixEnd_5181174 886810872192738955532407 := by
  unfold tailWord_5181174
  simp only [CollatzResearch.WordTrace]
  refine ⟨11810808783218684182242911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 125981960354332631277257717 11810808783218684182242911)
  ·
    refine ⟨17716213174828026273364367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11810808783218684182242911 17716213174828026273364367)
    ·
      refine ⟨26574319762242039410046551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17716213174828026273364367 26574319762242039410046551)
      ·
        refine ⟨39861479643363059115069827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26574319762242039410046551 39861479643363059115069827)
        ·
          refine ⟨59792219465044588672604741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39861479643363059115069827 59792219465044588672604741)
          ·
            refine ⟨11211041149695860376113389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59792219465044588672604741 11211041149695860376113389)
            ·
              refine ⟨4204140431135947641042521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11211041149695860376113389 4204140431135947641042521)
              ·
                refine ⟨3153105323351960730781891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4204140431135947641042521 3153105323351960730781891)
                ·
                  refine ⟨4729657985027941096172837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3153105323351960730781891 4729657985027941096172837)
                  ·
                    refine ⟨886810872192738955532407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4729657985027941096172837 886810872192738955532407)
                    ·
                      rfl

theorem cell23_5181174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 3, 2, 1, 4].length) (baseStart_5181174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5181174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5181174 prefixEnd_5181174 := by exact prefixLift 5181174
  have htrace : WordTrace (prefixWord ++ tailWord_5181174) baseStart_5181174 baseEnd_5181174 := by
    simpa [prefixWord, tailWord_5181174, baseEnd_5181174] using wordTrace_append hprefix tailTrace_5181174
  have hstable : (prefixWord ++ tailWord_5181174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5181174).length < 2 ^ (prefixWord ++ tailWord_5181174).sum := by decide
  have hdescent : baseEnd_5181174 < baseStart_5181174 := by decide
  rcases family_descends (prefixWord ++ tailWord_5181174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5181203 : List Nat := [1, 1, 1, 2, 1, 3, 2, 6, 1, 1, 4]
def baseStart_5181203 : Nat := 118140960795 + 5181203 * 2 ^ 59
def prefixEnd_5181203 : Nat := 4983230072969 + 3 ^ 40 * 5181203 * 2
def baseEnd_5181203 : Nat := 2660447507517197253134587

theorem tailTrace_5181203 : CollatzResearch.WordTrace tailWord_5181203 prefixEnd_5181203 2660447507517197253134587 := by
  unfold tailWord_5181203
  simp only [CollatzResearch.WordTrace]
  refine ⟨188973998248393884868692263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125982665498929256579128175 188973998248393884868692263)
  ·
    refine ⟨283460997372590827303038395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188973998248393884868692263 283460997372590827303038395)
    ·
      refine ⟨425191496058886240954557593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 283460997372590827303038395 425191496058886240954557593)
      ·
        refine ⟨318893622044164680715918195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 425191496058886240954557593 318893622044164680715918195)
        ·
          refine ⟨478340433066247021073877293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 318893622044164680715918195 478340433066247021073877293)
          ·
            refine ⟨179377662399842632902703985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 478340433066247021073877293 179377662399842632902703985)
            ·
              refine ⟨134533246799881974677027989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 179377662399842632902703985 134533246799881974677027989)
              ·
                refine ⟨6306245943744467562985687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 134533246799881974677027989 6306245943744467562985687)
                ·
                  refine ⟨9459368915616701344478531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6306245943744467562985687 9459368915616701344478531)
                  ·
                    refine ⟨14189053373425052016717797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9459368915616701344478531 14189053373425052016717797)
                    ·
                      refine ⟨2660447507517197253134587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14189053373425052016717797 2660447507517197253134587)
                      ·
                        rfl

theorem cell23_5181203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 6, 1, 1, 4].length) (baseStart_5181203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5181203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5181203 prefixEnd_5181203 := by exact prefixLift 5181203
  have htrace : WordTrace (prefixWord ++ tailWord_5181203) baseStart_5181203 baseEnd_5181203 := by
    simpa [prefixWord, tailWord_5181203, baseEnd_5181203] using wordTrace_append hprefix tailTrace_5181203
  have hstable : (prefixWord ++ tailWord_5181203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5181203).length < 2 ^ (prefixWord ++ tailWord_5181203).sum := by decide
  have hdescent : baseEnd_5181203 < baseStart_5181203 := by decide
  rcases family_descends (prefixWord ++ tailWord_5181203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5181207 : List Nat := [1, 1, 3, 4, 2, 2, 2, 1, 2, 3, 2]
def baseStart_5181207 : Nat := 118140960795 + 5181207 * 2 ^ 59
def prefixEnd_5181207 : Nat := 4983230072969 + 3 ^ 40 * 5181207 * 2
def baseEnd_5181207 : Nat := 2660449561439815237484569

theorem tailTrace_5181207 : CollatzResearch.WordTrace tailWord_5181207 prefixEnd_5181207 2660449561439815237484569 := by
  unfold tailWord_5181207
  simp only [CollatzResearch.WordTrace]
  refine ⟨188974144140379393551837875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125982762760252929034558583 188974144140379393551837875)
  ·
    refine ⟨283461216210569090327756813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188974144140379393551837875 283461216210569090327756813)
    ·
      refine ⟨106297956078963408872908805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 283461216210569090327756813 106297956078963408872908805)
      ·
        refine ⟨19930866764805639163670401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 106297956078963408872908805 19930866764805639163670401)
        ·
          refine ⟨14948150073604229372752801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19930866764805639163670401 14948150073604229372752801)
          ·
            refine ⟨11211112555203172029564601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14948150073604229372752801 11211112555203172029564601)
            ·
              refine ⟨8408334416402379022173451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11211112555203172029564601 8408334416402379022173451)
              ·
                refine ⟨12612501624603568533260177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8408334416402379022173451 12612501624603568533260177)
                ·
                  refine ⟨9459376218452676399945133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12612501624603568533260177 9459376218452676399945133)
                  ·
                    refine ⟨3547266081919753649979425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9459376218452676399945133 3547266081919753649979425)
                    ·
                      refine ⟨2660449561439815237484569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3547266081919753649979425 2660449561439815237484569)
                      ·
                        rfl

theorem cell23_5181207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 2, 1, 2, 3, 2].length) (baseStart_5181207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5181207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5181207 prefixEnd_5181207 := by exact prefixLift 5181207
  have htrace : WordTrace (prefixWord ++ tailWord_5181207) baseStart_5181207 baseEnd_5181207 := by
    simpa [prefixWord, tailWord_5181207, baseEnd_5181207] using wordTrace_append hprefix tailTrace_5181207
  have hstable : (prefixWord ++ tailWord_5181207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5181207).length < 2 ^ (prefixWord ++ tailWord_5181207).sum := by decide
  have hdescent : baseEnd_5181207 < baseStart_5181207 := by decide
  rcases family_descends (prefixWord ++ tailWord_5181207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5181226 : List Nat := [3, 1, 4, 15]
def baseStart_5181226 : Nat := 118140960795 + 5181226 * 2 ^ 59
def prefixEnd_5181226 : Nat := 4983230072969 + 3 ^ 40 * 5181226 * 2
def baseEnd_5181226 : Nat := 1216488028153749731663

theorem tailTrace_5181226 : CollatzResearch.WordTrace tailWord_5181226 prefixEnd_5181226 1216488028153749731663 := by
  unfold tailWord_5181226
  simp only [CollatzResearch.WordTrace]
  refine ⟨47243709281827639949194883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125983224751540373197853021 47243709281827639949194883)
  ·
    refine ⟨70865563922741459923792325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47243709281827639949194883 70865563922741459923792325)
    ·
      refine ⟨13287293235514023735711061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70865563922741459923792325 13287293235514023735711061)
      ·
        refine ⟨1216488028153749731663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 15 13287293235514023735711061 1216488028153749731663)
        ·
          rfl

theorem cell23_5181226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 15].length) (baseStart_5181226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5181226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5181226 prefixEnd_5181226 := by exact prefixLift 5181226
  have htrace : WordTrace (prefixWord ++ tailWord_5181226) baseStart_5181226 baseEnd_5181226 := by
    simpa [prefixWord, tailWord_5181226, baseEnd_5181226] using wordTrace_append hprefix tailTrace_5181226
  have hstable : (prefixWord ++ tailWord_5181226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5181226).length < 2 ^ (prefixWord ++ tailWord_5181226).sum := by decide
  have hdescent : baseEnd_5181226 < baseStart_5181226 := by decide
  rcases family_descends (prefixWord ++ tailWord_5181226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5181260 : List Nat := [2, 2, 1, 3, 4, 1, 3, 7]
def baseStart_5181260 : Nat := 118140960795 + 5181260 * 2 ^ 59
def prefixEnd_5181260 : Nat := 4983230072969 + 3 ^ 40 * 5181260 * 2
def baseEnd_5181260 : Nat := 98536176885722352967475

theorem tailTrace_5181260 : CollatzResearch.WordTrace tailWord_5181260 prefixEnd_5181260 98536176885722352967475 := by
  unfold tailWord_5181260
  simp only [CollatzResearch.WordTrace]
  refine ⟨94488038604593691801758617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125984051472791589069011489 94488038604593691801758617)
  ·
    refine ⟨70866028953445268851318963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94488038604593691801758617 70866028953445268851318963)
    ·
      refine ⟨106299043430167903276978445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70866028953445268851318963 106299043430167903276978445)
      ·
        refine ⟨39862141286312963728866917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106299043430167903276978445 39862141286312963728866917)
        ·
          refine ⟨7474151491183680699162547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39862141286312963728866917 7474151491183680699162547)
          ·
            refine ⟨11211227236775521048743821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7474151491183680699162547 11211227236775521048743821)
            ·
              refine ⟨4204210213790820393278933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11211227236775521048743821 4204210213790820393278933)
              ·
                refine ⟨98536176885722352967475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4204210213790820393278933 98536176885722352967475)
                ·
                  rfl

theorem cell23_5181260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 3, 7].length) (baseStart_5181260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5181260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5181260 prefixEnd_5181260 := by exact prefixLift 5181260
  have htrace : WordTrace (prefixWord ++ tailWord_5181260) baseStart_5181260 baseEnd_5181260 := by
    simpa [prefixWord, tailWord_5181260, baseEnd_5181260] using wordTrace_append hprefix tailTrace_5181260
  have hstable : (prefixWord ++ tailWord_5181260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5181260).length < 2 ^ (prefixWord ++ tailWord_5181260).sum := by decide
  have hdescent : baseEnd_5181260 < baseStart_5181260 := by decide
  rcases family_descends (prefixWord ++ tailWord_5181260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5181271 : List Nat := [1, 1, 3, 2, 5, 1, 2, 3, 1, 2, 2]
def baseStart_5181271 : Nat := 118140960795 + 5181271 * 2 ^ 59
def prefixEnd_5181271 : Nat := 4983230072969 + 3 ^ 40 * 5181271 * 2
def baseEnd_5181271 : Nat := 2660482424201702987084275

theorem tailTrace_5181271 : CollatzResearch.WordTrace tailWord_5181271 prefixEnd_5181271 2660482424201702987084275 := by
  unfold tailWord_5181271
  simp only [CollatzResearch.WordTrace]
  refine ⟨188976478412147532482167667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125984318941431688321445111 188976478412147532482167667)
  ·
    refine ⟨283464717618221298723251501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188976478412147532482167667 283464717618221298723251501)
    ·
      refine ⟨106299269106832987021219313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 283464717618221298723251501 106299269106832987021219313)
      ·
        refine ⟨79724451830124740265914485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106299269106832987021219313 79724451830124740265914485)
        ·
          refine ⟨7474167359074194399929483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 79724451830124740265914485 7474167359074194399929483)
          ·
            refine ⟨11211251038611291599894225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7474167359074194399929483 11211251038611291599894225)
            ·
              refine ⟨8408438278958468699920669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11211251038611291599894225 8408438278958468699920669)
              ·
                refine ⟨3153164354609425762470251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8408438278958468699920669 3153164354609425762470251)
                ·
                  refine ⟨4729746531914138643705377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3153164354609425762470251 4729746531914138643705377)
                  ·
                    refine ⟨3547309898935603982779033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4729746531914138643705377 3547309898935603982779033)
                    ·
                      refine ⟨2660482424201702987084275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3547309898935603982779033 2660482424201702987084275)
                      ·
                        rfl

theorem cell23_5181271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 2, 3, 1, 2, 2].length) (baseStart_5181271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5181271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5181271 prefixEnd_5181271 := by exact prefixLift 5181271
  have htrace : WordTrace (prefixWord ++ tailWord_5181271) baseStart_5181271 baseEnd_5181271 := by
    simpa [prefixWord, tailWord_5181271, baseEnd_5181271] using wordTrace_append hprefix tailTrace_5181271
  have hstable : (prefixWord ++ tailWord_5181271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5181271).length < 2 ^ (prefixWord ++ tailWord_5181271).sum := by decide
  have hdescent : baseEnd_5181271 < baseStart_5181271 := by decide
  rcases family_descends (prefixWord ++ tailWord_5181271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5181293 : List Nat := [1, 5, 1, 1, 1, 1, 2, 1, 1, 5, 4]
def baseStart_5181293 : Nat := 118140960795 + 5181293 * 2 ^ 59
def prefixEnd_5181293 : Nat := 4983230072969 + 3 ^ 40 * 5181293 * 2
def baseEnd_5181293 : Nat := 2660493720776101901009173

theorem tailTrace_5181293 : CollatzResearch.WordTrace tailWord_5181293 prefixEnd_5181293 2660493720776101901009173 := by
  unfold tailWord_5181293
  simp only [CollatzResearch.WordTrace]
  refine ⟨188977280818067830239468533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125984853878711886826312355 188977280818067830239468533)
  ·
    refine ⟨17716620076693859084950175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 188977280818067830239468533 17716620076693859084950175)
    ·
      refine ⟨26574930115040788627425263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17716620076693859084950175 26574930115040788627425263)
      ·
        refine ⟨39862395172561182941137895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26574930115040788627425263 39862395172561182941137895)
        ·
          refine ⟨59793592758841774411706843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39862395172561182941137895 59793592758841774411706843)
          ·
            refine ⟨89690389138262661617560265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59793592758841774411706843 89690389138262661617560265)
            ·
              refine ⟨67267791853696996213170199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89690389138262661617560265 67267791853696996213170199)
              ·
                refine ⟨100901687780545494319755299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67267791853696996213170199 100901687780545494319755299)
                ·
                  refine ⟨151352531670818241479632949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 100901687780545494319755299 151352531670818241479632949)
                  ·
                    refine ⟨14189299844139210138715589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 151352531670818241479632949 14189299844139210138715589)
                    ·
                      refine ⟨2660493720776101901009173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14189299844139210138715589 2660493720776101901009173)
                      ·
                        rfl

theorem cell23_5181293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 5, 4].length) (baseStart_5181293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5181293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5181293 prefixEnd_5181293 := by exact prefixLift 5181293
  have htrace : WordTrace (prefixWord ++ tailWord_5181293) baseStart_5181293 baseEnd_5181293 := by
    simpa [prefixWord, tailWord_5181293, baseEnd_5181293] using wordTrace_append hprefix tailTrace_5181293
  have hstable : (prefixWord ++ tailWord_5181293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5181293).length < 2 ^ (prefixWord ++ tailWord_5181293).sum := by decide
  have hdescent : baseEnd_5181293 < baseStart_5181293 := by decide
  rcases family_descends (prefixWord ++ tailWord_5181293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5181330 : List Nat := [3, 2, 3, 2, 1, 1, 1, 1, 1, 3, 5]
def baseStart_5181330 : Nat := 118140960795 + 5181330 * 2 ^ 59
def prefixEnd_5181330 : Nat := 4983230072969 + 3 ^ 40 * 5181330 * 2
def baseEnd_5181330 : Nat := 2660512719560318256246503

theorem tailTrace_5181330 : CollatzResearch.WordTrace tailWord_5181330 prefixEnd_5181330 2660512719560318256246503 := by
  unfold tailWord_5181330
  simp only [CollatzResearch.WordTrace]
  refine ⟨47244657579733446389641361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125985753545955857039043629 47244657579733446389641361)
  ·
    refine ⟨35433493184800084792231021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47244657579733446389641361 35433493184800084792231021)
    ·
      refine ⟨13287559944300031797086633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35433493184800084792231021 13287559944300031797086633)
      ·
        refine ⟨9965669958225023847814975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13287559944300031797086633 9965669958225023847814975)
        ·
          refine ⟨14948504937337535771722463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9965669958225023847814975 14948504937337535771722463)
          ·
            refine ⟨22422757406006303657583695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14948504937337535771722463 22422757406006303657583695)
            ·
              refine ⟨33634136109009455486375543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22422757406006303657583695 33634136109009455486375543)
              ·
                refine ⟨50451204163514183229563315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33634136109009455486375543 50451204163514183229563315)
                ·
                  refine ⟨75676806245271274844344973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50451204163514183229563315 75676806245271274844344973)
                  ·
                    refine ⟨28378802341976728066629365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 75676806245271274844344973 28378802341976728066629365)
                    ·
                      refine ⟨2660512719560318256246503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28378802341976728066629365 2660512719560318256246503)
                      ·
                        rfl

theorem cell23_5181330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_5181330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5181330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5181330 prefixEnd_5181330 := by exact prefixLift 5181330
  have htrace : WordTrace (prefixWord ++ tailWord_5181330) baseStart_5181330 baseEnd_5181330 := by
    simpa [prefixWord, tailWord_5181330, baseEnd_5181330] using wordTrace_append hprefix tailTrace_5181330
  have hstable : (prefixWord ++ tailWord_5181330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5181330).length < 2 ^ (prefixWord ++ tailWord_5181330).sum := by decide
  have hdescent : baseEnd_5181330 < baseStart_5181330 := by decide
  rcases family_descends (prefixWord ++ tailWord_5181330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5181361 : List Nat := [1, 2, 2, 4, 2, 1, 4, 1, 2, 2, 2]
def baseStart_5181361 : Nat := 118140960795 + 5181361 * 2 ^ 59
def prefixEnd_5181361 : Nat := 4983230072969 + 3 ^ 40 * 5181361 * 2
def baseEnd_5181361 : Nat := 2660528637460607634958861

theorem tailTrace_5181361 : CollatzResearch.WordTrace tailWord_5181361 prefixEnd_5181361 2660528637460607634958861 := by
  unfold tailWord_5181361
  simp only [CollatzResearch.WordTrace]
  refine ⟨188979760981821477852943937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125986507321214318568629291 188979760981821477852943937)
  ·
    refine ⟨141734820736366108389707953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188979760981821477852943937 141734820736366108389707953)
    ·
      refine ⟨106301115552274581292280965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141734820736366108389707953 106301115552274581292280965)
      ·
        refine ⟨19931459166051483992302681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 106301115552274581292280965 19931459166051483992302681)
        ·
          refine ⟨14948594374538612994227011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19931459166051483992302681 14948594374538612994227011)
          ·
            refine ⟨22422891561807919491340517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14948594374538612994227011 22422891561807919491340517)
            ·
              refine ⟨4204292167838984904626347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22422891561807919491340517 4204292167838984904626347)
              ·
                refine ⟨6306438251758477356939521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4204292167838984904626347 6306438251758477356939521)
                ·
                  refine ⟨4729828688818858017704641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6306438251758477356939521 4729828688818858017704641)
                  ·
                    refine ⟨3547371516614143513278481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4729828688818858017704641 3547371516614143513278481)
                    ·
                      refine ⟨2660528637460607634958861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3547371516614143513278481 2660528637460607634958861)
                      ·
                        rfl

theorem cell23_5181361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 4, 1, 2, 2, 2].length) (baseStart_5181361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5181361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5181361 prefixEnd_5181361 := by exact prefixLift 5181361
  have htrace : WordTrace (prefixWord ++ tailWord_5181361) baseStart_5181361 baseEnd_5181361 := by
    simpa [prefixWord, tailWord_5181361, baseEnd_5181361] using wordTrace_append hprefix tailTrace_5181361
  have hstable : (prefixWord ++ tailWord_5181361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5181361).length < 2 ^ (prefixWord ++ tailWord_5181361).sum := by decide
  have hdescent : baseEnd_5181361 < baseStart_5181361 := by decide
  rcases family_descends (prefixWord ++ tailWord_5181361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5181363 : List Nat := [1, 1, 1, 2, 3, 1, 3, 2, 4, 5]
def baseStart_5181363 : Nat := 118140960795 + 5181363 * 2 ^ 59
def prefixEnd_5181363 : Nat := 4983230072969 + 3 ^ 40 * 5181363 * 2
def baseEnd_5181363 : Nat := 886843221473972209044617

theorem tailTrace_5181363 : CollatzResearch.WordTrace tailWord_5181363 prefixEnd_5181363 886843221473972209044617 := by
  unfold tailWord_5181363
  simp only [CollatzResearch.WordTrace]
  refine ⟨188979833927814232194516743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125986555951876154796344495 188979833927814232194516743)
  ·
    refine ⟨283469750891721348291775115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188979833927814232194516743 283469750891721348291775115)
    ·
      refine ⟨425204626337582022437662673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 283469750891721348291775115 425204626337582022437662673)
      ·
        refine ⟨318903469753186516828247005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 425204626337582022437662673 318903469753186516828247005)
        ·
          refine ⟨119588801157444943810592627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 318903469753186516828247005 119588801157444943810592627)
          ·
            refine ⟨179383201736167415715888941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119588801157444943810592627 179383201736167415715888941)
            ·
              refine ⟨67268700651062780893458353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 179383201736167415715888941 67268700651062780893458353)
              ·
                refine ⟨50451525488297085670093765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67268700651062780893458353 50451525488297085670093765)
                ·
                  refine ⟨9459661029055703563142581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50451525488297085670093765 9459661029055703563142581)
                  ·
                    refine ⟨886843221473972209044617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9459661029055703563142581 886843221473972209044617)
                    ·
                      rfl

theorem cell23_5181363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 2, 4, 5].length) (baseStart_5181363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5181363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5181363 prefixEnd_5181363 := by exact prefixLift 5181363
  have htrace : WordTrace (prefixWord ++ tailWord_5181363) baseStart_5181363 baseEnd_5181363 := by
    simpa [prefixWord, tailWord_5181363, baseEnd_5181363] using wordTrace_append hprefix tailTrace_5181363
  have hstable : (prefixWord ++ tailWord_5181363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5181363).length < 2 ^ (prefixWord ++ tailWord_5181363).sum := by decide
  have hdescent : baseEnd_5181363 < baseStart_5181363 := by decide
  rcases family_descends (prefixWord ++ tailWord_5181363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5181370 : List Nat := [3, 1, 1, 1, 2, 1, 2, 1, 4, 5, 2]
def baseStart_5181370 : Nat := 118140960795 + 5181370 * 2 ^ 59
def prefixEnd_5181370 : Nat := 4983230072969 + 3 ^ 40 * 5181370 * 2
def baseEnd_5181370 : Nat := 2660533258786498099746319

theorem tailTrace_5181370 : CollatzResearch.WordTrace tailWord_5181370 prefixEnd_5181370 2660533258786498099746319 := by
  unfold tailWord_5181370
  simp only [CollatzResearch.WordTrace]
  refine ⟨47245022309697218097505391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125986726159192581593347709 47245022309697218097505391)
  ·
    refine ⟨70867533464545827146258087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47245022309697218097505391 70867533464545827146258087)
    ·
      refine ⟨106301300196818740719387131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70867533464545827146258087 106301300196818740719387131)
      ·
        refine ⟨159451950295228111079080697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106301300196818740719387131 159451950295228111079080697)
        ·
          refine ⟨119588962721421083309310523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 159451950295228111079080697 119588962721421083309310523)
          ·
            refine ⟨179383444082131624963965785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119588962721421083309310523 179383444082131624963965785)
            ·
              refine ⟨134537583061598718722974339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 179383444082131624963965785 134537583061598718722974339)
              ·
                refine ⟨201806374592398078084461509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 134537583061598718722974339 201806374592398078084461509)
                ·
                  refine ⟨37838695236074639640836533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 201806374592398078084461509 37838695236074639640836533)
                  ·
                    refine ⟨3547377678381997466328425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37838695236074639640836533 3547377678381997466328425)
                    ·
                      refine ⟨2660533258786498099746319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3547377678381997466328425 2660533258786498099746319)
                      ·
                        rfl

theorem cell23_5181370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 4, 5, 2].length) (baseStart_5181370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5181370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5181370 prefixEnd_5181370 := by exact prefixLift 5181370
  have htrace : WordTrace (prefixWord ++ tailWord_5181370) baseStart_5181370 baseEnd_5181370 := by
    simpa [prefixWord, tailWord_5181370, baseEnd_5181370] using wordTrace_append hprefix tailTrace_5181370
  have hstable : (prefixWord ++ tailWord_5181370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5181370).length < 2 ^ (prefixWord ++ tailWord_5181370).sum := by decide
  have hdescent : baseEnd_5181370 < baseStart_5181370 := by decide
  rcases family_descends (prefixWord ++ tailWord_5181370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5181400 : List Nat := [2, 1, 2, 2, 2, 2, 1, 4, 2, 1, 4]
def baseStart_5181400 : Nat := 118140960795 + 5181400 * 2 ^ 59
def prefixEnd_5181400 : Nat := 4983230072969 + 3 ^ 40 * 5181400 * 2
def baseEnd_5181400 : Nat := 2660548663206132982371181

theorem tailTrace_5181400 : CollatzResearch.WordTrace tailWord_5181400 prefixEnd_5181400 2660548663206132982371181 := by
  unfold tailWord_5181400
  simp only [CollatzResearch.WordTrace]
  refine ⟨94490591714340093756806827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125987455619120125009075769 94490591714340093756806827)
  ·
    refine ⟨141735887571510140635210241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94490591714340093756806827 141735887571510140635210241)
    ·
      refine ⟨106301915678632605476407681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141735887571510140635210241 106301915678632605476407681)
      ·
        refine ⟨79726436758974454107305761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106301915678632605476407681 79726436758974454107305761)
        ·
          refine ⟨59794827569230840580479321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79726436758974454107305761 59794827569230840580479321)
          ·
            refine ⟨44846120676923130435359491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59794827569230840580479321 44846120676923130435359491)
            ·
              refine ⟨67269181015384695653039237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44846120676923130435359491 67269181015384695653039237)
              ·
                refine ⟨12612971440384630434944857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 67269181015384695653039237 12612971440384630434944857)
                ·
                  refine ⟨9459728580288472826208643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12612971440384630434944857 9459728580288472826208643)
                  ·
                    refine ⟨14189592870432709239312965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9459728580288472826208643 14189592870432709239312965)
                    ·
                      refine ⟨2660548663206132982371181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14189592870432709239312965 2660548663206132982371181)
                      ·
                        rfl

theorem cell23_5181400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 4, 2, 1, 4].length) (baseStart_5181400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5181400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5181400 prefixEnd_5181400 := by exact prefixLift 5181400
  have htrace : WordTrace (prefixWord ++ tailWord_5181400) baseStart_5181400 baseEnd_5181400 := by
    simpa [prefixWord, tailWord_5181400, baseEnd_5181400] using wordTrace_append hprefix tailTrace_5181400
  have hstable : (prefixWord ++ tailWord_5181400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5181400).length < 2 ^ (prefixWord ++ tailWord_5181400).sum := by decide
  have hdescent : baseEnd_5181400 < baseStart_5181400 := by decide
  rcases family_descends (prefixWord ++ tailWord_5181400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5181401 : List Nat := [1, 2, 1, 2, 7, 1, 2, 2, 5]
def baseStart_5181401 : Nat := 118140960795 + 5181401 * 2 ^ 59
def prefixEnd_5181401 : Nat := 4983230072969 + 3 ^ 40 * 5181401 * 2
def baseEnd_5181401 : Nat := 295616575187420830939853

theorem tailTrace_5181401 : CollatzResearch.WordTrace tailWord_5181401 prefixEnd_5181401 295616575187420830939853 := by
  unfold tailWord_5181401
  simp only [CollatzResearch.WordTrace]
  refine ⟨188981219901676564684400057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125987479934451043122933371 188981219901676564684400057)
  ·
    refine ⟨141735914926257423513300043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188981219901676564684400057 141735914926257423513300043)
    ·
      refine ⟨212603872389386135269950065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141735914926257423513300043 212603872389386135269950065)
      ·
        refine ⟨159452904292039601452462549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 212603872389386135269950065 159452904292039601452462549)
        ·
          refine ⟨3737177444344678159042091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 159452904292039601452462549 3737177444344678159042091)
          ·
            refine ⟨5605766166517017238563137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3737177444344678159042091 5605766166517017238563137)
            ·
              refine ⟨4204324624887762928922353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5605766166517017238563137 4204324624887762928922353)
              ·
                refine ⟨3153243468665822196691765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4204324624887762928922353 3153243468665822196691765)
                ·
                  refine ⟨295616575187420830939853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3153243468665822196691765 295616575187420830939853)
                  ·
                    rfl

theorem cell23_5181401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 2, 2, 5].length) (baseStart_5181401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5181401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5181401 prefixEnd_5181401 := by exact prefixLift 5181401
  have htrace : WordTrace (prefixWord ++ tailWord_5181401) baseStart_5181401 baseEnd_5181401 := by
    simpa [prefixWord, tailWord_5181401, baseEnd_5181401] using wordTrace_append hprefix tailTrace_5181401
  have hstable : (prefixWord ++ tailWord_5181401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5181401).length < 2 ^ (prefixWord ++ tailWord_5181401).sum := by decide
  have hdescent : baseEnd_5181401 < baseStart_5181401 := by decide
  rcases family_descends (prefixWord ++ tailWord_5181401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5181420 : List Nat := [2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 3]
def baseStart_5181420 : Nat := 118140960795 + 5181420 * 2 ^ 59
def prefixEnd_5181420 : Nat := 4983230072969 + 3 ^ 40 * 5181420 * 2
def baseEnd_5181420 : Nat := 2660558932819222904121089

theorem tailTrace_5181420 : CollatzResearch.WordTrace tailWord_5181420 prefixEnd_5181420 2660558932819222904121089 := by
  unfold tailWord_5181420
  simp only [CollatzResearch.WordTrace]
  refine ⟨94490956444303865464670857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125987941925738487286227809 94490956444303865464670857)
  ·
    refine ⟨70868217333227899098503143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94490956444303865464670857 70868217333227899098503143)
    ·
      refine ⟨106302325999841848647754715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70868217333227899098503143 106302325999841848647754715)
      ·
        refine ⟨159453488999762772971632073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106302325999841848647754715 159453488999762772971632073)
        ·
          refine ⟨119590116749822079728724055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 159453488999762772971632073 119590116749822079728724055)
          ·
            refine ⟨179385175124733119593086083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119590116749822079728724055 179385175124733119593086083)
            ·
              refine ⟨269077762687099679389629125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 179385175124733119593086083 269077762687099679389629125)
              ·
                refine ⟨50452080503831189885555461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 269077762687099679389629125 50452080503831189885555461)
                ·
                  refine ⟨9459765094468348103541649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50452080503831189885555461 9459765094468348103541649)
                  ·
                    refine ⟨7094823820851261077656237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9459765094468348103541649 7094823820851261077656237)
                    ·
                      refine ⟨2660558932819222904121089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7094823820851261077656237 2660558932819222904121089)
                      ·
                        rfl

theorem cell23_5181420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 3].length) (baseStart_5181420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5181420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5181420 prefixEnd_5181420 := by exact prefixLift 5181420
  have htrace : WordTrace (prefixWord ++ tailWord_5181420) baseStart_5181420 baseEnd_5181420 := by
    simpa [prefixWord, tailWord_5181420, baseEnd_5181420] using wordTrace_append hprefix tailTrace_5181420
  have hstable : (prefixWord ++ tailWord_5181420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5181420).length < 2 ^ (prefixWord ++ tailWord_5181420).sum := by decide
  have hdescent : baseEnd_5181420 < baseStart_5181420 := by decide
  rcases family_descends (prefixWord ++ tailWord_5181420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5181437 : List Nat := [1, 4, 1, 1, 1, 2, 5, 1, 2, 2, 3]
def baseStart_5181437 : Nat := 118140960795 + 5181437 * 2 ^ 59
def prefixEnd_5181437 : Nat := 4983230072969 + 3 ^ 40 * 5181437 * 2
def baseEnd_5181437 : Nat := 2660567661990349337608511

theorem tailTrace_5181437 : CollatzResearch.WordTrace tailWord_5181437 prefixEnd_5181437 2660567661990349337608511 := by
  unfold tailWord_5181437
  simp only [CollatzResearch.WordTrace]
  refine ⟨188982532929546142832710565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125988355286364095221807043 188982532929546142832710565)
  ·
    refine ⟨35434224924289901781133231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 188982532929546142832710565 35434224924289901781133231)
    ·
      refine ⟨53151337386434852671699847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35434224924289901781133231 53151337386434852671699847)
      ·
        refine ⟨79727006079652279007549771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53151337386434852671699847 79727006079652279007549771)
        ·
          refine ⟨119590509119478418511324657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79727006079652279007549771 119590509119478418511324657)
          ·
            refine ⟨89692881839608813883493493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119590509119478418511324657 89692881839608813883493493)
            ·
              refine ⟨8408707672463326301577515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 89692881839608813883493493 8408707672463326301577515)
              ·
                refine ⟨12613061508694989452366273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8408707672463326301577515 12613061508694989452366273)
                ·
                  refine ⟨9459796131521242089274705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12613061508694989452366273 9459796131521242089274705)
                  ·
                    refine ⟨7094847098640931566956029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9459796131521242089274705 7094847098640931566956029)
                    ·
                      refine ⟨2660567661990349337608511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7094847098640931566956029 2660567661990349337608511)
                      ·
                        rfl

theorem cell23_5181437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 5, 1, 2, 2, 3].length) (baseStart_5181437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5181437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5181437 prefixEnd_5181437 := by exact prefixLift 5181437
  have htrace : WordTrace (prefixWord ++ tailWord_5181437) baseStart_5181437 baseEnd_5181437 := by
    simpa [prefixWord, tailWord_5181437, baseEnd_5181437] using wordTrace_append hprefix tailTrace_5181437
  have hstable : (prefixWord ++ tailWord_5181437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5181437).length < 2 ^ (prefixWord ++ tailWord_5181437).sum := by decide
  have hdescent : baseEnd_5181437 < baseStart_5181437 := by decide
  rcases family_descends (prefixWord ++ tailWord_5181437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5181443 : List Nat := [1, 1, 1, 3, 2, 1, 1, 2, 3, 2, 6]
def baseStart_5181443 : Nat := 118140960795 + 5181443 * 2 ^ 59
def prefixEnd_5181443 : Nat := 4983230072969 + 3 ^ 40 * 5181443 * 2
def baseEnd_5181443 : Nat := 2660570742874276314133483

theorem tailTrace_5181443 : CollatzResearch.WordTrace tailWord_5181443 prefixEnd_5181443 2660570742874276314133483 := by
  unfold tailWord_5181443
  simp only [CollatzResearch.WordTrace]
  refine ⟨188982751767524405857428983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125988501178349603904952655 188982751767524405857428983)
  ·
    refine ⟨283474127651286608786143475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188982751767524405857428983 283474127651286608786143475)
    ·
      refine ⟨425211191476929913179215213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 283474127651286608786143475 425211191476929913179215213)
      ·
        refine ⟨159454196803848717442205705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 425211191476929913179215213 159454196803848717442205705)
        ·
          refine ⟨119590647602886538081654279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 159454196803848717442205705 119590647602886538081654279)
          ·
            refine ⟨179385971404329807122481419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119590647602886538081654279 179385971404329807122481419)
            ·
              refine ⟨269078957106494710683722129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 179385971404329807122481419 269078957106494710683722129)
              ·
                refine ⟨201809217829871033012791597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 269078957106494710683722129 201809217829871033012791597)
                ·
                  refine ⟨75678456686201637379796849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 201809217829871033012791597 75678456686201637379796849)
                  ·
                    refine ⟨56758842514651228034847637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 75678456686201637379796849 56758842514651228034847637)
                    ·
                      refine ⟨2660570742874276314133483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56758842514651228034847637 2660570742874276314133483)
                      ·
                        rfl

theorem cell23_5181443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 3, 2, 6].length) (baseStart_5181443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5181443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5181443 prefixEnd_5181443 := by exact prefixLift 5181443
  have htrace : WordTrace (prefixWord ++ tailWord_5181443) baseStart_5181443 baseEnd_5181443 := by
    simpa [prefixWord, tailWord_5181443, baseEnd_5181443] using wordTrace_append hprefix tailTrace_5181443
  have hstable : (prefixWord ++ tailWord_5181443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5181443).length < 2 ^ (prefixWord ++ tailWord_5181443).sum := by decide
  have hdescent : baseEnd_5181443 < baseStart_5181443 := by decide
  rcases family_descends (prefixWord ++ tailWord_5181443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5181477 : List Nat := [1, 3, 1, 2, 2, 3, 1, 2, 1, 5, 2]
def baseStart_5181477 : Nat := 118140960795 + 5181477 * 2 ^ 59
def prefixEnd_5181477 : Nat := 4983230072969 + 3 ^ 40 * 5181477 * 2
def baseEnd_5181477 : Nat := 2660588201216529181108327

theorem tailTrace_5181477 : CollatzResearch.WordTrace tailWord_5181477 prefixEnd_5181477 2660588201216529181108327 := by
  unfold tailWord_5181477
  simp only [CollatzResearch.WordTrace]
  refine ⟨188983991849401229664166685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125989327899600819776111123 188983991849401229664166685)
  ·
    refine ⟨70868996943525461124062507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 188983991849401229664166685 70868996943525461124062507)
    ·
      refine ⟨106303495415288191686093761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70868996943525461124062507 106303495415288191686093761)
      ·
        refine ⟨79727621561466143764570321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106303495415288191686093761 79727621561466143764570321)
        ·
          refine ⟨59795716171099607823427741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79727621561466143764570321 59795716171099607823427741)
          ·
            refine ⟨22423393564162352933785403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59795716171099607823427741 22423393564162352933785403)
            ·
              refine ⟨33635090346243529400678105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22423393564162352933785403 33635090346243529400678105)
              ·
                refine ⟨25226317759682647050508579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33635090346243529400678105 25226317759682647050508579)
                ·
                  refine ⟨37839476639523970575762869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25226317759682647050508579 37839476639523970575762869)
                  ·
                    refine ⟨3547450934955372241477769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37839476639523970575762869 3547450934955372241477769)
                    ·
                      refine ⟨2660588201216529181108327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3547450934955372241477769 2660588201216529181108327)
                      ·
                        rfl

theorem cell23_5181477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 2, 1, 5, 2].length) (baseStart_5181477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5181477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5181477 prefixEnd_5181477 := by exact prefixLift 5181477
  have htrace : WordTrace (prefixWord ++ tailWord_5181477) baseStart_5181477 baseEnd_5181477 := by
    simpa [prefixWord, tailWord_5181477, baseEnd_5181477] using wordTrace_append hprefix tailTrace_5181477
  have hstable : (prefixWord ++ tailWord_5181477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5181477).length < 2 ^ (prefixWord ++ tailWord_5181477).sum := by decide
  have hdescent : baseEnd_5181477 < baseStart_5181477 := by decide
  rcases family_descends (prefixWord ++ tailWord_5181477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5181494 : List Nat := [5, 1, 2, 1, 1, 1, 1, 3, 1, 5, 2]
def baseStart_5181494 : Nat := 118140960795 + 5181494 * 2 ^ 59
def prefixEnd_5181494 : Nat := 4983230072969 + 3 ^ 40 * 5181494 * 2
def baseEnd_5181494 : Nat := 2660596930387655614595749

theorem tailTrace_5181494 : CollatzResearch.WordTrace tailWord_5181494 prefixEnd_5181494 2660596930387655614595749 := by
  unfold tailWord_5181494
  simp only [CollatzResearch.WordTrace]
  refine ⟨11811538243146227597970971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 125989741260226427711690357 11811538243146227597970971)
  ·
    refine ⟨17717307364719341396956457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11811538243146227597970971 17717307364719341396956457)
    ·
      refine ⟨13287980523539506047717343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17717307364719341396956457 13287980523539506047717343)
      ·
        refine ⟨19931970785309259071576015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13287980523539506047717343 19931970785309259071576015)
        ·
          refine ⟨29897956177963888607364023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19931970785309259071576015 29897956177963888607364023)
          ·
            refine ⟨44846934266945832911046035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29897956177963888607364023 44846934266945832911046035)
            ·
              refine ⟨67270401400418749366569053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44846934266945832911046035 67270401400418749366569053)
              ·
                refine ⟨25226400525157031012463395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67270401400418749366569053 25226400525157031012463395)
                ·
                  refine ⟨37839600787735546518695093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25226400525157031012463395 37839600787735546518695093)
                  ·
                    refine ⟨3547462573850207486127665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37839600787735546518695093 3547462573850207486127665)
                    ·
                      refine ⟨2660596930387655614595749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3547462573850207486127665 2660596930387655614595749)
                      ·
                        rfl

theorem cell23_5181494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 3, 1, 5, 2].length) (baseStart_5181494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5181494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5181494 prefixEnd_5181494 := by exact prefixLift 5181494
  have htrace : WordTrace (prefixWord ++ tailWord_5181494) baseStart_5181494 baseEnd_5181494 := by
    simpa [prefixWord, tailWord_5181494, baseEnd_5181494] using wordTrace_append hprefix tailTrace_5181494
  have hstable : (prefixWord ++ tailWord_5181494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5181494).length < 2 ^ (prefixWord ++ tailWord_5181494).sum := by decide
  have hdescent : baseEnd_5181494 < baseStart_5181494 := by decide
  rcases family_descends (prefixWord ++ tailWord_5181494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5181500 : List Nat := [2, 2, 2, 2, 2, 1, 2, 1, 3, 6]
def baseStart_5181500 : Nat := 118140960795 + 5181500 * 2 ^ 59
def prefixEnd_5181500 : Nat := 4983230072969 + 3 ^ 40 * 5181500 * 2
def baseEnd_5181500 : Nat := 886866670423860863706907

theorem tailTrace_5181500 : CollatzResearch.WordTrace tailWord_5181500 prefixEnd_5181500 886866670423860863706907 := by
  unfold tailWord_5181500
  simp only [CollatzResearch.WordTrace]
  refine ⟨94492415364158952296126977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125989887152211936394835969 94492415364158952296126977)
  ·
    refine ⟨70869311523119214222095233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94492415364158952296126977 70869311523119214222095233)
    ·
      refine ⟨53151983642339410666571425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70869311523119214222095233 53151983642339410666571425)
      ·
        refine ⟨39863987731754557999928569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53151983642339410666571425 39863987731754557999928569)
        ·
          refine ⟨29897990798815918499946427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39863987731754557999928569 29897990798815918499946427)
          ·
            refine ⟨44846986198223877749919641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29897990798815918499946427 44846986198223877749919641)
            ·
              refine ⟨33635239648667908312439731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44846986198223877749919641 33635239648667908312439731)
              ·
                refine ⟨50452859473001862468659597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33635239648667908312439731 50452859473001862468659597)
                ·
                  refine ⟨18919822302375698425747349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50452859473001862468659597 18919822302375698425747349)
                  ·
                    refine ⟨886866670423860863706907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18919822302375698425747349 886866670423860863706907)
                    ·
                      rfl

theorem cell23_5181500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 1, 3, 6].length) (baseStart_5181500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5181500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5181500 prefixEnd_5181500 := by exact prefixLift 5181500
  have htrace : WordTrace (prefixWord ++ tailWord_5181500) baseStart_5181500 baseEnd_5181500 := by
    simpa [prefixWord, tailWord_5181500, baseEnd_5181500] using wordTrace_append hprefix tailTrace_5181500
  have hstable : (prefixWord ++ tailWord_5181500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5181500).length < 2 ^ (prefixWord ++ tailWord_5181500).sum := by decide
  have hdescent : baseEnd_5181500 < baseStart_5181500 := by decide
  rcases family_descends (prefixWord ++ tailWord_5181500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5181518 : List Nat := [4, 1, 1, 1, 1, 5, 3, 2, 1, 1, 3]
def baseStart_5181518 : Nat := 118140960795 + 5181518 * 2 ^ 59
def prefixEnd_5181518 : Nat := 4983230072969 + 3 ^ 40 * 5181518 * 2
def baseEnd_5181518 : Nat := 2660609253923363520695639

theorem tailTrace_5181518 : CollatzResearch.WordTrace tailWord_5181518 prefixEnd_5181518 2660609253923363520695639 := by
  unfold tailWord_5181518
  simp only [CollatzResearch.WordTrace]
  refine ⟨23623185905281586708301151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125990324828168462444272805 23623185905281586708301151)
  ·
    refine ⟨35434778857922380062451727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23623185905281586708301151 35434778857922380062451727)
    ·
      refine ⟨53152168286883570093677591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35434778857922380062451727 53152168286883570093677591)
      ·
        refine ⟨79728252430325355140516387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53152168286883570093677591 79728252430325355140516387)
        ·
          refine ⟨119592378645488032710774581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79728252430325355140516387 119592378645488032710774581)
          ·
            refine ⟨11211785498014503066635117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 119592378645488032710774581 11211785498014503066635117)
            ·
              refine ⟨4204419561755438649988169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11211785498014503066635117 4204419561755438649988169)
              ·
                refine ⟨3153314671316578987491127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4204419561755438649988169 3153314671316578987491127)
                ·
                  refine ⟨4729972006974868481236691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3153314671316578987491127 4729972006974868481236691)
                  ·
                    refine ⟨7094958010462302721855037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4729972006974868481236691 7094958010462302721855037)
                    ·
                      refine ⟨2660609253923363520695639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7094958010462302721855037 2660609253923363520695639)
                      ·
                        rfl

theorem cell23_5181518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 3, 2, 1, 1, 3].length) (baseStart_5181518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5181518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5181518 prefixEnd_5181518 := by exact prefixLift 5181518
  have htrace : WordTrace (prefixWord ++ tailWord_5181518) baseStart_5181518 baseEnd_5181518 := by
    simpa [prefixWord, tailWord_5181518, baseEnd_5181518] using wordTrace_append hprefix tailTrace_5181518
  have hstable : (prefixWord ++ tailWord_5181518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5181518).length < 2 ^ (prefixWord ++ tailWord_5181518).sum := by decide
  have hdescent : baseEnd_5181518 < baseStart_5181518 := by decide
  rcases family_descends (prefixWord ++ tailWord_5181518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5181530 : List Nat := [3, 1, 1, 2, 1, 1, 6, 8]
def baseStart_5181530 : Nat := 118140960795 + 5181530 * 2 ^ 59
def prefixEnd_5181530 : Nat := 4983230072969 + 3 ^ 40 * 5181530 * 2
def baseEnd_5181530 : Nat := 98541311692267313842429

theorem tailTrace_5181530 : CollatzResearch.WordTrace tailWord_5181530 prefixEnd_5181530 98541311692267313842429 := by
  unfold tailWord_5181530
  simp only [CollatzResearch.WordTrace]
  refine ⟨47246481229552304928961511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125990616612139479810564029 47246481229552304928961511)
  ·
    refine ⟨70869721844328457393442267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47246481229552304928961511 70869721844328457393442267)
    ·
      refine ⟨106304582766492686090163401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70869721844328457393442267 106304582766492686090163401)
      ·
        refine ⟨79728437074869514567622551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106304582766492686090163401 79728437074869514567622551)
        ·
          refine ⟨119592655612304271851433827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79728437074869514567622551 119592655612304271851433827)
          ·
            refine ⟨179388983418456407777150741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119592655612304271851433827 179388983418456407777150741)
            ·
              refine ⟨8408858597740144114553941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 179388983418456407777150741 8408858597740144114553941)
              ·
                refine ⟨98541311692267313842429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8408858597740144114553941 98541311692267313842429)
                ·
                  rfl

theorem cell23_5181530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 6, 8].length) (baseStart_5181530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5181530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5181530 prefixEnd_5181530 := by exact prefixLift 5181530
  have htrace : WordTrace (prefixWord ++ tailWord_5181530) baseStart_5181530 baseEnd_5181530 := by
    simpa [prefixWord, tailWord_5181530, baseEnd_5181530] using wordTrace_append hprefix tailTrace_5181530
  have hstable : (prefixWord ++ tailWord_5181530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5181530).length < 2 ^ (prefixWord ++ tailWord_5181530).sum := by decide
  have hdescent : baseEnd_5181530 < baseStart_5181530 := by decide
  rcases family_descends (prefixWord ++ tailWord_5181530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5181538 : List Nat := [3, 3, 2, 2, 3, 1, 1, 2, 1, 5]
def baseStart_5181538 : Nat := 118140960795 + 5181538 * 2 ^ 59
def prefixEnd_5181538 : Nat := 4983230072969 + 3 ^ 40 * 5181538 * 2
def baseEnd_5181538 : Nat := 886873174512151147481849

theorem tailTrace_5181538 : CollatzResearch.WordTrace tailWord_5181538 prefixEnd_5181538 886873174512151147481849 := by
  unfold tailWord_5181538
  simp only [CollatzResearch.WordTrace]
  refine ⟨47246554175545059270534317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125990811134786824721424845 47246554175545059270534317)
  ·
    refine ⟨17717457815829397226450369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47246554175545059270534317 17717457815829397226450369)
    ·
      refine ⟨13288093361872047919837777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17717457815829397226450369 13288093361872047919837777)
      ·
        refine ⟨9966070021404035939878333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13288093361872047919837777 9966070021404035939878333)
        ·
          refine ⟨3737276258026513477454375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9966070021404035939878333 3737276258026513477454375)
          ·
            refine ⟨5605914387039770216181563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3737276258026513477454375 5605914387039770216181563)
            ·
              refine ⟨8408871580559655324272345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5605914387039770216181563 8408871580559655324272345)
              ·
                refine ⟨6306653685419741493204259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8408871580559655324272345 6306653685419741493204259)
                ·
                  refine ⟨9459980528129612239806389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6306653685419741493204259 9459980528129612239806389)
                  ·
                    refine ⟨886873174512151147481849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9459980528129612239806389 886873174512151147481849)
                    ·
                      rfl

theorem cell23_5181538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 1, 2, 1, 5].length) (baseStart_5181538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5181538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5181538 prefixEnd_5181538 := by exact prefixLift 5181538
  have htrace : WordTrace (prefixWord ++ tailWord_5181538) baseStart_5181538 baseEnd_5181538 := by
    simpa [prefixWord, tailWord_5181538, baseEnd_5181538] using wordTrace_append hprefix tailTrace_5181538
  have hstable : (prefixWord ++ tailWord_5181538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5181538).length < 2 ^ (prefixWord ++ tailWord_5181538).sum := by decide
  have hdescent : baseEnd_5181538 < baseStart_5181538 := by decide
  rcases family_descends (prefixWord ++ tailWord_5181538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5181561 : List Nat := [1, 2, 1, 3, 4, 2, 3, 1, 1, 2, 3]
def baseStart_5181561 : Nat := 118140960795 + 5181561 * 2 ^ 59
def prefixEnd_5181561 : Nat := 4983230072969 + 3 ^ 40 * 5181561 * 2
def baseEnd_5181561 : Nat := 2660631333591506852457941

theorem tailTrace_5181561 : CollatzResearch.WordTrace tailWord_5181561 prefixEnd_5181561 2660631333591506852457941 := by
  unfold tailWord_5181561
  simp only [CollatzResearch.WordTrace]
  refine ⟨188987055581096912010224537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125991370387397941340149691 188987055581096912010224537)
  ·
    refine ⟨141740291685822684007668403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188987055581096912010224537 141740291685822684007668403)
    ·
      refine ⟨212610437528734026011502605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141740291685822684007668403 212610437528734026011502605)
      ·
        refine ⟨79728914073275259754313477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 212610437528734026011502605 79728914073275259754313477)
        ·
          refine ⟨14949171388739111203933777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 79728914073275259754313477 14949171388739111203933777)
          ·
            refine ⟨11211878541554333402950333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14949171388739111203933777 11211878541554333402950333)
            ·
              refine ⟨4204454453082875026106375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11211878541554333402950333 4204454453082875026106375)
              ·
                refine ⟨6306681679624312539159563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4204454453082875026106375 6306681679624312539159563)
                ·
                  refine ⟨9460022519436468808739345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6306681679624312539159563 9460022519436468808739345)
                  ·
                    refine ⟨7095016889577351606554509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9460022519436468808739345 7095016889577351606554509)
                    ·
                      refine ⟨2660631333591506852457941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7095016889577351606554509 2660631333591506852457941)
                      ·
                        rfl

theorem cell23_5181561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 3, 1, 1, 2, 3].length) (baseStart_5181561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5181561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5181561 prefixEnd_5181561 := by exact prefixLift 5181561
  have htrace : WordTrace (prefixWord ++ tailWord_5181561) baseStart_5181561 baseEnd_5181561 := by
    simpa [prefixWord, tailWord_5181561, baseEnd_5181561] using wordTrace_append hprefix tailTrace_5181561
  have hstable : (prefixWord ++ tailWord_5181561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5181561).length < 2 ^ (prefixWord ++ tailWord_5181561).sum := by decide
  have hdescent : baseEnd_5181561 < baseStart_5181561 := by decide
  rcases family_descends (prefixWord ++ tailWord_5181561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5181647 : List Nat := [1, 1, 2, 1, 1, 3, 3, 3, 2, 3, 3]
def baseStart_5181647 : Nat := 118140960795 + 5181647 * 2 ^ 59
def prefixEnd_5181647 : Nat := 4983230072969 + 3 ^ 40 * 5181647 * 2
def baseEnd_5181647 : Nat := 2660675492927793515982545

theorem tailTrace_5181647 : CollatzResearch.WordTrace tailWord_5181647 prefixEnd_5181647 2660675492927793515982545 := by
  unfold tailWord_5181647
  simp only [CollatzResearch.WordTrace]
  refine ⟨188990192258785348697855195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125993461505856899131903463 188990192258785348697855195)
  ·
    refine ⟨283485288388178023046782793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188990192258785348697855195 283485288388178023046782793)
    ·
      refine ⟨212613966291133517285087095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 283485288388178023046782793 212613966291133517285087095)
      ·
        refine ⟨318920949436700275927630643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212613966291133517285087095 318920949436700275927630643)
        ·
          refine ⟨478381424155050413891445965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 318920949436700275927630643 478381424155050413891445965)
          ·
            refine ⟨179393034058143905209292237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 478381424155050413891445965 179393034058143905209292237)
            ·
              refine ⟨67272387771803964453484589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 179393034058143905209292237 67272387771803964453484589)
              ·
                refine ⟨25227145414426486670056721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67272387771803964453484589 25227145414426486670056721)
                ·
                  refine ⟨18920359060819865002542541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25227145414426486670056721 18920359060819865002542541)
                  ·
                    refine ⟨7095134647807449375953453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18920359060819865002542541 7095134647807449375953453)
                    ·
                      refine ⟨2660675492927793515982545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7095134647807449375953453 2660675492927793515982545)
                      ·
                        rfl

theorem cell23_5181647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 3, 2, 3, 3].length) (baseStart_5181647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5181647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5181647 prefixEnd_5181647 := by exact prefixLift 5181647
  have htrace : WordTrace (prefixWord ++ tailWord_5181647) baseStart_5181647 baseEnd_5181647 := by
    simpa [prefixWord, tailWord_5181647, baseEnd_5181647] using wordTrace_append hprefix tailTrace_5181647
  have hstable : (prefixWord ++ tailWord_5181647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5181647).length < 2 ^ (prefixWord ++ tailWord_5181647).sum := by decide
  have hdescent : baseEnd_5181647 < baseStart_5181647 := by decide
  rcases family_descends (prefixWord ++ tailWord_5181647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5181671 : List Nat := [1, 1, 5, 3, 1, 1, 3, 3, 5]
def baseStart_5181671 : Nat := 118140960795 + 5181671 * 2 ^ 59
def prefixEnd_5181671 : Nat := 4983230072969 + 3 ^ 40 * 5181671 * 2
def baseEnd_5181671 : Nat := 295631979607055713564715

theorem tailTrace_5181671 : CollatzResearch.WordTrace tailWord_5181671 prefixEnd_5181671 295631979607055713564715 := by
  unfold tailWord_5181671
  simp only [CollatzResearch.WordTrace]
  refine ⟨188991067610698400796728867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125994045073798933864485911 188991067610698400796728867)
  ·
    refine ⟨283486601416047601195093301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188991067610698400796728867 283486601416047601195093301)
    ·
      refine ⟨26576868882754462612039997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 283486601416047601195093301 26576868882754462612039997)
      ·
        refine ⟨9966325831032923479514999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26576868882754462612039997 9966325831032923479514999)
        ·
          refine ⟨14949488746549385219272499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9966325831032923479514999 14949488746549385219272499)
          ·
            refine ⟨22424233119824077828908749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14949488746549385219272499 22424233119824077828908749)
            ·
              refine ⟨8409087419934029185840781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22424233119824077828908749 8409087419934029185840781)
              ·
                refine ⟨3153407782475260944690293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8409087419934029185840781 3153407782475260944690293)
                ·
                  refine ⟨295631979607055713564715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3153407782475260944690293 295631979607055713564715)
                  ·
                    rfl

theorem cell23_5181671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 3, 3, 5].length) (baseStart_5181671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5181671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5181671 prefixEnd_5181671 := by exact prefixLift 5181671
  have htrace : WordTrace (prefixWord ++ tailWord_5181671) baseStart_5181671 baseEnd_5181671 := by
    simpa [prefixWord, tailWord_5181671, baseEnd_5181671] using wordTrace_append hprefix tailTrace_5181671
  have hstable : (prefixWord ++ tailWord_5181671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5181671).length < 2 ^ (prefixWord ++ tailWord_5181671).sum := by decide
  have hdescent : baseEnd_5181671 < baseStart_5181671 := by decide
  rcases family_descends (prefixWord ++ tailWord_5181671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5181694 : List Nat := [4, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5]
def baseStart_5181694 : Nat := 118140960795 + 5181694 * 2 ^ 59
def prefixEnd_5181694 : Nat := 4983230072969 + 3 ^ 40 * 5181694 * 2
def baseEnd_5181694 : Nat := 2660699626518554832094829

theorem tailTrace_5181694 : CollatzResearch.WordTrace tailWord_5181694 prefixEnd_5181694 2660699626518554832094829 := by
  unfold tailWord_5181694
  simp only [CollatzResearch.WordTrace]
  refine ⟨23623988311201884465602017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125994604326410050483210757 23623988311201884465602017)
  ·
    refine ⟨17717991233401413349201513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23623988311201884465602017 17717991233401413349201513)
    ·
      refine ⟨13288493425051060011901135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17717991233401413349201513 13288493425051060011901135)
      ·
        refine ⟨19932740137576590017851703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13288493425051060011901135 19932740137576590017851703)
        ·
          refine ⟨29899110206364885026777555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19932740137576590017851703 29899110206364885026777555)
          ·
            refine ⟨44848665309547327540166333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29899110206364885026777555 44848665309547327540166333)
            ·
              refine ⟨16818249491080247827562375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44848665309547327540166333 16818249491080247827562375)
              ·
                refine ⟨25227374236620371741343563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16818249491080247827562375 25227374236620371741343563)
                ·
                  refine ⟨37841061354930557612015345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25227374236620371741343563 37841061354930557612015345)
                  ·
                    refine ⟨28380796016197918209011509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37841061354930557612015345 28380796016197918209011509)
                    ·
                      refine ⟨2660699626518554832094829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28380796016197918209011509 2660699626518554832094829)
                      ·
                        rfl

theorem cell23_5181694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_5181694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5181694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5181694 prefixEnd_5181694 := by exact prefixLift 5181694
  have htrace : WordTrace (prefixWord ++ tailWord_5181694) baseStart_5181694 baseEnd_5181694 := by
    simpa [prefixWord, tailWord_5181694, baseEnd_5181694] using wordTrace_append hprefix tailTrace_5181694
  have hstable : (prefixWord ++ tailWord_5181694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5181694).length < 2 ^ (prefixWord ++ tailWord_5181694).sum := by decide
  have hdescent : baseEnd_5181694 < baseStart_5181694 := by decide
  rcases family_descends (prefixWord ++ tailWord_5181694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5181717 : List Nat := [1, 3, 2, 1, 2, 1, 2, 1, 2, 4, 4]
def baseStart_5181717 : Nat := 118140960795 + 5181717 * 2 ^ 59
def prefixEnd_5181717 : Nat := 4983230072969 + 3 ^ 40 * 5181717 * 2
def baseEnd_5181717 : Nat := 2660711436573608242107223

theorem tailTrace_5181717 : CollatzResearch.WordTrace tailWord_5181717 prefixEnd_5181717 2660711436573608242107223 := by
  unfold tailWord_5181717
  simp only [CollatzResearch.WordTrace]
  refine ⟨188992745368531750652903405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125995163579021167101935603 188992745368531750652903405)
  ·
    refine ⟨70872279513199406494838777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 188992745368531750652903405 70872279513199406494838777)
    ·
      refine ⟨53154209634899554871129083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70872279513199406494838777 53154209634899554871129083)
      ·
        refine ⟨79731314452349332306693625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53154209634899554871129083 79731314452349332306693625)
        ·
          refine ⟨59798485839261999230020219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79731314452349332306693625 59798485839261999230020219)
          ·
            refine ⟨89697728758892998845030329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59798485839261999230020219 89697728758892998845030329)
            ·
              refine ⟨67273296569169749133772747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89697728758892998845030329 67273296569169749133772747)
              ·
                refine ⟨100909944853754623700659121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67273296569169749133772747 100909944853754623700659121)
                ·
                  refine ⟨75682458640315967775494341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 100909944853754623700659121 75682458640315967775494341)
                  ·
                    refine ⟨14190460995059243957905189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 75682458640315967775494341 14190460995059243957905189)
                    ·
                      refine ⟨2660711436573608242107223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14190460995059243957905189 2660711436573608242107223)
                      ·
                        rfl

theorem cell23_5181717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 2, 4, 4].length) (baseStart_5181717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5181717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5181717 prefixEnd_5181717 := by exact prefixLift 5181717
  have htrace : WordTrace (prefixWord ++ tailWord_5181717) baseStart_5181717 baseEnd_5181717 := by
    simpa [prefixWord, tailWord_5181717, baseEnd_5181717] using wordTrace_append hprefix tailTrace_5181717
  have hstable : (prefixWord ++ tailWord_5181717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5181717).length < 2 ^ (prefixWord ++ tailWord_5181717).sum := by decide
  have hdescent : baseEnd_5181717 < baseStart_5181717 := by decide
  rcases family_descends (prefixWord ++ tailWord_5181717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5181731 : List Nat := [1, 1, 1, 4, 2, 2, 2, 5, 1, 4]
def baseStart_5181731 : Nat := 118140960795 + 5181731 * 2 ^ 59
def prefixEnd_5181731 : Nat := 4983230072969 + 3 ^ 40 * 5181731 * 2
def baseEnd_5181731 : Nat := 886906208434257062444053

theorem tailTrace_5181731 : CollatzResearch.WordTrace tailWord_5181731 prefixEnd_5181731 886906208434257062444053 := by
  unfold tailWord_5181731
  simp only [CollatzResearch.WordTrace]
  refine ⟨188993255990481031043913047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125995503993654020695942031 188993255990481031043913047)
  ·
    refine ⟨283489883985721546565869571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188993255990481031043913047 283489883985721546565869571)
    ·
      refine ⟨425234825978582319848804357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 283489883985721546565869571 425234825978582319848804357)
      ·
        refine ⟨79731529870984184971650817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 425234825978582319848804357 79731529870984184971650817)
        ·
          refine ⟨59798647403238138728738113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79731529870984184971650817 59798647403238138728738113)
          ·
            refine ⟨44848985552428604046553585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59798647403238138728738113 44848985552428604046553585)
            ·
              refine ⟨33636739164321453034915189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44848985552428604046553585 33636739164321453034915189)
              ·
                refine ⟨3153444296655136222023299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33636739164321453034915189 3153444296655136222023299)
                ·
                  refine ⟨4730166444982704333034949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3153444296655136222023299 4730166444982704333034949)
                  ·
                    refine ⟨886906208434257062444053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4730166444982704333034949 886906208434257062444053)
                    ·
                      rfl

theorem cell23_5181731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 5, 1, 4].length) (baseStart_5181731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5181731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5181731 prefixEnd_5181731 := by exact prefixLift 5181731
  have htrace : WordTrace (prefixWord ++ tailWord_5181731) baseStart_5181731 baseEnd_5181731 := by
    simpa [prefixWord, tailWord_5181731, baseEnd_5181731] using wordTrace_append hprefix tailTrace_5181731
  have hstable : (prefixWord ++ tailWord_5181731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5181731).length < 2 ^ (prefixWord ++ tailWord_5181731).sum := by decide
  have hdescent : baseEnd_5181731 < baseStart_5181731 := by decide
  rcases family_descends (prefixWord ++ tailWord_5181731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5181747 : List Nat := [1, 1, 1, 2, 5, 1, 2, 1, 1, 2, 6]
def baseStart_5181747 : Nat := 118140960795 + 5181747 * 2 ^ 59
def prefixEnd_5181747 : Nat := 4983230072969 + 3 ^ 40 * 5181747 * 2
def baseEnd_5181747 : Nat := 2660726840993243124732085

theorem tailTrace_5181747 : CollatzResearch.WordTrace tailWord_5181747 prefixEnd_5181747 2660726840993243124732085 := by
  unfold tailWord_5181747
  simp only [CollatzResearch.WordTrace]
  refine ⟨188993839558423065776495495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125995893038948710517663663 188993839558423065776495495)
  ·
    refine ⟨283490759337634598664743243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188993839558423065776495495 283490759337634598664743243)
    ·
      refine ⟨425236139006451897997114865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 283490759337634598664743243 425236139006451897997114865)
      ·
        refine ⟨318927104254838923497836149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 425236139006451897997114865 318927104254838923497836149)
        ·
          refine ⟨29899416023891149077922139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 318927104254838923497836149 29899416023891149077922139)
          ·
            refine ⟨44849124035836723616883209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29899416023891149077922139 44849124035836723616883209)
            ·
              refine ⟨33636843026877542712662407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44849124035836723616883209 33636843026877542712662407)
              ·
                refine ⟨50455264540316314068993611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33636843026877542712662407 50455264540316314068993611)
                ·
                  refine ⟨75682896810474471103490417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50455264540316314068993611 75682896810474471103490417)
                  ·
                    refine ⟨56762172607855853327617813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 75682896810474471103490417 56762172607855853327617813)
                    ·
                      refine ⟨2660726840993243124732085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56762172607855853327617813 2660726840993243124732085)
                      ·
                        rfl

theorem cell23_5181747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 1, 1, 2, 6].length) (baseStart_5181747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5181747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5181747 prefixEnd_5181747 := by exact prefixLift 5181747
  have htrace : WordTrace (prefixWord ++ tailWord_5181747) baseStart_5181747 baseEnd_5181747 := by
    simpa [prefixWord, tailWord_5181747, baseEnd_5181747] using wordTrace_append hprefix tailTrace_5181747
  have hstable : (prefixWord ++ tailWord_5181747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5181747).length < 2 ^ (prefixWord ++ tailWord_5181747).sum := by decide
  have hdescent : baseEnd_5181747 < baseStart_5181747 := by decide
  rcases family_descends (prefixWord ++ tailWord_5181747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5181767 : List Nat := [1, 1, 4, 1, 2, 2, 1, 1, 2, 1, 7]
def baseStart_5181767 : Nat := 118140960795 + 5181767 * 2 ^ 59
def prefixEnd_5181767 : Nat := 4983230072969 + 3 ^ 40 * 5181767 * 2
def baseEnd_5181767 : Nat := 2660737110606333046481993

theorem tailTrace_5181767 : CollatzResearch.WordTrace tailWord_5181767 prefixEnd_5181767 2660737110606333046481993 := by
  unfold tailWord_5181767
  simp only [CollatzResearch.WordTrace]
  refine ⟨188994569018350609192223555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125996379345567072794815703 188994569018350609192223555)
  ·
    refine ⟨283491853527525913788335333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188994569018350609192223555 283491853527525913788335333)
    ·
      refine ⟨53154722536411108835312875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 283491853527525913788335333 53154722536411108835312875)
      ·
        refine ⟨79732083804616663252969313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53154722536411108835312875 79732083804616663252969313)
        ·
          refine ⟨59799062853462497439726985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79732083804616663252969313 59799062853462497439726985)
          ·
            refine ⟨44849297140096873079795239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59799062853462497439726985 44849297140096873079795239)
            ·
              refine ⟨67273945710145309619692859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44849297140096873079795239 67273945710145309619692859)
              ·
                refine ⟨100910918565217964429539289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67273945710145309619692859 100910918565217964429539289)
                ·
                  refine ⟨75683188923913473322154467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 100910918565217964429539289 75683188923913473322154467)
                  ·
                    refine ⟨113524783385870209983231701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 75683188923913473322154467 113524783385870209983231701)
                    ·
                      refine ⟨2660737110606333046481993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 113524783385870209983231701 2660737110606333046481993)
                      ·
                        rfl

theorem cell23_5181767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 2, 1, 7].length) (baseStart_5181767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5181767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5181767 prefixEnd_5181767 := by exact prefixLift 5181767
  have htrace : WordTrace (prefixWord ++ tailWord_5181767) baseStart_5181767 baseEnd_5181767 := by
    simpa [prefixWord, tailWord_5181767, baseEnd_5181767] using wordTrace_append hprefix tailTrace_5181767
  have hstable : (prefixWord ++ tailWord_5181767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5181767).length < 2 ^ (prefixWord ++ tailWord_5181767).sum := by decide
  have hdescent : baseEnd_5181767 < baseStart_5181767 := by decide
  rcases family_descends (prefixWord ++ tailWord_5181767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5181791 : List Nat := [1, 1, 2, 3, 1, 2, 6, 1, 1, 5]
def baseStart_5181791 : Nat := 118140960795 + 5181791 * 2 ^ 59
def prefixEnd_5181791 : Nat := 4983230072969 + 3 ^ 40 * 5181791 * 2
def baseEnd_5181791 : Nat := 886916478047346984193961

theorem tailTrace_5181791 : CollatzResearch.WordTrace tailWord_5181791 prefixEnd_5181791 886916478047346984193961 := by
  unfold tailWord_5181791
  simp only [CollatzResearch.WordTrace]
  refine ⟨188995444370263661291097227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125996962913509107527398151 188995444370263661291097227)
  ·
    refine ⟨283493166555395491936645841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188995444370263661291097227 283493166555395491936645841)
    ·
      refine ⟨212619874916546618952484381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 283493166555395491936645841 212619874916546618952484381)
      ·
        refine ⟨79732453093704982107181643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 212619874916546618952484381 79732453093704982107181643)
        ·
          refine ⟨119598679640557473160772465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79732453093704982107181643 119598679640557473160772465)
          ·
            refine ⟨89699009730418104870579349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119598679640557473160772465 89699009730418104870579349)
            ·
              refine ⟨4204641081113348665808407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 89699009730418104870579349 4204641081113348665808407)
              ·
                refine ⟨6306961621670022998712611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4204641081113348665808407 6306961621670022998712611)
                ·
                  refine ⟨9460442432505034498068917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6306961621670022998712611 9460442432505034498068917)
                  ·
                    refine ⟨886916478047346984193961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9460442432505034498068917 886916478047346984193961)
                    ·
                      rfl

theorem cell23_5181791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 6, 1, 1, 5].length) (baseStart_5181791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5181791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5181791 prefixEnd_5181791 := by exact prefixLift 5181791
  have htrace : WordTrace (prefixWord ++ tailWord_5181791) baseStart_5181791 baseEnd_5181791 := by
    simpa [prefixWord, tailWord_5181791, baseEnd_5181791] using wordTrace_append hprefix tailTrace_5181791
  have hstable : (prefixWord ++ tailWord_5181791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5181791).length < 2 ^ (prefixWord ++ tailWord_5181791).sum := by decide
  have hdescent : baseEnd_5181791 < baseStart_5181791 := by decide
  rcases family_descends (prefixWord ++ tailWord_5181791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5181811 : List Nat := [1, 1, 1, 2, 2, 1, 2, 2, 7, 2, 2]
def baseStart_5181811 : Nat := 118140960795 + 5181811 * 2 ^ 59
def prefixEnd_5181811 : Nat := 4983230072969 + 3 ^ 40 * 5181811 * 2
def baseEnd_5181811 : Nat := 2660759703755130874331791

theorem tailTrace_5181811 : CollatzResearch.WordTrace tailWord_5181811 prefixEnd_5181811 2660759703755130874331791 := by
  unfold tailWord_5181811
  simp only [CollatzResearch.WordTrace]
  refine ⟨188996173830191204706825287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125997449220127469804550191 188996173830191204706825287)
  ·
    refine ⟨283494260745286807060237931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188996173830191204706825287 283494260745286807060237931)
    ·
      refine ⟨425241391117930210590356897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 283494260745286807060237931 425241391117930210590356897)
      ·
        refine ⟨318931043338447657942767673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 425241391117930210590356897 318931043338447657942767673)
        ·
          refine ⟨239198282503835743457075755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 318931043338447657942767673 239198282503835743457075755)
          ·
            refine ⟨358797423755753615185613633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 239198282503835743457075755 358797423755753615185613633)
            ·
              refine ⟨269098067816815211389210225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 358797423755753615185613633 269098067816815211389210225)
              ·
                refine ⟨201823550862611408541907669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 269098067816815211389210225 201823550862611408541907669)
                ·
                  refine ⟨4730239473342454887700961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 201823550862611408541907669 4730239473342454887700961)
                  ·
                    refine ⟨3547679605006841165775721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4730239473342454887700961 3547679605006841165775721)
                    ·
                      refine ⟨2660759703755130874331791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3547679605006841165775721 2660759703755130874331791)
                      ·
                        rfl

theorem cell23_5181811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 7, 2, 2].length) (baseStart_5181811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5181811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5181811 prefixEnd_5181811 := by exact prefixLift 5181811
  have htrace : WordTrace (prefixWord ++ tailWord_5181811) baseStart_5181811 baseEnd_5181811 := by
    simpa [prefixWord, tailWord_5181811, baseEnd_5181811] using wordTrace_append hprefix tailTrace_5181811
  have hstable : (prefixWord ++ tailWord_5181811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5181811).length < 2 ^ (prefixWord ++ tailWord_5181811).sum := by decide
  have hdescent : baseEnd_5181811 < baseStart_5181811 := by decide
  rcases family_descends (prefixWord ++ tailWord_5181811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5181817 : List Nat := [1, 2, 1, 3, 2, 1, 1, 12]
def baseStart_5181817 : Nat := 118140960795 + 5181817 * 2 ^ 59
def prefixEnd_5181817 : Nat := 4983230072969 + 3 ^ 40 * 5181817 * 2
def baseEnd_5181817 : Nat := 98546769801446587068769

theorem tailTrace_5181817 : CollatzResearch.WordTrace tailWord_5181817 prefixEnd_5181817 98546769801446587068769 := by
  unfold tailWord_5181817
  simp only [CollatzResearch.WordTrace]
  refine ⟨188996392668169467731543705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125997595112112978487695803 188996392668169467731543705)
  ·
    refine ⟨141747294501127100798657779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188996392668169467731543705 141747294501127100798657779)
    ·
      refine ⟨212620941751690651197986669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141747294501127100798657779 212620941751690651197986669)
      ·
        refine ⟨79732853156883994199245001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 212620941751690651197986669 79732853156883994199245001)
        ·
          refine ⟨59799639867662995649433751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79732853156883994199245001 59799639867662995649433751)
          ·
            refine ⟨89699459801494493474150627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59799639867662995649433751 89699459801494493474150627)
            ·
              refine ⟨134549189702241740211225941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89699459801494493474150627 134549189702241740211225941)
              ·
                refine ⟨98546769801446587068769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 134549189702241740211225941 98546769801446587068769)
                ·
                  rfl

theorem cell23_5181817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 12].length) (baseStart_5181817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5181817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5181817 prefixEnd_5181817 := by exact prefixLift 5181817
  have htrace : WordTrace (prefixWord ++ tailWord_5181817) baseStart_5181817 baseEnd_5181817 := by
    simpa [prefixWord, tailWord_5181817, baseEnd_5181817] using wordTrace_append hprefix tailTrace_5181817
  have hstable : (prefixWord ++ tailWord_5181817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5181817).length < 2 ^ (prefixWord ++ tailWord_5181817).sum := by decide
  have hdescent : baseEnd_5181817 < baseStart_5181817 := by decide
  rcases family_descends (prefixWord ++ tailWord_5181817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5181821 : List Nat := [1, 4, 1, 1, 2, 5, 1, 1, 1, 6]
def baseStart_5181821 : Nat := 118140960795 + 5181821 * 2 ^ 59
def prefixEnd_5181821 : Nat := 4983230072969 + 3 ^ 40 * 5181821 * 2
def baseEnd_5181821 : Nat := 886921612853891945068915

theorem tailTrace_5181821 : CollatzResearch.WordTrace tailWord_5181821 prefixEnd_5181821 886921612853891945068915 := by
  unfold tailWord_5181821
  simp only [CollatzResearch.WordTrace]
  refine ⟨188996538560154976414689317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125997692373436650943126211 188996538560154976414689317)
  ·
    refine ⟨35436850980029058077754247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 188996538560154976414689317 35436850980029058077754247)
    ·
      refine ⟨53155276470043587116631371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35436850980029058077754247 53155276470043587116631371)
      ·
        refine ⟨79732914705065380674947057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53155276470043587116631371 79732914705065380674947057)
        ·
          refine ⟨59799686028799035506210293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79732914705065380674947057 59799686028799035506210293)
          ·
            refine ⟨5606220565199909578707215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 59799686028799035506210293 5606220565199909578707215)
            ·
              refine ⟨8409330847799864368060823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5606220565199909578707215 8409330847799864368060823)
              ·
                refine ⟨12613996271699796552091235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8409330847799864368060823 12613996271699796552091235)
                ·
                  refine ⟨18920994407549694828136853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12613996271699796552091235 18920994407549694828136853)
                  ·
                    refine ⟨886921612853891945068915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18920994407549694828136853 886921612853891945068915)
                    ·
                      rfl

theorem cell23_5181821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 1, 1, 1, 6].length) (baseStart_5181821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5181821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5181821 prefixEnd_5181821 := by exact prefixLift 5181821
  have htrace : WordTrace (prefixWord ++ tailWord_5181821) baseStart_5181821 baseEnd_5181821 := by
    simpa [prefixWord, tailWord_5181821, baseEnd_5181821] using wordTrace_append hprefix tailTrace_5181821
  have hstable : (prefixWord ++ tailWord_5181821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5181821).length < 2 ^ (prefixWord ++ tailWord_5181821).sum := by decide
  have hdescent : baseEnd_5181821 < baseStart_5181821 := by decide
  rcases family_descends (prefixWord ++ tailWord_5181821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5181828 : List Nat := [2, 3, 2, 1, 1, 2, 1, 4, 3, 2, 2]
def baseStart_5181828 : Nat := 118140960795 + 5181828 * 2 ^ 59
def prefixEnd_5181828 : Nat := 4983230072969 + 3 ^ 40 * 5181828 * 2
def baseEnd_5181828 : Nat := 2660768432926257307819213

theorem tailTrace_5181828 : CollatzResearch.WordTrace tailWord_5181828 prefixEnd_5181828 2660768432926257307819213 := by
  unfold tailWord_5181828
  simp only [CollatzResearch.WordTrace]
  refine ⟨94498396935564808305097069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125997862580753077740129425 94498396935564808305097069)
  ·
    refine ⟨35436898850836803114411401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94498396935564808305097069 35436898850836803114411401)
    ·
      refine ⟨26577674138127602335808551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35436898850836803114411401 26577674138127602335808551)
      ·
        refine ⟨39866511207191403503712827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26577674138127602335808551 39866511207191403503712827)
        ·
          refine ⟨59799766810787105255569241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39866511207191403503712827 59799766810787105255569241)
          ·
            refine ⟨44849825108090328941676931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59799766810787105255569241 44849825108090328941676931)
            ·
              refine ⟨67274737662135493412515397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44849825108090328941676931 67274737662135493412515397)
              ·
                refine ⟨12614013311650405014846637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 67274737662135493412515397 12614013311650405014846637)
                ·
                  refine ⟨4730254991868901880567489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12614013311650405014846637 4730254991868901880567489)
                  ·
                    refine ⟨3547691243901676410425617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4730254991868901880567489 3547691243901676410425617)
                    ·
                      refine ⟨2660768432926257307819213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3547691243901676410425617 2660768432926257307819213)
                      ·
                        rfl

theorem cell23_5181828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 4, 3, 2, 2].length) (baseStart_5181828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5181828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5181828 prefixEnd_5181828 := by exact prefixLift 5181828
  have htrace : WordTrace (prefixWord ++ tailWord_5181828) baseStart_5181828 baseEnd_5181828 := by
    simpa [prefixWord, tailWord_5181828, baseEnd_5181828] using wordTrace_append hprefix tailTrace_5181828
  have hstable : (prefixWord ++ tailWord_5181828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5181828).length < 2 ^ (prefixWord ++ tailWord_5181828).sum := by decide
  have hdescent : baseEnd_5181828 < baseStart_5181828 := by decide
  rcases family_descends (prefixWord ++ tailWord_5181828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5181848 : List Nat := [2, 1, 2, 5, 1, 1, 2, 3, 1, 2, 3]
def baseStart_5181848 : Nat := 118140960795 + 5181848 * 2 ^ 59
def prefixEnd_5181848 : Nat := 4983230072969 + 3 ^ 40 * 5181848 * 2
def baseEnd_5181848 : Nat := 2660778702539347229569121

theorem tailTrace_5181848 : CollatzResearch.WordTrace tailWord_5181848 prefixEnd_5181848 2660778702539347229569121 := by
  unfold tailWord_5181848
  simp only [CollatzResearch.WordTrace]
  refine ⟨94498761665528580012961099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125998348887371440017281465 94498761665528580012961099)
  ·
    refine ⟨141748142498292870019441649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94498761665528580012961099 141748142498292870019441649)
    ·
      refine ⟨106311106873719652514581237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141748142498292870019441649 106311106873719652514581237)
      ·
        refine ⟨9966666269411217423241991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 106311106873719652514581237 9966666269411217423241991)
        ·
          refine ⟨14949999404116826134862987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9966666269411217423241991 14949999404116826134862987)
          ·
            refine ⟨22424999106175239202294481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14949999404116826134862987 22424999106175239202294481)
            ·
              refine ⟨16818749329631429401720861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22424999106175239202294481 16818749329631429401720861)
              ·
                refine ⟨6307030998611786025645323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16818749329631429401720861 6307030998611786025645323)
                ·
                  refine ⟨9460546497917679038467985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6307030998611786025645323 9460546497917679038467985)
                  ·
                    refine ⟨7095409873438259278850989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9460546497917679038467985 7095409873438259278850989)
                    ·
                      refine ⟨2660778702539347229569121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7095409873438259278850989 2660778702539347229569121)
                      ·
                        rfl

theorem cell23_5181848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_5181848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5181848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5181848 prefixEnd_5181848 := by exact prefixLift 5181848
  have htrace : WordTrace (prefixWord ++ tailWord_5181848) baseStart_5181848 baseEnd_5181848 := by
    simpa [prefixWord, tailWord_5181848, baseEnd_5181848] using wordTrace_append hprefix tailTrace_5181848
  have hstable : (prefixWord ++ tailWord_5181848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5181848).length < 2 ^ (prefixWord ++ tailWord_5181848).sum := by decide
  have hdescent : baseEnd_5181848 < baseStart_5181848 := by decide
  rcases family_descends (prefixWord ++ tailWord_5181848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5181861 : List Nat := [1, 3, 1, 2, 1, 1, 3, 3, 4, 1, 3]
def baseStart_5181861 : Nat := 118140960795 + 5181861 * 2 ^ 59
def prefixEnd_5181861 : Nat := 4983230072969 + 3 ^ 40 * 5181861 * 2
def baseEnd_5181861 : Nat := 2660785377787855678706561

theorem tailTrace_5181861 : CollatzResearch.WordTrace tailWord_5181861 prefixEnd_5181861 2660785377787855678706561 := by
  unfold tailWord_5181861
  simp only [CollatzResearch.WordTrace]
  refine ⟨188997997480010063246145437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125998664986673375497430291 188997997480010063246145437)
  ·
    refine ⟨70874249055003773717304539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 188997997480010063246145437 70874249055003773717304539)
    ·
      refine ⟨106311373582505660575956809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70874249055003773717304539 106311373582505660575956809)
      ·
        refine ⟨79733530186879245431967607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106311373582505660575956809 79733530186879245431967607)
        ·
          refine ⟨119600295280318868147951411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79733530186879245431967607 119600295280318868147951411)
          ·
            refine ⟨179400442920478302221927117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119600295280318868147951411 179400442920478302221927117)
            ·
              refine ⟨67275166095179363333222669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 179400442920478302221927117 67275166095179363333222669)
              ·
                refine ⟨25228187285692261249958501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67275166095179363333222669 25228187285692261249958501)
                ·
                  refine ⟨4730285116067298984367219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25228187285692261249958501 4730285116067298984367219)
                  ·
                    refine ⟨7095427674100948476550829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4730285116067298984367219 7095427674100948476550829)
                    ·
                      refine ⟨2660785377787855678706561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7095427674100948476550829 2660785377787855678706561)
                      ·
                        rfl

theorem cell23_5181861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 3, 4, 1, 3].length) (baseStart_5181861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5181861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5181861 prefixEnd_5181861 := by exact prefixLift 5181861
  have htrace : WordTrace (prefixWord ++ tailWord_5181861) baseStart_5181861 baseEnd_5181861 := by
    simpa [prefixWord, tailWord_5181861, baseEnd_5181861] using wordTrace_append hprefix tailTrace_5181861
  have hstable : (prefixWord ++ tailWord_5181861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5181861).length < 2 ^ (prefixWord ++ tailWord_5181861).sum := by decide
  have hdescent : baseEnd_5181861 < baseStart_5181861 := by decide
  rcases family_descends (prefixWord ++ tailWord_5181861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5181904 : List Nat := [2, 1, 1, 1, 1, 2, 2, 1, 3, 6, 3]
def baseStart_5181904 : Nat := 118140960795 + 5181904 * 2 ^ 59
def prefixEnd_5181904 : Nat := 4983230072969 + 3 ^ 40 * 5181904 * 2
def baseEnd_5181904 : Nat := 2660807457455999010468863

theorem tailTrace_5181904 : CollatzResearch.WordTrace tailWord_5181904 prefixEnd_5181904 2660807457455999010468863 := by
  unfold tailWord_5181904
  simp only [CollatzResearch.WordTrace]
  refine ⟨94499782909427140794980383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125999710545902854393307177 94499782909427140794980383)
  ·
    refine ⟨141749674364140711192470575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94499782909427140794980383 141749674364140711192470575)
    ·
      refine ⟨212624511546211066788705863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141749674364140711192470575 212624511546211066788705863)
      ·
        refine ⟨318936767319316600183058795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212624511546211066788705863 318936767319316600183058795)
        ·
          refine ⟨478405150978974900274588193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 318936767319316600183058795 478405150978974900274588193)
          ·
            refine ⟨358803863234231175205941145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 478405150978974900274588193 358803863234231175205941145)
            ·
              refine ⟨269102897425673381404455859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 358803863234231175205941145 269102897425673381404455859)
              ·
                refine ⟨403654346138510072106683789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 269102897425673381404455859 403654346138510072106683789)
                ·
                  refine ⟨151370379801941277040006421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 403654346138510072106683789 151370379801941277040006421)
                  ·
                    refine ⟨7095486553215997361250301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 151370379801941277040006421 7095486553215997361250301)
                    ·
                      refine ⟨2660807457455999010468863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7095486553215997361250301 2660807457455999010468863)
                      ·
                        rfl

theorem cell23_5181904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 3, 6, 3].length) (baseStart_5181904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5181904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5181904 prefixEnd_5181904 := by exact prefixLift 5181904
  have htrace : WordTrace (prefixWord ++ tailWord_5181904) baseStart_5181904 baseEnd_5181904 := by
    simpa [prefixWord, tailWord_5181904, baseEnd_5181904] using wordTrace_append hprefix tailTrace_5181904
  have hstable : (prefixWord ++ tailWord_5181904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5181904).length < 2 ^ (prefixWord ++ tailWord_5181904).sum := by decide
  have hdescent : baseEnd_5181904 < baseStart_5181904 := by decide
  rcases family_descends (prefixWord ++ tailWord_5181904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5181961 : List Nat := [1, 2, 1, 1, 3, 1, 2, 2, 1, 7, 2]
def baseStart_5181961 : Nat := 118140960795 + 5181961 * 2 ^ 59
def prefixEnd_5181961 : Nat := 4983230072969 + 3 ^ 40 * 5181961 * 2
def baseEnd_5181961 : Nat := 2660836725853305287456101

theorem tailTrace_5181961 : CollatzResearch.WordTrace tailWord_5181961 prefixEnd_5181961 2660836725853305287456101 := by
  unfold tailWord_5181961
  simp only [CollatzResearch.WordTrace]
  refine ⟨189001644779647780324785737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126001096519765186883190491 189001644779647780324785737)
  ·
    refine ⟨141751233584735835243589303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189001644779647780324785737 141751233584735835243589303)
    ·
      refine ⟨212626850377103752865383955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141751233584735835243589303 212626850377103752865383955)
      ·
        refine ⟨318940275565655629298075933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212626850377103752865383955 318940275565655629298075933)
        ·
          refine ⟨119602603337120860986778475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 318940275565655629298075933 119602603337120860986778475)
          ·
            refine ⟨179403905005681291480167713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119602603337120860986778475 179403905005681291480167713)
            ·
              refine ⟨134552928754260968610125785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 179403905005681291480167713 134552928754260968610125785)
              ·
                refine ⟨100914696565695726457594339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 134552928754260968610125785 100914696565695726457594339)
                ·
                  refine ⟨151372044848543589686391509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 100914696565695726457594339 151372044848543589686391509)
                  ·
                    refine ⟨3547782301137740383274801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 151372044848543589686391509 3547782301137740383274801)
                    ·
                      refine ⟨2660836725853305287456101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3547782301137740383274801 2660836725853305287456101)
                      ·
                        rfl

theorem cell23_5181961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 7, 2].length) (baseStart_5181961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5181961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5181961 prefixEnd_5181961 := by exact prefixLift 5181961
  have htrace : WordTrace (prefixWord ++ tailWord_5181961) baseStart_5181961 baseEnd_5181961 := by
    simpa [prefixWord, tailWord_5181961, baseEnd_5181961] using wordTrace_append hprefix tailTrace_5181961
  have hstable : (prefixWord ++ tailWord_5181961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5181961).length < 2 ^ (prefixWord ++ tailWord_5181961).sum := by decide
  have hdescent : baseEnd_5181961 < baseStart_5181961 := by decide
  rcases family_descends (prefixWord ++ tailWord_5181961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5181965 : List Nat := [1, 7, 1, 1, 1, 1, 1, 2, 2, 2, 4]
def baseStart_5181965 : Nat := 118140960795 + 5181965 * 2 ^ 59
def prefixEnd_5181965 : Nat := 4983230072969 + 3 ^ 40 * 5181965 * 2
def baseEnd_5181965 : Nat := 2660838779775923271806083

theorem tailTrace_5181965 : CollatzResearch.WordTrace tailWord_5181965 prefixEnd_5181965 2660838779775923271806083 := by
  unfold tailWord_5181965
  simp only [CollatzResearch.WordTrace]
  refine ⟨189001790671633289007931349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126001193781088859338620899 189001790671633289007931349)
  ·
    refine ⟨4429729468866405211123391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 189001790671633289007931349 4429729468866405211123391)
    ·
      refine ⟨6644594203299607816685087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4429729468866405211123391 6644594203299607816685087)
      ·
        refine ⟨9966891304949411725027631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6644594203299607816685087 9966891304949411725027631)
        ·
          refine ⟨14950336957424117587541447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9966891304949411725027631 14950336957424117587541447)
          ·
            refine ⟨22425505436136176381312171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14950336957424117587541447 22425505436136176381312171)
            ·
              refine ⟨33638258154204264571968257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22425505436136176381312171 33638258154204264571968257)
              ·
                refine ⟨25228693615653198428976193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33638258154204264571968257 25228693615653198428976193)
                ·
                  refine ⟨18921520211739898821732145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25228693615653198428976193 18921520211739898821732145)
                  ·
                    refine ⟨14191140158804924116299109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18921520211739898821732145 14191140158804924116299109)
                    ·
                      refine ⟨2660838779775923271806083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14191140158804924116299109 2660838779775923271806083)
                      ·
                        rfl

theorem cell23_5181965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_5181965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5181965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5181965 prefixEnd_5181965 := by exact prefixLift 5181965
  have htrace : WordTrace (prefixWord ++ tailWord_5181965) baseStart_5181965 baseEnd_5181965 := by
    simpa [prefixWord, tailWord_5181965, baseEnd_5181965] using wordTrace_append hprefix tailTrace_5181965
  have hstable : (prefixWord ++ tailWord_5181965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5181965).length < 2 ^ (prefixWord ++ tailWord_5181965).sum := by decide
  have hdescent : baseEnd_5181965 < baseStart_5181965 := by decide
  rcases family_descends (prefixWord ++ tailWord_5181965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5182028 : List Nat := [2, 2, 1, 3, 1, 2, 3, 2, 2, 2, 3]
def baseStart_5182028 : Nat := 118140960795 + 5182028 * 2 ^ 59
def prefixEnd_5182028 : Nat := 4983230072969 + 3 ^ 40 * 5182028 * 2
def baseEnd_5182028 : Nat := 2660871129057156525318293

theorem tailTrace_5182028 : CollatzResearch.WordTrace tailWord_5182028 prefixEnd_5182028 2660871129057156525318293 := by
  unfold tailWord_5182028
  simp only [CollatzResearch.WordTrace]
  refine ⟨94502044235202525383737369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126002725646936700511649825 94502044235202525383737369)
  ·
    refine ⟨70876533176401894037803027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94502044235202525383737369 70876533176401894037803027)
    ·
      refine ⟨106314799764602841056704541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70876533176401894037803027 106314799764602841056704541)
      ·
        refine ⟨39868049911726065396264203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106314799764602841056704541 39868049911726065396264203)
        ·
          refine ⟨59802074867589098094396305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39868049911726065396264203 59802074867589098094396305)
          ·
            refine ⟨44851556150691823570797229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59802074867589098094396305 44851556150691823570797229)
            ·
              refine ⟨16819333556509433839048961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44851556150691823570797229 16819333556509433839048961)
              ·
                refine ⟨12614500167382075379286721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16819333556509433839048961 12614500167382075379286721)
                ·
                  refine ⟨9460875125536556534465041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12614500167382075379286721 9460875125536556534465041)
                  ·
                    refine ⟨7095656344152417400848781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9460875125536556534465041 7095656344152417400848781)
                    ·
                      refine ⟨2660871129057156525318293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7095656344152417400848781 2660871129057156525318293)
                      ·
                        rfl

theorem cell23_5182028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 2, 2, 2, 3].length) (baseStart_5182028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5182028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5182028 prefixEnd_5182028 := by exact prefixLift 5182028
  have htrace : WordTrace (prefixWord ++ tailWord_5182028) baseStart_5182028 baseEnd_5182028 := by
    simpa [prefixWord, tailWord_5182028, baseEnd_5182028] using wordTrace_append hprefix tailTrace_5182028
  have hstable : (prefixWord ++ tailWord_5182028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5182028).length < 2 ^ (prefixWord ++ tailWord_5182028).sum := by decide
  have hdescent : baseEnd_5182028 < baseStart_5182028 := by decide
  rcases family_descends (prefixWord ++ tailWord_5182028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5182048 : List Nat := [2, 1, 1, 3, 2, 1, 6, 1, 6]
def baseStart_5182048 : Nat := 118140960795 + 5182048 * 2 ^ 59
def prefixEnd_5182048 : Nat := 4983230072969 + 3 ^ 40 * 5182048 * 2
def baseEnd_5182048 : Nat := 295653488741138494118689

theorem tailTrace_5182048 : CollatzResearch.WordTrace tailWord_5182048 prefixEnd_5182048 295653488741138494118689 := by
  unfold tailWord_5182048
  simp only [CollatzResearch.WordTrace]
  refine ⟨94502408965166297091601399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126003211953555062788801865 94502408965166297091601399)
  ·
    refine ⟨141753613447749445637402099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94502408965166297091601399 141753613447749445637402099)
    ·
      refine ⟨212630420171624168456103149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141753613447749445637402099 212630420171624168456103149)
      ·
        refine ⟨79736407564359063171038681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 212630420171624168456103149 79736407564359063171038681)
        ·
          refine ⟨59802305673269297378279011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79736407564359063171038681 59802305673269297378279011)
          ·
            refine ⟨89703458509903946067418517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59802305673269297378279011 89703458509903946067418517)
            ·
              refine ⟨4204849617651747471910243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 89703458509903946067418517 4204849617651747471910243)
              ·
                refine ⟨6307274426477621207865365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4204849617651747471910243 6307274426477621207865365)
                ·
                  refine ⟨295653488741138494118689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6307274426477621207865365 295653488741138494118689)
                  ·
                    rfl

theorem cell23_5182048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 6, 1, 6].length) (baseStart_5182048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5182048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5182048 prefixEnd_5182048 := by exact prefixLift 5182048
  have htrace : WordTrace (prefixWord ++ tailWord_5182048) baseStart_5182048 baseEnd_5182048 := by
    simpa [prefixWord, tailWord_5182048, baseEnd_5182048] using wordTrace_append hprefix tailTrace_5182048
  have hstable : (prefixWord ++ tailWord_5182048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5182048).length < 2 ^ (prefixWord ++ tailWord_5182048).sum := by decide
  have hdescent : baseEnd_5182048 < baseStart_5182048 := by decide
  rcases family_descends (prefixWord ++ tailWord_5182048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5182085 : List Nat := [1, 3, 1, 1, 4, 2, 2, 2, 2, 3, 2]
def baseStart_5182085 : Nat := 118140960795 + 5182085 * 2 ^ 59
def prefixEnd_5182085 : Nat := 4983230072969 + 3 ^ 40 * 5182085 * 2
def baseEnd_5182085 : Nat := 2660900397454462802305531

theorem tailTrace_5182085 : CollatzResearch.WordTrace tailWord_5182085 prefixEnd_5182085 2660900397454462802305531 := by
  unfold tailWord_5182085
  simp only [CollatzResearch.WordTrace]
  refine ⟨189006167431198549502299709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126004111620799033001533139 189006167431198549502299709)
  ·
    refine ⟨70877312786699456063362391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 189006167431198549502299709 70877312786699456063362391)
    ·
      refine ⟨106315969180049184095043587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70877312786699456063362391 106315969180049184095043587)
      ·
        refine ⟨159473953770073776142565381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106315969180049184095043587 159473953770073776142565381)
        ·
          refine ⟨29901366331888833026731009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 159473953770073776142565381 29901366331888833026731009)
          ·
            refine ⟨22426024748916624770048257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29901366331888833026731009 22426024748916624770048257)
            ·
              refine ⟨16819518561687468577536193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22426024748916624770048257 16819518561687468577536193)
              ·
                refine ⟨12614638921265601433152145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16819518561687468577536193 12614638921265601433152145)
                ·
                  refine ⟨9460979190949201074864109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12614638921265601433152145 9460979190949201074864109)
                  ·
                    refine ⟨3547867196605950403074041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9460979190949201074864109 3547867196605950403074041)
                    ·
                      refine ⟨2660900397454462802305531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3547867196605950403074041 2660900397454462802305531)
                      ·
                        rfl

theorem cell23_5182085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 2, 2, 3, 2].length) (baseStart_5182085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5182085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5182085 prefixEnd_5182085 := by exact prefixLift 5182085
  have htrace : WordTrace (prefixWord ++ tailWord_5182085) baseStart_5182085 baseEnd_5182085 := by
    simpa [prefixWord, tailWord_5182085, baseEnd_5182085] using wordTrace_append hprefix tailTrace_5182085
  have hstable : (prefixWord ++ tailWord_5182085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5182085).length < 2 ^ (prefixWord ++ tailWord_5182085).sum := by decide
  have hdescent : baseEnd_5182085 < baseStart_5182085 := by decide
  rcases family_descends (prefixWord ++ tailWord_5182085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5182108 : List Nat := [2, 2, 3, 2, 2, 1, 1, 3, 1, 6]
def baseStart_5182108 : Nat := 118140960795 + 5182108 * 2 ^ 59
def prefixEnd_5182108 : Nat := 4983230072969 + 3 ^ 40 * 5182108 * 2
def baseEnd_5182108 : Nat := 886970735836505404105975

theorem tailTrace_5182108 : CollatzResearch.WordTrace tailWord_5182108 prefixEnd_5182108 886970735836505404105975 := by
  unfold tailWord_5182108
  simp only [CollatzResearch.WordTrace]
  refine ⟨94503503155057612215193489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126004670873410149620257985 94503503155057612215193489)
  ·
    refine ⟨70877627366293209161395117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94503503155057612215193489 70877627366293209161395117)
    ·
      refine ⟨26579110262359953435523169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70877627366293209161395117 26579110262359953435523169)
      ·
        refine ⟨19934332696769965076642377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26579110262359953435523169 19934332696769965076642377)
        ·
          refine ⟨14950749522577473807481783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19934332696769965076642377 14950749522577473807481783)
          ·
            refine ⟨22426124283866210711222675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14950749522577473807481783 22426124283866210711222675)
            ·
              refine ⟨33639186425799316066834013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22426124283866210711222675 33639186425799316066834013)
              ·
                refine ⟨12614694909674743525062755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33639186425799316066834013 12614694909674743525062755)
                ·
                  refine ⟨18922042364512115287594133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12614694909674743525062755 18922042364512115287594133)
                  ·
                    refine ⟨886970735836505404105975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18922042364512115287594133 886970735836505404105975)
                    ·
                      rfl

theorem cell23_5182108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 3, 1, 6].length) (baseStart_5182108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5182108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5182108 prefixEnd_5182108 := by exact prefixLift 5182108
  have htrace : WordTrace (prefixWord ++ tailWord_5182108) baseStart_5182108 baseEnd_5182108 := by
    simpa [prefixWord, tailWord_5182108, baseEnd_5182108] using wordTrace_append hprefix tailTrace_5182108
  have hstable : (prefixWord ++ tailWord_5182108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5182108).length < 2 ^ (prefixWord ++ tailWord_5182108).sum := by decide
  have hdescent : baseEnd_5182108 < baseStart_5182108 := by decide
  rcases family_descends (prefixWord ++ tailWord_5182108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5182126 : List Nat := [4, 1, 4, 1, 1, 2, 2, 3, 1, 1, 3]
def baseStart_5182126 : Nat := 118140960795 + 5182126 * 2 ^ 59
def prefixEnd_5182126 : Nat := 4983230072969 + 3 ^ 40 * 5182126 * 2
def baseEnd_5182126 : Nat := 2660921450161297141892843

theorem tailTrace_5182126 : CollatzResearch.WordTrace tailWord_5182126 prefixEnd_5182126 2660921450161297141892843 := by
  unfold tailWord_5182126
  simp only [CollatzResearch.WordTrace]
  refine ⟨23625957853006251688067779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126005108549366675669694821 23625957853006251688067779)
  ·
    refine ⟨35438936779509377532101669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23625957853006251688067779 35438936779509377532101669)
    ·
      refine ⟨6644800646158008287269063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35438936779509377532101669 6644800646158008287269063)
      ·
        refine ⟨9967200969237012430903595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6644800646158008287269063 9967200969237012430903595)
        ·
          refine ⟨14950801453855518646355393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9967200969237012430903595 14950801453855518646355393)
          ·
            refine ⟨11213101090391638984766545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14950801453855518646355393 11213101090391638984766545)
            ·
              refine ⟨8409825817793729238574909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11213101090391638984766545 8409825817793729238574909)
              ·
                refine ⟨3153684681672648464465591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8409825817793729238574909 3153684681672648464465591)
                ·
                  refine ⟨4730527022508972696698387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3153684681672648464465591 4730527022508972696698387)
                  ·
                    refine ⟨7095790533763459045047581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4730527022508972696698387 7095790533763459045047581)
                    ·
                      refine ⟨2660921450161297141892843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7095790533763459045047581 2660921450161297141892843)
                      ·
                        rfl

theorem cell23_5182126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 2, 3, 1, 1, 3].length) (baseStart_5182126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5182126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5182126 prefixEnd_5182126 := by exact prefixLift 5182126
  have htrace : WordTrace (prefixWord ++ tailWord_5182126) baseStart_5182126 baseEnd_5182126 := by
    simpa [prefixWord, tailWord_5182126, baseEnd_5182126] using wordTrace_append hprefix tailTrace_5182126
  have hstable : (prefixWord ++ tailWord_5182126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5182126).length < 2 ^ (prefixWord ++ tailWord_5182126).sum := by decide
  have hdescent : baseEnd_5182126 < baseStart_5182126 := by decide
  rcases family_descends (prefixWord ++ tailWord_5182126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5182129 : List Nat := [1, 2, 2, 6, 1, 2, 2, 1, 1, 5]
def baseStart_5182129 : Nat := 118140960795 + 5182129 * 2 ^ 59
def prefixEnd_5182129 : Nat := 4983230072969 + 3 ^ 40 * 5182129 * 2
def baseEnd_5182129 : Nat := 886974330201086876718443

theorem tailTrace_5182129 : CollatzResearch.WordTrace tailWord_5182129 prefixEnd_5182129 886974330201086876718443 := by
  unfold tailWord_5182129
  simp only [CollatzResearch.WordTrace]
  refine ⟨189007772243039145016901441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126005181495359430011267627 189007772243039145016901441)
  ·
    refine ⟨141755829182279358762676081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189007772243039145016901441 141755829182279358762676081)
    ·
      refine ⟨106316871886709519072007061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141755829182279358762676081 106316871886709519072007061)
      ·
        refine ⟨4983603369689508706500331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 106316871886709519072007061 4983603369689508706500331)
        ·
          refine ⟨7475405054534263059750497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4983603369689508706500331 7475405054534263059750497)
          ·
            refine ⟨5606553790900697294812873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7475405054534263059750497 5606553790900697294812873)
            ·
              refine ⟨4204915343175522971109655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5606553790900697294812873 4204915343175522971109655)
              ·
                refine ⟨6307373014763284456664483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4204915343175522971109655 6307373014763284456664483)
                ·
                  refine ⟨9461059522144926684996725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6307373014763284456664483 9461059522144926684996725)
                  ·
                    refine ⟨886974330201086876718443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9461059522144926684996725 886974330201086876718443)
                    ·
                      rfl

theorem cell23_5182129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 2, 1, 1, 5].length) (baseStart_5182129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5182129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5182129 prefixEnd_5182129 := by exact prefixLift 5182129
  have htrace : WordTrace (prefixWord ++ tailWord_5182129) baseStart_5182129 baseEnd_5182129 := by
    simpa [prefixWord, tailWord_5182129, baseEnd_5182129] using wordTrace_append hprefix tailTrace_5182129
  have hstable : (prefixWord ++ tailWord_5182129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5182129).length < 2 ^ (prefixWord ++ tailWord_5182129).sum := by decide
  have hdescent : baseEnd_5182129 < baseStart_5182129 := by decide
  rcases family_descends (prefixWord ++ tailWord_5182129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5182151 : List Nat := [1, 1, 4, 1, 1, 1, 2, 3, 2, 7]
def baseStart_5182151 : Nat := 118140960795 + 5182151 * 2 ^ 59
def prefixEnd_5182151 : Nat := 4983230072969 + 3 ^ 40 * 5182151 * 2
def baseEnd_5182151 : Nat := 886978095725886514693409

theorem tailTrace_5182151 : CollatzResearch.WordTrace tailWord_5182151 prefixEnd_5182151 886978095725886514693409 := by
  unfold tailWord_5182151
  simp only [CollatzResearch.WordTrace]
  refine ⟨189008574648959442774202307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126005716432639628516134871 189008574648959442774202307)
  ·
    refine ⟨283512861973439164161303461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189008574648959442774202307 283512861973439164161303461)
    ·
      refine ⟨53158661620019843280244399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 283512861973439164161303461 53158661620019843280244399)
      ·
        refine ⟨79737992430029764920366599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53158661620019843280244399 79737992430029764920366599)
        ·
          refine ⟨119606988645044647380549899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79737992430029764920366599 119606988645044647380549899)
          ·
            refine ⟨179410482967566971070824849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119606988645044647380549899 179410482967566971070824849)
            ·
              refine ⟨134557862225675228303118637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 179410482967566971070824849 134557862225675228303118637)
              ·
                refine ⟨50459198334628210613669489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 134557862225675228303118637 50459198334628210613669489)
                ·
                  refine ⟨37844398750971157960252117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50459198334628210613669489 37844398750971157960252117)
                  ·
                    refine ⟨886978095725886514693409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37844398750971157960252117 886978095725886514693409)
                    ·
                      rfl

theorem cell23_5182151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 3, 2, 7].length) (baseStart_5182151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5182151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5182151 prefixEnd_5182151 := by exact prefixLift 5182151
  have htrace : WordTrace (prefixWord ++ tailWord_5182151) baseStart_5182151 baseEnd_5182151 := by
    simpa [prefixWord, tailWord_5182151, baseEnd_5182151] using wordTrace_append hprefix tailTrace_5182151
  have hstable : (prefixWord ++ tailWord_5182151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5182151).length < 2 ^ (prefixWord ++ tailWord_5182151).sum := by decide
  have hdescent : baseEnd_5182151 < baseStart_5182151 := by decide
  rcases family_descends (prefixWord ++ tailWord_5182151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5182162 : List Nat := [3, 2, 2, 2, 3, 2, 1, 1, 1, 2, 4]
def baseStart_5182162 : Nat := 118140960795 + 5182162 * 2 ^ 59
def prefixEnd_5182162 : Nat := 4983230072969 + 3 ^ 40 * 5182162 * 2
def baseEnd_5182162 : Nat := 2660939935464859001042677

theorem tailTrace_5182162 : CollatzResearch.WordTrace tailWord_5182162 prefixEnd_5182162 2660939935464859001042677 := by
  unfold tailWord_5182162
  simp only [CollatzResearch.WordTrace]
  refine ⟨47252243962979897913213185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126005983901279727768568493 47252243962979897913213185)
  ·
    refine ⟨35439182972234923434909889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47252243962979897913213185 35439182972234923434909889)
    ·
      refine ⟨26579387229176192576182417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35439182972234923434909889 26579387229176192576182417)
      ·
        refine ⟨19934540421882144432136813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26579387229176192576182417 19934540421882144432136813)
        ·
          refine ⟨7475452658205804162051305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19934540421882144432136813 7475452658205804162051305)
          ·
            refine ⟨5606589493654353121538479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7475452658205804162051305 5606589493654353121538479)
            ·
              refine ⟨8409884240481529682307719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5606589493654353121538479 8409884240481529682307719)
              ·
                refine ⟨12614826360722294523461579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8409884240481529682307719 12614826360722294523461579)
                ·
                  refine ⟨18922239541083441785192369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12614826360722294523461579 18922239541083441785192369)
                  ·
                    refine ⟨14191679655812581338894277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18922239541083441785192369 14191679655812581338894277)
                    ·
                      refine ⟨2660939935464859001042677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14191679655812581338894277 2660939935464859001042677)
                      ·
                        rfl

theorem cell23_5182162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 1, 1, 1, 2, 4].length) (baseStart_5182162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5182162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5182162 prefixEnd_5182162 := by exact prefixLift 5182162
  have htrace : WordTrace (prefixWord ++ tailWord_5182162) baseStart_5182162 baseEnd_5182162 := by
    simpa [prefixWord, tailWord_5182162, baseEnd_5182162] using wordTrace_append hprefix tailTrace_5182162
  have hstable : (prefixWord ++ tailWord_5182162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5182162).length < 2 ^ (prefixWord ++ tailWord_5182162).sum := by decide
  have hdescent : baseEnd_5182162 < baseStart_5182162 := by decide
  rcases family_descends (prefixWord ++ tailWord_5182162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5182172 : List Nat := [2, 2, 5, 1, 1, 3, 2, 7]
def baseStart_5182172 : Nat := 118140960795 + 5182172 * 2 ^ 59
def prefixEnd_5182172 : Nat := 4983230072969 + 3 ^ 40 * 5182172 * 2
def baseEnd_5182172 : Nat := 98553521121163109700653

theorem tailTrace_5182172 : CollatzResearch.WordTrace tailWord_5182172 prefixEnd_5182172 98553521121163109700653 := by
  unfold tailWord_5182172
  simp only [CollatzResearch.WordTrace]
  refine ⟨94504670290941681680358385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126006227054588908907144513 94504670290941681680358385)
  ·
    refine ⟨70878502718206261260268789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94504670290941681680358385 70878502718206261260268789)
    ·
      refine ⟨6644859629831836993150199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 70878502718206261260268789 6644859629831836993150199)
      ·
        refine ⟨9967289444747755489725299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6644859629831836993150199 9967289444747755489725299)
        ·
          refine ⟨14950934167121633234587949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9967289444747755489725299 14950934167121633234587949)
          ·
            refine ⟨5606600312670612462970481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14950934167121633234587949 5606600312670612462970481)
            ·
              refine ⟨4204950234502959347227861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5606600312670612462970481 4204950234502959347227861)
              ·
                refine ⟨98553521121163109700653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4204950234502959347227861 98553521121163109700653)
                ·
                  rfl

theorem cell23_5182172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 2, 7].length) (baseStart_5182172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5182172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5182172 prefixEnd_5182172 := by exact prefixLift 5182172
  have htrace : WordTrace (prefixWord ++ tailWord_5182172) baseStart_5182172 baseEnd_5182172 := by
    simpa [prefixWord, tailWord_5182172, baseEnd_5182172] using wordTrace_append hprefix tailTrace_5182172
  have hstable : (prefixWord ++ tailWord_5182172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5182172).length < 2 ^ (prefixWord ++ tailWord_5182172).sum := by decide
  have hdescent : baseEnd_5182172 < baseStart_5182172 := by decide
  rcases family_descends (prefixWord ++ tailWord_5182172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5182218 : List Nat := [3, 1, 2, 2, 1, 2, 2, 1, 1, 4, 4]
def baseStart_5182218 : Nat := 118140960795 + 5182218 * 2 ^ 59
def prefixEnd_5182218 : Nat := 4983230072969 + 3 ^ 40 * 5182218 * 2
def baseEnd_5182218 : Nat := 2660968690381510781942419

theorem tailTrace_5182218 : CollatzResearch.WordTrace tailWord_5182218 prefixEnd_5182218 2660968690381510781942419 := by
  unfold tailWord_5182218
  simp only [CollatzResearch.WordTrace]
  refine ⟨47252754584929178304222827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126007345559811142144594205 47252754584929178304222827)
  ·
    refine ⟨70879131877393767456334241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47252754584929178304222827 70879131877393767456334241)
    ·
      refine ⟨53159348908045325592250681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70879131877393767456334241 53159348908045325592250681)
      ·
        refine ⟨39869511681033994194188011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53159348908045325592250681 39869511681033994194188011)
        ·
          refine ⟨59804267521550991291282017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39869511681033994194188011 59804267521550991291282017)
          ·
            refine ⟨44853200641163243468461513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59804267521550991291282017 44853200641163243468461513)
            ·
              refine ⟨33639900480872432601346135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44853200641163243468461513 33639900480872432601346135)
              ·
                refine ⟨50459850721308648902019203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33639900480872432601346135 50459850721308648902019203)
                ·
                  refine ⟨75689776081962973353028805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50459850721308648902019203 75689776081962973353028805)
                  ·
                    refine ⟨14191833015368057503692901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 75689776081962973353028805 14191833015368057503692901)
                    ·
                      refine ⟨2660968690381510781942419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14191833015368057503692901 2660968690381510781942419)
                      ·
                        rfl

theorem cell23_5182218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 1, 1, 4, 4].length) (baseStart_5182218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5182218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5182218 prefixEnd_5182218 := by exact prefixLift 5182218
  have htrace : WordTrace (prefixWord ++ tailWord_5182218) baseStart_5182218 baseEnd_5182218 := by
    simpa [prefixWord, tailWord_5182218, baseEnd_5182218] using wordTrace_append hprefix tailTrace_5182218
  have hstable : (prefixWord ++ tailWord_5182218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5182218).length < 2 ^ (prefixWord ++ tailWord_5182218).sum := by decide
  have hdescent : baseEnd_5182218 < baseStart_5182218 := by decide
  rcases family_descends (prefixWord ++ tailWord_5182218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5182245 : List Nat := [1, 3, 1, 2, 3, 1, 2, 5, 5]
def baseStart_5182245 : Nat := 118140960795 + 5182245 * 2 ^ 59
def prefixEnd_5182245 : Nat := 4983230072969 + 3 ^ 40 * 5182245 * 2
def baseEnd_5182245 : Nat := 295664728262131352922755

theorem tailTrace_5182245 : CollatzResearch.WordTrace tailWord_5182245 prefixEnd_5182245 295664728262131352922755 := by
  unfold tailWord_5182245
  simp only [CollatzResearch.WordTrace]
  refine ⟨189012003110618896828124189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126008002073745931218749459 189012003110618896828124189)
  ·
    refine ⟨70879501166482086310546571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 189012003110618896828124189 70879501166482086310546571)
    ·
      refine ⟨106319251749723129465819857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70879501166482086310546571 106319251749723129465819857)
      ·
        refine ⟨79739438812292347099364893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106319251749723129465819857 79739438812292347099364893)
        ·
          refine ⟨29902289554609630162261835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79739438812292347099364893 29902289554609630162261835)
          ·
            refine ⟨44853434331914445243392753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29902289554609630162261835 44853434331914445243392753)
            ·
              refine ⟨33640075748935833932544565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44853434331914445243392753 33640075748935833932544565)
              ·
                refine ⟨3153757101462734431176053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33640075748935833932544565 3153757101462734431176053)
                ·
                  refine ⟨295664728262131352922755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3153757101462734431176053 295664728262131352922755)
                  ·
                    rfl

theorem cell23_5182245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 5, 5].length) (baseStart_5182245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5182245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5182245 prefixEnd_5182245 := by exact prefixLift 5182245
  have htrace : WordTrace (prefixWord ++ tailWord_5182245) baseStart_5182245 baseEnd_5182245 := by
    simpa [prefixWord, tailWord_5182245, baseEnd_5182245] using wordTrace_append hprefix tailTrace_5182245
  have hstable : (prefixWord ++ tailWord_5182245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5182245).length < 2 ^ (prefixWord ++ tailWord_5182245).sum := by decide
  have hdescent : baseEnd_5182245 < baseStart_5182245 := by decide
  rcases family_descends (prefixWord ++ tailWord_5182245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5182295 : List Nat := [1, 1, 3, 2, 4, 2, 1, 1, 1, 3, 4]
def baseStart_5182295 : Nat := 118140960795 + 5182295 * 2 ^ 59
def prefixEnd_5182295 : Nat := 4983230072969 + 3 ^ 40 * 5182295 * 2
def baseEnd_5182295 : Nat := 2661008228391906980679565

theorem tailTrace_5182295 : CollatzResearch.WordTrace tailWord_5182295 prefixEnd_5182295 2661008228391906980679565 := by
  unfold tailWord_5182295
  simp only [CollatzResearch.WordTrace]
  refine ⟨189013826760437755367444339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126009217840291836911629559 189013826760437755367444339)
  ·
    refine ⟨283520740140656633051166509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189013826760437755367444339 283520740140656633051166509)
    ·
      refine ⟨106320277552746237394187441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 283520740140656633051166509 106320277552746237394187441)
      ·
        refine ⟨79740208164559678045640581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106320277552746237394187441 79740208164559678045640581)
        ·
          refine ⟨14951289030854939633557609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 79740208164559678045640581 14951289030854939633557609)
          ·
            refine ⟨11213466773141204725168207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14951289030854939633557609 11213466773141204725168207)
            ·
              refine ⟨16820200159711807087752311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11213466773141204725168207 16820200159711807087752311)
              ·
                refine ⟨25230300239567710631628467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16820200159711807087752311 25230300239567710631628467)
                ·
                  refine ⟨37845450359351565947442701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25230300239567710631628467 37845450359351565947442701)
                  ·
                    refine ⟨14192043884756837230291013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37845450359351565947442701 14192043884756837230291013)
                    ·
                      refine ⟨2661008228391906980679565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14192043884756837230291013 2661008228391906980679565)
                      ·
                        rfl

theorem cell23_5182295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 1, 1, 3, 4].length) (baseStart_5182295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5182295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5182295 prefixEnd_5182295 := by exact prefixLift 5182295
  have htrace : WordTrace (prefixWord ++ tailWord_5182295) baseStart_5182295 baseEnd_5182295 := by
    simpa [prefixWord, tailWord_5182295, baseEnd_5182295] using wordTrace_append hprefix tailTrace_5182295
  have hstable : (prefixWord ++ tailWord_5182295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5182295).length < 2 ^ (prefixWord ++ tailWord_5182295).sum := by decide
  have hdescent : baseEnd_5182295 < baseStart_5182295 := by decide
  rcases family_descends (prefixWord ++ tailWord_5182295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5182312 : List Nat := [2, 1, 4, 2, 1, 2, 1, 2, 2, 4, 2]
def baseStart_5182312 : Nat := 118140960795 + 5182312 * 2 ^ 59
def prefixEnd_5182312 : Nat := 4983230072969 + 3 ^ 40 * 5182312 * 2
def baseEnd_5182312 : Nat := 2661016957563033414166987

theorem tailTrace_5182312 : CollatzResearch.WordTrace tailWord_5182312 prefixEnd_5182312 2661016957563033414166987 := by
  unfold tailWord_5182312
  simp only [CollatzResearch.WordTrace]
  refine ⟨94507223400688083635406595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126009631200917444847208793 94507223400688083635406595)
  ·
    refine ⟨141760835101032125453109893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94507223400688083635406595 141760835101032125453109893)
    ·
      refine ⟨26580156581443523522458105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 141760835101032125453109893 26580156581443523522458105)
      ·
        refine ⟨19935117436082642641843579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26580156581443523522458105 19935117436082642641843579)
        ·
          refine ⟨29902676154123963962765369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19935117436082642641843579 29902676154123963962765369)
          ·
            refine ⟨22427007115592972972074027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29902676154123963962765369 22427007115592972972074027)
            ·
              refine ⟨33640510673389459458111041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22427007115592972972074027 33640510673389459458111041)
              ·
                refine ⟨25230383005042094593583281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33640510673389459458111041 25230383005042094593583281)
                ·
                  refine ⟨18922787253781570945187461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25230383005042094593583281 18922787253781570945187461)
                  ·
                    refine ⟨3548022610084044552222649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18922787253781570945187461 3548022610084044552222649)
                    ·
                      refine ⟨2661016957563033414166987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3548022610084044552222649 2661016957563033414166987)
                      ·
                        rfl

theorem cell23_5182312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 2, 2, 4, 2].length) (baseStart_5182312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5182312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5182312 prefixEnd_5182312 := by exact prefixLift 5182312
  have htrace : WordTrace (prefixWord ++ tailWord_5182312) baseStart_5182312 baseEnd_5182312 := by
    simpa [prefixWord, tailWord_5182312, baseEnd_5182312] using wordTrace_append hprefix tailTrace_5182312
  have hstable : (prefixWord ++ tailWord_5182312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5182312).length < 2 ^ (prefixWord ++ tailWord_5182312).sum := by decide
  have hdescent : baseEnd_5182312 < baseStart_5182312 := by decide
  rcases family_descends (prefixWord ++ tailWord_5182312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5182315 : List Nat := [1, 1, 1, 1, 2, 2, 4, 4, 2, 2, 3]
def baseStart_5182315 : Nat := 118140960795 + 5182315 * 2 ^ 59
def prefixEnd_5182315 : Nat := 4983230072969 + 3 ^ 40 * 5182315 * 2
def baseEnd_5182315 : Nat := 2661018498004996902429473

theorem tailTrace_5182315 : CollatzResearch.WordTrace tailWord_5182315 prefixEnd_5182315 2661018498004996902429473 := by
  unfold tailWord_5182315
  simp only [CollatzResearch.WordTrace]
  refine ⟨189014556220365298783172399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126009704146910199188781599 189014556220365298783172399)
  ·
    refine ⟨283521834330547948174758599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189014556220365298783172399 283521834330547948174758599)
    ·
      refine ⟨425282751495821922262137899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 283521834330547948174758599 425282751495821922262137899)
      ·
        refine ⟨637924127243732883393206849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 425282751495821922262137899 637924127243732883393206849)
        ·
          refine ⟨478443095432799662544905137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 637924127243732883393206849 478443095432799662544905137)
          ·
            refine ⟨358832321574599746908678853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 478443095432799662544905137 358832321574599746908678853)
            ·
              refine ⟨67281060295237452545377285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 358832321574599746908678853 67281060295237452545377285)
              ·
                refine ⟨12615198805357022352258241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 67281060295237452545377285 12615198805357022352258241)
                ·
                  refine ⟨9461399104017766764193681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12615198805357022352258241 9461399104017766764193681)
                  ·
                    refine ⟨7096049328013325073145261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9461399104017766764193681 7096049328013325073145261)
                    ·
                      refine ⟨2661018498004996902429473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7096049328013325073145261 2661018498004996902429473)
                      ·
                        rfl

theorem cell23_5182315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 4, 2, 2, 3].length) (baseStart_5182315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5182315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5182315 prefixEnd_5182315 := by exact prefixLift 5182315
  have htrace : WordTrace (prefixWord ++ tailWord_5182315) baseStart_5182315 baseEnd_5182315 := by
    simpa [prefixWord, tailWord_5182315, baseEnd_5182315] using wordTrace_append hprefix tailTrace_5182315
  have hstable : (prefixWord ++ tailWord_5182315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5182315).length < 2 ^ (prefixWord ++ tailWord_5182315).sum := by decide
  have hdescent : baseEnd_5182315 < baseStart_5182315 := by decide
  rcases family_descends (prefixWord ++ tailWord_5182315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5182415 : List Nat := [1, 1, 2, 1, 1, 6, 1, 1, 3, 2, 4]
def baseStart_5182415 : Nat := 118140960795 + 5182415 * 2 ^ 59
def prefixEnd_5182415 : Nat := 4983230072969 + 3 ^ 40 * 5182415 * 2
def baseEnd_5182415 : Nat := 2661069846070446511179013

theorem tailTrace_5182415 : CollatzResearch.WordTrace tailWord_5182415 prefixEnd_5182415 2661069846070446511179013 := by
  unfold tailWord_5182415
  simp only [CollatzResearch.WordTrace]
  refine ⟨189018203520003015861812699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126012135680002010574541799 189018203520003015861812699)
  ·
    refine ⟨283527305280004523792719049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189018203520003015861812699 283527305280004523792719049)
    ·
      refine ⟨212645478960003392844539287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 283527305280004523792719049 212645478960003392844539287)
      ·
        refine ⟨318968218440005089266808931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212645478960003392844539287 318968218440005089266808931)
        ·
          refine ⟨478452327660007633900213397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 318968218440005089266808931 478452327660007633900213397)
          ·
            refine ⟨22427452859062857839072503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 478452327660007633900213397 22427452859062857839072503)
            ·
              refine ⟨33641179288594286758608755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22427452859062857839072503 33641179288594286758608755)
              ·
                refine ⟨50461768932891430137913133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33641179288594286758608755 50461768932891430137913133)
                ·
                  refine ⟨18923163349834286301717425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50461768932891430137913133 18923163349834286301717425)
                  ·
                    refine ⟨14192372512375714726288069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18923163349834286301717425 14192372512375714726288069)
                    ·
                      refine ⟨2661069846070446511179013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14192372512375714726288069 2661069846070446511179013)
                      ·
                        rfl

theorem cell23_5182415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 1, 3, 2, 4].length) (baseStart_5182415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5182415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5182415 prefixEnd_5182415 := by exact prefixLift 5182415
  have htrace : WordTrace (prefixWord ++ tailWord_5182415) baseStart_5182415 baseEnd_5182415 := by
    simpa [prefixWord, tailWord_5182415, baseEnd_5182415] using wordTrace_append hprefix tailTrace_5182415
  have hstable : (prefixWord ++ tailWord_5182415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5182415).length < 2 ^ (prefixWord ++ tailWord_5182415).sum := by decide
  have hdescent : baseEnd_5182415 < baseStart_5182415 := by decide
  rcases family_descends (prefixWord ++ tailWord_5182415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5182429 : List Nat := [1, 4, 3, 1, 2, 1, 1, 4, 2, 4]
def baseStart_5182429 : Nat := 118140960795 + 5182429 * 2 ^ 59
def prefixEnd_5182429 : Nat := 4983230072969 + 3 ^ 40 * 5182429 * 2
def baseEnd_5182429 : Nat := 887025678266536485467983

theorem tailTrace_5182429 : CollatzResearch.WordTrace tailWord_5182429 prefixEnd_5182429 887025678266536485467983 := by
  unfold tailWord_5182429
  simp only [CollatzResearch.WordTrace]
  refine ⟨189018714141952296252822341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126012476094634864168548227 189018714141952296252822341)
  ·
    refine ⟨35441008901616055547404189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 189018714141952296252822341 35441008901616055547404189)
    ·
      refine ⟨13290378338106020830276571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35441008901616055547404189 13290378338106020830276571)
      ·
        refine ⟨19935567507159031245414857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13290378338106020830276571 19935567507159031245414857)
        ·
          refine ⟨14951675630369273434061143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19935567507159031245414857 14951675630369273434061143)
          ·
            refine ⟨22427513445553910151091715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14951675630369273434061143 22427513445553910151091715)
            ·
              refine ⟨33641270168330865226637573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22427513445553910151091715 33641270168330865226637573)
              ·
                refine ⟨6307738156562037229994545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33641270168330865226637573 6307738156562037229994545)
                ·
                  refine ⟨4730803617421527922495909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6307738156562037229994545 4730803617421527922495909)
                  ·
                    refine ⟨887025678266536485467983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4730803617421527922495909 887025678266536485467983)
                    ·
                      rfl

theorem cell23_5182429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 4, 2, 4].length) (baseStart_5182429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5182429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5182429 prefixEnd_5182429 := by exact prefixLift 5182429
  have htrace : WordTrace (prefixWord ++ tailWord_5182429) baseStart_5182429 baseEnd_5182429 := by
    simpa [prefixWord, tailWord_5182429, baseEnd_5182429] using wordTrace_append hprefix tailTrace_5182429
  have hstable : (prefixWord ++ tailWord_5182429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5182429).length < 2 ^ (prefixWord ++ tailWord_5182429).sum := by decide
  have hdescent : baseEnd_5182429 < baseStart_5182429 := by decide
  rcases family_descends (prefixWord ++ tailWord_5182429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5182442 : List Nat := [3, 1, 3, 1, 2, 4, 1, 8]
def baseStart_5182442 : Nat := 118140960795 + 5182442 * 2 ^ 59
def prefixEnd_5182442 : Nat := 4983230072969 + 3 ^ 40 * 5182442 * 2
def baseEnd_5182442 : Nat := 98558655927708070575607

theorem tailTrace_5182442 : CollatzResearch.WordTrace tailWord_5182442 prefixEnd_5182442 98558655927708070575607 := by
  unfold tailWord_5182442
  simp only [CollatzResearch.WordTrace]
  refine ⟨47254797072726299868261395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126012792193936799648697053 47254797072726299868261395)
  ·
    refine ⟨70882195609089449802392093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47254797072726299868261395 70882195609089449802392093)
    ·
      refine ⟨26580823353408543675897035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70882195609089449802392093 26580823353408543675897035)
      ·
        refine ⟨39871235030112815513845553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26580823353408543675897035 39871235030112815513845553)
        ·
          refine ⟨29903426272584611635384165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39871235030112815513845553 29903426272584611635384165)
          ·
            refine ⟨5606892426109614681634531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29903426272584611635384165 5606892426109614681634531)
            ·
              refine ⟨8410338639164422022451797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5606892426109614681634531 8410338639164422022451797)
              ·
                refine ⟨98558655927708070575607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8410338639164422022451797 98558655927708070575607)
                ·
                  rfl

theorem cell23_5182442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 1, 8].length) (baseStart_5182442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5182442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5182442 prefixEnd_5182442 := by exact prefixLift 5182442
  have htrace : WordTrace (prefixWord ++ tailWord_5182442) baseStart_5182442 baseEnd_5182442 := by
    simpa [prefixWord, tailWord_5182442, baseEnd_5182442] using wordTrace_append hprefix tailTrace_5182442
  have hstable : (prefixWord ++ tailWord_5182442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5182442).length < 2 ^ (prefixWord ++ tailWord_5182442).sum := by decide
  have hdescent : baseEnd_5182442 < baseStart_5182442 := by decide
  rcases family_descends (prefixWord ++ tailWord_5182442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5182529 : List Nat := [1, 2, 5, 1, 3, 1, 1, 1, 2, 1, 5]
def baseStart_5182529 : Nat := 118140960795 + 5182529 * 2 ^ 59
def prefixEnd_5182529 : Nat := 4983230072969 + 3 ^ 40 * 5182529 * 2
def baseEnd_5182529 : Nat := 2661128382865059065153489

theorem tailTrace_5182529 : CollatzResearch.WordTrace tailWord_5182529 prefixEnd_5182529 2661128382865059065153489 := by
  unfold tailWord_5182529
  simp only [CollatzResearch.WordTrace]
  refine ⟨189022361441590013331462641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126014907627726675554308427 189022361441590013331462641)
  ·
    refine ⟨141766771081192509998596981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189022361441590013331462641 141766771081192509998596981)
    ·
      refine ⟨13290634788861797812368467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 141766771081192509998596981 13290634788861797812368467)
      ·
        refine ⟨19935952183292696718552701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13290634788861797812368467 19935952183292696718552701)
        ·
          refine ⟨7475982068734761269457263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19935952183292696718552701 7475982068734761269457263)
          ·
            refine ⟨11213973103102141904185895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7475982068734761269457263 11213973103102141904185895)
            ·
              refine ⟨16820959654653212856278843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11213973103102141904185895 16820959654653212856278843)
              ·
                refine ⟨25231439481979819284418265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16820959654653212856278843 25231439481979819284418265)
                ·
                  refine ⟨18923579611484864463313699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25231439481979819284418265 18923579611484864463313699)
                  ·
                    refine ⟨28385369417227296694970549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18923579611484864463313699 28385369417227296694970549)
                    ·
                      refine ⟨2661128382865059065153489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28385369417227296694970549 2661128382865059065153489)
                      ·
                        rfl

theorem cell23_5182529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 1, 2, 1, 5].length) (baseStart_5182529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5182529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5182529 prefixEnd_5182529 := by exact prefixLift 5182529
  have htrace : WordTrace (prefixWord ++ tailWord_5182529) baseStart_5182529 baseEnd_5182529 := by
    simpa [prefixWord, tailWord_5182529, baseEnd_5182529] using wordTrace_append hprefix tailTrace_5182529
  have hstable : (prefixWord ++ tailWord_5182529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5182529).length < 2 ^ (prefixWord ++ tailWord_5182529).sum := by decide
  have hdescent : baseEnd_5182529 < baseStart_5182529 := by decide
  rcases family_descends (prefixWord ++ tailWord_5182529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5182599 : List Nat := [1, 1, 4, 2, 1, 1, 1, 4, 2, 4, 2]
def baseStart_5182599 : Nat := 118140960795 + 5182599 * 2 ^ 59
def prefixEnd_5182599 : Nat := 4983230072969 + 3 ^ 40 * 5182599 * 2
def baseEnd_5182599 : Nat := 2661164326510873791278167

theorem tailTrace_5182599 : CollatzResearch.WordTrace tailWord_5182599 prefixEnd_5182599 2661164326510873791278167 := by
  unfold tailWord_5182599
  simp only [CollatzResearch.WordTrace]
  refine ⟨189024914551336415286510851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126016609700890943524340567 189024914551336415286510851)
  ·
    refine ⟨283537371827004622929766277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189024914551336415286510851 283537371827004622929766277)
    ·
      refine ⟨53163257217563366799331177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 283537371827004622929766277 53163257217563366799331177)
      ·
        refine ⟨39872442913172525099498383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53163257217563366799331177 39872442913172525099498383)
        ·
          refine ⟨59808664369758787649247575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39872442913172525099498383 59808664369758787649247575)
          ·
            refine ⟨89712996554638181473871363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59808664369758787649247575 89712996554638181473871363)
            ·
              refine ⟨134569494831957272210807045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89712996554638181473871363 134569494831957272210807045)
              ·
                refine ⟨25231780280991988539526321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 134569494831957272210807045 25231780280991988539526321)
                ·
                  refine ⟨18923835210743991404644741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25231780280991988539526321 18923835210743991404644741)
                  ·
                    refine ⟨3548219102014498388370889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18923835210743991404644741 3548219102014498388370889)
                    ·
                      refine ⟨2661164326510873791278167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3548219102014498388370889 2661164326510873791278167)
                      ·
                        rfl

theorem cell23_5182599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 4, 2, 4, 2].length) (baseStart_5182599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5182599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5182599 prefixEnd_5182599 := by exact prefixLift 5182599
  have htrace : WordTrace (prefixWord ++ tailWord_5182599) baseStart_5182599 baseEnd_5182599 := by
    simpa [prefixWord, tailWord_5182599, baseEnd_5182599] using wordTrace_append hprefix tailTrace_5182599
  have hstable : (prefixWord ++ tailWord_5182599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5182599).length < 2 ^ (prefixWord ++ tailWord_5182599).sum := by decide
  have hdescent : baseEnd_5182599 < baseStart_5182599 := by decide
  rcases family_descends (prefixWord ++ tailWord_5182599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5182600 : List Nat := [2, 1, 3, 4, 3, 1, 2, 2, 5]
def baseStart_5182600 : Nat := 118140960795 + 5182600 * 2 ^ 59
def prefixEnd_5182600 : Nat := 4983230072969 + 3 ^ 40 * 5182600 * 2
def baseEnd_5182600 : Nat := 295684982221280920818407

theorem tailTrace_5182600 : CollatzResearch.WordTrace tailWord_5182600 prefixEnd_5182600 295684982221280920818407 := by
  unfold tailWord_5182600
  simp only [CollatzResearch.WordTrace]
  refine ⟨94512475512166396228648627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126016634016221861638198169 94512475512166396228648627)
  ·
    refine ⟨141768713268249594342972941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94512475512166396228648627 141768713268249594342972941)
    ·
      refine ⟨53163267475593597878614853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141768713268249594342972941 53163267475593597878614853)
      ·
        refine ⟨9968112651673799602240285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53163267475593597878614853 9968112651673799602240285)
        ·
          refine ⟨3738042244377674850840107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9968112651673799602240285 3738042244377674850840107)
          ·
            refine ⟨5607063366566512276260161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3738042244377674850840107 5607063366566512276260161)
            ·
              refine ⟨4205297524924884207195121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5607063366566512276260161 4205297524924884207195121)
              ·
                refine ⟨3153973143693663155396341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4205297524924884207195121 3153973143693663155396341)
                ·
                  refine ⟨295684982221280920818407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3153973143693663155396341 295684982221280920818407)
                  ·
                    rfl

theorem cell23_5182600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 2, 2, 5].length) (baseStart_5182600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5182600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5182600 prefixEnd_5182600 := by exact prefixLift 5182600
  have htrace : WordTrace (prefixWord ++ tailWord_5182600) baseStart_5182600 baseEnd_5182600 := by
    simpa [prefixWord, tailWord_5182600, baseEnd_5182600] using wordTrace_append hprefix tailTrace_5182600
  have hstable : (prefixWord ++ tailWord_5182600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5182600).length < 2 ^ (prefixWord ++ tailWord_5182600).sum := by decide
  have hdescent : baseEnd_5182600 < baseStart_5182600 := by decide
  rcases family_descends (prefixWord ++ tailWord_5182600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5182602 : List Nat := [3, 1, 2, 3, 1, 1, 1, 1, 2, 3, 5]
def baseStart_5182602 : Nat := 118140960795 + 5182602 * 2 ^ 59
def prefixEnd_5182602 : Nat := 4983230072969 + 3 ^ 40 * 5182602 * 2
def baseEnd_5182602 : Nat := 2661165866952837279540653

theorem tailTrace_5182602 : CollatzResearch.WordTrace tailWord_5182602 prefixEnd_5182602 2661165866952837279540653 := by
  unfold tailWord_5182602
  simp only [CollatzResearch.WordTrace]
  refine ⟨47256255992581386699717515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126016682646883697865913373 47256255992581386699717515)
  ·
    refine ⟨70884383988872080049576273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47256255992581386699717515 70884383988872080049576273)
    ·
      refine ⟨53163287991654060037182205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70884383988872080049576273 53163287991654060037182205)
      ·
        refine ⟨19936232996870272513943327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53163287991654060037182205 19936232996870272513943327)
        ·
          refine ⟨29904349495305408770914991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19936232996870272513943327 29904349495305408770914991)
          ·
            refine ⟨44856524242958113156372487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29904349495305408770914991 44856524242958113156372487)
            ·
              refine ⟨67284786364437169734558731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44856524242958113156372487 67284786364437169734558731)
              ·
                refine ⟨100927179546655754601838097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67284786364437169734558731 100927179546655754601838097)
                ·
                  refine ⟨75695384659991815951378573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 100927179546655754601838097 75695384659991815951378573)
                  ·
                    refine ⟨28385769247496930981766965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 75695384659991815951378573 28385769247496930981766965)
                    ·
                      refine ⟨2661165866952837279540653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28385769247496930981766965 2661165866952837279540653)
                      ·
                        rfl

theorem cell23_5182602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_5182602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5182602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5182602 prefixEnd_5182602 := by exact prefixLift 5182602
  have htrace : WordTrace (prefixWord ++ tailWord_5182602) baseStart_5182602 baseEnd_5182602 := by
    simpa [prefixWord, tailWord_5182602, baseEnd_5182602] using wordTrace_append hprefix tailTrace_5182602
  have hstable : (prefixWord ++ tailWord_5182602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5182602).length < 2 ^ (prefixWord ++ tailWord_5182602).sum := by decide
  have hdescent : baseEnd_5182602 < baseStart_5182602 := by decide
  rcases family_descends (prefixWord ++ tailWord_5182602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5182616 : List Nat := [2, 1, 2, 4, 2, 2, 1, 1, 2, 4, 2]
def baseStart_5182616 : Nat := 118140960795 + 5182616 * 2 ^ 59
def prefixEnd_5182616 : Nat := 4983230072969 + 3 ^ 40 * 5182616 * 2
def baseEnd_5182616 : Nat := 2661173055682000224765589

theorem tailTrace_5182616 : CollatzResearch.WordTrace tailWord_5182616 prefixEnd_5182616 2661173055682000224765589 := by
  unfold tailWord_5182616
  simp only [CollatzResearch.WordTrace]
  refine ⟨94512767296137413594939851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126017023061516551459919801 94512767296137413594939851)
  ·
    refine ⟨141769150944206120392409777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94512767296137413594939851 141769150944206120392409777)
    ·
      refine ⟨106326863208154590294307333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141769150944206120392409777 106326863208154590294307333)
      ·
        refine ⟨19936286851528985680182625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 106326863208154590294307333 19936286851528985680182625)
        ·
          refine ⟨14952215138646739260136969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19936286851528985680182625 14952215138646739260136969)
          ·
            refine ⟨11214161353985054445102727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14952215138646739260136969 11214161353985054445102727)
            ·
              refine ⟨16821242030977581667654091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11214161353985054445102727 16821242030977581667654091)
              ·
                refine ⟨25231863046466372501481137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16821242030977581667654091 25231863046466372501481137)
                ·
                  refine ⟨18923897284849779376110853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25231863046466372501481137 18923897284849779376110853)
                  ·
                    refine ⟨3548230740909333633020785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18923897284849779376110853 3548230740909333633020785)
                    ·
                      refine ⟨2661173055682000224765589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3548230740909333633020785 2661173055682000224765589)
                      ·
                        rfl

theorem cell23_5182616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 1, 2, 4, 2].length) (baseStart_5182616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5182616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5182616 prefixEnd_5182616 := by exact prefixLift 5182616
  have htrace : WordTrace (prefixWord ++ tailWord_5182616) baseStart_5182616 baseEnd_5182616 := by
    simpa [prefixWord, tailWord_5182616, baseEnd_5182616] using wordTrace_append hprefix tailTrace_5182616
  have hstable : (prefixWord ++ tailWord_5182616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5182616).length < 2 ^ (prefixWord ++ tailWord_5182616).sum := by decide
  have hdescent : baseEnd_5182616 < baseStart_5182616 := by decide
  rcases family_descends (prefixWord ++ tailWord_5182616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5182656 : List Nat := [2, 1, 1, 2, 6, 2, 1, 2, 6]
def baseStart_5182656 : Nat := 118140960795 + 5182656 * 2 ^ 59
def prefixEnd_5182656 : Nat := 4983230072969 + 3 ^ 40 * 5182656 * 2
def baseEnd_5182656 : Nat := 295688177212020007585045

theorem tailTrace_5182656 : CollatzResearch.WordTrace tailWord_5182656 prefixEnd_5182656 295688177212020007585045 := by
  unfold tailWord_5182656
  simp only [CollatzResearch.WordTrace]
  refine ⟨94513496756064957010667911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126017995674753276014223881 94513496756064957010667911)
  ·
    refine ⟨141770245134097435516001867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94513496756064957010667911 141770245134097435516001867)
    ·
      refine ⟨212655367701146153274002801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141770245134097435516001867 212655367701146153274002801)
      ·
        refine ⟨159491525775859614955502101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 212655367701146153274002801 159491525775859614955502101)
        ·
          refine ⟨7476165270743419451039161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 159491525775859614955502101 7476165270743419451039161)
          ·
            refine ⟨5607123953057564588279371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7476165270743419451039161 5607123953057564588279371)
            ·
              refine ⟨8410685929586346882419057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5607123953057564588279371 8410685929586346882419057)
              ·
                refine ⟨6308014447189760161814293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8410685929586346882419057 6308014447189760161814293)
                ·
                  refine ⟨295688177212020007585045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6308014447189760161814293 295688177212020007585045)
                  ·
                    rfl

theorem cell23_5182656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 1, 2, 6].length) (baseStart_5182656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5182656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5182656 prefixEnd_5182656 := by exact prefixLift 5182656
  have htrace : WordTrace (prefixWord ++ tailWord_5182656) baseStart_5182656 baseEnd_5182656 := by
    simpa [prefixWord, tailWord_5182656, baseEnd_5182656] using wordTrace_append hprefix tailTrace_5182656
  have hstable : (prefixWord ++ tailWord_5182656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5182656).length < 2 ^ (prefixWord ++ tailWord_5182656).sum := by decide
  have hdescent : baseEnd_5182656 < baseStart_5182656 := by decide
  rcases family_descends (prefixWord ++ tailWord_5182656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5182666 : List Nat := [3, 1, 2, 1, 3, 2, 1, 3, 3, 1, 3]
def baseStart_5182666 : Nat := 118140960795 + 5182666 * 2 ^ 59
def prefixEnd_5182666 : Nat := 4983230072969 + 3 ^ 40 * 5182666 * 2
def baseEnd_5182666 : Nat := 2661198729714725029140359

theorem tailTrace_5182666 : CollatzResearch.WordTrace tailWord_5182666 prefixEnd_5182666 2661198729714725029140359 := by
  unfold tailWord_5182666
  simp only [CollatzResearch.WordTrace]
  refine ⟨47256839560523421432299963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126018238828062457152799901 47256839560523421432299963)
  ·
    refine ⟨70885259340785132148449945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47256839560523421432299963 70885259340785132148449945)
    ·
      refine ⟨53163944505588849111337459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70885259340785132148449945 53163944505588849111337459)
      ·
        refine ⟨79745916758383273667006189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53163944505588849111337459 79745916758383273667006189)
        ·
          refine ⟨29904718784393727625127321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79745916758383273667006189 29904718784393727625127321)
          ·
            refine ⟨22428539088295295718845491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29904718784393727625127321 22428539088295295718845491)
            ·
              refine ⟨33642808632442943578268237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22428539088295295718845491 33642808632442943578268237)
              ·
                refine ⟨12616053237166103841850589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33642808632442943578268237 12616053237166103841850589)
                ·
                  refine ⟨4731019963937288940693971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12616053237166103841850589 4731019963937288940693971)
                  ·
                    refine ⟨7096529945905933411040957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4731019963937288940693971 7096529945905933411040957)
                    ·
                      refine ⟨2661198729714725029140359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7096529945905933411040957 2661198729714725029140359)
                      ·
                        rfl

theorem cell23_5182666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 3, 3, 1, 3].length) (baseStart_5182666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5182666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5182666 prefixEnd_5182666 := by exact prefixLift 5182666
  have htrace : WordTrace (prefixWord ++ tailWord_5182666) baseStart_5182666 baseEnd_5182666 := by
    simpa [prefixWord, tailWord_5182666, baseEnd_5182666] using wordTrace_append hprefix tailTrace_5182666
  have hstable : (prefixWord ++ tailWord_5182666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5182666).length < 2 ^ (prefixWord ++ tailWord_5182666).sum := by decide
  have hdescent : baseEnd_5182666 < baseStart_5182666 := by decide
  rcases family_descends (prefixWord ++ tailWord_5182666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5182699 : List Nat := [1, 1, 1, 1, 2, 6, 1, 2, 4, 4]
def baseStart_5182699 : Nat := 118140960795 + 5182699 * 2 ^ 59
def prefixEnd_5182699 : Nat := 4983230072969 + 3 ^ 40 * 5182699 * 2
def baseEnd_5182699 : Nat := 887071891525441133342569

theorem tailTrace_5182699 : CollatzResearch.WordTrace tailWord_5182699 prefixEnd_5182699 887071891525441133342569 := by
  unfold tailWord_5182699
  simp only [CollatzResearch.WordTrace]
  refine ⟨189028561850974132365151151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126019041233982754910100767 189028561850974132365151151)
  ·
    refine ⟨283542842776461198547726727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189028561850974132365151151 283542842776461198547726727)
    ·
      refine ⟨425314264164691797821590091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 283542842776461198547726727 425314264164691797821590091)
      ·
        refine ⟨637971396247037696732385137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 425314264164691797821590091 637971396247037696732385137)
        ·
          refine ⟨478478547185278272549288853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 637971396247037696732385137 478478547185278272549288853)
          ·
            refine ⟨22428681899309919025747915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 478478547185278272549288853 22428681899309919025747915)
            ·
              refine ⟨33643022848964878538621873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22428681899309919025747915 33643022848964878538621873)
              ·
                refine ⟨25232267136723658903966405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33643022848964878538621873 25232267136723658903966405)
                ·
                  refine ⟨4731050088135686044493701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25232267136723658903966405 4731050088135686044493701)
                  ·
                    refine ⟨887071891525441133342569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4731050088135686044493701 887071891525441133342569)
                    ·
                      rfl

theorem cell23_5182699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 2, 4, 4].length) (baseStart_5182699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5182699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5182699 prefixEnd_5182699 := by exact prefixLift 5182699
  have htrace : WordTrace (prefixWord ++ tailWord_5182699) baseStart_5182699 baseEnd_5182699 := by
    simpa [prefixWord, tailWord_5182699, baseEnd_5182699] using wordTrace_append hprefix tailTrace_5182699
  have hstable : (prefixWord ++ tailWord_5182699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5182699).length < 2 ^ (prefixWord ++ tailWord_5182699).sum := by decide
  have hdescent : baseEnd_5182699 < baseStart_5182699 := by decide
  rcases family_descends (prefixWord ++ tailWord_5182699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5182700 : List Nat := [2, 2, 1, 1, 2, 6, 1, 3, 1, 1, 3]
def baseStart_5182700 : Nat := 118140960795 + 5182700 * 2 ^ 59
def prefixEnd_5182700 : Nat := 4983230072969 + 3 ^ 40 * 5182700 * 2
def baseEnd_5182700 : Nat := 2661216188056977896115203

theorem tailTrace_5182700 : CollatzResearch.WordTrace tailWord_5182700 prefixEnd_5182700 2661216188056977896115203 := by
  unfold tailWord_5182700
  simp only [CollatzResearch.WordTrace]
  refine ⟨94514299161985254767968777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126019065549313673023958369 94514299161985254767968777)
  ·
    refine ⟨70885724371488941075976583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94514299161985254767968777 70885724371488941075976583)
    ·
      refine ⟨106328586557233411613964875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70885724371488941075976583 106328586557233411613964875)
      ·
        refine ⟨159492879835850117420947313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106328586557233411613964875 159492879835850117420947313)
        ·
          refine ⟨119619659876887588065710485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 159492879835850117420947313 119619659876887588065710485)
          ·
            refine ⟨5607171556729105690580179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 119619659876887588065710485 5607171556729105690580179)
            ·
              refine ⟨8410757335093658535870269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5607171556729105690580179 8410757335093658535870269)
              ·
                refine ⟨3154034000660121950951351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8410757335093658535870269 3154034000660121950951351)
                ·
                  refine ⟨4731051000990182926427027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3154034000660121950951351 4731051000990182926427027)
                  ·
                    refine ⟨7096576501485274389640541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4731051000990182926427027 7096576501485274389640541)
                    ·
                      refine ⟨2661216188056977896115203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7096576501485274389640541 2661216188056977896115203)
                      ·
                        rfl

theorem cell23_5182700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 1, 3, 1, 1, 3].length) (baseStart_5182700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5182700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5182700 prefixEnd_5182700 := by exact prefixLift 5182700
  have htrace : WordTrace (prefixWord ++ tailWord_5182700) baseStart_5182700 baseEnd_5182700 := by
    simpa [prefixWord, tailWord_5182700, baseEnd_5182700] using wordTrace_append hprefix tailTrace_5182700
  have hstable : (prefixWord ++ tailWord_5182700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5182700).length < 2 ^ (prefixWord ++ tailWord_5182700).sum := by decide
  have hdescent : baseEnd_5182700 < baseStart_5182700 := by decide
  rcases family_descends (prefixWord ++ tailWord_5182700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5182723 : List Nat := [1, 1, 1, 3, 2, 4, 3, 1, 3, 2, 2]
def baseStart_5182723 : Nat := 118140960795 + 5182723 * 2 ^ 59
def prefixEnd_5182723 : Nat := 4983230072969 + 3 ^ 40 * 5182723 * 2
def baseEnd_5182723 : Nat := 2661227998112031306127597

theorem tailTrace_5182723 : CollatzResearch.WordTrace tailWord_5182723 prefixEnd_5182723 2661227998112031306127597 := by
  unfold tailWord_5182723
  simp only [CollatzResearch.WordTrace]
  refine ⟨189029437202887184464024823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126019624801924789642683215 189029437202887184464024823)
  ·
    refine ⟨283544155804330776696037235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189029437202887184464024823 283544155804330776696037235)
    ·
      refine ⟨425316233706496165044055853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 283544155804330776696037235 425316233706496165044055853)
      ·
        refine ⟨159493587639936061891520945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 425316233706496165044055853 159493587639936061891520945)
        ·
          refine ⟨119620190729952046418640709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 159493587639936061891520945 119620190729952046418640709)
          ·
            refine ⟨22428785761866008703495133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 119620190729952046418640709 22428785761866008703495133)
            ·
              refine ⟨8410794660699753263810675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22428785761866008703495133 8410794660699753263810675)
              ·
                refine ⟨12616191991049629895716013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8410794660699753263810675 12616191991049629895716013)
                ·
                  refine ⟨4731071996643611210893505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12616191991049629895716013 4731071996643611210893505)
                  ·
                    refine ⟨3548303997482708408170129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4731071996643611210893505 3548303997482708408170129)
                    ·
                      refine ⟨2661227998112031306127597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3548303997482708408170129 2661227998112031306127597)
                      ·
                        rfl

theorem cell23_5182723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 3, 1, 3, 2, 2].length) (baseStart_5182723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5182723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5182723 prefixEnd_5182723 := by exact prefixLift 5182723
  have htrace : WordTrace (prefixWord ++ tailWord_5182723) baseStart_5182723 baseEnd_5182723 := by
    simpa [prefixWord, tailWord_5182723, baseEnd_5182723] using wordTrace_append hprefix tailTrace_5182723
  have hstable : (prefixWord ++ tailWord_5182723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5182723).length < 2 ^ (prefixWord ++ tailWord_5182723).sum := by decide
  have hdescent : baseEnd_5182723 < baseStart_5182723 := by decide
  rcases family_descends (prefixWord ++ tailWord_5182723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5182756 : List Nat := [2, 3, 1, 3, 1, 1, 3, 2, 1, 3, 3]
def baseStart_5182756 : Nat := 118140960795 + 5182756 * 2 ^ 59
def prefixEnd_5182756 : Nat := 4983230072969 + 3 ^ 40 * 5182756 * 2
def baseEnd_5182756 : Nat := 2661244942973629677014945

theorem tailTrace_5182756 : CollatzResearch.WordTrace tailWord_5182756 prefixEnd_5182756 2661244942973629677014945 := by
  unfold tailWord_5182756
  simp only [CollatzResearch.WordTrace]
  refine ⟨94515320405883815549988061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126020427207845087399984081 94515320405883815549988061)
  ·
    refine ⟨35443245152206430831245523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94515320405883815549988061 35443245152206430831245523)
    ·
      refine ⟨53164867728309646246868285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35443245152206430831245523 53164867728309646246868285)
      ·
        refine ⟨19936825398116117342575607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53164867728309646246868285 19936825398116117342575607)
        ·
          refine ⟨29905238097174176013863411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19936825398116117342575607 29905238097174176013863411)
          ·
            refine ⟨44857857145761264020795117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29905238097174176013863411 44857857145761264020795117)
            ·
              refine ⟨16821696429660474007798169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44857857145761264020795117 16821696429660474007798169)
              ·
                refine ⟨12616272322245355505848627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16821696429660474007798169 12616272322245355505848627)
                ·
                  refine ⟨18924408483368033258772941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12616272322245355505848627 18924408483368033258772941)
                  ·
                    refine ⟨7096653181263012472039853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18924408483368033258772941 7096653181263012472039853)
                    ·
                      refine ⟨2661244942973629677014945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7096653181263012472039853 2661244942973629677014945)
                      ·
                        rfl

theorem cell23_5182756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 2, 1, 3, 3].length) (baseStart_5182756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5182756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5182756 prefixEnd_5182756 := by exact prefixLift 5182756
  have htrace : WordTrace (prefixWord ++ tailWord_5182756) baseStart_5182756 baseEnd_5182756 := by
    simpa [prefixWord, tailWord_5182756, baseEnd_5182756] using wordTrace_append hprefix tailTrace_5182756
  have hstable : (prefixWord ++ tailWord_5182756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5182756).length < 2 ^ (prefixWord ++ tailWord_5182756).sum := by decide
  have hdescent : baseEnd_5182756 < baseStart_5182756 := by decide
  rcases family_descends (prefixWord ++ tailWord_5182756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5182760 : List Nat := [2, 1, 5, 1, 2, 2, 3, 1, 1, 2, 3]
def baseStart_5182760 : Nat := 118140960795 + 5182760 * 2 ^ 59
def prefixEnd_5182760 : Nat := 4983230072969 + 3 ^ 40 * 5182760 * 2
def baseEnd_5182760 : Nat := 2661246996896247661364927

theorem tailTrace_5182760 : CollatzResearch.WordTrace tailWord_5182760 prefixEnd_5182760 2661246996896247661364927 := by
  unfold tailWord_5182760
  simp only [CollatzResearch.WordTrace]
  refine ⟨94515393351876569891560867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126020524469168759855414489 94515393351876569891560867)
  ·
    refine ⟨141773090027814854837341301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94515393351876569891560867 141773090027814854837341301)
    ·
      refine ⟨13291227190107642641000747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 141773090027814854837341301 13291227190107642641000747)
      ·
        refine ⟨19936840785161463961501121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13291227190107642641000747 19936840785161463961501121)
        ·
          refine ⟨14952630588871097971125841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19936840785161463961501121 14952630588871097971125841)
          ·
            refine ⟨11214472941653323478344381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14952630588871097971125841 11214472941653323478344381)
            ·
              refine ⟨4205427353119996304379143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11214472941653323478344381 4205427353119996304379143)
              ·
                refine ⟨6308141029679994456568715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4205427353119996304379143 6308141029679994456568715)
                ·
                  refine ⟨9462211544519991684853073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6308141029679994456568715 9462211544519991684853073)
                  ·
                    refine ⟨7096658658389993763639805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9462211544519991684853073 7096658658389993763639805)
                    ·
                      refine ⟨2661246996896247661364927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7096658658389993763639805 2661246996896247661364927)
                      ·
                        rfl

theorem cell23_5182760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 3, 1, 1, 2, 3].length) (baseStart_5182760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5182760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5182760 prefixEnd_5182760 := by exact prefixLift 5182760
  have htrace : WordTrace (prefixWord ++ tailWord_5182760) baseStart_5182760 baseEnd_5182760 := by
    simpa [prefixWord, tailWord_5182760, baseEnd_5182760] using wordTrace_append hprefix tailTrace_5182760
  have hstable : (prefixWord ++ tailWord_5182760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5182760).length < 2 ^ (prefixWord ++ tailWord_5182760).sum := by decide
  have hdescent : baseEnd_5182760 < baseStart_5182760 := by decide
  rcases family_descends (prefixWord ++ tailWord_5182760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5182773 : List Nat := [1, 3, 3, 1, 2, 2, 1, 4, 2, 1, 3]
def baseStart_5182773 : Nat := 118140960795 + 5182773 * 2 ^ 59
def prefixEnd_5182773 : Nat := 4983230072969 + 3 ^ 40 * 5182773 * 2
def baseEnd_5182773 : Nat := 2661253672144756110502367

theorem tailTrace_5182773 : CollatzResearch.WordTrace tailWord_5182773 prefixEnd_5182773 2661253672144756110502367 := by
  unfold tailWord_5182773
  simp only [CollatzResearch.WordTrace]
  refine ⟨189031260852706043003344973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126020840568470695335563315 189031260852706043003344973)
  ·
    refine ⟨70886722819764766126254365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 189031260852706043003344973 70886722819764766126254365)
    ·
      refine ⟨26582521057411787297345387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70886722819764766126254365 26582521057411787297345387)
      ·
        refine ⟨39873781586117680946018081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26582521057411787297345387 39873781586117680946018081)
        ·
          refine ⟨29905336189588260709513561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39873781586117680946018081 29905336189588260709513561)
          ·
            refine ⟨22429002142191195532135171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29905336189588260709513561 22429002142191195532135171)
            ·
              refine ⟨33643503213286793298202757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22429002142191195532135171 33643503213286793298202757)
              ·
                refine ⟨6308156852491273743413017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33643503213286793298202757 6308156852491273743413017)
                ·
                  refine ⟨4731117639368455307559763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6308156852491273743413017 4731117639368455307559763)
                  ·
                    refine ⟨7096676459052682961339645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4731117639368455307559763 7096676459052682961339645)
                    ·
                      refine ⟨2661253672144756110502367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7096676459052682961339645 2661253672144756110502367)
                      ·
                        rfl

theorem cell23_5182773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 4, 2, 1, 3].length) (baseStart_5182773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5182773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5182773 prefixEnd_5182773 := by exact prefixLift 5182773
  have htrace : WordTrace (prefixWord ++ tailWord_5182773) baseStart_5182773 baseEnd_5182773 := by
    simpa [prefixWord, tailWord_5182773, baseEnd_5182773] using wordTrace_append hprefix tailTrace_5182773
  have hstable : (prefixWord ++ tailWord_5182773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5182773).length < 2 ^ (prefixWord ++ tailWord_5182773).sum := by decide
  have hdescent : baseEnd_5182773 < baseStart_5182773 := by decide
  rcases family_descends (prefixWord ++ tailWord_5182773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5182893 : List Nat := [1, 5, 2, 2, 1, 2, 1, 1, 1, 2, 5]
def baseStart_5182893 : Nat := 118140960795 + 5182893 * 2 ^ 59
def prefixEnd_5182893 : Nat := 4983230072969 + 3 ^ 40 * 5182893 * 2
def baseEnd_5182893 : Nat := 2661315289823295641001815

theorem tailTrace_5182893 : CollatzResearch.WordTrace tailWord_5182893 prefixEnd_5182893 2661315289823295641001815 := by
  unfold tailWord_5182893
  simp only [CollatzResearch.WordTrace]
  refine ⟨189035637612271303497713333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126023758408180868998475555 189035637612271303497713333)
  ·
    refine ⟨17722091026150434702910625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 189035637612271303497713333 17722091026150434702910625)
    ·
      refine ⟨13291568269612826027182969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17722091026150434702910625 13291568269612826027182969)
      ·
        refine ⟨9968676202209619520387227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13291568269612826027182969 9968676202209619520387227)
        ·
          refine ⟨14953014303314429280580841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9968676202209619520387227 14953014303314429280580841)
          ·
            refine ⟨11214760727485821960435631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14953014303314429280580841 11214760727485821960435631)
            ·
              refine ⟨16822141091228732940653447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11214760727485821960435631 16822141091228732940653447)
              ·
                refine ⟨25233211636843099410980171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16822141091228732940653447 25233211636843099410980171)
                ·
                  refine ⟨37849817455264649116470257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25233211636843099410980171 37849817455264649116470257)
                  ·
                    refine ⟨28387363091448486837352693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37849817455264649116470257 28387363091448486837352693)
                    ·
                      refine ⟨2661315289823295641001815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28387363091448486837352693 2661315289823295641001815)
                      ·
                        rfl

theorem cell23_5182893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_5182893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5182893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5182893 prefixEnd_5182893 := by exact prefixLift 5182893
  have htrace : WordTrace (prefixWord ++ tailWord_5182893) baseStart_5182893 baseEnd_5182893 := by
    simpa [prefixWord, tailWord_5182893, baseEnd_5182893] using wordTrace_append hprefix tailTrace_5182893
  have hstable : (prefixWord ++ tailWord_5182893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5182893).length < 2 ^ (prefixWord ++ tailWord_5182893).sum := by decide
  have hdescent : baseEnd_5182893 < baseStart_5182893 := by decide
  rcases family_descends (prefixWord ++ tailWord_5182893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5182896 : List Nat := [2, 1, 1, 1, 2, 1, 1, 7, 3, 4]
def baseStart_5182896 : Nat := 118140960795 + 5182896 * 2 ^ 59
def prefixEnd_5182896 : Nat := 4983230072969 + 3 ^ 40 * 5182896 * 2
def baseEnd_5182896 : Nat := 887105610088419709754767

theorem tailTrace_5182896 : CollatzResearch.WordTrace tailWord_5182896 prefixEnd_5182896 887105610088419709754767 := by
  unfold tailWord_5182896
  simp only [CollatzResearch.WordTrace]
  refine ⟨94517873515630217505036271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126023831354173623340048361 94517873515630217505036271)
  ·
    refine ⟨141776810273445326257554407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94517873515630217505036271 141776810273445326257554407)
    ·
      refine ⟨212665215410167989386331611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141776810273445326257554407 212665215410167989386331611)
      ·
        refine ⟨318997823115251984079497417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212665215410167989386331611 318997823115251984079497417)
        ·
          refine ⟨239248367336438988059623063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 318997823115251984079497417 239248367336438988059623063)
          ·
            refine ⟨358872551004658482089434595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 239248367336438988059623063 358872551004658482089434595)
            ·
              refine ⟨538308826506987723134151893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 358872551004658482089434595 538308826506987723134151893)
              ·
                refine ⟨12616613121257524760956685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 538308826506987723134151893 12616613121257524760956685)
                ·
                  refine ⟨4731229920471571785358757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12616613121257524760956685 4731229920471571785358757)
                  ·
                    refine ⟨887105610088419709754767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4731229920471571785358757 887105610088419709754767)
                    ·
                      rfl

theorem cell23_5182896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 7, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 7, 3, 4].length) (baseStart_5182896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5182896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5182896 prefixEnd_5182896 := by exact prefixLift 5182896
  have htrace : WordTrace (prefixWord ++ tailWord_5182896) baseStart_5182896 baseEnd_5182896 := by
    simpa [prefixWord, tailWord_5182896, baseEnd_5182896] using wordTrace_append hprefix tailTrace_5182896
  have hstable : (prefixWord ++ tailWord_5182896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5182896).length < 2 ^ (prefixWord ++ tailWord_5182896).sum := by decide
  have hdescent : baseEnd_5182896 < baseStart_5182896 := by decide
  rcases family_descends (prefixWord ++ tailWord_5182896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5182899 : List Nat := [1, 1, 1, 2, 3, 1, 1, 4, 2, 1, 6]
def baseStart_5182899 : Nat := 118140960795 + 5182899 * 2 ^ 59
def prefixEnd_5182899 : Nat := 4983230072969 + 3 ^ 40 * 5182899 * 2
def baseEnd_5182899 : Nat := 2661318370707222617526787

theorem tailTrace_5182899 : CollatzResearch.WordTrace tailWord_5182899 prefixEnd_5182899 2661318370707222617526787 := by
  unfold tailWord_5182899
  simp only [CollatzResearch.WordTrace]
  refine ⟨189035856450249566522431751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126023904300166377681621167 189035856450249566522431751)
  ·
    refine ⟨283553784675374349783647627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189035856450249566522431751 283553784675374349783647627)
    ·
      refine ⟨425330677013061524675471441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 283553784675374349783647627 425330677013061524675471441)
      ·
        refine ⟨318998007759796143506603581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 425330677013061524675471441 318998007759796143506603581)
        ·
          refine ⟨119624252909923553814976343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 318998007759796143506603581 119624252909923553814976343)
          ·
            refine ⟨179436379364885330722464515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119624252909923553814976343 179436379364885330722464515)
            ·
              refine ⟨269154569047327996083696773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 179436379364885330722464515 269154569047327996083696773)
              ·
                refine ⟨50466481696373999265693145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 269154569047327996083696773 50466481696373999265693145)
                ·
                  refine ⟨37849861272280499449269859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50466481696373999265693145 37849861272280499449269859)
                  ·
                    refine ⟨56774791908420749173904789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37849861272280499449269859 56774791908420749173904789)
                    ·
                      refine ⟨2661318370707222617526787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56774791908420749173904789 2661318370707222617526787)
                      ·
                        rfl

theorem cell23_5182899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 4, 2, 1, 6].length) (baseStart_5182899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5182899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5182899 prefixEnd_5182899 := by exact prefixLift 5182899
  have htrace : WordTrace (prefixWord ++ tailWord_5182899) baseStart_5182899 baseEnd_5182899 := by
    simpa [prefixWord, tailWord_5182899, baseEnd_5182899] using wordTrace_append hprefix tailTrace_5182899
  have hstable : (prefixWord ++ tailWord_5182899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5182899).length < 2 ^ (prefixWord ++ tailWord_5182899).sum := by decide
  have hdescent : baseEnd_5182899 < baseStart_5182899 := by decide
  rcases family_descends (prefixWord ++ tailWord_5182899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5182929 : List Nat := [1, 2, 2, 1, 2, 1, 1, 1, 3, 1, 8]
def baseStart_5182929 : Nat := 118140960795 + 5182929 * 2 ^ 59
def prefixEnd_5182929 : Nat := 4983230072969 + 3 ^ 40 * 5182929 * 2
def baseEnd_5182929 : Nat := 2661333775126857500151649

theorem tailTrace_5182929 : CollatzResearch.WordTrace tailWord_5182929 prefixEnd_5182929 2661333775126857500151649 := by
  unfold tailWord_5182929
  simp only [CollatzResearch.WordTrace]
  refine ⟨189036950640140881646023841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126024633760093921097349227 189036950640140881646023841)
  ·
    refine ⟨141777712980105661234517881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189036950640140881646023841 141777712980105661234517881)
    ·
      refine ⟨106333284735079245925888411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141777712980105661234517881 106333284735079245925888411)
      ·
        refine ⟨159499927102618868888832617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106333284735079245925888411 159499927102618868888832617)
        ·
          refine ⟨119624945326964151666624463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 159499927102618868888832617 119624945326964151666624463)
          ·
            refine ⟨179437417990446227499936695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119624945326964151666624463 179437417990446227499936695)
            ·
              refine ⟨269156126985669341249905043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 179437417990446227499936695 269156126985669341249905043)
              ·
                refine ⟨403734190478504011874857565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 269156126985669341249905043 403734190478504011874857565)
                ·
                  refine ⟨151400321429439004453071587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 403734190478504011874857565 151400321429439004453071587)
                  ·
                    refine ⟨227100482144158506679607381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 151400321429439004453071587 227100482144158506679607381)
                    ·
                      refine ⟨2661333775126857500151649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 227100482144158506679607381 2661333775126857500151649)
                      ·
                        rfl

theorem cell23_5182929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 1, 8].length) (baseStart_5182929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5182929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5182929 prefixEnd_5182929 := by exact prefixLift 5182929
  have htrace : WordTrace (prefixWord ++ tailWord_5182929) baseStart_5182929 baseEnd_5182929 := by
    simpa [prefixWord, tailWord_5182929, baseEnd_5182929] using wordTrace_append hprefix tailTrace_5182929
  have hstable : (prefixWord ++ tailWord_5182929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5182929).length < 2 ^ (prefixWord ++ tailWord_5182929).sum := by decide
  have hdescent : baseEnd_5182929 < baseStart_5182929 := by decide
  rcases family_descends (prefixWord ++ tailWord_5182929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5182947 : List Nat := [1, 1, 1, 6, 2, 1, 4, 2, 1, 4]
def baseStart_5182947 : Nat := 118140960795 + 5182947 * 2 ^ 59
def prefixEnd_5182947 : Nat := 4983230072969 + 3 ^ 40 * 5182947 * 2
def baseEnd_5182947 : Nat := 887114339259546143242189

theorem tailTrace_5182947 : CollatzResearch.WordTrace tailWord_5182947 prefixEnd_5182947 887114339259546143242189 := by
  unfold tailWord_5182947
  simp only [CollatzResearch.WordTrace]
  refine ⟨189037607154075670720179095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126025071436050447146786063 189037607154075670720179095)
  ·
    refine ⟨283556410731113506080268643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189037607154075670720179095 283556410731113506080268643)
    ·
      refine ⟨425334616096670259120402965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 283556410731113506080268643 425334616096670259120402965)
      ·
        refine ⟨19937560129531418396268889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 425334616096670259120402965 19937560129531418396268889)
        ·
          refine ⟨14953170097148563797201667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19937560129531418396268889 14953170097148563797201667)
          ·
            refine ⟨22429755145722845695802501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14953170097148563797201667 22429755145722845695802501)
            ·
              refine ⟨4205579089823033567962969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22429755145722845695802501 4205579089823033567962969)
              ·
                refine ⟨3154184317367275175972227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4205579089823033567962969 3154184317367275175972227)
                ·
                  refine ⟨4731276476050912763958341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3154184317367275175972227 4731276476050912763958341)
                  ·
                    refine ⟨887114339259546143242189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4731276476050912763958341 887114339259546143242189)
                    ·
                      rfl

theorem cell23_5182947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 4, 2, 1, 4].length) (baseStart_5182947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5182947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5182947 prefixEnd_5182947 := by exact prefixLift 5182947
  have htrace : WordTrace (prefixWord ++ tailWord_5182947) baseStart_5182947 baseEnd_5182947 := by
    simpa [prefixWord, tailWord_5182947, baseEnd_5182947] using wordTrace_append hprefix tailTrace_5182947
  have hstable : (prefixWord ++ tailWord_5182947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5182947).length < 2 ^ (prefixWord ++ tailWord_5182947).sum := by decide
  have hdescent : baseEnd_5182947 < baseStart_5182947 := by decide
  rcases family_descends (prefixWord ++ tailWord_5182947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5182974 : List Nat := [4, 2, 2, 3, 1, 2, 1, 1, 2, 2, 3]
def baseStart_5182974 : Nat := 118140960795 + 5182974 * 2 ^ 59
def prefixEnd_5182974 : Nat := 4983230072969 + 3 ^ 40 * 5182974 * 2
def baseEnd_5182974 : Nat := 2661356881756309824088943

theorem tailTrace_5182974 : CollatzResearch.WordTrace tailWord_5182974 prefixEnd_5182974 2661356881756309824088943 := by
  unfold tailWord_5182974
  simp only [CollatzResearch.WordTrace]
  refine ⟨23629823990622231791426497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126025727949985236220941317 23629823990622231791426497)
  ·
    refine ⟨17722367992966673843569873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23629823990622231791426497 17722367992966673843569873)
    ·
      refine ⟨13291775994725005382677405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17722367992966673843569873 13291775994725005382677405)
      ·
        refine ⟨4984415998021877018504027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13291775994725005382677405 4984415998021877018504027)
        ·
          refine ⟨7476623997032815527756041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4984415998021877018504027 7476623997032815527756041)
          ·
            refine ⟨5607467997774611645817031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7476623997032815527756041 5607467997774611645817031)
            ·
              refine ⟨8411201996661917468725547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5607467997774611645817031 8411201996661917468725547)
              ·
                refine ⟨12616802994992876203088321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8411201996661917468725547 12616802994992876203088321)
                ·
                  refine ⟨9462602246244657152316241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12616802994992876203088321 9462602246244657152316241)
                  ·
                    refine ⟨7096951684683492864237181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9462602246244657152316241 7096951684683492864237181)
                    ·
                      refine ⟨2661356881756309824088943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7096951684683492864237181 2661356881756309824088943)
                      ·
                        rfl

theorem cell23_5182974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_5182974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5182974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5182974 prefixEnd_5182974 := by exact prefixLift 5182974
  have htrace : WordTrace (prefixWord ++ tailWord_5182974) baseStart_5182974 baseEnd_5182974 := by
    simpa [prefixWord, tailWord_5182974, baseEnd_5182974] using wordTrace_append hprefix tailTrace_5182974
  have hstable : (prefixWord ++ tailWord_5182974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5182974).length < 2 ^ (prefixWord ++ tailWord_5182974).sum := by decide
  have hdescent : baseEnd_5182974 < baseStart_5182974 := by decide
  rcases family_descends (prefixWord ++ tailWord_5182974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5182990 : List Nat := [4, 1, 1, 2, 4, 1, 1, 3, 1, 5]
def baseStart_5182990 : Nat := 118140960795 + 5182990 * 2 ^ 59
def prefixEnd_5182990 : Nat := 4983230072969 + 3 ^ 40 * 5182990 * 2
def baseEnd_5182990 : Nat := 887121699148927253829623

theorem tailTrace_5182990 : CollatzResearch.WordTrace tailWord_5182990 prefixEnd_5182990 887121699148927253829623 := by
  unfold tailWord_5182990
  simp only [CollatzResearch.WordTrace]
  refine ⟨23629896936614986132999303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126026116995279926042662949 23629896936614986132999303)
  ·
    refine ⟨35444845404922479199498955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23629896936614986132999303 35444845404922479199498955)
    ·
      refine ⟨53167268107383718799248433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35444845404922479199498955 53167268107383718799248433)
      ·
        refine ⟨39875451080537789099436325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53167268107383718799248433 39875451080537789099436325)
        ·
          refine ⟨7476647077600835456144311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39875451080537789099436325 7476647077600835456144311)
          ·
            refine ⟨11214970616401253184216467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7476647077600835456144311 11214970616401253184216467)
            ·
              refine ⟨16822455924601879776324701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11214970616401253184216467 16822455924601879776324701)
              ·
                refine ⟨6308420971725704916121763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16822455924601879776324701 6308420971725704916121763)
                ·
                  refine ⟨9462631457588557374182645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6308420971725704916121763 9462631457588557374182645)
                  ·
                    refine ⟨887121699148927253829623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9462631457588557374182645 887121699148927253829623)
                    ·
                      rfl

theorem cell23_5182990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 3, 1, 5].length) (baseStart_5182990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5182990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5182990 prefixEnd_5182990 := by exact prefixLift 5182990
  have htrace : WordTrace (prefixWord ++ tailWord_5182990) baseStart_5182990 baseEnd_5182990 := by
    simpa [prefixWord, tailWord_5182990, baseEnd_5182990] using wordTrace_append hprefix tailTrace_5182990
  have hstable : (prefixWord ++ tailWord_5182990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5182990).length < 2 ^ (prefixWord ++ tailWord_5182990).sum := by decide
  have hdescent : baseEnd_5182990 < baseStart_5182990 := by decide
  rcases family_descends (prefixWord ++ tailWord_5182990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5182993 : List Nat := [1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 4]
def baseStart_5182993 : Nat := 118140960795 + 5182993 * 2 ^ 59
def prefixEnd_5182993 : Nat := 4983230072969 + 3 ^ 40 * 5182993 * 2
def baseEnd_5182993 : Nat := 2661366637888745249751355

theorem tailTrace_5182993 : CollatzResearch.WordTrace tailWord_5182993 prefixEnd_5182993 2661366637888745249751355 := by
  unfold tailWord_5182993
  simp only [CollatzResearch.WordTrace]
  refine ⟨189039284911909020576353633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126026189941272680384235755 189039284911909020576353633)
  ·
    refine ⟨141779463683931765432265225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189039284911909020576353633 141779463683931765432265225)
    ·
      refine ⟨106334597762948824074198919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141779463683931765432265225 106334597762948824074198919)
      ·
        refine ⟨159501896644423236111298379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106334597762948824074198919 159501896644423236111298379)
        ·
          refine ⟨239252844966634854166947569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159501896644423236111298379 239252844966634854166947569)
          ·
            refine ⟨179439633724976140625210677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 239252844966634854166947569 179439633724976140625210677)
            ·
              refine ⟨16822465661716513183613501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 179439633724976140625210677 16822465661716513183613501)
              ·
                refine ⟨6308424623143692443855063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16822465661716513183613501 6308424623143692443855063)
                ·
                  refine ⟨9462636934715538665782595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6308424623143692443855063 9462636934715538665782595)
                  ·
                    refine ⟨14193955402073307998673893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9462636934715538665782595 14193955402073307998673893)
                    ·
                      refine ⟨2661366637888745249751355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14193955402073307998673893 2661366637888745249751355)
                      ·
                        rfl

theorem cell23_5182993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 4].length) (baseStart_5182993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5182993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5182993 prefixEnd_5182993 := by exact prefixLift 5182993
  have htrace : WordTrace (prefixWord ++ tailWord_5182993) baseStart_5182993 baseEnd_5182993 := by
    simpa [prefixWord, tailWord_5182993, baseEnd_5182993] using wordTrace_append hprefix tailTrace_5182993
  have hstable : (prefixWord ++ tailWord_5182993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5182993).length < 2 ^ (prefixWord ++ tailWord_5182993).sum := by decide
  have hdescent : baseEnd_5182993 < baseStart_5182993 := by decide
  rcases family_descends (prefixWord ++ tailWord_5182993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5183033 : List Nat := [1, 2, 1, 5, 1, 2, 4, 7]
def baseStart_5183033 : Nat := 118140960795 + 5183033 * 2 ^ 59
def prefixEnd_5183033 : Nat := 4983230072969 + 3 ^ 40 * 5183033 * 2
def baseEnd_5183033 : Nat := 98569895448700929379673

theorem tailTrace_5183033 : CollatzResearch.WordTrace tailWord_5183033 prefixEnd_5183033 98569895448700929379673 := by
  unfold tailWord_5183033
  simp only [CollatzResearch.WordTrace]
  refine ⟨189040743831764107407809753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126027162554509404938539835 189040743831764107407809753)
  ·
    refine ⟨141780557873823080555857315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189040743831764107407809753 141780557873823080555857315)
    ·
      refine ⟨212670836810734620833785973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141780557873823080555857315 212670836810734620833785973)
      ·
        refine ⟨19937890951006370703167435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 212670836810734620833785973 19937890951006370703167435)
        ·
          refine ⟨29906836426509556054751153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19937890951006370703167435 29906836426509556054751153)
          ·
            refine ⟨22430127319882167041063365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29906836426509556054751153 22430127319882167041063365)
            ·
              refine ⟨4205648872477906320199381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22430127319882167041063365 4205648872477906320199381)
              ·
                refine ⟨98569895448700929379673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4205648872477906320199381 98569895448700929379673)
                ·
                  rfl

theorem cell23_5183033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 4, 7].length) (baseStart_5183033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5183033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5183033 prefixEnd_5183033 := by exact prefixLift 5183033
  have htrace : WordTrace (prefixWord ++ tailWord_5183033) baseStart_5183033 baseEnd_5183033 := by
    simpa [prefixWord, tailWord_5183033, baseEnd_5183033] using wordTrace_append hprefix tailTrace_5183033
  have hstable : (prefixWord ++ tailWord_5183033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5183033).length < 2 ^ (prefixWord ++ tailWord_5183033).sum := by decide
  have hdescent : baseEnd_5183033 < baseStart_5183033 := by decide
  rcases family_descends (prefixWord ++ tailWord_5183033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5183056 : List Nat := [2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 5]
def baseStart_5183056 : Nat := 118140960795 + 5183056 * 2 ^ 59
def prefixEnd_5183056 : Nat := 4983230072969 + 3 ^ 40 * 5183056 * 2
def baseEnd_5183056 : Nat := 2661398987169978503263565

theorem tailTrace_5183056 : CollatzResearch.WordTrace tailWord_5183056 prefixEnd_5183056 2661398987169978503263565 := by
  unfold tailWord_5183056
  simp only [CollatzResearch.WordTrace]
  refine ⟨94520791355340391167948511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126027721807120521557264681 94520791355340391167948511)
  ·
    refine ⟨141781187033010586751922767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94520791355340391167948511 141781187033010586751922767)
    ·
      refine ⟨212671780549515880127884151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141781187033010586751922767 212671780549515880127884151)
      ·
        refine ⟨319007670824273820191826227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212671780549515880127884151 319007670824273820191826227)
        ·
          refine ⟨478511506236410730287739341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 319007670824273820191826227 478511506236410730287739341)
          ·
            refine ⟨179441814838654023857902253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 478511506236410730287739341 179441814838654023857902253)
            ·
              refine ⟨67290680564495258946713345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 179441814838654023857902253 67290680564495258946713345)
              ·
                refine ⟨50468010423371444210035009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67290680564495258946713345 50468010423371444210035009)
                ·
                  refine ⟨37851007817528583157526257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50468010423371444210035009 37851007817528583157526257)
                  ·
                    refine ⟨28388255863146437368144693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37851007817528583157526257 28388255863146437368144693)
                    ·
                      refine ⟨2661398987169978503263565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28388255863146437368144693 2661398987169978503263565)
                      ·
                        rfl

theorem cell23_5183056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 5].length) (baseStart_5183056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5183056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5183056 prefixEnd_5183056 := by exact prefixLift 5183056
  have htrace : WordTrace (prefixWord ++ tailWord_5183056) baseStart_5183056 baseEnd_5183056 := by
    simpa [prefixWord, tailWord_5183056, baseEnd_5183056] using wordTrace_append hprefix tailTrace_5183056
  have hstable : (prefixWord ++ tailWord_5183056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5183056).length < 2 ^ (prefixWord ++ tailWord_5183056).sum := by decide
  have hdescent : baseEnd_5183056 < baseStart_5183056 := by decide
  rcases family_descends (prefixWord ++ tailWord_5183056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5183060 : List Nat := [2, 4, 1, 1, 1, 2, 1, 3, 4, 1, 3]
def baseStart_5183060 : Nat := 118140960795 + 5183060 * 2 ^ 59
def prefixEnd_5183060 : Nat := 4983230072969 + 3 ^ 40 * 5183060 * 2
def baseEnd_5183060 : Nat := 2661401041092596487613547

theorem tailTrace_5183060 : CollatzResearch.WordTrace tailWord_5183060 prefixEnd_5183060 2661401041092596487613547 := by
  unfold tailWord_5183060
  simp only [CollatzResearch.WordTrace]
  refine ⟨94520864301333145509521317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126027819068444194012695089 94520864301333145509521317)
  ·
    refine ⟨17722662056499964783035247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94520864301333145509521317 17722662056499964783035247)
    ·
      refine ⟨26583993084749947174552871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17722662056499964783035247 26583993084749947174552871)
      ·
        refine ⟨39875989627124920761829307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26583993084749947174552871 39875989627124920761829307)
        ·
          refine ⟨59813984440687381142743961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39875989627124920761829307 59813984440687381142743961)
          ·
            refine ⟨44860488330515535857057971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59813984440687381142743961 44860488330515535857057971)
            ·
              refine ⟨67290732495773303785586957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44860488330515535857057971 67290732495773303785586957)
              ·
                refine ⟨25234024685914988919595109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67290732495773303785586957 25234024685914988919595109)
                ·
                  refine ⟨4731379628609060422424083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25234024685914988919595109 4731379628609060422424083)
                  ·
                    refine ⟨7097069442913590633636125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4731379628609060422424083 7097069442913590633636125)
                    ·
                      refine ⟨2661401041092596487613547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7097069442913590633636125 2661401041092596487613547)
                      ·
                        rfl

theorem cell23_5183060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 3, 4, 1, 3].length) (baseStart_5183060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5183060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5183060 prefixEnd_5183060 := by exact prefixLift 5183060
  have htrace : WordTrace (prefixWord ++ tailWord_5183060) baseStart_5183060 baseEnd_5183060 := by
    simpa [prefixWord, tailWord_5183060, baseEnd_5183060] using wordTrace_append hprefix tailTrace_5183060
  have hstable : (prefixWord ++ tailWord_5183060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5183060).length < 2 ^ (prefixWord ++ tailWord_5183060).sum := by decide
  have hdescent : baseEnd_5183060 < baseStart_5183060 := by decide
  rcases family_descends (prefixWord ++ tailWord_5183060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5183077 : List Nat := [1, 3, 1, 3, 3, 2, 1, 3, 2, 1, 3]
def baseStart_5183077 : Nat := 118140960795 + 5183077 * 2 ^ 59
def prefixEnd_5183077 : Nat := 4983230072969 + 3 ^ 40 * 5183077 * 2
def baseEnd_5183077 : Nat := 2661409770263722921100969

theorem tailTrace_5183077 : CollatzResearch.WordTrace tailWord_5183077 prefixEnd_5183077 2661409770263722921100969 := by
  unfold tailWord_5183077
  simp only [CollatzResearch.WordTrace]
  refine ⟨189042348643604702922411485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126028232429069801948274323 189042348643604702922411485)
  ·
    refine ⟨70890880741351763595904307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 189042348643604702922411485 70890880741351763595904307)
    ·
      refine ⟨106336321112027645393856461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70890880741351763595904307 106336321112027645393856461)
      ·
        refine ⟨39876120417010367022696173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106336321112027645393856461 39876120417010367022696173)
        ·
          refine ⟨14953545156378887633511065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39876120417010367022696173 14953545156378887633511065)
          ·
            refine ⟨11215158867284165725133299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14953545156378887633511065 11215158867284165725133299)
            ·
              refine ⟨16822738300926248587699949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11215158867284165725133299 16822738300926248587699949)
              ·
                refine ⟨6308526862847343220387481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16822738300926248587699949 6308526862847343220387481)
                ·
                  refine ⟨4731395147135507415290611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6308526862847343220387481 4731395147135507415290611)
                  ·
                    refine ⟨7097092720703261122935917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4731395147135507415290611 7097092720703261122935917)
                    ·
                      refine ⟨2661409770263722921100969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7097092720703261122935917 2661409770263722921100969)
                      ·
                        rfl

theorem cell23_5183077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 3, 2, 1, 3].length) (baseStart_5183077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5183077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5183077 prefixEnd_5183077 := by exact prefixLift 5183077
  have htrace : WordTrace (prefixWord ++ tailWord_5183077) baseStart_5183077 baseEnd_5183077 := by
    simpa [prefixWord, tailWord_5183077, baseEnd_5183077] using wordTrace_append hprefix tailTrace_5183077
  have hstable : (prefixWord ++ tailWord_5183077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5183077).length < 2 ^ (prefixWord ++ tailWord_5183077).sum := by decide
  have hdescent : baseEnd_5183077 < baseStart_5183077 := by decide
  rcases family_descends (prefixWord ++ tailWord_5183077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5183134 : List Nat := [4, 3, 1, 1, 1, 3, 2, 1, 1, 4, 2]
def baseStart_5183134 : Nat := 118140960795 + 5183134 * 2 ^ 59
def prefixEnd_5183134 : Nat := 4983230072969 + 3 ^ 40 * 5183134 * 2
def baseEnd_5183134 : Nat := 2661439038661029198088207

theorem tailTrace_5183134 : CollatzResearch.WordTrace tailWord_5183134 prefixEnd_5183134 2661439038661029198088207 := by
  unfold tailWord_5183134
  simp only [CollatzResearch.WordTrace]
  refine ⟨23630553450549775207154557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126029618402932134438157637 23630553450549775207154557)
  ·
    refine ⟨8861457543956165702682959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23630553450549775207154557 8861457543956165702682959)
    ·
      refine ⟨13292186315934248554024439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8861457543956165702682959 13292186315934248554024439)
      ·
        refine ⟨19938279473901372831036659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13292186315934248554024439 19938279473901372831036659)
        ·
          refine ⟨29907419210852059246554989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19938279473901372831036659 29907419210852059246554989)
          ·
            refine ⟨11215282204069522217458121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29907419210852059246554989 11215282204069522217458121)
            ·
              refine ⟨8411461653052141663093591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11215282204069522217458121 8411461653052141663093591)
              ·
                refine ⟨12617192479578212494640387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8411461653052141663093591 12617192479578212494640387)
                ·
                  refine ⟨18925788719367318741960581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12617192479578212494640387 18925788719367318741960581)
                  ·
                    refine ⟨3548585384881372264117609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18925788719367318741960581 3548585384881372264117609)
                    ·
                      refine ⟨2661439038661029198088207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3548585384881372264117609 2661439038661029198088207)
                      ·
                        rfl

theorem cell23_5183134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 2, 1, 1, 4, 2].length) (baseStart_5183134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5183134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5183134 prefixEnd_5183134 := by exact prefixLift 5183134
  have htrace : WordTrace (prefixWord ++ tailWord_5183134) baseStart_5183134 baseEnd_5183134 := by
    simpa [prefixWord, tailWord_5183134, baseEnd_5183134] using wordTrace_append hprefix tailTrace_5183134
  have hstable : (prefixWord ++ tailWord_5183134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5183134).length < 2 ^ (prefixWord ++ tailWord_5183134).sum := by decide
  have hdescent : baseEnd_5183134 < baseStart_5183134 := by decide
  rcases family_descends (prefixWord ++ tailWord_5183134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5183174 : List Nat := [6, 1, 2, 1, 1, 2, 2, 1, 7]
def baseStart_5183174 : Nat := 118140960795 + 5183174 * 2 ^ 59
def prefixEnd_5183174 : Nat := 4983230072969 + 3 ^ 40 * 5183174 * 2
def baseEnd_5183174 : Nat := 295717730876356560176447

theorem tailTrace_5183174 : CollatzResearch.WordTrace tailWord_5183174 prefixEnd_5183174 295717730876356560176447 := by
  unfold tailWord_5183174
  simp only [CollatzResearch.WordTrace]
  refine ⟨5907683953882915265271643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 126030591016168858992461717 5907683953882915265271643)
  ·
    refine ⟨8861525930824372897907465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5907683953882915265271643 8861525930824372897907465)
    ·
      refine ⟨6646144448118279673430599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8861525930824372897907465 6646144448118279673430599)
      ·
        refine ⟨9969216672177419510145899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6646144448118279673430599 9969216672177419510145899)
        ·
          refine ⟨14953825008266129265218849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9969216672177419510145899 14953825008266129265218849)
          ·
            refine ⟨11215368756199596948914137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14953825008266129265218849 11215368756199596948914137)
            ·
              refine ⟨8411526567149697711685603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11215368756199596948914137 8411526567149697711685603)
              ·
                refine ⟨12617289850724546567528405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8411526567149697711685603 12617289850724546567528405)
                ·
                  refine ⟨295717730876356560176447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12617289850724546567528405 295717730876356560176447)
                  ·
                    rfl

theorem cell23_5183174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 2, 1, 7].length) (baseStart_5183174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5183174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5183174 prefixEnd_5183174 := by exact prefixLift 5183174
  have htrace : WordTrace (prefixWord ++ tailWord_5183174) baseStart_5183174 baseEnd_5183174 := by
    simpa [prefixWord, tailWord_5183174, baseEnd_5183174] using wordTrace_append hprefix tailTrace_5183174
  have hstable : (prefixWord ++ tailWord_5183174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5183174).length < 2 ^ (prefixWord ++ tailWord_5183174).sum := by decide
  have hdescent : baseEnd_5183174 < baseStart_5183174 := by decide
  rcases family_descends (prefixWord ++ tailWord_5183174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5183200 : List Nat := [2, 1, 1, 3, 1, 2, 4, 2, 3, 4]
def baseStart_5183200 : Nat := 118140960795 + 5183200 * 2 ^ 59
def prefixEnd_5183200 : Nat := 4983230072969 + 3 ^ 40 * 5183200 * 2
def baseEnd_5183200 : Nat := 887157642794741979954301

theorem tailTrace_5183200 : CollatzResearch.WordTrace tailWord_5183200 prefixEnd_5183200 887157642794741979954301 := by
  unfold tailWord_5183200
  simp only [CollatzResearch.WordTrace]
  refine ⟨94523417411079547464569527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126031223214772729952759369 94523417411079547464569527)
  ·
    refine ⟨141785126116619321196854291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94523417411079547464569527 141785126116619321196854291)
    ·
      refine ⟨212677689174928981795281437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141785126116619321196854291 212677689174928981795281437)
      ·
        refine ⟨79754133440598368173230539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 212677689174928981795281437 79754133440598368173230539)
        ·
          refine ⟨119631200160897552259845809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79754133440598368173230539 119631200160897552259845809)
          ·
            refine ⟨89723400120673164194884357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119631200160897552259845809 89723400120673164194884357)
            ·
              refine ⟨16823137522626218286540817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 89723400120673164194884357 16823137522626218286540817)
              ·
                refine ⟨12617353141969663714905613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16823137522626218286540817 12617353141969663714905613)
                ·
                  refine ⟨4731507428238623893089605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12617353141969663714905613 4731507428238623893089605)
                  ·
                    refine ⟨887157642794741979954301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4731507428238623893089605 887157642794741979954301)
                    ·
                      rfl

theorem cell23_5183200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 2, 3, 4].length) (baseStart_5183200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5183200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5183200 prefixEnd_5183200 := by exact prefixLift 5183200
  have htrace : WordTrace (prefixWord ++ tailWord_5183200) baseStart_5183200 baseEnd_5183200 := by
    simpa [prefixWord, tailWord_5183200, baseEnd_5183200] using wordTrace_append hprefix tailTrace_5183200
  have hstable : (prefixWord ++ tailWord_5183200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5183200).length < 2 ^ (prefixWord ++ tailWord_5183200).sum := by decide
  have hdescent : baseEnd_5183200 < baseStart_5183200 := by decide
  rcases family_descends (prefixWord ++ tailWord_5183200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5183210 : List Nat := [3, 1, 3, 1, 1, 1, 4, 1, 1, 4, 3]
def baseStart_5183210 : Nat := 118140960795 + 5183210 * 2 ^ 59
def prefixEnd_5183210 : Nat := 4983230072969 + 3 ^ 40 * 5183210 * 2
def baseEnd_5183210 : Nat := 2661478063190770900737857

theorem tailTrace_5183210 : CollatzResearch.WordTrace tailWord_5183210 prefixEnd_5183210 2661478063190770900737857 := by
  unfold tailWord_5183210
  simp only [CollatzResearch.WordTrace]
  refine ⟨47261799888030716659250771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126031466368081911091335389 47261799888030716659250771)
  ·
    refine ⟨70892699832046074988876157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47261799888030716659250771 70892699832046074988876157)
    ·
      refine ⟨26584762437017278120828559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70892699832046074988876157 26584762437017278120828559)
      ·
        refine ⟨39877143655525917181242839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26584762437017278120828559 39877143655525917181242839)
        ·
          refine ⟨59815715483288875771864259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39877143655525917181242839 59815715483288875771864259)
          ·
            refine ⟨89723573224933313657796389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59815715483288875771864259 89723573224933313657796389)
            ·
              refine ⟨16823169979674996310836823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 89723573224933313657796389 16823169979674996310836823)
              ·
                refine ⟨25234754969512494466255235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16823169979674996310836823 25234754969512494466255235)
                ·
                  refine ⟨37852132454268741699382853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25234754969512494466255235 37852132454268741699382853)
                  ·
                    refine ⟨7097274835175389068634285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37852132454268741699382853 7097274835175389068634285)
                    ·
                      refine ⟨2661478063190770900737857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7097274835175389068634285 2661478063190770900737857)
                      ·
                        rfl

theorem cell23_5183210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 1, 1, 4, 3].length) (baseStart_5183210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5183210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5183210 prefixEnd_5183210 := by exact prefixLift 5183210
  have htrace : WordTrace (prefixWord ++ tailWord_5183210) baseStart_5183210 baseEnd_5183210 := by
    simpa [prefixWord, tailWord_5183210, baseEnd_5183210] using wordTrace_append hprefix tailTrace_5183210
  have hstable : (prefixWord ++ tailWord_5183210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5183210).length < 2 ^ (prefixWord ++ tailWord_5183210).sum := by decide
  have hdescent : baseEnd_5183210 < baseStart_5183210 := by decide
  rcases family_descends (prefixWord ++ tailWord_5183210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5183233 : List Nat := [1, 2, 4, 1, 1, 1, 2, 1, 1, 1, 8]
def baseStart_5183233 : Nat := 118140960795 + 5183233 * 2 ^ 59
def prefixEnd_5183233 : Nat := 4983230072969 + 3 ^ 40 * 5183233 * 2
def baseEnd_5183233 : Nat := 2661489873245824310750251

theorem tailTrace_5183233 : CollatzResearch.WordTrace tailWord_5183233 prefixEnd_5183233 2661489873245824310750251 := by
  unfold tailWord_5183233
  simp only [CollatzResearch.WordTrace]
  refine ⟨189048038431039541565090353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126032025620693027710060235 189048038431039541565090353)
  ·
    refine ⟨141786028823279656173817765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189048038431039541565090353 141786028823279656173817765)
    ·
      refine ⟨26584880404364935532590831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 141786028823279656173817765 26584880404364935532590831)
      ·
        refine ⟨39877320606547403298886247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26584880404364935532590831 39877320606547403298886247)
        ·
          refine ⟨59815980909821104948329371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39877320606547403298886247 59815980909821104948329371)
          ·
            refine ⟨89723971364731657422494057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59815980909821104948329371 89723971364731657422494057)
            ·
              refine ⟨67292978523548743066870543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89723971364731657422494057 67292978523548743066870543)
              ·
                refine ⟨100939467785323114600305815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67292978523548743066870543 100939467785323114600305815)
                ·
                  refine ⟨151409201677984671900458723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 100939467785323114600305815 151409201677984671900458723)
                  ·
                    refine ⟨227113802516977007850688085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 151409201677984671900458723 227113802516977007850688085)
                    ·
                      refine ⟨2661489873245824310750251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 227113802516977007850688085 2661489873245824310750251)
                      ·
                        rfl

theorem cell23_5183233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 1, 8].length) (baseStart_5183233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5183233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5183233 prefixEnd_5183233 := by exact prefixLift 5183233
  have htrace : WordTrace (prefixWord ++ tailWord_5183233) baseStart_5183233 baseEnd_5183233 := by
    simpa [prefixWord, tailWord_5183233, baseEnd_5183233] using wordTrace_append hprefix tailTrace_5183233
  have hstable : (prefixWord ++ tailWord_5183233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5183233).length < 2 ^ (prefixWord ++ tailWord_5183233).sum := by decide
  have hdescent : baseEnd_5183233 < baseStart_5183233 := by decide
  rcases family_descends (prefixWord ++ tailWord_5183233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5183260 : List Nat := [2, 2, 3, 1, 1, 2, 3, 1, 3, 5]
def baseStart_5183260 : Nat := 118140960795 + 5183260 * 2 ^ 59
def prefixEnd_5183260 : Nat := 4983230072969 + 3 ^ 40 * 5183260 * 2
def baseEnd_5183260 : Nat := 887167912407831901704209

theorem tailTrace_5183260 : CollatzResearch.WordTrace tailWord_5183260 prefixEnd_5183260 887167912407831901704209 := by
  unfold tailWord_5183260
  simp only [CollatzResearch.WordTrace]
  refine ⟨94524511600970862588161617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126032682134627816784215489 94524511600970862588161617)
  ·
    refine ⟨70893383700728146941121213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94524511600970862588161617 70893383700728146941121213)
    ·
      refine ⟨26585018887773055102920455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70893383700728146941121213 26585018887773055102920455)
      ·
        refine ⟨39877528331659582654380683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26585018887773055102920455 39877528331659582654380683)
        ·
          refine ⟨59816292497489373981571025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39877528331659582654380683 59816292497489373981571025)
          ·
            refine ⟨44862219373117030486178269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59816292497489373981571025 44862219373117030486178269)
            ·
              refine ⟨16823332264918886432316851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44862219373117030486178269 16823332264918886432316851)
              ·
                refine ⟨25234998397378329648475277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16823332264918886432316851 25234998397378329648475277)
                ·
                  refine ⟨9463124399016873618178229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25234998397378329648475277 9463124399016873618178229)
                  ·
                    refine ⟨887167912407831901704209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9463124399016873618178229 887167912407831901704209)
                    ·
                      rfl

theorem cell23_5183260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 1, 3, 5].length) (baseStart_5183260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5183260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5183260 prefixEnd_5183260 := by exact prefixLift 5183260
  have htrace : WordTrace (prefixWord ++ tailWord_5183260) baseStart_5183260 baseEnd_5183260 := by
    simpa [prefixWord, tailWord_5183260, baseEnd_5183260] using wordTrace_append hprefix tailTrace_5183260
  have hstable : (prefixWord ++ tailWord_5183260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5183260).length < 2 ^ (prefixWord ++ tailWord_5183260).sum := by decide
  have hdescent : baseEnd_5183260 < baseStart_5183260 := by decide
  rcases family_descends (prefixWord ++ tailWord_5183260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5183267 : List Nat := [1, 1, 1, 4, 2, 1, 3, 3, 2, 3, 2]
def baseStart_5183267 : Nat := 118140960795 + 5183267 * 2 ^ 59
def prefixEnd_5183267 : Nat := 4983230072969 + 3 ^ 40 * 5183267 * 2
def baseEnd_5183267 : Nat := 2661507331588077177725095

theorem tailTrace_5183267 : CollatzResearch.WordTrace tailWord_5183267 prefixEnd_5183267 2661507331588077177725095 := by
  unfold tailWord_5183267
  simp only [CollatzResearch.WordTrace]
  refine ⟨189049278512916365371828055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126032852341944243581218703 189049278512916365371828055)
  ·
    refine ⟨283573917769374548057742083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189049278512916365371828055 283573917769374548057742083)
    ·
      refine ⟨425360876654061822086613125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 283573917769374548057742083 425360876654061822086613125)
      ·
        refine ⟨79755164372636591641239961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 425360876654061822086613125 79755164372636591641239961)
        ·
          refine ⟨59816373279477443730929971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79755164372636591641239961 59816373279477443730929971)
          ·
            refine ⟨89724559919216165596394957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59816373279477443730929971 89724559919216165596394957)
            ·
              refine ⟨33646709969706062098648109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89724559919216165596394957 33646709969706062098648109)
              ·
                refine ⟨12617516238639773286993041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33646709969706062098648109 12617516238639773286993041)
                ·
                  refine ⟨9463137178979829965244781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12617516238639773286993041 9463137178979829965244781)
                  ·
                    refine ⟨3548676442117436236966793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9463137178979829965244781 3548676442117436236966793)
                    ·
                      refine ⟨2661507331588077177725095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3548676442117436236966793 2661507331588077177725095)
                      ·
                        rfl

theorem cell23_5183267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 3, 2, 3, 2].length) (baseStart_5183267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5183267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5183267 prefixEnd_5183267 := by exact prefixLift 5183267
  have htrace : WordTrace (prefixWord ++ tailWord_5183267) baseStart_5183267 baseEnd_5183267 := by
    simpa [prefixWord, tailWord_5183267, baseEnd_5183267] using wordTrace_append hprefix tailTrace_5183267
  have hstable : (prefixWord ++ tailWord_5183267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5183267).length < 2 ^ (prefixWord ++ tailWord_5183267).sum := by decide
  have hdescent : baseEnd_5183267 < baseStart_5183267 := by decide
  rcases family_descends (prefixWord ++ tailWord_5183267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5183314 : List Nat := [3, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2]
def baseStart_5183314 : Nat := 118140960795 + 5183314 * 2 ^ 59
def prefixEnd_5183314 : Nat := 4983230072969 + 3 ^ 40 * 5183314 * 2
def baseEnd_5183314 : Nat := 2661531465178838493837379

theorem tailTrace_5183314 : CollatzResearch.WordTrace tailWord_5183314 prefixEnd_5183314 2661531465178838493837379 := by
  unfold tailWord_5183314
  simp only [CollatzResearch.WordTrace]
  refine ⟨47262748185936523099697249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126033995162497394932525997 47262748185936523099697249)
  ·
    refine ⟨35447061139452392324772937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47262748185936523099697249 35447061139452392324772937)
    ·
      refine ⟨26585295854589294243579703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35447061139452392324772937 26585295854589294243579703)
      ·
        refine ⟨39877943781883941365369555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26585295854589294243579703 39877943781883941365369555)
        ·
          refine ⟨59816915672825912048054333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39877943781883941365369555 59816915672825912048054333)
          ·
            refine ⟨22431343377309717018020375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59816915672825912048054333 22431343377309717018020375)
            ·
              refine ⟨33647015065964575527030563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22431343377309717018020375 33647015065964575527030563)
              ·
                refine ⟨50470522598946863290545845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33647015065964575527030563 50470522598946863290545845)
                ·
                  refine ⟨4731611493651268433488673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 50470522598946863290545845 4731611493651268433488673)
                  ·
                    refine ⟨3548708620238451325116505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4731611493651268433488673 3548708620238451325116505)
                    ·
                      refine ⟨2661531465178838493837379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3548708620238451325116505 2661531465178838493837379)
                      ·
                        rfl

theorem cell23_5183314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2].length) (baseStart_5183314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5183314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5183314 prefixEnd_5183314 := by exact prefixLift 5183314
  have htrace : WordTrace (prefixWord ++ tailWord_5183314) baseStart_5183314 baseEnd_5183314 := by
    simpa [prefixWord, tailWord_5183314, baseEnd_5183314] using wordTrace_append hprefix tailTrace_5183314
  have hstable : (prefixWord ++ tailWord_5183314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5183314).length < 2 ^ (prefixWord ++ tailWord_5183314).sum := by decide
  have hdescent : baseEnd_5183314 < baseStart_5183314 := by decide
  rcases family_descends (prefixWord ++ tailWord_5183314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5183317 : List Nat := [1, 3, 2, 2, 2, 2, 2, 1, 3, 2, 3]
def baseStart_5183317 : Nat := 118140960795 + 5183317 * 2 ^ 59
def prefixEnd_5183317 : Nat := 4983230072969 + 3 ^ 40 * 5183317 * 2
def baseEnd_5183317 : Nat := 2661533005620801982099865

theorem tailTrace_5183317 : CollatzResearch.WordTrace tailWord_5183317 prefixEnd_5183317 2661533005620801982099865 := by
  unfold tailWord_5183317
  simp only [CollatzResearch.WordTrace]
  refine ⟨189051102162735223911148205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126034068108490149274098803 189051102162735223911148205)
  ·
    refine ⟨70894163311025708966680577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 189051102162735223911148205 70894163311025708966680577)
    ·
      refine ⟨53170622483269281725010433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70894163311025708966680577 53170622483269281725010433)
      ·
        refine ⟨39877966862451961293757825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53170622483269281725010433 39877966862451961293757825)
        ·
          refine ⟨29908475146838970970318369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39877966862451961293757825 29908475146838970970318369)
          ·
            refine ⟨22431356360129228227738777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29908475146838970970318369 22431356360129228227738777)
            ·
              refine ⟨16823517270096921170804083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22431356360129228227738777 16823517270096921170804083)
              ·
                refine ⟨25235275905145381756206125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16823517270096921170804083 25235275905145381756206125)
                ·
                  refine ⟨9463228464429518158577297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25235275905145381756206125 9463228464429518158577297)
                  ·
                    refine ⟨7097421348322138618932973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9463228464429518158577297 7097421348322138618932973)
                    ·
                      refine ⟨2661533005620801982099865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7097421348322138618932973 2661533005620801982099865)
                      ·
                        rfl

theorem cell23_5183317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 1, 3, 2, 3].length) (baseStart_5183317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5183317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5183317 prefixEnd_5183317 := by exact prefixLift 5183317
  have htrace : WordTrace (prefixWord ++ tailWord_5183317) baseStart_5183317 baseEnd_5183317 := by
    simpa [prefixWord, tailWord_5183317, baseEnd_5183317] using wordTrace_append hprefix tailTrace_5183317
  have hstable : (prefixWord ++ tailWord_5183317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5183317).length < 2 ^ (prefixWord ++ tailWord_5183317).sum := by decide
  have hdescent : baseEnd_5183317 < baseStart_5183317 := by decide
  rcases family_descends (prefixWord ++ tailWord_5183317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5183331 : List Nat := [1, 1, 1, 5, 4, 2, 2, 1, 1, 1, 4]
def baseStart_5183331 : Nat := 118140960795 + 5183331 * 2 ^ 59
def prefixEnd_5183331 : Nat := 4983230072969 + 3 ^ 40 * 5183331 * 2
def baseEnd_5183331 : Nat := 2661540194349964927324801

theorem tailTrace_5183331 : CollatzResearch.WordTrace tailWord_5183331 prefixEnd_5183331 2661540194349964927324801 := by
  unfold tailWord_5183331
  simp only [CollatzResearch.WordTrace]
  refine ⟨189051612784684504302157847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126034408523123002868105231 189051612784684504302157847)
  ·
    refine ⟨283577419177026756453236771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189051612784684504302157847 283577419177026756453236771)
    ·
      refine ⟨425366128765540134679855157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 283577419177026756453236771 425366128765540134679855157)
      ·
        refine ⟨39878074571769387626236421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 425366128765540134679855157 39878074571769387626236421)
        ·
          refine ⟨7477138982206760179919329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39878074571769387626236421 7477138982206760179919329)
          ·
            refine ⟨5607854236655070134939497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7477138982206760179919329 5607854236655070134939497)
            ·
              refine ⟨4205890677491302601204623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5607854236655070134939497 4205890677491302601204623)
              ·
                refine ⟨6308836016236953901806935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4205890677491302601204623 6308836016236953901806935)
                ·
                  refine ⟨9463254024355430852710403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6308836016236953901806935 9463254024355430852710403)
                  ·
                    refine ⟨14194881036533146279065605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9463254024355430852710403 14194881036533146279065605)
                    ·
                      refine ⟨2661540194349964927324801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14194881036533146279065605 2661540194349964927324801)
                      ·
                        rfl

theorem cell23_5183331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 2, 1, 1, 1, 4].length) (baseStart_5183331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5183331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5183331 prefixEnd_5183331 := by exact prefixLift 5183331
  have htrace : WordTrace (prefixWord ++ tailWord_5183331) baseStart_5183331 baseEnd_5183331 := by
    simpa [prefixWord, tailWord_5183331, baseEnd_5183331] using wordTrace_append hprefix tailTrace_5183331
  have hstable : (prefixWord ++ tailWord_5183331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5183331).length < 2 ^ (prefixWord ++ tailWord_5183331).sum := by decide
  have hdescent : baseEnd_5183331 < baseStart_5183331 := by decide
  rcases family_descends (prefixWord ++ tailWord_5183331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5183358 : List Nat := [4, 2, 3, 1, 1, 2, 3, 1, 2, 4]
def baseStart_5183358 : Nat := 118140960795 + 5183358 * 2 ^ 59
def prefixEnd_5183358 : Nat := 4983230072969 + 3 ^ 40 * 5183358 * 2
def baseEnd_5183358 : Nat := 887184686109212107229059

theorem tailTrace_5183358 : CollatzResearch.WordTrace tailWord_5183358 prefixEnd_5183358 887184686109212107229059 := by
  unfold tailWord_5183358
  simp only [CollatzResearch.WordTrace]
  refine ⟨23631574694448335989173841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126035065037057791942260485 23631574694448335989173841)
  ·
    refine ⟨17723681020836251991880381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23631574694448335989173841 17723681020836251991880381)
    ·
      refine ⟨6646380382813594496955143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17723681020836251991880381 6646380382813594496955143)
      ·
        refine ⟨9969570574220391745432715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6646380382813594496955143 9969570574220391745432715)
        ·
          refine ⟨14954355861330587618149073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9969570574220391745432715 14954355861330587618149073)
          ·
            refine ⟨11215766895997940713611805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14954355861330587618149073 11215766895997940713611805)
            ·
              refine ⟨4205912585999227767604427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11215766895997940713611805 4205912585999227767604427)
              ·
                refine ⟨6308868878998841651406641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4205912585999227767604427 6308868878998841651406641)
                ·
                  refine ⟨4731651659249131238554981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6308868878998841651406641 4731651659249131238554981)
                  ·
                    refine ⟨887184686109212107229059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4731651659249131238554981 887184686109212107229059)
                    ·
                      rfl

theorem cell23_5183358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_5183358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5183358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5183358 prefixEnd_5183358 := by exact prefixLift 5183358
  have htrace : WordTrace (prefixWord ++ tailWord_5183358) baseStart_5183358 baseEnd_5183358 := by
    simpa [prefixWord, tailWord_5183358, baseEnd_5183358] using wordTrace_append hprefix tailTrace_5183358
  have hstable : (prefixWord ++ tailWord_5183358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5183358).length < 2 ^ (prefixWord ++ tailWord_5183358).sum := by decide
  have hdescent : baseEnd_5183358 < baseStart_5183358 := by decide
  rcases family_descends (prefixWord ++ tailWord_5183358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5183361 : List Nat := [1, 2, 4, 4, 1, 2, 1, 1, 1, 2, 4]
def baseStart_5183361 : Nat := 118140960795 + 5183361 * 2 ^ 59
def prefixEnd_5183361 : Nat := 4983230072969 + 3 ^ 40 * 5183361 * 2
def baseEnd_5183361 : Nat := 2661555598769599809949663

theorem tailTrace_5183361 : CollatzResearch.WordTrace tailWord_5183361 prefixEnd_5183361 2661555598769599809949663 := by
  unfold tailWord_5183361
  simp only [CollatzResearch.WordTrace]
  refine ⟨189052706974575819425749937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126035137983050546283833291 189052706974575819425749937)
  ·
    refine ⟨141789530230931864569312453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189052706974575819425749937 141789530230931864569312453)
    ·
      refine ⟨26585536918299724606746085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 141789530230931864569312453 26585536918299724606746085)
      ·
        refine ⟨4984788172181198363764891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26585536918299724606746085 4984788172181198363764891)
        ·
          refine ⟨7477182258271797545647337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4984788172181198363764891 7477182258271797545647337)
          ·
            refine ⟨5607886693703848159235503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7477182258271797545647337 5607886693703848159235503)
            ·
              refine ⟨8411830040555772238853255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5607886693703848159235503 8411830040555772238853255)
              ·
                refine ⟨12617745060833658358279883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8411830040555772238853255 12617745060833658358279883)
                ·
                  refine ⟨18926617591250487537419825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12617745060833658358279883 18926617591250487537419825)
                  ·
                    refine ⟨14194963193437865653064869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18926617591250487537419825 14194963193437865653064869)
                    ·
                      refine ⟨2661555598769599809949663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14194963193437865653064869 2661555598769599809949663)
                      ·
                        rfl

theorem cell23_5183361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_5183361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5183361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5183361 prefixEnd_5183361 := by exact prefixLift 5183361
  have htrace : WordTrace (prefixWord ++ tailWord_5183361) baseStart_5183361 baseEnd_5183361 := by
    simpa [prefixWord, tailWord_5183361, baseEnd_5183361] using wordTrace_append hprefix tailTrace_5183361
  have hstable : (prefixWord ++ tailWord_5183361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5183361).length < 2 ^ (prefixWord ++ tailWord_5183361).sum := by decide
  have hdescent : baseEnd_5183361 < baseStart_5183361 := by decide
  rcases family_descends (prefixWord ++ tailWord_5183361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5183364 : List Nat := [2, 3, 2, 1, 1, 1, 2, 5, 2, 1, 3]
def baseStart_5183364 : Nat := 118140960795 + 5183364 * 2 ^ 59
def prefixEnd_5183364 : Nat := 4983230072969 + 3 ^ 40 * 5183364 * 2
def baseEnd_5183364 : Nat := 2661557139211563298212149

theorem tailTrace_5183364 : CollatzResearch.WordTrace tailWord_5183364 prefixEnd_5183364 2661557139211563298212149 := by
  unfold tailWord_5183364
  simp only [CollatzResearch.WordTrace]
  refine ⟨94526408196782475469054573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126035210929043300625406097 94526408196782475469054573)
  ·
    refine ⟨35447403073793428300895465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94526408196782475469054573 35447403073793428300895465)
    ·
      refine ⟨26585552305345071225671599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35447403073793428300895465 26585552305345071225671599)
      ·
        refine ⟨39878328458017606838507399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26585552305345071225671599 39878328458017606838507399)
        ·
          refine ⟨59817492687026410257761099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39878328458017606838507399 59817492687026410257761099)
          ·
            refine ⟨89726239030539615386641649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59817492687026410257761099 89726239030539615386641649)
            ·
              refine ⟨67294679272904711539981237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89726239030539615386641649 67294679272904711539981237)
              ·
                refine ⟨6308876181834816706873241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 67294679272904711539981237 6308876181834816706873241)
                ·
                  refine ⟨4731657136376112530154931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6308876181834816706873241 4731657136376112530154931)
                  ·
                    refine ⟨7097485704564168795232397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4731657136376112530154931 7097485704564168795232397)
                    ·
                      refine ⟨2661557139211563298212149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7097485704564168795232397 2661557139211563298212149)
                      ·
                        rfl

theorem cell23_5183364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 5, 2, 1, 3].length) (baseStart_5183364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5183364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5183364 prefixEnd_5183364 := by exact prefixLift 5183364
  have htrace : WordTrace (prefixWord ++ tailWord_5183364) baseStart_5183364 baseEnd_5183364 := by
    simpa [prefixWord, tailWord_5183364, baseEnd_5183364] using wordTrace_append hprefix tailTrace_5183364
  have hstable : (prefixWord ++ tailWord_5183364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5183364).length < 2 ^ (prefixWord ++ tailWord_5183364).sum := by decide
  have hdescent : baseEnd_5183364 < baseStart_5183364 := by decide
  rcases family_descends (prefixWord ++ tailWord_5183364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5183440 : List Nat := [2, 1, 1, 1, 1, 2, 4, 3, 1, 7]
def baseStart_5183440 : Nat := 118140960795 + 5183440 * 2 ^ 59
def prefixEnd_5183440 : Nat := 4983230072969 + 3 ^ 40 * 5183440 * 2
def baseEnd_5183440 : Nat := 887198721247101666953933

theorem tailTrace_5183440 : CollatzResearch.WordTrace tailWord_5183440 prefixEnd_5183440 887198721247101666953933 := by
  unfold tailWord_5183440
  simp only [CollatzResearch.WordTrace]
  refine ⟨94527794170644807958937887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126037058894193077278583849 94527794170644807958937887)
  ·
    refine ⟨141791691255967211938406831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94527794170644807958937887 141791691255967211938406831)
    ·
      refine ⟨212687536883950817907610247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141791691255967211938406831 212687536883950817907610247)
      ·
        refine ⟨319031305325926226861415371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212687536883950817907610247 319031305325926226861415371)
        ·
          refine ⟨478546957988889340292123057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 319031305325926226861415371 478546957988889340292123057)
          ·
            refine ⟨358910218491667005219092293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 478546957988889340292123057 358910218491667005219092293)
            ·
              refine ⟨67295665967187563478579805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 358910218491667005219092293 67295665967187563478579805)
              ·
                refine ⟨25235874737695336304467427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67295665967187563478579805 25235874737695336304467427)
                ·
                  refine ⟨37853812106543004456701141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25235874737695336304467427 37853812106543004456701141)
                  ·
                    refine ⟨887198721247101666953933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37853812106543004456701141 887198721247101666953933)
                    ·
                      rfl

theorem cell23_5183440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 3, 1, 7].length) (baseStart_5183440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5183440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5183440 prefixEnd_5183440 := by exact prefixLift 5183440
  have htrace : WordTrace (prefixWord ++ tailWord_5183440) baseStart_5183440 baseEnd_5183440 := by
    simpa [prefixWord, tailWord_5183440, baseEnd_5183440] using wordTrace_append hprefix tailTrace_5183440
  have hstable : (prefixWord ++ tailWord_5183440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5183440).length < 2 ^ (prefixWord ++ tailWord_5183440).sum := by decide
  have hdescent : baseEnd_5183440 < baseStart_5183440 := by decide
  rcases family_descends (prefixWord ++ tailWord_5183440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5183444 : List Nat := [2, 4, 1, 2, 1, 1, 2, 5, 5]
def baseStart_5183444 : Nat := 118140960795 + 5183444 * 2 ^ 59
def prefixEnd_5183444 : Nat := 4983230072969 + 3 ^ 40 * 5183444 * 2
def baseEnd_5183444 : Nat := 295733135295991442801309

theorem tailTrace_5183444 : CollatzResearch.WordTrace tailWord_5183444 prefixEnd_5183444 295733135295991442801309 := by
  unfold tailWord_5183444
  simp only [CollatzResearch.WordTrace]
  refine ⟨94527867116637562300510693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126037156155516749734014257 94527867116637562300510693)
  ·
    refine ⟨17723975084369542931345755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94527867116637562300510693 17723975084369542931345755)
    ·
      refine ⟨26585962626554314397018633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17723975084369542931345755 26585962626554314397018633)
      ·
        refine ⟨19939471969915735797763975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26585962626554314397018633 19939471969915735797763975)
        ·
          refine ⟨29909207954873603696645963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19939471969915735797763975 29909207954873603696645963)
          ·
            refine ⟨44863811932310405544968945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29909207954873603696645963 44863811932310405544968945)
            ·
              refine ⟨33647858949232804158726709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44863811932310405544968945 33647858949232804158726709)
              ·
                refine ⟨3154486776490575389880629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33647858949232804158726709 3154486776490575389880629)
                ·
                  refine ⟨295733135295991442801309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3154486776490575389880629 295733135295991442801309)
                  ·
                    rfl

theorem cell23_5183444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 5, 5].length) (baseStart_5183444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5183444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5183444 prefixEnd_5183444 := by exact prefixLift 5183444
  have htrace : WordTrace (prefixWord ++ tailWord_5183444) baseStart_5183444 baseEnd_5183444 := by
    simpa [prefixWord, tailWord_5183444, baseEnd_5183444] using wordTrace_append hprefix tailTrace_5183444
  have hstable : (prefixWord ++ tailWord_5183444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5183444).length < 2 ^ (prefixWord ++ tailWord_5183444).sum := by decide
  have hdescent : baseEnd_5183444 < baseStart_5183444 := by decide
  rcases family_descends (prefixWord ++ tailWord_5183444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5183457 : List Nat := [1, 2, 3, 1, 2, 1, 4, 2, 2, 5]
def baseStart_5183457 : Nat := 118140960795 + 5183457 * 2 ^ 59
def prefixEnd_5183457 : Nat := 4983230072969 + 3 ^ 40 * 5183457 * 2
def baseEnd_5183457 : Nat := 887201630970810478116407

theorem tailTrace_5183457 : CollatzResearch.WordTrace tailWord_5183457 prefixEnd_5183457 887201630970810478116407 := by
  unfold tailWord_5183457
  simp only [CollatzResearch.WordTrace]
  refine ⟨189056208382228027821244625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126037472254818685214163083 189056208382228027821244625)
  ·
    refine ⟨141792156286671020865933469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189056208382228027821244625 141792156286671020865933469)
    ·
      refine ⟨53172058607501632824725051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141792156286671020865933469 53172058607501632824725051)
      ·
        refine ⟨79758087911252449237087577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53172058607501632824725051 79758087911252449237087577)
        ·
          refine ⟨59818565933439336927815683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79758087911252449237087577 59818565933439336927815683)
          ·
            refine ⟨89727848900159005391723525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59818565933439336927815683 89727848900159005391723525)
            ·
              refine ⟨16823971668779813510948161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 89727848900159005391723525 16823971668779813510948161)
              ·
                refine ⟨12617978751584860133211121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16823971668779813510948161 12617978751584860133211121)
                ·
                  refine ⟨9463484063688645099908341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12617978751584860133211121 9463484063688645099908341)
                  ·
                    refine ⟨887201630970810478116407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9463484063688645099908341 887201630970810478116407)
                    ·
                      rfl

theorem cell23_5183457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 2, 2, 5].length) (baseStart_5183457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5183457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5183457 prefixEnd_5183457 := by exact prefixLift 5183457
  have htrace : WordTrace (prefixWord ++ tailWord_5183457) baseStart_5183457 baseEnd_5183457 := by
    simpa [prefixWord, tailWord_5183457, baseEnd_5183457] using wordTrace_append hprefix tailTrace_5183457
  have hstable : (prefixWord ++ tailWord_5183457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5183457).length < 2 ^ (prefixWord ++ tailWord_5183457).sum := by decide
  have hdescent : baseEnd_5183457 < baseStart_5183457 := by decide
  rcases family_descends (prefixWord ++ tailWord_5183457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5183521 : List Nat := [1, 2, 3, 2, 4, 1, 2, 1, 3, 4]
def baseStart_5183521 : Nat := 118140960795 + 5183521 * 2 ^ 59
def prefixEnd_5183521 : Nat := 4983230072969 + 3 ^ 40 * 5183521 * 2
def baseEnd_5183521 : Nat := 887212585224773061316309

theorem tailTrace_5183521 : CollatzResearch.WordTrace tailWord_5183521 prefixEnd_5183521 887212585224773061316309 := by
  unfold tailWord_5183521
  simp only [CollatzResearch.WordTrace]
  refine ⟨189058542653996166751574417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126039028435997444501049611 189058542653996166751574417)
  ·
    refine ⟨141793906990497125063680813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189058542653996166751574417 141793906990497125063680813)
    ·
      refine ⟨53172715121436421898880305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141793906990497125063680813 53172715121436421898880305)
      ·
        refine ⟨39879536341077316424160229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53172715121436421898880305 39879536341077316424160229)
        ·
          refine ⟨7477413063951996829530043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39879536341077316424160229 7477413063951996829530043)
          ·
            refine ⟨11216119595927995244295065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7477413063951996829530043 11216119595927995244295065)
            ·
              refine ⟨8412089696945996433221299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11216119595927995244295065 8412089696945996433221299)
              ·
                refine ⟨12618134545418994649831949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8412089696945996433221299 12618134545418994649831949)
                ·
                  refine ⟨4731800454532122993686981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12618134545418994649831949 4731800454532122993686981)
                  ·
                    refine ⟨887212585224773061316309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4731800454532122993686981 887212585224773061316309)
                    ·
                      rfl

theorem cell23_5183521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 2, 1, 3, 4].length) (baseStart_5183521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5183521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5183521 prefixEnd_5183521 := by exact prefixLift 5183521
  have htrace : WordTrace (prefixWord ++ tailWord_5183521) baseStart_5183521 baseEnd_5183521 := by
    simpa [prefixWord, tailWord_5183521, baseEnd_5183521] using wordTrace_append hprefix tailTrace_5183521
  have hstable : (prefixWord ++ tailWord_5183521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5183521).length < 2 ^ (prefixWord ++ tailWord_5183521).sum := by decide
  have hdescent : baseEnd_5183521 < baseStart_5183521 := by decide
  rcases family_descends (prefixWord ++ tailWord_5183521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5183564 : List Nat := [2, 2, 1, 3, 1, 1, 4, 3, 1, 5]
def baseStart_5183564 : Nat := 118140960795 + 5183564 * 2 ^ 59
def prefixEnd_5183564 : Nat := 4983230072969 + 3 ^ 40 * 5183564 * 2
def baseEnd_5183564 : Nat := 887219945114154171903743

theorem tailTrace_5183564 : CollatzResearch.WordTrace tailWord_5183564 prefixEnd_5183564 887219945114154171903743 := by
  unfold tailWord_5183564
  simp only [CollatzResearch.WordTrace]
  refine ⟨94530055496420192547694873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126040073995226923396926497 94530055496420192547694873)
  ·
    refine ⟨70897541622315144410771155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94530055496420192547694873 70897541622315144410771155)
    ·
      refine ⟨106346312433472716616156733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70897541622315144410771155 106346312433472716616156733)
      ·
        refine ⟨39879867162552268731058775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106346312433472716616156733 39879867162552268731058775)
        ·
          refine ⟨59819800743828403096588163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39879867162552268731058775 59819800743828403096588163)
          ·
            refine ⟨89729701115742604644882245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59819800743828403096588163 89729701115742604644882245)
            ·
              refine ⟨16824318959201738370915421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 89729701115742604644882245 16824318959201738370915421)
              ·
                refine ⟨6309119609700651889093283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16824318959201738370915421 6309119609700651889093283)
                ·
                  refine ⟨9463679414550977833639925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6309119609700651889093283 9463679414550977833639925)
                  ·
                    refine ⟨887219945114154171903743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9463679414550977833639925 887219945114154171903743)
                    ·
                      rfl

theorem cell23_5183564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 3, 1, 5].length) (baseStart_5183564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5183564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5183564 prefixEnd_5183564 := by exact prefixLift 5183564
  have htrace : WordTrace (prefixWord ++ tailWord_5183564) baseStart_5183564 baseEnd_5183564 := by
    simpa [prefixWord, tailWord_5183564, baseEnd_5183564] using wordTrace_append hprefix tailTrace_5183564
  have hstable : (prefixWord ++ tailWord_5183564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5183564).length < 2 ^ (prefixWord ++ tailWord_5183564).sum := by decide
  have hdescent : baseEnd_5183564 < baseStart_5183564 := by decide
  rcases family_descends (prefixWord ++ tailWord_5183564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5183601 : List Nat := [1, 2, 2, 2, 1, 1, 4, 1, 5, 2, 2]
def baseStart_5183601 : Nat := 118140960795 + 5183601 * 2 ^ 59
def prefixEnd_5183601 : Nat := 4983230072969 + 3 ^ 40 * 5183601 * 2
def baseEnd_5183601 : Nat := 2661678834126678870948559

theorem tailTrace_5183601 : CollatzResearch.WordTrace tailWord_5183601 prefixEnd_5183601 2661678834126678870948559 := by
  unfold tailWord_5183601
  simp only [CollatzResearch.WordTrace]
  refine ⟨189061460493706340414486657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126040973662470893609657771 189061460493706340414486657)
  ·
    refine ⟨141796095370279755310864993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189061460493706340414486657 141796095370279755310864993)
    ·
      refine ⟨106347071527709816483148745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141796095370279755310864993 106347071527709816483148745)
      ·
        refine ⟨79760303645782362362361559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106347071527709816483148745 79760303645782362362361559)
        ·
          refine ⟨119640455468673543543542339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79760303645782362362361559 119640455468673543543542339)
          ·
            refine ⟨179460683203010315315313509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119640455468673543543542339 179460683203010315315313509)
            ·
              refine ⟨33648878100564434121621283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 179460683203010315315313509 33648878100564434121621283)
              ·
                refine ⟨50473317150846651182431925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33648878100564434121621283 50473317150846651182431925)
                ·
                  refine ⟨4731873482891873548352993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 50473317150846651182431925 4731873482891873548352993)
                  ·
                    refine ⟨3548905112168905161264745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4731873482891873548352993 3548905112168905161264745)
                    ·
                      refine ⟨2661678834126678870948559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3548905112168905161264745 2661678834126678870948559)
                      ·
                        rfl

theorem cell23_5183601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 1, 5, 2, 2].length) (baseStart_5183601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5183601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5183601 prefixEnd_5183601 := by exact prefixLift 5183601
  have htrace : WordTrace (prefixWord ++ tailWord_5183601) baseStart_5183601 baseEnd_5183601 := by
    simpa [prefixWord, tailWord_5183601, baseEnd_5183601] using wordTrace_append hprefix tailTrace_5183601
  have hstable : (prefixWord ++ tailWord_5183601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5183601).length < 2 ^ (prefixWord ++ tailWord_5183601).sum := by decide
  have hdescent : baseEnd_5183601 < baseStart_5183601 := by decide
  rcases family_descends (prefixWord ++ tailWord_5183601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5183607 : List Nat := [1, 1, 3, 1, 1, 5, 2, 9]
def baseStart_5183607 : Nat := 118140960795 + 5183607 * 2 ^ 59
def prefixEnd_5183607 : Nat := 4983230072969 + 3 ^ 40 * 5183607 * 2
def baseEnd_5183607 : Nat := 98580811667059475832353

theorem tailTrace_5183607 : CollatzResearch.WordTrace tailWord_5183607 prefixEnd_5183607 98580811667059475832353 := by
  unfold tailWord_5183607
  simp only [CollatzResearch.WordTrace]
  refine ⟨189061679331684603439205075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126041119554456402292803383 189061679331684603439205075)
  ·
    refine ⟨283592518997526905158807613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189061679331684603439205075 283592518997526905158807613)
    ·
      refine ⟨106347194624072589434552855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 283592518997526905158807613 106347194624072589434552855)
      ·
        refine ⟨159520791936108884151829283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106347194624072589434552855 159520791936108884151829283)
        ·
          refine ⟨239281187904163326227743925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159520791936108884151829283 239281187904163326227743925)
          ·
            refine ⟨22432611366015311833850993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 239281187904163326227743925 22432611366015311833850993)
            ·
              refine ⟨16824458524511483875388245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22432611366015311833850993 16824458524511483875388245)
              ·
                refine ⟨98580811667059475832353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16824458524511483875388245 98580811667059475832353)
                ·
                  rfl

theorem cell23_5183607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 9].length) (baseStart_5183607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5183607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5183607 prefixEnd_5183607 := by exact prefixLift 5183607
  have htrace : WordTrace (prefixWord ++ tailWord_5183607) baseStart_5183607 baseEnd_5183607 := by
    simpa [prefixWord, tailWord_5183607, baseEnd_5183607] using wordTrace_append hprefix tailTrace_5183607
  have hstable : (prefixWord ++ tailWord_5183607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5183607).length < 2 ^ (prefixWord ++ tailWord_5183607).sum := by decide
  have hdescent : baseEnd_5183607 < baseStart_5183607 := by decide
  rcases family_descends (prefixWord ++ tailWord_5183607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5183621 : List Nat := [1, 3, 1, 1, 5, 3, 1, 1, 1, 1, 5]
def baseStart_5183621 : Nat := 118140960795 + 5183621 * 2 ^ 59
def prefixEnd_5183621 : Nat := 4983230072969 + 3 ^ 40 * 5183621 * 2
def baseEnd_5183621 : Nat := 2661689103739768792698467

theorem tailTrace_5183621 : CollatzResearch.WordTrace tailWord_5183621 prefixEnd_5183621 2661689103739768792698467 := by
  unfold tailWord_5183621
  simp only [CollatzResearch.WordTrace]
  refine ⟨189062189953633883830214717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126041459969089255886809811 189062189953633883830214717)
  ·
    refine ⟨70898321232612706436330519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 189062189953633883830214717 70898321232612706436330519)
    ·
      refine ⟨106347481848919059654495779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70898321232612706436330519 106347481848919059654495779)
      ·
        refine ⟨159521222773378589481743669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106347481848919059654495779 159521222773378589481743669)
        ·
          refine ⟨14955114635004242763913469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 159521222773378589481743669 14955114635004242763913469)
          ·
            refine ⟨5608167988126591036467551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14955114635004242763913469 5608167988126591036467551)
            ·
              refine ⟨8412251982189886554701327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5608167988126591036467551 8412251982189886554701327)
              ·
                refine ⟨12618377973284829832051991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8412251982189886554701327 12618377973284829832051991)
                ·
                  refine ⟨18927566959927244748077987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12618377973284829832051991 18927566959927244748077987)
                  ·
                    refine ⟨28391350439890867122116981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18927566959927244748077987 28391350439890867122116981)
                    ·
                      refine ⟨2661689103739768792698467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28391350439890867122116981 2661689103739768792698467)
                      ·
                        rfl

theorem cell23_5183621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 1, 1, 1, 1, 5].length) (baseStart_5183621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5183621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5183621 prefixEnd_5183621 := by exact prefixLift 5183621
  have htrace : WordTrace (prefixWord ++ tailWord_5183621) baseStart_5183621 baseEnd_5183621 := by
    simpa [prefixWord, tailWord_5183621, baseEnd_5183621] using wordTrace_append hprefix tailTrace_5183621
  have hstable : (prefixWord ++ tailWord_5183621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5183621).length < 2 ^ (prefixWord ++ tailWord_5183621).sum := by decide
  have hdescent : baseEnd_5183621 < baseStart_5183621 := by decide
  rcases family_descends (prefixWord ++ tailWord_5183621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5183637 : List Nat := [1, 3, 2, 1, 1, 1, 3, 1, 1, 9]
def baseStart_5183637 : Nat := 118140960795 + 5183637 * 2 ^ 59
def prefixEnd_5183637 : Nat := 4983230072969 + 3 ^ 40 * 5183637 * 2
def baseEnd_5183637 : Nat := 887232439810080243366131

theorem tailTrace_5183637 : CollatzResearch.WordTrace tailWord_5183637 prefixEnd_5183637 887232439810080243366131 := by
  unfold tailWord_5183637
  simp only [CollatzResearch.WordTrace]
  refine ⟨189062773521575918562797165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126041849014383945708531443 189062773521575918562797165)
  ·
    refine ⟨70898540070590969461048937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 189062773521575918562797165 70898540070590969461048937)
    ·
      refine ⟨53173905052943227095786703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70898540070590969461048937 53173905052943227095786703)
      ·
        refine ⟨79760857579414840643680055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53173905052943227095786703 79760857579414840643680055)
        ·
          refine ⟨119641286369122260965520083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79760857579414840643680055 119641286369122260965520083)
          ·
            refine ⟨179461929553683391448280125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119641286369122260965520083 179461929553683391448280125)
            ·
              refine ⟨67298223582631271793105047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 179461929553683391448280125 67298223582631271793105047)
              ·
                refine ⟨100947335373946907689657571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67298223582631271793105047 100947335373946907689657571)
                ·
                  refine ⟨151421003060920361534486357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 100947335373946907689657571 151421003060920361534486357)
                  ·
                    refine ⟨887232439810080243366131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 151421003060920361534486357 887232439810080243366131)
                    ·
                      rfl

theorem cell23_5183637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 9].length) (baseStart_5183637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5183637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5183637 prefixEnd_5183637 := by exact prefixLift 5183637
  have htrace : WordTrace (prefixWord ++ tailWord_5183637) baseStart_5183637 baseEnd_5183637 := by
    simpa [prefixWord, tailWord_5183637, baseEnd_5183637] using wordTrace_append hprefix tailTrace_5183637
  have hstable : (prefixWord ++ tailWord_5183637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5183637).length < 2 ^ (prefixWord ++ tailWord_5183637).sum := by decide
  have hdescent : baseEnd_5183637 < baseStart_5183637 := by decide
  rcases family_descends (prefixWord ++ tailWord_5183637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5183658 : List Nat := [3, 1, 5, 1, 2, 1, 3, 7]
def baseStart_5183658 : Nat := 118140960795 + 5183658 * 2 ^ 59
def prefixEnd_5183658 : Nat := 4983230072969 + 3 ^ 40 * 5183658 * 2
def baseEnd_5183658 : Nat := 98581781574962412886511

theorem tailTrace_5183658 : CollatzResearch.WordTrace tailWord_5183658 prefixEnd_5183658 98581781574962412886511 := by
  unfold tailWord_5183658
  simp only [CollatzResearch.WordTrace]
  refine ⟨47265884863624959787327907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126042359636333226099541085 47265884863624959787327907)
  ·
    refine ⟨70898827295437439680991861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47265884863624959787327907 70898827295437439680991861)
    ·
      refine ⟨6646765058947259970092987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 70898827295437439680991861 6646765058947259970092987)
      ·
        refine ⟨9970147588420889955139481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6646765058947259970092987 9970147588420889955139481)
        ·
          refine ⟨7477610691315667466354611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9970147588420889955139481 7477610691315667466354611)
          ·
            refine ⟨11216416036973501199531917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7477610691315667466354611 11216416036973501199531917)
            ·
              refine ⟨4206156013865062949824469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11216416036973501199531917 4206156013865062949824469)
              ·
                refine ⟨98581781574962412886511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4206156013865062949824469 98581781574962412886511)
                ·
                  rfl

theorem cell23_5183658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 3, 7].length) (baseStart_5183658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5183658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5183658 prefixEnd_5183658 := by exact prefixLift 5183658
  have htrace : WordTrace (prefixWord ++ tailWord_5183658) baseStart_5183658 baseEnd_5183658 := by
    simpa [prefixWord, tailWord_5183658, baseEnd_5183658] using wordTrace_append hprefix tailTrace_5183658
  have hstable : (prefixWord ++ tailWord_5183658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5183658).length < 2 ^ (prefixWord ++ tailWord_5183658).sum := by decide
  have hdescent : baseEnd_5183658 < baseStart_5183658 := by decide
  rcases family_descends (prefixWord ++ tailWord_5183658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5183667 : List Nat := [1, 1, 1, 2, 3, 2, 1, 1, 3, 8]
def baseStart_5183667 : Nat := 118140960795 + 5183667 * 2 ^ 59
def prefixEnd_5183667 : Nat := 4983230072969 + 3 ^ 40 * 5183667 * 2
def baseEnd_5183667 : Nat := 887237574616625204241085

theorem tailTrace_5183667 : CollatzResearch.WordTrace tailWord_5183667 prefixEnd_5183667 887237574616625204241085 := by
  unfold tailWord_5183667
  simp only [CollatzResearch.WordTrace]
  refine ⟨189063867711467233686389255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126042578474311489124259503 189063867711467233686389255)
  ·
    refine ⟨283595801567200850529583883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189063867711467233686389255 283595801567200850529583883)
    ·
      refine ⟨425393702350801275794375825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 283595801567200850529583883 425393702350801275794375825)
      ·
        refine ⟨319045276763100956845781869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 425393702350801275794375825 319045276763100956845781869)
        ·
          refine ⟨119641978786162858817168201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 319045276763100956845781869 119641978786162858817168201)
          ·
            refine ⟨89731484089622144112876151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119641978786162858817168201 89731484089622144112876151)
            ·
              refine ⟨134597226134433216169314227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89731484089622144112876151 134597226134433216169314227)
              ·
                refine ⟨201895839201649824253971341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 134597226134433216169314227 201895839201649824253971341)
                ·
                  refine ⟨75710939700618684095239253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 201895839201649824253971341 75710939700618684095239253)
                  ·
                    refine ⟨887237574616625204241085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 75710939700618684095239253 887237574616625204241085)
                    ·
                      rfl

theorem cell23_5183667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 3, 8].length) (baseStart_5183667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5183667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5183667 prefixEnd_5183667 := by exact prefixLift 5183667
  have htrace : WordTrace (prefixWord ++ tailWord_5183667) baseStart_5183667 baseEnd_5183667 := by
    simpa [prefixWord, tailWord_5183667, baseEnd_5183667] using wordTrace_append hprefix tailTrace_5183667
  have hstable : (prefixWord ++ tailWord_5183667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5183667).length < 2 ^ (prefixWord ++ tailWord_5183667).sum := by decide
  have hdescent : baseEnd_5183667 < baseStart_5183667 := by decide
  rcases family_descends (prefixWord ++ tailWord_5183667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5183669 : List Nat := [1, 3, 3, 4, 1, 1, 2, 3, 1, 2, 2]
def baseStart_5183669 : Nat := 118140960795 + 5183669 * 2 ^ 59
def prefixEnd_5183669 : Nat := 4983230072969 + 3 ^ 40 * 5183669 * 2
def baseEnd_5183669 : Nat := 2661713750811184604898247

theorem tailTrace_5183669 : CollatzResearch.WordTrace tailWord_5183669 prefixEnd_5183669 2661713750811184604898247 := by
  unfold tailWord_5183669
  simp only [CollatzResearch.WordTrace]
  refine ⟨189063940657459988027962061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126042627104973325351974707 189063940657459988027962061)
  ·
    refine ⟨70898977746547495510485773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 189063940657459988027962061 70898977746547495510485773)
    ·
      refine ⟨26587116654955310816432165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70898977746547495510485773 26587116654955310816432165)
      ·
        refine ⟨4985084372804120778081031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26587116654955310816432165 4985084372804120778081031)
        ·
          refine ⟨7477626559206181167121547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4985084372804120778081031 7477626559206181167121547)
          ·
            refine ⟨11216439838809271750682321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7477626559206181167121547 11216439838809271750682321)
            ·
              refine ⟨8412329879106953813011741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11216439838809271750682321 8412329879106953813011741)
              ·
                refine ⟨3154623704665107679879403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8412329879106953813011741 3154623704665107679879403)
                ·
                  refine ⟨4731935556997661519819105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3154623704665107679879403 4731935556997661519819105)
                  ·
                    refine ⟨3548951667748246139864329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4731935556997661519819105 3548951667748246139864329)
                    ·
                      refine ⟨2661713750811184604898247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3548951667748246139864329 2661713750811184604898247)
                      ·
                        rfl

theorem cell23_5183669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_5183669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5183669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5183669 prefixEnd_5183669 := by exact prefixLift 5183669
  have htrace : WordTrace (prefixWord ++ tailWord_5183669) baseStart_5183669 baseEnd_5183669 := by
    simpa [prefixWord, tailWord_5183669, baseEnd_5183669] using wordTrace_append hprefix tailTrace_5183669
  have hstable : (prefixWord ++ tailWord_5183669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5183669).length < 2 ^ (prefixWord ++ tailWord_5183669).sum := by decide
  have hdescent : baseEnd_5183669 < baseStart_5183669 := by decide
  rcases family_descends (prefixWord ++ tailWord_5183669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5183744 : List Nat := [2, 1, 1, 2, 1, 1, 5, 1, 4, 5]
def baseStart_5183744 : Nat := 118140960795 + 5183744 * 2 ^ 59
def prefixEnd_5183744 : Nat := 4983230072969 + 3 ^ 40 * 5183744 * 2
def baseEnd_5183744 : Nat := 887250753953423937153467

theorem tailTrace_5183744 : CollatzResearch.WordTrace tailWord_5183744 prefixEnd_5183744 887250753953423937153467 := by
  unfold tailWord_5183744
  simp only [CollatzResearch.WordTrace]
  refine ⟨94533338066094137918471143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126044450754792183891294857 94533338066094137918471143)
  ·
    refine ⟨141800007099141206877706715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94533338066094137918471143 141800007099141206877706715)
    ·
      refine ⟨212700010648711810316560073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141800007099141206877706715 212700010648711810316560073)
      ·
        refine ⟨159525007986533857737420055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 212700010648711810316560073 159525007986533857737420055)
        ·
          refine ⟨239287511979800786606130083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159525007986533857737420055 239287511979800786606130083)
          ·
            refine ⟨358931267969701179909195125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 239287511979800786606130083 358931267969701179909195125)
            ·
              refine ⟨33649806372159485616487043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 358931267969701179909195125 33649806372159485616487043)
              ·
                refine ⟨50474709558239228424730565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33649806372159485616487043 50474709558239228424730565)
                ·
                  refine ⟨9464008042169855329636981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50474709558239228424730565 9464008042169855329636981)
                  ·
                    refine ⟨887250753953423937153467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9464008042169855329636981 887250753953423937153467)
                    ·
                      rfl

theorem cell23_5183744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 1, 4, 5].length) (baseStart_5183744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5183744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5183744 prefixEnd_5183744 := by exact prefixLift 5183744
  have htrace : WordTrace (prefixWord ++ tailWord_5183744) baseStart_5183744 baseEnd_5183744 := by
    simpa [prefixWord, tailWord_5183744, baseEnd_5183744] using wordTrace_append hprefix tailTrace_5183744
  have hstable : (prefixWord ++ tailWord_5183744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5183744).length < 2 ^ (prefixWord ++ tailWord_5183744).sum := by decide
  have hdescent : baseEnd_5183744 < baseStart_5183744 := by decide
  rcases family_descends (prefixWord ++ tailWord_5183744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5183748 : List Nat := [2, 3, 2, 2, 3, 2, 1, 1, 7]
def baseStart_5183748 : Nat := 118140960795 + 5183748 * 2 ^ 59
def prefixEnd_5183748 : Nat := 4983230072969 + 3 ^ 40 * 5183748 * 2
def baseEnd_5183748 : Nat := 295750479531432199534487

theorem tailTrace_5183748 : CollatzResearch.WordTrace tailWord_5183748 prefixEnd_5183748 295750479531432199534487 := by
  unfold tailWord_5183748
  simp only [CollatzResearch.WordTrace]
  refine ⟨94533411012086892260043949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126044548016115856346725265 94533411012086892260043949)
  ·
    refine ⟨35450029129532584597516481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94533411012086892260043949 35450029129532584597516481)
    ·
      refine ⟨26587521847149438448137361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35450029129532584597516481 26587521847149438448137361)
      ·
        refine ⟨19940641385362078836103021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26587521847149438448137361 19940641385362078836103021)
        ·
          refine ⟨7477740519510779563538633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19940641385362078836103021 7477740519510779563538633)
          ·
            refine ⟨5608305389633084672653975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7477740519510779563538633 5608305389633084672653975)
            ·
              refine ⟨8412458084449627008980963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5608305389633084672653975 8412458084449627008980963)
              ·
                refine ⟨12618687126674440513471445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8412458084449627008980963 12618687126674440513471445)
                ·
                  refine ⟨295750479531432199534487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12618687126674440513471445 295750479531432199534487)
                  ·
                    rfl

theorem cell23_5183748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 1, 1, 7].length) (baseStart_5183748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5183748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5183748 prefixEnd_5183748 := by exact prefixLift 5183748
  have htrace : WordTrace (prefixWord ++ tailWord_5183748) baseStart_5183748 baseEnd_5183748 := by
    simpa [prefixWord, tailWord_5183748, baseEnd_5183748] using wordTrace_append hprefix tailTrace_5183748
  have hstable : (prefixWord ++ tailWord_5183748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5183748).length < 2 ^ (prefixWord ++ tailWord_5183748).sum := by decide
  have hdescent : baseEnd_5183748 < baseStart_5183748 := by decide
  rcases family_descends (prefixWord ++ tailWord_5183748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5183754 : List Nat := [3, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7]
def baseStart_5183754 : Nat := 118140960795 + 5183754 * 2 ^ 59
def prefixEnd_5183754 : Nat := 4983230072969 + 3 ^ 40 * 5183754 * 2
def baseEnd_5183754 : Nat := 2661757396666816772335355

theorem tailTrace_5183754 : CollatzResearch.WordTrace tailWord_5183754 prefixEnd_5183754 2661757396666816772335355 := by
  unfold tailWord_5183754
  simp only [CollatzResearch.WordTrace]
  refine ⟨47266760215538011886201579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126044693908101365029870877 47266760215538011886201579)
  ·
    refine ⟨70900140323307017829302369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47266760215538011886201579 70900140323307017829302369)
    ·
      refine ⟨53175105242480263371976777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70900140323307017829302369 53175105242480263371976777)
      ·
        refine ⟨39881328931860197528982583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53175105242480263371976777 39881328931860197528982583)
        ·
          refine ⟨59821993397790296293473875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39881328931860197528982583 59821993397790296293473875)
          ·
            refine ⟨89732990096685444440210813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59821993397790296293473875 89732990096685444440210813)
            ·
              refine ⟨33649871286257041665079055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89732990096685444440210813 33649871286257041665079055)
              ·
                refine ⟨50474806929385562497618583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33649871286257041665079055 50474806929385562497618583)
                ·
                  refine ⟨75712210394078343746427875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50474806929385562497618583 75712210394078343746427875)
                  ·
                    refine ⟨113568315591117515619641813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 75712210394078343746427875 113568315591117515619641813)
                    ·
                      refine ⟨2661757396666816772335355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 113568315591117515619641813 2661757396666816772335355)
                      ·
                        rfl

theorem cell23_5183754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7].length) (baseStart_5183754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5183754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5183754 prefixEnd_5183754 := by exact prefixLift 5183754
  have htrace : WordTrace (prefixWord ++ tailWord_5183754) baseStart_5183754 baseEnd_5183754 := by
    simpa [prefixWord, tailWord_5183754, baseEnd_5183754] using wordTrace_append hprefix tailTrace_5183754
  have hstable : (prefixWord ++ tailWord_5183754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5183754).length < 2 ^ (prefixWord ++ tailWord_5183754).sum := by decide
  have hdescent : baseEnd_5183754 < baseStart_5183754 := by decide
  rcases family_descends (prefixWord ++ tailWord_5183754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5183778 : List Nat := [3, 3, 1, 1, 3, 2, 2, 1, 2, 5]
def baseStart_5183778 : Nat := 118140960795 + 5183778 * 2 ^ 59
def prefixEnd_5183778 : Nat := 4983230072969 + 3 ^ 40 * 5183778 * 2
def baseEnd_5183778 : Nat := 887256573400841559478415

theorem tailTrace_5183778 : CollatzResearch.WordTrace tailWord_5183778 prefixEnd_5183778 887256573400841559478415 := by
  unfold tailWord_5183778
  simp only [CollatzResearch.WordTrace]
  refine ⟨47266979053516274910919997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126045277476043399762453325 47266979053516274910919997)
  ·
    refine ⟨17725117145068603091594999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47266979053516274910919997 17725117145068603091594999)
    ·
      refine ⟨26587675717602904637392499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17725117145068603091594999 26587675717602904637392499)
      ·
        refine ⟨39881513576404356956088749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26587675717602904637392499 39881513576404356956088749)
        ·
          refine ⟨14955567591151633858533281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39881513576404356956088749 14955567591151633858533281)
          ·
            refine ⟨11216675693363725393899961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14955567591151633858533281 11216675693363725393899961)
            ·
              refine ⟨8412506770022794045424971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11216675693363725393899961 8412506770022794045424971)
              ·
                refine ⟨12618760155034191068137457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8412506770022794045424971 12618760155034191068137457)
                ·
                  refine ⟨9464070116275643301103093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12618760155034191068137457 9464070116275643301103093)
                  ·
                    refine ⟨887256573400841559478415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9464070116275643301103093 887256573400841559478415)
                    ·
                      rfl

theorem cell23_5183778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 2, 1, 2, 5].length) (baseStart_5183778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5183778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5183778 prefixEnd_5183778 := by exact prefixLift 5183778
  have htrace : WordTrace (prefixWord ++ tailWord_5183778) baseStart_5183778 baseEnd_5183778 := by
    simpa [prefixWord, tailWord_5183778, baseEnd_5183778] using wordTrace_append hprefix tailTrace_5183778
  have hstable : (prefixWord ++ tailWord_5183778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5183778).length < 2 ^ (prefixWord ++ tailWord_5183778).sum := by decide
  have hdescent : baseEnd_5183778 < baseStart_5183778 := by decide
  rcases family_descends (prefixWord ++ tailWord_5183778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5183842 : List Nat := [3, 3, 2, 1, 1, 3, 2, 3, 1, 4]
def baseStart_5183842 : Nat := 118140960795 + 5183842 * 2 ^ 59
def prefixEnd_5183842 : Nat := 4983230072969 + 3 ^ 40 * 5183842 * 2
def baseEnd_5183842 : Nat := 887267527654804142678317

theorem tailTrace_5183842 : CollatzResearch.WordTrace tailWord_5183842 prefixEnd_5183842 887267527654804142678317 := by
  unfold tailWord_5183842
  simp only [CollatzResearch.WordTrace]
  refine ⟨47267562621458309643502445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126046833657222159049339853 47267562621458309643502445)
  ·
    refine ⟨17725335983046866116313417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47267562621458309643502445 17725335983046866116313417)
    ·
      refine ⟨13294001987285149587235063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17725335983046866116313417 13294001987285149587235063)
      ·
        refine ⟨19941002980927724380852595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13294001987285149587235063 19941002980927724380852595)
        ·
          refine ⟨29911504471391586571278893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19941002980927724380852595 29911504471391586571278893)
          ·
            refine ⟨11216814176771844964229585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29911504471391586571278893 11216814176771844964229585)
            ·
              refine ⟨8412610632578883723172189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11216814176771844964229585 8412610632578883723172189)
              ·
                refine ⟨3154728987217081396189571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8412610632578883723172189 3154728987217081396189571)
                ·
                  refine ⟨4732093480825622094284357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3154728987217081396189571 4732093480825622094284357)
                  ·
                    refine ⟨887267527654804142678317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4732093480825622094284357 887267527654804142678317)
                    ·
                      rfl

theorem cell23_5183842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 2, 3, 1, 4].length) (baseStart_5183842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5183842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5183842 prefixEnd_5183842 := by exact prefixLift 5183842
  have htrace : WordTrace (prefixWord ++ tailWord_5183842) baseStart_5183842 baseEnd_5183842 := by
    simpa [prefixWord, tailWord_5183842, baseEnd_5183842] using wordTrace_append hprefix tailTrace_5183842
  have hstable : (prefixWord ++ tailWord_5183842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5183842).length < 2 ^ (prefixWord ++ tailWord_5183842).sum := by decide
  have hdescent : baseEnd_5183842 < baseStart_5183842 := by decide
  rcases family_descends (prefixWord ++ tailWord_5183842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5183851 : List Nat := [1, 1, 1, 1, 2, 2, 2, 7, 1, 5]
def baseStart_5183851 : Nat := 118140960795 + 5183851 * 2 ^ 59
def prefixEnd_5183851 : Nat := 4983230072969 + 3 ^ 40 * 5183851 * 2
def baseEnd_5183851 : Nat := 887269068096767630940803

theorem tailTrace_5183851 : CollatzResearch.WordTrace tailWord_5183851 prefixEnd_5183851 887269068096767630940803 := by
  unfold tailWord_5183851
  simp only [CollatzResearch.WordTrace]
  refine ⟨189070578742800633111087407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126047052495200422074058271 189070578742800633111087407)
  ·
    refine ⟨283605868114200949666631111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189070578742800633111087407 283605868114200949666631111)
    ·
      refine ⟨425408802171301424499946667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 283605868114200949666631111 425408802171301424499946667)
      ·
        refine ⟨638113203256952136749920001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 425408802171301424499946667 638113203256952136749920001)
        ·
          refine ⟨478584902442714102562440001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 638113203256952136749920001 478584902442714102562440001)
          ·
            refine ⟨358938676832035576921830001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 478584902442714102562440001 358938676832035576921830001)
            ·
              refine ⟨269204007624026682691372501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 358938676832035576921830001 269204007624026682691372501)
              ·
                refine ⟨6309468928688125375579043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 269204007624026682691372501 6309468928688125375579043)
                ·
                  refine ⟨9464203393032188063368565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6309468928688125375579043 9464203393032188063368565)
                  ·
                    refine ⟨887269068096767630940803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9464203393032188063368565 887269068096767630940803)
                    ·
                      rfl

theorem cell23_5183851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 7, 1, 5].length) (baseStart_5183851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5183851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5183851 prefixEnd_5183851 := by exact prefixLift 5183851
  have htrace : WordTrace (prefixWord ++ tailWord_5183851) baseStart_5183851 baseEnd_5183851 := by
    simpa [prefixWord, tailWord_5183851, baseEnd_5183851] using wordTrace_append hprefix tailTrace_5183851
  have hstable : (prefixWord ++ tailWord_5183851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5183851).length < 2 ^ (prefixWord ++ tailWord_5183851).sum := by decide
  have hdescent : baseEnd_5183851 < baseStart_5183851 := by decide
  rcases family_descends (prefixWord ++ tailWord_5183851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5183864 : List Nat := [2, 1, 2, 1, 1, 1, 1, 1, 1, 12]
def baseStart_5183864 : Nat := 118140960795 + 5183864 * 2 ^ 59
def prefixEnd_5183864 : Nat := 4983230072969 + 3 ^ 40 * 5183864 * 2
def baseEnd_5183864 : Nat := 887271293179603780653283

theorem tailTrace_5183864 : CollatzResearch.WordTrace tailWord_5183864 prefixEnd_5183864 887271293179603780653283 := by
  unfold tailWord_5183864
  simp only [CollatzResearch.WordTrace]
  refine ⟨94535526445876768165655323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126047368594502357554207097 94535526445876768165655323)
  ·
    refine ⟨141803289668815152248482985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94535526445876768165655323 141803289668815152248482985)
    ·
      refine ⟨106352467251611364186362239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141803289668815152248482985 106352467251611364186362239)
      ·
        refine ⟨159528700877417046279543359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106352467251611364186362239 159528700877417046279543359)
        ·
          refine ⟨239293051316125569419315039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159528700877417046279543359 239293051316125569419315039)
          ·
            refine ⟨358939576974188354128972559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 239293051316125569419315039 358939576974188354128972559)
            ·
              refine ⟨538409365461282531193458839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 358939576974188354128972559 538409365461282531193458839)
              ·
                refine ⟨807614048191923796790188259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 538409365461282531193458839 807614048191923796790188259)
                ·
                  refine ⟨1211421072287885695185282389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 807614048191923796790188259 1211421072287885695185282389)
                  ·
                    refine ⟨887271293179603780653283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 12 1211421072287885695185282389 887271293179603780653283)
                    ·
                      rfl

theorem cell23_5183864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 1, 12].length) (baseStart_5183864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5183864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5183864 prefixEnd_5183864 := by exact prefixLift 5183864
  have htrace : WordTrace (prefixWord ++ tailWord_5183864) baseStart_5183864 baseEnd_5183864 := by
    simpa [prefixWord, tailWord_5183864, baseEnd_5183864] using wordTrace_append hprefix tailTrace_5183864
  have hstable : (prefixWord ++ tailWord_5183864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5183864).length < 2 ^ (prefixWord ++ tailWord_5183864).sum := by decide
  have hdescent : baseEnd_5183864 < baseStart_5183864 := by decide
  rcases family_descends (prefixWord ++ tailWord_5183864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5183898 : List Nat := [3, 1, 1, 4, 1, 2, 1, 2, 4, 4]
def baseStart_5183898 : Nat := 118140960795 + 5183898 * 2 ^ 59
def prefixEnd_5183898 : Nat := 4983230072969 + 3 ^ 40 * 5183898 * 2
def baseEnd_5183898 : Nat := 887277112627021402978231

theorem tailTrace_5183898 : CollatzResearch.WordTrace tailWord_5183898 prefixEnd_5183898 887277112627021402978231 := by
  unfold tailWord_5183898
  simp only [CollatzResearch.WordTrace]
  refine ⟨47268073243407590034512087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126048195315753573425365565 47268073243407590034512087)
  ·
    refine ⟨70902109865111385051768131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47268073243407590034512087 70902109865111385051768131)
    ·
      refine ⟨106353164797667077577652197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70902109865111385051768131 106353164797667077577652197)
      ·
        refine ⟨19941218399562577045809787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 106353164797667077577652197 19941218399562577045809787)
        ·
          refine ⟨29911827599343865568714681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19941218399562577045809787 29911827599343865568714681)
          ·
            refine ⟨22433870699507899176536011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29911827599343865568714681 22433870699507899176536011)
            ·
              refine ⟨33650806049261848764804017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22433870699507899176536011 33650806049261848764804017)
              ·
                refine ⟨25238104536946386573603013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33650806049261848764804017 25238104536946386573603013)
                ·
                  refine ⟨4732144600677447482550565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25238104536946386573603013 4732144600677447482550565)
                  ·
                    refine ⟨887277112627021402978231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4732144600677447482550565 887277112627021402978231)
                    ·
                      rfl

theorem cell23_5183898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 2, 4, 4].length) (baseStart_5183898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5183898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5183898 prefixEnd_5183898 := by exact prefixLift 5183898
  have htrace : WordTrace (prefixWord ++ tailWord_5183898) baseStart_5183898 baseEnd_5183898 := by
    simpa [prefixWord, tailWord_5183898, baseEnd_5183898] using wordTrace_append hprefix tailTrace_5183898
  have hstable : (prefixWord ++ tailWord_5183898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5183898).length < 2 ^ (prefixWord ++ tailWord_5183898).sum := by decide
  have hdescent : baseEnd_5183898 < baseStart_5183898 := by decide
  rcases family_descends (prefixWord ++ tailWord_5183898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5183911 : List Nat := [1, 1, 6, 1, 1, 2, 11]
def baseStart_5183911 : Nat := 118140960795 + 5183911 * 2 ^ 59
def prefixEnd_5183911 : Nat := 4983230072969 + 3 ^ 40 * 5183911 * 2
def baseEnd_5183911 : Nat := 32862197692957687136693

theorem tailTrace_5183911 : CollatzResearch.WordTrace tailWord_5183911 prefixEnd_5183911 32862197692957687136693 := by
  unfold tailWord_5183911
  simp only [CollatzResearch.WordTrace]
  refine ⟨189072767122583263358271587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126048511415055508905514391 189072767122583263358271587)
  ·
    refine ⟨283609150683874895037407381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189072767122583263358271587 283609150683874895037407381)
    ·
      refine ⟨13294178938306635704878471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 283609150683874895037407381 13294178938306635704878471)
      ·
        refine ⟨19941268407459953557317707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13294178938306635704878471 19941268407459953557317707)
        ·
          refine ⟨29911902611189930335976561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19941268407459953557317707 29911902611189930335976561)
          ·
            refine ⟨22433926958392447751982421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29911902611189930335976561 22433926958392447751982421)
            ·
              refine ⟨32862197692957687136693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 22433926958392447751982421 32862197692957687136693)
              ·
                rfl

theorem cell23_5183911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 11].length) (baseStart_5183911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5183911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5183911 prefixEnd_5183911 := by exact prefixLift 5183911
  have htrace : WordTrace (prefixWord ++ tailWord_5183911) baseStart_5183911 baseEnd_5183911 := by
    simpa [prefixWord, tailWord_5183911, baseEnd_5183911] using wordTrace_append hprefix tailTrace_5183911
  have hstable : (prefixWord ++ tailWord_5183911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5183911).length < 2 ^ (prefixWord ++ tailWord_5183911).sum := by decide
  have hdescent : baseEnd_5183911 < baseStart_5183911 := by decide
  rcases family_descends (prefixWord ++ tailWord_5183911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5183932 : List Nat := [2, 2, 2, 4, 1, 1, 4, 1, 2, 4]
def baseStart_5183932 : Nat := 118140960795 + 5183932 * 2 ^ 59
def prefixEnd_5183932 : Nat := 4983230072969 + 3 ^ 40 * 5183932 * 2
def baseEnd_5183932 : Nat := 887282932074439025303179

theorem tailTrace_5183932 : CollatzResearch.WordTrace tailWord_5183932 prefixEnd_5183932 887282932074439025303179 := by
  unfold tailWord_5183932
  simp only [CollatzResearch.WordTrace]
  refine ⟨94536766527753591972393025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126049022037004789296524033 94536766527753591972393025)
  ·
    refine ⟨70902574895815193979294769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94536766527753591972393025 70902574895815193979294769)
    ·
      refine ⟨53176931171861395484471077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70902574895815193979294769 53176931171861395484471077)
      ·
        refine ⟨9970674594724011653338327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53176931171861395484471077 9970674594724011653338327)
        ·
          refine ⟨14956011892086017480007491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9970674594724011653338327 14956011892086017480007491)
          ·
            refine ⟨22434017838129026220011237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14956011892086017480007491 22434017838129026220011237)
            ·
              refine ⟨4206378344649192416252107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22434017838129026220011237 4206378344649192416252107)
              ·
                refine ⟨6309567516973788624378161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4206378344649192416252107 6309567516973788624378161)
                ·
                  refine ⟨4732175637730341468283621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6309567516973788624378161 4732175637730341468283621)
                  ·
                    refine ⟨887282932074439025303179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4732175637730341468283621 887282932074439025303179)
                    ·
                      rfl

theorem cell23_5183932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 4, 1, 2, 4].length) (baseStart_5183932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5183932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5183932 prefixEnd_5183932 := by exact prefixLift 5183932
  have htrace : WordTrace (prefixWord ++ tailWord_5183932) baseStart_5183932 baseEnd_5183932 := by
    simpa [prefixWord, tailWord_5183932, baseEnd_5183932] using wordTrace_append hprefix tailTrace_5183932
  have hstable : (prefixWord ++ tailWord_5183932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5183932).length < 2 ^ (prefixWord ++ tailWord_5183932).sum := by decide
  have hdescent : baseEnd_5183932 < baseStart_5183932 := by decide
  rcases family_descends (prefixWord ++ tailWord_5183932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5183973 : List Nat := [1, 3, 1, 5, 2, 2, 2, 2, 1, 2, 2]
def baseStart_5183973 : Nat := 118140960795 + 5183973 * 2 ^ 59
def prefixEnd_5183973 : Nat := 4983230072969 + 3 ^ 40 * 5183973 * 2
def baseEnd_5183973 : Nat := 2661869848930151415496849

theorem tailTrace_5183973 : CollatzResearch.WordTrace tailWord_5183973 prefixEnd_5183973 2661869848930151415496849 := by
  unfold tailWord_5183973
  simp only [CollatzResearch.WordTrace]
  refine ⟨189075028448358647947028573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126050018965572431964685715 189075028448358647947028573)
  ·
    refine ⟨70903135668134492980135715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 189075028448358647947028573 70903135668134492980135715)
    ·
      refine ⟨106354703502201739470203573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70903135668134492980135715 106354703502201739470203573)
      ·
        refine ⟨9970753453331413075331585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 106354703502201739470203573 9970753453331413075331585)
        ·
          refine ⟨7478065089998559806498689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9970753453331413075331585 7478065089998559806498689)
          ·
            refine ⟨5608548817498919854874017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7478065089998559806498689 5608548817498919854874017)
            ·
              refine ⟨4206411613124189891155513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5608548817498919854874017 4206411613124189891155513)
              ·
                refine ⟨3154808709843142418366635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4206411613124189891155513 3154808709843142418366635)
                ·
                  refine ⟨4732213064764713627549953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3154808709843142418366635 4732213064764713627549953)
                  ·
                    refine ⟨3549159798573535220662465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4732213064764713627549953 3549159798573535220662465)
                    ·
                      refine ⟨2661869848930151415496849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3549159798573535220662465 2661869848930151415496849)
                      ·
                        rfl

theorem cell23_5183973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 2, 2, 1, 2, 2].length) (baseStart_5183973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5183973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5183973 prefixEnd_5183973 := by exact prefixLift 5183973
  have htrace : WordTrace (prefixWord ++ tailWord_5183973) baseStart_5183973 baseEnd_5183973 := by
    simpa [prefixWord, tailWord_5183973, baseEnd_5183973] using wordTrace_append hprefix tailTrace_5183973
  have hstable : (prefixWord ++ tailWord_5183973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5183973).length < 2 ^ (prefixWord ++ tailWord_5183973).sum := by decide
  have hdescent : baseEnd_5183973 < baseStart_5183973 := by decide
  rcases family_descends (prefixWord ++ tailWord_5183973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5183978 : List Nat := [3, 1, 3, 1, 3, 1, 1, 1, 2, 3, 4]
def baseStart_5183978 : Nat := 118140960795 + 5183978 * 2 ^ 59
def prefixEnd_5183978 : Nat := 4983230072969 + 3 ^ 40 * 5183978 * 2
def baseEnd_5183978 : Nat := 2661872416333423895934325

theorem tailTrace_5183978 : CollatzResearch.WordTrace tailWord_5183978 prefixEnd_5183978 2661872416333423895934325 := by
  unfold tailWord_5183978
  simp only [CollatzResearch.WordTrace]
  refine ⟨47268802703335133450240147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126050140542227022533973725 47268802703335133450240147)
  ·
    refine ⟨70903204055002700175360221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47268802703335133450240147 70903204055002700175360221)
    ·
      refine ⟨26588701520626012565760083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70903204055002700175360221 26588701520626012565760083)
      ·
        refine ⟨39883052280939018848640125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26588701520626012565760083 39883052280939018848640125)
        ·
          refine ⟨14956144605352132068240047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39883052280939018848640125 14956144605352132068240047)
          ·
            refine ⟨22434216908028198102360071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14956144605352132068240047 22434216908028198102360071)
            ·
              refine ⟨33651325362042297153540107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22434216908028198102360071 33651325362042297153540107)
              ·
                refine ⟨50476988043063445730310161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33651325362042297153540107 50476988043063445730310161)
                ·
                  refine ⟨37857741032297584297732621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50476988043063445730310161 37857741032297584297732621)
                  ·
                    refine ⟨14196652887111594111649733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37857741032297584297732621 14196652887111594111649733)
                    ·
                      refine ⟨2661872416333423895934325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14196652887111594111649733 2661872416333423895934325)
                      ·
                        rfl

theorem cell23_5183978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 2, 3, 4].length) (baseStart_5183978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5183978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5183978 prefixEnd_5183978 := by exact prefixLift 5183978
  have htrace : WordTrace (prefixWord ++ tailWord_5183978) baseStart_5183978 baseEnd_5183978 := by
    simpa [prefixWord, tailWord_5183978, baseEnd_5183978] using wordTrace_append hprefix tailTrace_5183978
  have hstable : (prefixWord ++ tailWord_5183978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5183978).length < 2 ^ (prefixWord ++ tailWord_5183978).sum := by decide
  have hdescent : baseEnd_5183978 < baseStart_5183978 := by decide
  rcases family_descends (prefixWord ++ tailWord_5183978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5184029 : List Nat := [1, 4, 2, 2, 1, 2, 3, 2, 2, 2, 2]
def baseStart_5184029 : Nat := 118140960795 + 5184029 * 2 ^ 59
def prefixEnd_5184029 : Nat := 4983230072969 + 3 ^ 40 * 5184029 * 2
def baseEnd_5184029 : Nat := 2661898603846803196396591

theorem tailTrace_5184029 : CollatzResearch.WordTrace tailWord_5184029 prefixEnd_5184029 2661898603846803196396591 := by
  unfold tailWord_5184029
  simp only [CollatzResearch.WordTrace]
  refine ⟨189077070936155769511067141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126051380624103846340711427 189077070936155769511067141)
  ·
    refine ⟨35451950800529206783325089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 189077070936155769511067141 35451950800529206783325089)
    ·
      refine ⟨26588963100396905087493817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35451950800529206783325089 26588963100396905087493817)
      ·
        refine ⟨19941722325297678815620363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26588963100396905087493817 19941722325297678815620363)
        ·
          refine ⟨29912583487946518223430545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19941722325297678815620363 29912583487946518223430545)
          ·
            refine ⟨22434437615959888667572909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29912583487946518223430545 22434437615959888667572909)
            ·
              refine ⟨8412914105984958250339841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22434437615959888667572909 8412914105984958250339841)
              ·
                refine ⟨6309685579488718687754881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8412914105984958250339841 6309685579488718687754881)
                ·
                  refine ⟨4732264184616539015816161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6309685579488718687754881 4732264184616539015816161)
                  ·
                    refine ⟨3549198138462404261862121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4732264184616539015816161 3549198138462404261862121)
                    ·
                      refine ⟨2661898603846803196396591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3549198138462404261862121 2661898603846803196396591)
                      ·
                        rfl

theorem cell23_5184029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 3, 2, 2, 2, 2].length) (baseStart_5184029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5184029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5184029 prefixEnd_5184029 := by exact prefixLift 5184029
  have htrace : WordTrace (prefixWord ++ tailWord_5184029) baseStart_5184029 baseEnd_5184029 := by
    simpa [prefixWord, tailWord_5184029, baseEnd_5184029] using wordTrace_append hprefix tailTrace_5184029
  have hstable : (prefixWord ++ tailWord_5184029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5184029).length < 2 ^ (prefixWord ++ tailWord_5184029).sum := by decide
  have hdescent : baseEnd_5184029 < baseStart_5184029 := by decide
  rcases family_descends (prefixWord ++ tailWord_5184029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5184035 : List Nat := [1, 1, 1, 4, 4, 1, 2, 4, 5]
def baseStart_5184035 : Nat := 118140960795 + 5184035 * 2 ^ 59
def prefixEnd_5184035 : Nat := 4983230072969 + 3 ^ 40 * 5184035 * 2
def baseEnd_5184035 : Nat := 295766853858970019213507

theorem tailTrace_5184035 : CollatzResearch.WordTrace tailWord_5184035 prefixEnd_5184035 295766853858970019213507 := by
  unfold tailWord_5184035
  simp only [CollatzResearch.WordTrace]
  refine ⟨189077289774134032535785559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126051526516089355023857039 189077289774134032535785559)
  ·
    refine ⟨283615934661201048803678339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189077289774134032535785559 283615934661201048803678339)
    ·
      refine ⟨425423901991801573205517509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 283615934661201048803678339 425423901991801573205517509)
      ·
        refine ⟨79766981623462794976034533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 425423901991801573205517509 79766981623462794976034533)
        ·
          refine ⟨14956309054399274058006475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 79766981623462794976034533 14956309054399274058006475)
          ·
            refine ⟨22434463581598911087009713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14956309054399274058006475 22434463581598911087009713)
            ·
              refine ⟨16825847686199183315257285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22434463581598911087009713 16825847686199183315257285)
              ·
                refine ⟨3154846441162346871610741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16825847686199183315257285 3154846441162346871610741)
                ·
                  refine ⟨295766853858970019213507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3154846441162346871610741 295766853858970019213507)
                  ·
                    rfl

theorem cell23_5184035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 4, 5].length) (baseStart_5184035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5184035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5184035 prefixEnd_5184035 := by exact prefixLift 5184035
  have htrace : WordTrace (prefixWord ++ tailWord_5184035) baseStart_5184035 baseEnd_5184035 := by
    simpa [prefixWord, tailWord_5184035, baseEnd_5184035] using wordTrace_append hprefix tailTrace_5184035
  have hstable : (prefixWord ++ tailWord_5184035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5184035).length < 2 ^ (prefixWord ++ tailWord_5184035).sum := by decide
  have hdescent : baseEnd_5184035 < baseStart_5184035 := by decide
  rcases family_descends (prefixWord ++ tailWord_5184035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5184046 : List Nat := [4, 1, 3, 1, 4, 1, 1, 1, 1, 4, 2]
def baseStart_5184046 : Nat := 118140960795 + 5184046 * 2 ^ 59
def prefixEnd_5184046 : Nat := 4983230072969 + 3 ^ 40 * 5184046 * 2
def baseEnd_5184046 : Nat := 2661907333017929629884013

theorem tailTrace_5184046 : CollatzResearch.WordTrace tailWord_5184046 prefixEnd_5184046 2661907333017929629884013 := by
  unfold tailWord_5184046
  simp only [CollatzResearch.WordTrace]
  refine ⟨23634711372136772676804499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126051793984729454276290661 23634711372136772676804499)
  ·
    refine ⟨35452067058205159015206749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23634711372136772676804499 35452067058205159015206749)
    ·
      refine ⟨13294525146826934630702531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35452067058205159015206749 13294525146826934630702531)
      ·
        refine ⟨19941787720240401946053797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13294525146826934630702531 19941787720240401946053797)
        ·
          refine ⟨3739085197545075364885087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19941787720240401946053797 3739085197545075364885087)
          ·
            refine ⟨5608627796317613047327631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3739085197545075364885087 5608627796317613047327631)
            ·
              refine ⟨8412941694476419570991447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5608627796317613047327631 8412941694476419570991447)
              ·
                refine ⟨12619412541714629356487171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8412941694476419570991447 12619412541714629356487171)
                ·
                  refine ⟨18929118812571944034730757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12619412541714629356487171 18929118812571944034730757)
                  ·
                    refine ⟨3549209777357239506512017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18929118812571944034730757 3549209777357239506512017)
                    ·
                      refine ⟨2661907333017929629884013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3549209777357239506512017 2661907333017929629884013)
                      ·
                        rfl

theorem cell23_5184046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 1, 1, 1, 4, 2].length) (baseStart_5184046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5184046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5184046 prefixEnd_5184046 := by exact prefixLift 5184046
  have htrace : WordTrace (prefixWord ++ tailWord_5184046) baseStart_5184046 baseEnd_5184046 := by
    simpa [prefixWord, tailWord_5184046, baseEnd_5184046] using wordTrace_append hprefix tailTrace_5184046
  have hstable : (prefixWord ++ tailWord_5184046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5184046).length < 2 ^ (prefixWord ++ tailWord_5184046).sum := by decide
  have hdescent : baseEnd_5184046 < baseStart_5184046 := by decide
  rcases family_descends (prefixWord ++ tailWord_5184046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5184085 : List Nat := [1, 3, 2, 2, 1, 1, 2, 1, 4, 4, 2]
def baseStart_5184085 : Nat := 118140960795 + 5184085 * 2 ^ 59
def prefixEnd_5184085 : Nat := 4983230072969 + 3 ^ 40 * 5184085 * 2
def baseEnd_5184085 : Nat := 2661927358763454977296333

theorem tailTrace_5184085 : CollatzResearch.WordTrace tailWord_5184085 prefixEnd_5184085 2661927358763454977296333 := by
  unfold tailWord_5184085
  simp only [CollatzResearch.WordTrace]
  refine ⟨189079113423952891075105709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126052742282635260716737139 189079113423952891075105709)
  ·
    refine ⟨70904667533982334153164641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 189079113423952891075105709 70904667533982334153164641)
    ·
      refine ⟨53178500650486750614873481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70904667533982334153164641 53178500650486750614873481)
      ·
        refine ⟨39883875487865062961155111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53178500650486750614873481 39883875487865062961155111)
        ·
          refine ⟨59825813231797594441732667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39883875487865062961155111 59825813231797594441732667)
          ·
            refine ⟨89738719847696391662599001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59825813231797594441732667 89738719847696391662599001)
            ·
              refine ⟨67304039885772293746949251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89738719847696391662599001 67304039885772293746949251)
              ·
                refine ⟨100956059828658440620423877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67304039885772293746949251 100956059828658440620423877)
                ·
                  refine ⟨18929261217873457616329477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 100956059828658440620423877 18929261217873457616329477)
                  ·
                    refine ⟨3549236478351273303061777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18929261217873457616329477 3549236478351273303061777)
                    ·
                      refine ⟨2661927358763454977296333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3549236478351273303061777 2661927358763454977296333)
                      ·
                        rfl

theorem cell23_5184085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 4, 4, 2].length) (baseStart_5184085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5184085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5184085 prefixEnd_5184085 := by exact prefixLift 5184085
  have htrace : WordTrace (prefixWord ++ tailWord_5184085) baseStart_5184085 baseEnd_5184085 := by
    simpa [prefixWord, tailWord_5184085, baseEnd_5184085] using wordTrace_append hprefix tailTrace_5184085
  have hstable : (prefixWord ++ tailWord_5184085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5184085).length < 2 ^ (prefixWord ++ tailWord_5184085).sum := by decide
  have hdescent : baseEnd_5184085 < baseStart_5184085 := by decide
  rcases family_descends (prefixWord ++ tailWord_5184085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5184146 : List Nat := [3, 2, 3, 1, 2, 1, 4, 2, 1, 4]
def baseStart_5184146 : Nat := 118140960795 + 5184146 * 2 ^ 59
def prefixEnd_5184146 : Nat := 4983230072969 + 3 ^ 40 * 5184146 * 2
def baseEnd_5184146 : Nat := 887319560361126412877851

theorem tailTrace_5184146 : CollatzResearch.WordTrace tailWord_5184146 prefixEnd_5184146 887319560361126412877851 := by
  unfold tailWord_5184146
  simp only [CollatzResearch.WordTrace]
  refine ⟨47270334569182974623269073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126054225517821265662050861 47270334569182974623269073)
  ·
    refine ⟨35452750926887230967451805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47270334569182974623269073 35452750926887230967451805)
    ·
      refine ⟨13294781597582711612794427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35452750926887230967451805 13294781597582711612794427)
      ·
        refine ⟨19942172396374067419191641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13294781597582711612794427 19942172396374067419191641)
        ·
          refine ⟨14956629297280550564393731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19942172396374067419191641 14956629297280550564393731)
          ·
            refine ⟨22434943945920825846590597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14956629297280550564393731 22434943945920825846590597)
            ·
              refine ⟨4206551989860154846235737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22434943945920825846590597 4206551989860154846235737)
              ·
                refine ⟨3154913992395116134676803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4206551989860154846235737 3154913992395116134676803)
                ·
                  refine ⟨4732370988592674202015205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3154913992395116134676803 4732370988592674202015205)
                  ·
                    refine ⟨887319560361126412877851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4732370988592674202015205 887319560361126412877851)
                    ·
                      rfl

theorem cell23_5184146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 4, 2, 1, 4].length) (baseStart_5184146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5184146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5184146 prefixEnd_5184146 := by exact prefixLift 5184146
  have htrace : WordTrace (prefixWord ++ tailWord_5184146) baseStart_5184146 baseEnd_5184146 := by
    simpa [prefixWord, tailWord_5184146, baseEnd_5184146] using wordTrace_append hprefix tailTrace_5184146
  have hstable : (prefixWord ++ tailWord_5184146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5184146).length < 2 ^ (prefixWord ++ tailWord_5184146).sum := by decide
  have hdescent : baseEnd_5184146 < baseStart_5184146 := by decide
  rcases family_descends (prefixWord ++ tailWord_5184146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5184152 : List Nat := [2, 1, 2, 4, 1, 1, 2, 3, 3, 1, 3]
def baseStart_5184152 : Nat := 118140960795 + 5184152 * 2 ^ 59
def prefixEnd_5184152 : Nat := 4983230072969 + 3 ^ 40 * 5184152 * 2
def baseEnd_5184152 : Nat := 2661961761967306215158525

theorem tailTrace_5184152 : CollatzResearch.WordTrace tailWord_5184152 prefixEnd_5184152 2661961761967306215158525 := by
  unfold tailWord_5184152
  simp only [CollatzResearch.WordTrace]
  refine ⟨94540778557355080758897355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126054371409806774345196473 94540778557355080758897355)
  ·
    refine ⟨141811167836032621138346033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94540778557355080758897355 141811167836032621138346033)
    ·
      refine ⟨106358375877024465853759525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141811167836032621138346033 106358375877024465853759525)
      ·
        refine ⟨19942195476942087347579911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 106358375877024465853759525 19942195476942087347579911)
        ·
          refine ⟨29913293215413131021369867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19942195476942087347579911 29913293215413131021369867)
          ·
            refine ⟨44869939823119696532054801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29913293215413131021369867 44869939823119696532054801)
            ·
              refine ⟨33652454867339772399041101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44869939823119696532054801 33652454867339772399041101)
              ·
                refine ⟨12619670575252414649640413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33652454867339772399041101 12619670575252414649640413)
                ·
                  refine ⟨4732376465719655493615155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12619670575252414649640413 4732376465719655493615155)
                  ·
                    refine ⟨7098564698579483240422733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4732376465719655493615155 7098564698579483240422733)
                    ·
                      refine ⟨2661961761967306215158525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7098564698579483240422733 2661961761967306215158525)
                      ·
                        rfl

theorem cell23_5184152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 3, 3, 1, 3].length) (baseStart_5184152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5184152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5184152 prefixEnd_5184152 := by exact prefixLift 5184152
  have htrace : WordTrace (prefixWord ++ tailWord_5184152) baseStart_5184152 baseEnd_5184152 := by
    simpa [prefixWord, tailWord_5184152, baseEnd_5184152] using wordTrace_append hprefix tailTrace_5184152
  have hstable : (prefixWord ++ tailWord_5184152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5184152).length < 2 ^ (prefixWord ++ tailWord_5184152).sum := by decide
  have hdescent : baseEnd_5184152 < baseStart_5184152 := by decide
  rcases family_descends (prefixWord ++ tailWord_5184152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5184175 : List Nat := [1, 1, 2, 1, 2, 5, 2, 1, 3, 1, 4]
def baseStart_5184175 : Nat := 118140960795 + 5184175 * 2 ^ 59
def prefixEnd_5184175 : Nat := 4983230072969 + 3 ^ 40 * 5184175 * 2
def baseEnd_5184175 : Nat := 2661973572022359625170919

theorem tailTrace_5184175 : CollatzResearch.WordTrace tailWord_5184175 prefixEnd_5184175 2661973572022359625170919 := by
  unfold tailWord_5184175
  simp only [CollatzResearch.WordTrace]
  refine ⟨189082395993626836445881979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126054930662417890963921319 189082395993626836445881979)
  ·
    refine ⟨283623593990440254668822969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189082395993626836445881979 283623593990440254668822969)
    ·
      refine ⟨212717695492830191001617227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 283623593990440254668822969 212717695492830191001617227)
      ·
        refine ⟨319076543239245286502425841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212717695492830191001617227 319076543239245286502425841)
        ·
          refine ⟨239307407429433964876819381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 319076543239245286502425841 239307407429433964876819381)
          ·
            refine ⟨22435069446509434207201817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 239307407429433964876819381 22435069446509434207201817)
            ·
              refine ⟨16826302084882075655401363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22435069446509434207201817 16826302084882075655401363)
              ·
                refine ⟨25239453127323113483102045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16826302084882075655401363 25239453127323113483102045)
                ·
                  refine ⟨9464794922746167556163267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25239453127323113483102045 9464794922746167556163267)
                  ·
                    refine ⟨14197192384119251334244901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9464794922746167556163267 14197192384119251334244901)
                    ·
                      refine ⟨2661973572022359625170919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14197192384119251334244901 2661973572022359625170919)
                      ·
                        rfl

theorem cell23_5184175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 1, 3, 1, 4].length) (baseStart_5184175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5184175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5184175 prefixEnd_5184175 := by exact prefixLift 5184175
  have htrace : WordTrace (prefixWord ++ tailWord_5184175) baseStart_5184175 baseEnd_5184175 := by
    simpa [prefixWord, tailWord_5184175, baseEnd_5184175] using wordTrace_append hprefix tailTrace_5184175
  have hstable : (prefixWord ++ tailWord_5184175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5184175).length < 2 ^ (prefixWord ++ tailWord_5184175).sum := by decide
  have hdescent : baseEnd_5184175 < baseStart_5184175 := by decide
  rcases family_descends (prefixWord ++ tailWord_5184175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5184179 : List Nat := [1, 1, 1, 2, 3, 6, 1, 1, 2, 3, 2]
def baseStart_5184179 : Nat := 118140960795 + 5184179 * 2 ^ 59
def prefixEnd_5184179 : Nat := 4983230072969 + 3 ^ 40 * 5184179 * 2
def baseEnd_5184179 : Nat := 2661975625944977609520901

theorem tailTrace_5184179 : CollatzResearch.WordTrace tailWord_5184179 prefixEnd_5184179 2661975625944977609520901 := by
  unfold tailWord_5184179
  simp only [CollatzResearch.WordTrace]
  refine ⟨189082541885612345129027591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126055027923741563419351727 189082541885612345129027591)
  ·
    refine ⟨283623812828418517693541387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189082541885612345129027591 283623812828418517693541387)
    ·
      refine ⟨425435719242627776540312081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 283623812828418517693541387 425435719242627776540312081)
      ·
        refine ⟨319076789431970832405234061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 425435719242627776540312081 319076789431970832405234061)
        ·
          refine ⟨119653796036989062151962773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 319076789431970832405234061 119653796036989062151962773)
          ·
            refine ⟨5608771689233862288373255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 119653796036989062151962773 5608771689233862288373255)
            ·
              refine ⟨8413157533850793432559883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5608771689233862288373255 8413157533850793432559883)
              ·
                refine ⟨12619736300776190148839825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8413157533850793432559883 12619736300776190148839825)
                ·
                  refine ⟨9464802225582142611629869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12619736300776190148839825 9464802225582142611629869)
                  ·
                    refine ⟨3549300834593303479361201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9464802225582142611629869 3549300834593303479361201)
                    ·
                      refine ⟨2661975625944977609520901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3549300834593303479361201 2661975625944977609520901)
                      ·
                        rfl

theorem cell23_5184179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 1, 1, 2, 3, 2].length) (baseStart_5184179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5184179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5184179 prefixEnd_5184179 := by exact prefixLift 5184179
  have htrace : WordTrace (prefixWord ++ tailWord_5184179) baseStart_5184179 baseEnd_5184179 := by
    simpa [prefixWord, tailWord_5184179, baseEnd_5184179] using wordTrace_append hprefix tailTrace_5184179
  have hstable : (prefixWord ++ tailWord_5184179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5184179).length < 2 ^ (prefixWord ++ tailWord_5184179).sum := by decide
  have hdescent : baseEnd_5184179 < baseStart_5184179 := by decide
  rcases family_descends (prefixWord ++ tailWord_5184179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5184185 : List Nat := [1, 2, 1, 4, 1, 1, 1, 4, 4, 4]
def baseStart_5184185 : Nat := 118140960795 + 5184185 * 2 ^ 59
def prefixEnd_5184185 : Nat := 4983230072969 + 3 ^ 40 * 5184185 * 2
def baseEnd_5184185 : Nat := 887326235609634862015291

theorem tailTrace_5184185 : CollatzResearch.WordTrace tailWord_5184185 prefixEnd_5184185 887326235609634862015291 := by
  unfold tailWord_5184185
  simp only [CollatzResearch.WordTrace]
  refine ⟨189082760723590608153746009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126055173815727072102497339 189082760723590608153746009)
  ·
    refine ⟨141812070542692956115309507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189082760723590608153746009 141812070542692956115309507)
    ·
      refine ⟨212718105814039434172964261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141812070542692956115309507 212718105814039434172964261)
      ·
        refine ⟨39884644840132393907430799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 212718105814039434172964261 39884644840132393907430799)
        ·
          refine ⟨59826967260198590861146199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39884644840132393907430799 59826967260198590861146199)
          ·
            refine ⟨89740450890297886291719299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59826967260198590861146199 89740450890297886291719299)
            ·
              refine ⟨134610676335446829437578949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89740450890297886291719299 134610676335446829437578949)
              ·
                refine ⟨25239501812896280519546053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 134610676335446829437578949 25239501812896280519546053)
                ·
                  refine ⟨4732406589918052597414885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25239501812896280519546053 4732406589918052597414885)
                  ·
                    refine ⟨887326235609634862015291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4732406589918052597414885 887326235609634862015291)
                    ·
                      rfl

theorem cell23_5184185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 4, 4, 4].length) (baseStart_5184185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5184185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5184185 prefixEnd_5184185 := by exact prefixLift 5184185
  have htrace : WordTrace (prefixWord ++ tailWord_5184185) baseStart_5184185 baseEnd_5184185 := by
    simpa [prefixWord, tailWord_5184185, baseEnd_5184185] using wordTrace_append hprefix tailTrace_5184185
  have hstable : (prefixWord ++ tailWord_5184185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5184185).length < 2 ^ (prefixWord ++ tailWord_5184185).sum := by decide
  have hdescent : baseEnd_5184185 < baseStart_5184185 := by decide
  rcases family_descends (prefixWord ++ tailWord_5184185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5184189 : List Nat := [1, 4, 1, 2, 1, 5, 2, 1, 1, 5]
def baseStart_5184189 : Nat := 118140960795 + 5184189 * 2 ^ 59
def prefixEnd_5184189 : Nat := 4983230072969 + 3 ^ 40 * 5184189 * 2
def baseEnd_5184189 : Nat := 887326920250507523465285

theorem tailTrace_5184189 : CollatzResearch.WordTrace tailWord_5184189 prefixEnd_5184189 887326920250507523465285 := by
  unfold tailWord_5184189
  simp only [CollatzResearch.WordTrace]
  refine ⟨189082906615576116836891621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126055271077050744557927747 189082906615576116836891621)
  ·
    refine ⟨35453044990420521906917179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 189082906615576116836891621 35453044990420521906917179)
    ·
      refine ⟨53179567485630782860375769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35453044990420521906917179 53179567485630782860375769)
      ·
        refine ⟨39884675614223087145281827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53179567485630782860375769 39884675614223087145281827)
        ·
          refine ⟨59827013421334630717922741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39884675614223087145281827 59827013421334630717922741)
          ·
            refine ⟨5608782508250121629805257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 59827013421334630717922741 5608782508250121629805257)
            ·
              refine ⟨4206586881187591222353943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5608782508250121629805257 4206586881187591222353943)
              ·
                refine ⟨6309880321781386833530915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4206586881187591222353943 6309880321781386833530915)
                ·
                  refine ⟨9464820482672080250296373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6309880321781386833530915 9464820482672080250296373)
                  ·
                    refine ⟨887326920250507523465285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9464820482672080250296373 887326920250507523465285)
                    ·
                      rfl

theorem cell23_5184189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 2, 1, 1, 5].length) (baseStart_5184189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5184189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5184189 prefixEnd_5184189 := by exact prefixLift 5184189
  have htrace : WordTrace (prefixWord ++ tailWord_5184189) baseStart_5184189 baseEnd_5184189 := by
    simpa [prefixWord, tailWord_5184189, baseEnd_5184189] using wordTrace_append hprefix tailTrace_5184189
  have hstable : (prefixWord ++ tailWord_5184189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5184189).length < 2 ^ (prefixWord ++ tailWord_5184189).sum := by decide
  have hdescent : baseEnd_5184189 < baseStart_5184189 := by decide
  rcases family_descends (prefixWord ++ tailWord_5184189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5184192 : List Nat := [2, 1, 1, 2, 4, 3, 1, 3, 1, 1, 4]
def baseStart_5184192 : Nat := 118140960795 + 5184192 * 2 ^ 59
def prefixEnd_5184192 : Nat := 4983230072969 + 3 ^ 40 * 5184192 * 2
def baseEnd_5184192 : Nat := 2661982301193486058658341

theorem tailTrace_5184192 : CollatzResearch.WordTrace tailWord_5184192 prefixEnd_5184192 2661982301193486058658341 := by
  unfold tailWord_5184192
  simp only [CollatzResearch.WordTrace]
  refine ⟨94541508017282624174625415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126055344023043498899500553 94541508017282624174625415)
  ·
    refine ⟨141812262025923936261938123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94541508017282624174625415 141812262025923936261938123)
    ·
      refine ⟨212718393038885904392907185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141812262025923936261938123 212718393038885904392907185)
      ·
        refine ⟨159538794779164428294680389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 212718393038885904392907185 159538794779164428294680389)
        ·
          refine ⟨29913524021093330305252573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 159538794779164428294680389 29913524021093330305252573)
          ·
            refine ⟨11217571507909998864469715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29913524021093330305252573 11217571507909998864469715)
            ·
              refine ⟨16826357261864998296704573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11217571507909998864469715 16826357261864998296704573)
              ·
                refine ⟨6309883973199374361264215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16826357261864998296704573 6309883973199374361264215)
                ·
                  refine ⟨9464825959799061541896323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6309883973199374361264215 9464825959799061541896323)
                  ·
                    refine ⟨14197238939698592312844485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9464825959799061541896323 14197238939698592312844485)
                    ·
                      refine ⟨2661982301193486058658341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14197238939698592312844485 2661982301193486058658341)
                      ·
                        rfl

theorem cell23_5184192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 3, 1, 1, 4].length) (baseStart_5184192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5184192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5184192 prefixEnd_5184192 := by exact prefixLift 5184192
  have htrace : WordTrace (prefixWord ++ tailWord_5184192) baseStart_5184192 baseEnd_5184192 := by
    simpa [prefixWord, tailWord_5184192, baseEnd_5184192] using wordTrace_append hprefix tailTrace_5184192
  have hstable : (prefixWord ++ tailWord_5184192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5184192).length < 2 ^ (prefixWord ++ tailWord_5184192).sum := by decide
  have hdescent : baseEnd_5184192 < baseStart_5184192 := by decide
  rcases family_descends (prefixWord ++ tailWord_5184192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5184202 : List Nat := [3, 1, 2, 1, 4, 2, 1, 1, 4, 4]
def baseStart_5184202 : Nat := 118140960795 + 5184202 * 2 ^ 59
def prefixEnd_5184202 : Nat := 4983230072969 + 3 ^ 40 * 5184202 * 2
def baseEnd_5184202 : Nat := 887329145333343673177765

theorem tailTrace_5184202 : CollatzResearch.WordTrace tailWord_5184202 prefixEnd_5184202 887329145333343673177765 := by
  unfold tailWord_5184202
  simp only [CollatzResearch.WordTrace]
  refine ⟨47270845191132255014278715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126055587176352680038076573 47270845191132255014278715)
  ·
    refine ⟨70906267786698382521418073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47270845191132255014278715 70906267786698382521418073)
    ·
      refine ⟨53179700840023786891063555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70906267786698382521418073 53179700840023786891063555)
      ·
        refine ⟨79769551260035680336595333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53179700840023786891063555 79769551260035680336595333)
        ·
          refine ⟨14956790861256690063111625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 79769551260035680336595333 14956790861256690063111625)
          ·
            refine ⟨11217593145942517547333719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14956790861256690063111625 11217593145942517547333719)
            ·
              refine ⟨16826389718913776321000579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11217593145942517547333719 16826389718913776321000579)
              ·
                refine ⟨25239584578370664481500869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16826389718913776321000579 25239584578370664481500869)
                ·
                  refine ⟨4732422108444499590281413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25239584578370664481500869 4732422108444499590281413)
                  ·
                    refine ⟨887329145333343673177765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4732422108444499590281413 887329145333343673177765)
                    ·
                      rfl

theorem cell23_5184202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 1, 4, 4].length) (baseStart_5184202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5184202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5184202 prefixEnd_5184202 := by exact prefixLift 5184202
  have htrace : WordTrace (prefixWord ++ tailWord_5184202) baseStart_5184202 baseEnd_5184202 := by
    simpa [prefixWord, tailWord_5184202, baseEnd_5184202] using wordTrace_append hprefix tailTrace_5184202
  have hstable : (prefixWord ++ tailWord_5184202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5184202).length < 2 ^ (prefixWord ++ tailWord_5184202).sum := by decide
  have hdescent : baseEnd_5184202 < baseStart_5184202 := by decide
  rcases family_descends (prefixWord ++ tailWord_5184202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5184209 : List Nat := [1, 2, 2, 1, 2, 3, 4, 1, 3, 2, 2]
def baseStart_5184209 : Nat := 118140960795 + 5184209 * 2 ^ 59
def prefixEnd_5184209 : Nat := 4983230072969 + 3 ^ 40 * 5184209 * 2
def baseEnd_5184209 : Nat := 2661991030364612492145763

theorem tailTrace_5184209 : CollatzResearch.WordTrace tailWord_5184209 prefixEnd_5184209 2661991030364612492145763 := by
  unfold tailWord_5184209
  simp only [CollatzResearch.WordTrace]
  refine ⟨189083636075503660252619681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126055757383669106835079787 189083636075503660252619681)
  ·
    refine ⟨141812727056627745189464761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189083636075503660252619681 141812727056627745189464761)
    ·
      refine ⟨106359545292470808892098571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141812727056627745189464761 106359545292470808892098571)
      ·
        refine ⟨159539317938706213338147857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106359545292470808892098571 159539317938706213338147857)
        ·
          refine ⟨119654488454029660003610893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 159539317938706213338147857 119654488454029660003610893)
          ·
            refine ⟨44870433170261122501354085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 119654488454029660003610893 44870433170261122501354085)
            ·
              refine ⟨8413206219423960469003891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44870433170261122501354085 8413206219423960469003891)
              ·
                refine ⟨12619809329135940703505837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8413206219423960469003891 12619809329135940703505837)
                ·
                  refine ⟨4732428498425977763814689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12619809329135940703505837 4732428498425977763814689)
                  ·
                    refine ⟨3549321373819483322861017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4732428498425977763814689 3549321373819483322861017)
                    ·
                      refine ⟨2661991030364612492145763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3549321373819483322861017 2661991030364612492145763)
                      ·
                        rfl

theorem cell23_5184209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 4, 1, 3, 2, 2].length) (baseStart_5184209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5184209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5184209 prefixEnd_5184209 := by exact prefixLift 5184209
  have htrace : WordTrace (prefixWord ++ tailWord_5184209) baseStart_5184209 baseEnd_5184209 := by
    simpa [prefixWord, tailWord_5184209, baseEnd_5184209] using wordTrace_append hprefix tailTrace_5184209
  have hstable : (prefixWord ++ tailWord_5184209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5184209).length < 2 ^ (prefixWord ++ tailWord_5184209).sum := by decide
  have hdescent : baseEnd_5184209 < baseStart_5184209 := by decide
  rcases family_descends (prefixWord ++ tailWord_5184209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5184229 : List Nat := [1, 3, 1, 4, 1, 3, 2, 2, 1, 2, 3]
def baseStart_5184229 : Nat := 118140960795 + 5184229 * 2 ^ 59
def prefixEnd_5184229 : Nat := 4983230072969 + 3 ^ 40 * 5184229 * 2
def baseEnd_5184229 : Nat := 2662001299977702413895671

theorem tailTrace_5184229 : CollatzResearch.WordTrace tailWord_5184229 prefixEnd_5184229 2662001299977702413895671 := by
  unfold tailWord_5184229
  simp only [CollatzResearch.WordTrace]
  refine ⟨189084365535431203668347741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126056243690287469112231827 189084365535431203668347741)
  ·
    refine ⟨70906637075786701375630403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 189084365535431203668347741 70906637075786701375630403)
    ·
      refine ⟨106359955613680052063445605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70906637075786701375630403 106359955613680052063445605)
      ·
        refine ⟨19942491677565009761896051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 106359955613680052063445605 19942491677565009761896051)
        ·
          refine ⟨29913737516347514642844077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19942491677565009761896051 29913737516347514642844077)
          ·
            refine ⟨11217651568630317991066529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29913737516347514642844077 11217651568630317991066529)
            ·
              refine ⟨8413238676472738493299897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11217651568630317991066529 8413238676472738493299897)
              ·
                refine ⟨6309929007354553869974923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8413238676472738493299897 6309929007354553869974923)
                ·
                  refine ⟨9464893511031830804962385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6309929007354553869974923 9464893511031830804962385)
                  ·
                    refine ⟨7098670133273873103721789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9464893511031830804962385 7098670133273873103721789)
                    ·
                      refine ⟨2662001299977702413895671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7098670133273873103721789 2662001299977702413895671)
                      ·
                        rfl

theorem cell23_5184229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 2, 2, 1, 2, 3].length) (baseStart_5184229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5184229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5184229 prefixEnd_5184229 := by exact prefixLift 5184229
  have htrace : WordTrace (prefixWord ++ tailWord_5184229) baseStart_5184229 baseEnd_5184229 := by
    simpa [prefixWord, tailWord_5184229, baseEnd_5184229] using wordTrace_append hprefix tailTrace_5184229
  have hstable : (prefixWord ++ tailWord_5184229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5184229).length < 2 ^ (prefixWord ++ tailWord_5184229).sum := by decide
  have hdescent : baseEnd_5184229 < baseStart_5184229 := by decide
  rcases family_descends (prefixWord ++ tailWord_5184229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5184326 : List Nat := [6, 1, 1, 2, 2, 1, 1, 1, 2, 6]
def baseStart_5184326 : Nat := 118140960795 + 5184326 * 2 ^ 59
def prefixEnd_5184326 : Nat := 4983230072969 + 3 ^ 40 * 5184326 * 2
def baseEnd_5184326 : Nat := 887350369200396178127575

theorem tailTrace_5184326 : CollatzResearch.WordTrace tailWord_5184326 prefixEnd_5184326 887350369200396178127575 := by
  unfold tailWord_5184326
  simp only [CollatzResearch.WordTrace]
  refine ⟨5908996981752493413582151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 126058602277386526156419221 5908996981752493413582151)
  ·
    refine ⟨8863495472628740120373227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5908996981752493413582151 8863495472628740120373227)
    ·
      refine ⟨13295243208943110180559841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8863495472628740120373227 13295243208943110180559841)
      ·
        refine ⟨9971432406707332635419881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13295243208943110180559841 9971432406707332635419881)
        ·
          refine ⟨7478574305030499476564911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9971432406707332635419881 7478574305030499476564911)
          ·
            refine ⟨11217861457545749214847367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7478574305030499476564911 11217861457545749214847367)
            ·
              refine ⟨16826792186318623822271051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11217861457545749214847367 16826792186318623822271051)
              ·
                refine ⟨25240188279477935733406577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16826792186318623822271051 25240188279477935733406577)
                ·
                  refine ⟨18930141209608451800054933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25240188279477935733406577 18930141209608451800054933)
                  ·
                    refine ⟨887350369200396178127575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18930141209608451800054933 887350369200396178127575)
                    ·
                      rfl

theorem cell23_5184326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 1, 2, 6].length) (baseStart_5184326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5184326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5184326 prefixEnd_5184326 := by exact prefixLift 5184326
  have htrace : WordTrace (prefixWord ++ tailWord_5184326) baseStart_5184326 baseEnd_5184326 := by
    simpa [prefixWord, tailWord_5184326, baseEnd_5184326] using wordTrace_append hprefix tailTrace_5184326
  have hstable : (prefixWord ++ tailWord_5184326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5184326).length < 2 ^ (prefixWord ++ tailWord_5184326).sum := by decide
  have hdescent : baseEnd_5184326 < baseStart_5184326 := by decide
  rcases family_descends (prefixWord ++ tailWord_5184326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5184332 : List Nat := [2, 2, 1, 3, 3, 1, 1, 1, 1, 5, 3]
def baseStart_5184332 : Nat := 118140960795 + 5184332 * 2 ^ 59
def prefixEnd_5184332 : Nat := 4983230072969 + 3 ^ 40 * 5184332 * 2
def baseEnd_5184332 : Nat := 2662054188485115510907697

theorem tailTrace_5184332 : CollatzResearch.WordTrace tailWord_5184332 prefixEnd_5184332 2662054188485115510907697 := by
  unfold tailWord_5184332
  simp only [CollatzResearch.WordTrace]
  refine ⟨94544061127029026129673625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126058748169372034839564833 94544061127029026129673625)
  ·
    refine ⟨70908045845271769597255219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94544061127029026129673625 70908045845271769597255219)
    ·
      refine ⟨106362068767907654395882829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70908045845271769597255219 106362068767907654395882829)
      ·
        refine ⟨39885775787965370398456061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106362068767907654395882829 39885775787965370398456061)
        ·
          refine ⟨14957165920487013899421023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39885775787965370398456061 14957165920487013899421023)
          ·
            refine ⟨22435748880730520849131535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14957165920487013899421023 22435748880730520849131535)
            ·
              refine ⟨33653623321095781273697303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22435748880730520849131535 33653623321095781273697303)
              ·
                refine ⟨50480434981643671910545955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33653623321095781273697303 50480434981643671910545955)
                ·
                  refine ⟨75720652472465507865818933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50480434981643671910545955 75720652472465507865818933)
                  ·
                    refine ⟨7098811169293641362420525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 75720652472465507865818933 7098811169293641362420525)
                    ·
                      refine ⟨2662054188485115510907697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7098811169293641362420525 2662054188485115510907697)
                      ·
                        rfl

theorem cell23_5184332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 1, 1, 5, 3].length) (baseStart_5184332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5184332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5184332 prefixEnd_5184332 := by exact prefixLift 5184332
  have htrace : WordTrace (prefixWord ++ tailWord_5184332) baseStart_5184332 baseEnd_5184332 := by
    simpa [prefixWord, tailWord_5184332, baseEnd_5184332] using wordTrace_append hprefix tailTrace_5184332
  have hstable : (prefixWord ++ tailWord_5184332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5184332).length < 2 ^ (prefixWord ++ tailWord_5184332).sum := by decide
  have hdescent : baseEnd_5184332 < baseStart_5184332 := by decide
  rcases family_descends (prefixWord ++ tailWord_5184332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5184333 : List Nat := [1, 6, 1, 2, 2, 1, 2, 1, 1, 4, 2]
def baseStart_5184333 : Nat := 118140960795 + 5184333 * 2 ^ 59
def prefixEnd_5184333 : Nat := 4983230072969 + 3 ^ 40 * 5184333 * 2
def baseEnd_5184333 : Nat := 2662054701965770006995193

theorem tailTrace_5184333 : CollatzResearch.WordTrace tailWord_5184333 prefixEnd_5184333 2662054701965770006995193 := by
  unfold tailWord_5184333
  simp only [CollatzResearch.WordTrace]
  refine ⟨189088158727054429430133653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126058772484702952953422435 189088158727054429430133653)
  ·
    refine ⟨8863507440330676379537515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 189088158727054429430133653 8863507440330676379537515)
    ·
      refine ⟨13295261160496014569306273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8863507440330676379537515 13295261160496014569306273)
      ·
        refine ⟨9971445870372010926979705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13295261160496014569306273 9971445870372010926979705)
        ·
          refine ⟨7478584402779008195234779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9971445870372010926979705 7478584402779008195234779)
          ·
            refine ⟨11217876604168512292852169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7478584402779008195234779 11217876604168512292852169)
            ·
              refine ⟨8413407453126384219639127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11217876604168512292852169 8413407453126384219639127)
              ·
                refine ⟨12620111179689576329458691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8413407453126384219639127 12620111179689576329458691)
                ·
                  refine ⟨18930166769534364494188037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12620111179689576329458691 18930166769534364494188037)
                  ·
                    refine ⟨3549406269287693342660257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18930166769534364494188037 3549406269287693342660257)
                    ·
                      refine ⟨2662054701965770006995193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3549406269287693342660257 2662054701965770006995193)
                      ·
                        rfl

theorem cell23_5184333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 2, 1, 1, 4, 2].length) (baseStart_5184333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5184333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5184333 prefixEnd_5184333 := by exact prefixLift 5184333
  have htrace : WordTrace (prefixWord ++ tailWord_5184333) baseStart_5184333 baseEnd_5184333 := by
    simpa [prefixWord, tailWord_5184333, baseEnd_5184333] using wordTrace_append hprefix tailTrace_5184333
  have hstable : (prefixWord ++ tailWord_5184333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5184333).length < 2 ^ (prefixWord ++ tailWord_5184333).sum := by decide
  have hdescent : baseEnd_5184333 < baseStart_5184333 := by decide
  rcases family_descends (prefixWord ++ tailWord_5184333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5184375 : List Nat := [1, 1, 3, 1, 1, 2, 1, 3, 2, 3, 5]
def baseStart_5184375 : Nat := 118140960795 + 5184375 * 2 ^ 59
def prefixEnd_5184375 : Nat := 4983230072969 + 3 ^ 40 * 5184375 * 2
def baseEnd_5184375 : Nat := 2662076268153258842669999

theorem tailTrace_5184375 : CollatzResearch.WordTrace tailWord_5184375 prefixEnd_5184375 2662076268153258842669999 := by
  unfold tailWord_5184375
  simp only [CollatzResearch.WordTrace]
  refine ⟨189089690592902270603162579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126059793728601513735441719 189089690592902270603162579)
  ·
    refine ⟨283634535889353405904743869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189089690592902270603162579 283634535889353405904743869)
    ·
      refine ⟨106362950958507527214278951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 283634535889353405904743869 106362950958507527214278951)
      ·
        refine ⟨159544426437761290821418427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106362950958507527214278951 159544426437761290821418427)
        ·
          refine ⟨239316639656641936232127641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159544426437761290821418427 239316639656641936232127641)
          ·
            refine ⟨179487479742481452174095731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 239316639656641936232127641 179487479742481452174095731)
            ·
              refine ⟨269231219613722178261143597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 179487479742481452174095731 269231219613722178261143597)
              ·
                refine ⟨100961707355145816847928849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 269231219613722178261143597 100961707355145816847928849)
                ·
                  refine ⟨75721280516359362635946637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 100961707355145816847928849 75721280516359362635946637)
                  ·
                    refine ⟨28395480193634760988479989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 75721280516359362635946637 28395480193634760988479989)
                    ·
                      refine ⟨2662076268153258842669999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28395480193634760988479989 2662076268153258842669999)
                      ·
                        rfl

theorem cell23_5184375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 2, 3, 5].length) (baseStart_5184375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5184375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5184375 prefixEnd_5184375 := by exact prefixLift 5184375
  have htrace : WordTrace (prefixWord ++ tailWord_5184375) baseStart_5184375 baseEnd_5184375 := by
    simpa [prefixWord, tailWord_5184375, baseEnd_5184375] using wordTrace_append hprefix tailTrace_5184375
  have hstable : (prefixWord ++ tailWord_5184375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5184375).length < 2 ^ (prefixWord ++ tailWord_5184375).sum := by decide
  have hdescent : baseEnd_5184375 < baseStart_5184375 := by decide
  rcases family_descends (prefixWord ++ tailWord_5184375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5184389 : List Nat := [1, 3, 1, 1, 3, 3, 2, 1, 2, 4, 2]
def baseStart_5184389 : Nat := 118140960795 + 5184389 * 2 ^ 59
def prefixEnd_5184389 : Nat := 4983230072969 + 3 ^ 40 * 5184389 * 2
def baseEnd_5184389 : Nat := 2662083456882421787894935

theorem tailTrace_5184389 : CollatzResearch.WordTrace tailWord_5184389 prefixEnd_5184389 2662083456882421787894935 := by
  unfold tailWord_5184389
  simp only [CollatzResearch.WordTrace]
  refine ⟨189090201214851550994172221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126060134143234367329448147 189090201214851550994172221)
  ·
    refine ⟨70908825455569331622814583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 189090201214851550994172221 70908825455569331622814583)
    ·
      refine ⟨106363238183353997434221875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70908825455569331622814583 106363238183353997434221875)
      ·
        refine ⟨159544857275030996151332813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106363238183353997434221875 159544857275030996151332813)
        ·
          refine ⟨59829321478136623556749805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 159544857275030996151332813 59829321478136623556749805)
          ·
            refine ⟨22435995554301233833781177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59829321478136623556749805 22435995554301233833781177)
            ·
              refine ⟨16826996665725925375335883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22435995554301233833781177 16826996665725925375335883)
              ·
                refine ⟨25240494998588888063003825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16826996665725925375335883 25240494998588888063003825)
                ·
                  refine ⟨18930371248941666047252869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25240494998588888063003825 18930371248941666047252869)
                  ·
                    refine ⟨3549444609176562383859913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18930371248941666047252869 3549444609176562383859913)
                    ·
                      refine ⟨2662083456882421787894935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3549444609176562383859913 2662083456882421787894935)
                      ·
                        rfl

theorem cell23_5184389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 1, 2, 4, 2].length) (baseStart_5184389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5184389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5184389 prefixEnd_5184389 := by exact prefixLift 5184389
  have htrace : WordTrace (prefixWord ++ tailWord_5184389) baseStart_5184389 baseEnd_5184389 := by
    simpa [prefixWord, tailWord_5184389, baseEnd_5184389] using wordTrace_append hprefix tailTrace_5184389
  have hstable : (prefixWord ++ tailWord_5184389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5184389).length < 2 ^ (prefixWord ++ tailWord_5184389).sum := by decide
  have hdescent : baseEnd_5184389 < baseStart_5184389 := by decide
  rcases family_descends (prefixWord ++ tailWord_5184389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5184416 : List Nat := [2, 1, 1, 4, 1, 1, 5, 3, 1, 4]
def baseStart_5184416 : Nat := 118140960795 + 5184416 * 2 ^ 59
def prefixEnd_5184416 : Nat := 4983230072969 + 3 ^ 40 * 5184416 * 2
def baseEnd_5184416 : Nat := 887365773620031060752437

theorem tailTrace_5184416 : CollatzResearch.WordTrace tailWord_5184416 prefixEnd_5184416 887365773620031060752437 := by
  unfold tailWord_5184416
  simp only [CollatzResearch.WordTrace]
  refine ⟨94545592992876867302702551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126060790657169156403603401 94545592992876867302702551)
  ·
    refine ⟨141818389489315300954053827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94545592992876867302702551 141818389489315300954053827)
    ·
      refine ⟨212727584233972951431080741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141818389489315300954053827 212727584233972951431080741)
      ·
        refine ⟨39886422043869928393327639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 212727584233972951431080741 39886422043869928393327639)
        ·
          refine ⟨59829633065804892589991459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39886422043869928393327639 59829633065804892589991459)
          ·
            refine ⟨89744449598707338884987189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59829633065804892589991459 89744449598707338884987189)
            ·
              refine ⟨8413542149878813020467549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 89744449598707338884987189 8413542149878813020467549)
              ·
                refine ⟨3155078306204554882675331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8413542149878813020467549 3155078306204554882675331)
                ·
                  refine ⟨4732617459306832324012997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3155078306204554882675331 4732617459306832324012997)
                  ·
                    refine ⟨887365773620031060752437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4732617459306832324012997 887365773620031060752437)
                    ·
                      rfl

theorem cell23_5184416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 5, 3, 1, 4].length) (baseStart_5184416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5184416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5184416 prefixEnd_5184416 := by exact prefixLift 5184416
  have htrace : WordTrace (prefixWord ++ tailWord_5184416) baseStart_5184416 baseEnd_5184416 := by
    simpa [prefixWord, tailWord_5184416, baseEnd_5184416] using wordTrace_append hprefix tailTrace_5184416
  have hstable : (prefixWord ++ tailWord_5184416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5184416).length < 2 ^ (prefixWord ++ tailWord_5184416).sum := by decide
  have hdescent : baseEnd_5184416 < baseStart_5184416 := by decide
  rcases family_descends (prefixWord ++ tailWord_5184416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5184433 : List Nat := [1, 2, 2, 4, 4, 1, 1, 1, 3, 4]
def baseStart_5184433 : Nat := 118140960795 + 5184433 * 2 ^ 59
def prefixEnd_5184433 : Nat := 4983230072969 + 3 ^ 40 * 5184433 * 2
def baseEnd_5184433 : Nat := 887368683343739871914911

theorem tailTrace_5184433 : CollatzResearch.WordTrace tailWord_5184433 prefixEnd_5184433 887368683343739871914911 := by
  unfold tailWord_5184433
  simp only [CollatzResearch.WordTrace]
  refine ⟨189091806026692146508773953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126061204017794764339182635 189091806026692146508773953)
  ·
    refine ⟨141818854520019109881580465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189091806026692146508773953 141818854520019109881580465)
    ·
      refine ⟨106364140890014332411185349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141818854520019109881580465 106364140890014332411185349)
      ·
        refine ⟨19943276416877687327097253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 106364140890014332411185349 19943276416877687327097253)
        ·
          refine ⟨3739364328164566373830735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19943276416877687327097253 3739364328164566373830735)
          ·
            refine ⟨5609046492246849560746103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3739364328164566373830735 5609046492246849560746103)
            ·
              refine ⟨8413569738370274341119155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5609046492246849560746103 8413569738370274341119155)
              ·
                refine ⟨12620354607555411511678733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8413569738370274341119155 12620354607555411511678733)
                ·
                  refine ⟨4732632977833279316879525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12620354607555411511678733 4732632977833279316879525)
                  ·
                    refine ⟨887368683343739871914911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4732632977833279316879525 887368683343739871914911)
                    ·
                      rfl

theorem cell23_5184433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 1, 1, 3, 4].length) (baseStart_5184433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5184433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5184433 prefixEnd_5184433 := by exact prefixLift 5184433
  have htrace : WordTrace (prefixWord ++ tailWord_5184433) baseStart_5184433 baseEnd_5184433 := by
    simpa [prefixWord, tailWord_5184433, baseEnd_5184433] using wordTrace_append hprefix tailTrace_5184433
  have hstable : (prefixWord ++ tailWord_5184433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5184433).length < 2 ^ (prefixWord ++ tailWord_5184433).sum := by decide
  have hdescent : baseEnd_5184433 < baseStart_5184433 := by decide
  rcases family_descends (prefixWord ++ tailWord_5184433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5184442 : List Nat := [3, 1, 1, 1, 2, 1, 4, 2, 3, 5]
def baseStart_5184442 : Nat := 118140960795 + 5184442 * 2 ^ 59
def prefixEnd_5184442 : Nat := 4983230072969 + 3 ^ 40 * 5184442 * 2
def baseEnd_5184442 : Nat := 887370223785703360177397

theorem tailTrace_5184442 : CollatzResearch.WordTrace tailWord_5184442 prefixEnd_5184442 887370223785703360177397 := by
  unfold tailWord_5184442
  simp only [CollatzResearch.WordTrace]
  refine ⟨47273033570914885261462895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126061422855773027363901053 47273033570914885261462895)
  ·
    refine ⟨70909550356372327892194343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47273033570914885261462895 70909550356372327892194343)
    ·
      refine ⟨106364325534558491838291515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70909550356372327892194343 106364325534558491838291515)
      ·
        refine ⟨159546488301837737757437273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106364325534558491838291515 159546488301837737757437273)
        ·
          refine ⟨119659866226378303318077955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 159546488301837737757437273 119659866226378303318077955)
          ·
            refine ⟨179489799339567454977116933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119659866226378303318077955 179489799339567454977116933)
            ·
              refine ⟨33654337376168897808209425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 179489799339567454977116933 33654337376168897808209425)
              ·
                refine ⟨25240753032126673356157069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33654337376168897808209425 25240753032126673356157069)
                ·
                  refine ⟨9465282387047502508558901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25240753032126673356157069 9465282387047502508558901)
                  ·
                    refine ⟨887370223785703360177397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9465282387047502508558901 887370223785703360177397)
                    ·
                      rfl

theorem cell23_5184442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 2, 3, 5].length) (baseStart_5184442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5184442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5184442 prefixEnd_5184442 := by exact prefixLift 5184442
  have htrace : WordTrace (prefixWord ++ tailWord_5184442) baseStart_5184442 baseEnd_5184442 := by
    simpa [prefixWord, tailWord_5184442, baseEnd_5184442] using wordTrace_append hprefix tailTrace_5184442
  have hstable : (prefixWord ++ tailWord_5184442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5184442).length < 2 ^ (prefixWord ++ tailWord_5184442).sum := by decide
  have hdescent : baseEnd_5184442 < baseStart_5184442 := by decide
  rcases family_descends (prefixWord ++ tailWord_5184442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5184459 : List Nat := [1, 1, 1, 1, 3, 5, 3, 2, 1, 5]
def baseStart_5184459 : Nat := 118140960795 + 5184459 * 2 ^ 59
def prefixEnd_5184459 : Nat := 4983230072969 + 3 ^ 40 * 5184459 * 2
def baseEnd_5184459 : Nat := 887373133509412171339871

theorem tailTrace_5184459 : CollatzResearch.WordTrace tailWord_5184459 prefixEnd_5184459 887373133509412171339871 := by
  unfold tailWord_5184459
  simp only [CollatzResearch.WordTrace]
  refine ⟨189092754324597952949220431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126061836216398635299480287 189092754324597952949220431)
  ·
    refine ⟨283639131486896929423830647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189092754324597952949220431 283639131486896929423830647)
    ·
      refine ⟨425458697230345394135745971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 283639131486896929423830647 425458697230345394135745971)
      ·
        refine ⟨638188045845518091203618957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 425458697230345394135745971 638188045845518091203618957)
        ·
          refine ⟨239320517192069284201357109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 638188045845518091203618957 239320517192069284201357109)
          ·
            refine ⟨22436298486756495393877229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 239320517192069284201357109 22436298486756495393877229)
            ·
              refine ⟨8413611932533685772703961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22436298486756495393877229 8413611932533685772703961)
              ·
                refine ⟨6310208949400264329527971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8413611932533685772703961 6310208949400264329527971)
                ·
                  refine ⟨9465313424100396494291957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6310208949400264329527971 9465313424100396494291957)
                  ·
                    refine ⟨887373133509412171339871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9465313424100396494291957 887373133509412171339871)
                    ·
                      rfl

theorem cell23_5184459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 3, 2, 1, 5].length) (baseStart_5184459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5184459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5184459 prefixEnd_5184459 := by exact prefixLift 5184459
  have htrace : WordTrace (prefixWord ++ tailWord_5184459) baseStart_5184459 baseEnd_5184459 := by
    simpa [prefixWord, tailWord_5184459, baseEnd_5184459] using wordTrace_append hprefix tailTrace_5184459
  have hstable : (prefixWord ++ tailWord_5184459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5184459).length < 2 ^ (prefixWord ++ tailWord_5184459).sum := by decide
  have hdescent : baseEnd_5184459 < baseStart_5184459 := by decide
  rcases family_descends (prefixWord ++ tailWord_5184459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5184472 : List Nat := [2, 1, 2, 2, 2, 3, 1, 1, 3, 6]
def baseStart_5184472 : Nat := 118140960795 + 5184472 * 2 ^ 59
def prefixEnd_5184472 : Nat := 4983230072969 + 3 ^ 40 * 5184472 * 2
def baseEnd_5184472 : Nat := 887375358592248321052351

theorem tailTrace_5184472 : CollatzResearch.WordTrace tailWord_5184472 prefixEnd_5184472 887375358592248321052351 := by
  unfold tailWord_5184472
  simp only [CollatzResearch.WordTrace]
  refine ⟨94546614236775428084721835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126062152315700570779629113 94546614236775428084721835)
  ·
    refine ⟨141819921355163142127082753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94546614236775428084721835 141819921355163142127082753)
    ·
      refine ⟨106364941016372356595312065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141819921355163142127082753 106364941016372356595312065)
      ·
        refine ⟨79773705762279267446484049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106364941016372356595312065 79773705762279267446484049)
        ·
          refine ⟨59830279321709450584863037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79773705762279267446484049 59830279321709450584863037)
          ·
            refine ⟨22436354745641043969323639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59830279321709450584863037 22436354745641043969323639)
            ·
              refine ⟨33654532118461565953985459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22436354745641043969323639 33654532118461565953985459)
              ·
                refine ⟨50481798177692348930978189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33654532118461565953985459 50481798177692348930978189)
                ·
                  refine ⟨18930674316634630849116821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50481798177692348930978189 18930674316634630849116821)
                  ·
                    refine ⟨887375358592248321052351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18930674316634630849116821 887375358592248321052351)
                    ·
                      rfl

theorem cell23_5184472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 1, 3, 6].length) (baseStart_5184472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5184472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5184472 prefixEnd_5184472 := by exact prefixLift 5184472
  have htrace : WordTrace (prefixWord ++ tailWord_5184472) baseStart_5184472 baseEnd_5184472 := by
    simpa [prefixWord, tailWord_5184472, baseEnd_5184472] using wordTrace_append hprefix tailTrace_5184472
  have hstable : (prefixWord ++ tailWord_5184472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5184472).length < 2 ^ (prefixWord ++ tailWord_5184472).sum := by decide
  have hdescent : baseEnd_5184472 < baseStart_5184472 := by decide
  rcases family_descends (prefixWord ++ tailWord_5184472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5184490 : List Nat := [3, 1, 3, 1, 2, 2, 4, 2, 1, 1, 3]
def baseStart_5184490 : Nat := 118140960795 + 5184490 * 2 ^ 59
def prefixEnd_5184490 : Nat := 4983230072969 + 3 ^ 40 * 5184490 * 2
def baseEnd_5184490 : Nat := 2662135318428525892731971

theorem tailTrace_5184490 : CollatzResearch.WordTrace tailWord_5184490 prefixEnd_5184490 2662135318428525892731971 := by
  unfold tailWord_5184490
  simp only [CollatzResearch.WordTrace]
  refine ⟨47273471246871411310899731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126062589991657096829065949 47273471246871411310899731)
  ·
    refine ⟨70910206870307116966349597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47273471246871411310899731 70910206870307116966349597)
    ·
      refine ⟨26591327576365168862381099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70910206870307116966349597 26591327576365168862381099)
      ·
        refine ⟨39886991364547753293571649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26591327576365168862381099 39886991364547753293571649)
        ·
          refine ⟨29915243523410814970178737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39886991364547753293571649 29915243523410814970178737)
          ·
            refine ⟨22436432642558111227634053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29915243523410814970178737 22436432642558111227634053)
            ·
              refine ⟨4206831120479645855181385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22436432642558111227634053 4206831120479645855181385)
              ·
                refine ⟨3155123340359734391386039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4206831120479645855181385 3155123340359734391386039)
                ·
                  refine ⟨4732685010539601587079059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3155123340359734391386039 4732685010539601587079059)
                  ·
                    refine ⟨7099027515809402380618589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4732685010539601587079059 7099027515809402380618589)
                    ·
                      refine ⟨2662135318428525892731971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7099027515809402380618589 2662135318428525892731971)
                      ·
                        rfl

theorem cell23_5184490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 4, 2, 1, 1, 3].length) (baseStart_5184490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5184490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5184490 prefixEnd_5184490 := by exact prefixLift 5184490
  have htrace : WordTrace (prefixWord ++ tailWord_5184490) baseStart_5184490 baseEnd_5184490 := by
    simpa [prefixWord, tailWord_5184490, baseEnd_5184490] using wordTrace_append hprefix tailTrace_5184490
  have hstable : (prefixWord ++ tailWord_5184490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5184490).length < 2 ^ (prefixWord ++ tailWord_5184490).sum := by decide
  have hdescent : baseEnd_5184490 < baseStart_5184490 := by decide
  rcases family_descends (prefixWord ++ tailWord_5184490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5184496 : List Nat := [2, 1, 1, 1, 3, 2, 1, 5, 3, 2, 2]
def baseStart_5184496 : Nat := 118140960795 + 5184496 * 2 ^ 59
def prefixEnd_5184496 : Nat := 4983230072969 + 3 ^ 40 * 5184496 * 2
def baseEnd_5184496 : Nat := 2662138399312452869256943

theorem tailTrace_5184496 : CollatzResearch.WordTrace tailWord_5184496 prefixEnd_5184496 2662138399312452869256943 := by
  unfold tailWord_5184496
  simp only [CollatzResearch.WordTrace]
  refine ⟨94547051912731954134158671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126062735883642605512211561 94547051912731954134158671)
  ·
    refine ⟨141820577869097931201238007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94547051912731954134158671 141820577869097931201238007)
    ·
      refine ⟨212730866803646896801857011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141820577869097931201238007 212730866803646896801857011)
      ·
        refine ⟨319096300205470345202785517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212730866803646896801857011 319096300205470345202785517)
        ·
          refine ⟨119661112577051379451044569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 319096300205470345202785517 119661112577051379451044569)
          ·
            refine ⟨89745834432788534588283427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119661112577051379451044569 89745834432788534588283427)
            ·
              refine ⟨134618751649182801882425141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89745834432788534588283427 134618751649182801882425141)
              ·
                refine ⟨12620507967110887676477357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 134618751649182801882425141 12620507967110887676477357)
                ·
                  refine ⟨4732690487666582878679009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12620507967110887676477357 4732690487666582878679009)
                  ·
                    refine ⟨3549517865749937159009257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4732690487666582878679009 3549517865749937159009257)
                    ·
                      refine ⟨2662138399312452869256943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3549517865749937159009257 2662138399312452869256943)
                      ·
                        rfl

theorem cell23_5184496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 5, 3, 2, 2].length) (baseStart_5184496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5184496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5184496 prefixEnd_5184496 := by exact prefixLift 5184496
  have htrace : WordTrace (prefixWord ++ tailWord_5184496) baseStart_5184496 baseEnd_5184496 := by
    simpa [prefixWord, tailWord_5184496, baseEnd_5184496] using wordTrace_append hprefix tailTrace_5184496
  have hstable : (prefixWord ++ tailWord_5184496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5184496).length < 2 ^ (prefixWord ++ tailWord_5184496).sum := by decide
  have hdescent : baseEnd_5184496 < baseStart_5184496 := by decide
  rcases family_descends (prefixWord ++ tailWord_5184496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5184513 : List Nat := [1, 2, 4, 1, 2, 3, 1, 2, 3, 2, 2]
def baseStart_5184513 : Nat := 118140960795 + 5184513 * 2 ^ 59
def prefixEnd_5184513 : Nat := 4983230072969 + 3 ^ 40 * 5184513 * 2
def baseEnd_5184513 : Nat := 2662147128483579302744365

theorem tailTrace_5184513 : CollatzResearch.WordTrace tailWord_5184513 prefixEnd_5184513 2662147128483579302744365 := by
  unfold tailWord_5184513
  simp only [CollatzResearch.WordTrace]
  refine ⟨189094723866402320171686193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126063149244268213447790795 189094723866402320171686193)
  ·
    refine ⟨141821042899801740128764645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189094723866402320171686193 141821042899801740128764645)
    ·
      refine ⟨26591445543712826274143371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 141821042899801740128764645 26591445543712826274143371)
      ·
        refine ⟨39887168315569239411215057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26591445543712826274143371 39887168315569239411215057)
        ·
          refine ⟨29915376236676929558411293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39887168315569239411215057 29915376236676929558411293)
          ·
            refine ⟨11218266088753848584404235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29915376236676929558411293 11218266088753848584404235)
            ·
              refine ⟨16827399133130772876606353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11218266088753848584404235 16827399133130772876606353)
              ·
                refine ⟨12620549349848079657454765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16827399133130772876606353 12620549349848079657454765)
                ·
                  refine ⟨4732706006193029871545537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12620549349848079657454765 4732706006193029871545537)
                  ·
                    refine ⟨3549529504644772403659153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4732706006193029871545537 3549529504644772403659153)
                    ·
                      refine ⟨2662147128483579302744365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3549529504644772403659153 2662147128483579302744365)
                      ·
                        rfl

theorem cell23_5184513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 2, 3, 2, 2].length) (baseStart_5184513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5184513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5184513 prefixEnd_5184513 := by exact prefixLift 5184513
  have htrace : WordTrace (prefixWord ++ tailWord_5184513) baseStart_5184513 baseEnd_5184513 := by
    simpa [prefixWord, tailWord_5184513, baseEnd_5184513] using wordTrace_append hprefix tailTrace_5184513
  have hstable : (prefixWord ++ tailWord_5184513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5184513).length < 2 ^ (prefixWord ++ tailWord_5184513).sum := by decide
  have hdescent : baseEnd_5184513 < baseStart_5184513 := by decide
  rcases family_descends (prefixWord ++ tailWord_5184513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5184519 : List Nat := [1, 1, 4, 3, 1, 1, 5, 7]
def baseStart_5184519 : Nat := 118140960795 + 5184519 * 2 ^ 59
def prefixEnd_5184519 : Nat := 4983230072969 + 3 ^ 40 * 5184519 * 2
def baseEnd_5184519 : Nat := 98598155902500232565531

theorem tailTrace_5184519 : CollatzResearch.WordTrace tailWord_5184519 prefixEnd_5184519 98598155902500232565531 := by
  unfold tailWord_5184519
  simp only [CollatzResearch.WordTrace]
  refine ⟨189094942704380583196404611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126063295136253722130936407 189094942704380583196404611)
  ·
    refine ⟨283642414056570874794606917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189094942704380583196404611 283642414056570874794606917)
    ·
      refine ⟨53182952635607039023988797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 283642414056570874794606917 53182952635607039023988797)
      ·
        refine ⟨19943607238352639633995799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53182952635607039023988797 19943607238352639633995799)
        ·
          refine ⟨29915410857528959450993699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19943607238352639633995799 29915410857528959450993699)
          ·
            refine ⟨44873116286293439176490549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29915410857528959450993699 44873116286293439176490549)
            ·
              refine ⟨4206854651840009922795989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44873116286293439176490549 4206854651840009922795989)
              ·
                refine ⟨98598155902500232565531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4206854651840009922795989 98598155902500232565531)
                ·
                  rfl

theorem cell23_5184519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 5, 7].length) (baseStart_5184519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5184519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5184519 prefixEnd_5184519 := by exact prefixLift 5184519
  have htrace : WordTrace (prefixWord ++ tailWord_5184519) baseStart_5184519 baseEnd_5184519 := by
    simpa [prefixWord, tailWord_5184519, baseEnd_5184519] using wordTrace_append hprefix tailTrace_5184519
  have hstable : (prefixWord ++ tailWord_5184519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5184519).length < 2 ^ (prefixWord ++ tailWord_5184519).sum := by decide
  have hdescent : baseEnd_5184519 < baseStart_5184519 := by decide
  rcases family_descends (prefixWord ++ tailWord_5184519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5184533 : List Nat := [1, 3, 2, 1, 4, 1, 4, 1, 1, 2, 3]
def baseStart_5184533 : Nat := 118140960795 + 5184533 * 2 ^ 59
def prefixEnd_5184533 : Nat := 4983230072969 + 3 ^ 40 * 5184533 * 2
def baseEnd_5184533 : Nat := 2662157398096669224494273

theorem tailTrace_5184533 : CollatzResearch.WordTrace tailWord_5184533 prefixEnd_5184533 2662157398096669224494273 := by
  unfold tailWord_5184533
  simp only [CollatzResearch.WordTrace]
  refine ⟨189095453326329863587414253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126063635550886575724942835 189095453326329863587414253)
  ·
    refine ⟨70910794997373698845280345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 189095453326329863587414253 70910794997373698845280345)
    ·
      refine ⟨53183096248030274133960259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70910794997373698845280345 53183096248030274133960259)
      ·
        refine ⟨79774644372045411200940389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53183096248030274133960259 79774644372045411200940389)
        ·
          refine ⟨14957745819758514600176323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 79774644372045411200940389 14957745819758514600176323)
          ·
            refine ⟨22436618729637771900264485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14957745819758514600176323 22436618729637771900264485)
            ·
              refine ⟨4206866011807082231299591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22436618729637771900264485 4206866011807082231299591)
              ·
                refine ⟨6310299017710623346949387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4206866011807082231299591 6310299017710623346949387)
                ·
                  refine ⟨9465448526565935020424081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6310299017710623346949387 9465448526565935020424081)
                  ·
                    refine ⟨7099086394924451265318061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9465448526565935020424081 7099086394924451265318061)
                    ·
                      refine ⟨2662157398096669224494273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7099086394924451265318061 2662157398096669224494273)
                      ·
                        rfl

theorem cell23_5184533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 4, 1, 1, 2, 3].length) (baseStart_5184533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5184533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5184533 prefixEnd_5184533 := by exact prefixLift 5184533
  have htrace : WordTrace (prefixWord ++ tailWord_5184533) baseStart_5184533 baseEnd_5184533 := by
    simpa [prefixWord, tailWord_5184533, baseEnd_5184533] using wordTrace_append hprefix tailTrace_5184533
  have hstable : (prefixWord ++ tailWord_5184533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5184533).length < 2 ^ (prefixWord ++ tailWord_5184533).sum := by decide
  have hdescent : baseEnd_5184533 < baseStart_5184533 := by decide
  rcases family_descends (prefixWord ++ tailWord_5184533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5184540 : List Nat := [2, 2, 3, 1, 5, 1, 1, 2, 2, 4]
def baseStart_5184540 : Nat := 118140960795 + 5184540 * 2 ^ 59
def prefixEnd_5184540 : Nat := 4983230072969 + 3 ^ 40 * 5184540 * 2
def baseEnd_5184540 : Nat := 887386997487083565702247

theorem tailTrace_5184540 : CollatzResearch.WordTrace tailWord_5184540 prefixEnd_5184540 887386997487083565702247 := by
  unfold tailWord_5184540
  simp only [CollatzResearch.WordTrace]
  refine ⟨94547854318652251891459537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126063805758203002521946049 94547854318652251891459537)
  ·
    refine ⟨70910890738989188918594653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94547854318652251891459537 70910890738989188918594653)
    ·
      refine ⟨26591584027120945844472995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70910890738989188918594653 26591584027120945844472995)
      ·
        refine ⟨39887376040681418766709493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26591584027120945844472995 39887376040681418766709493)
        ·
          refine ⟨3739441503813883009379015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 39887376040681418766709493 3739441503813883009379015)
          ·
            refine ⟨5609162255720824514068523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3739441503813883009379015 5609162255720824514068523)
            ·
              refine ⟨8413743383581236771102785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5609162255720824514068523 8413743383581236771102785)
              ·
                refine ⟨6310307537685927578327089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8413743383581236771102785 6310307537685927578327089)
                ·
                  refine ⟨4732730653264445683745317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6310307537685927578327089 4732730653264445683745317)
                  ·
                    refine ⟨887386997487083565702247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4732730653264445683745317 887386997487083565702247)
                    ·
                      rfl

theorem cell23_5184540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 1, 2, 2, 4].length) (baseStart_5184540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5184540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5184540 prefixEnd_5184540 := by exact prefixLift 5184540
  have htrace : WordTrace (prefixWord ++ tailWord_5184540) baseStart_5184540 baseEnd_5184540 := by
    simpa [prefixWord, tailWord_5184540, baseEnd_5184540] using wordTrace_append hprefix tailTrace_5184540
  have hstable : (prefixWord ++ tailWord_5184540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5184540).length < 2 ^ (prefixWord ++ tailWord_5184540).sum := by decide
  have hdescent : baseEnd_5184540 < baseStart_5184540 := by decide
  rcases family_descends (prefixWord ++ tailWord_5184540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5184573 : List Nat := [1, 4, 1, 3, 1, 2, 1, 4, 1, 3, 2]
def baseStart_5184573 : Nat := 118140960795 + 5184573 * 2 ^ 59
def prefixEnd_5184573 : Nat := 4983230072969 + 3 ^ 40 * 5184573 * 2
def baseEnd_5184573 : Nat := 2662177937322849067994089

theorem tailTrace_5184573 : CollatzResearch.WordTrace tailWord_5184573 prefixEnd_5184573 2662177937322849067994089 := by
  unfold tailWord_5184573
  simp only [CollatzResearch.WordTrace]
  refine ⟨189096912246184950418870373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126064608164123300279246915 189096912246184950418870373)
  ·
    refine ⟨35455671046159678203538195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 189096912246184950418870373 35455671046159678203538195)
    ·
      refine ⟨53183506569239517305307293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35455671046159678203538195 53183506569239517305307293)
      ·
        refine ⟨19943814963464818989490235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53183506569239517305307293 19943814963464818989490235)
        ·
          refine ⟨29915722445197228484235353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19943814963464818989490235 29915722445197228484235353)
          ·
            refine ⟨22436791833897921363176515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29915722445197228484235353 22436791833897921363176515)
            ·
              refine ⟨33655187750846882044764773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22436791833897921363176515 33655187750846882044764773)
              ·
                refine ⟨6310347703283790383393395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33655187750846882044764773 6310347703283790383393395)
                ·
                  refine ⟨9465521554925685575090093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6310347703283790383393395 9465521554925685575090093)
                  ·
                    refine ⟨3549570583097132090658785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9465521554925685575090093 3549570583097132090658785)
                    ·
                      refine ⟨2662177937322849067994089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3549570583097132090658785 2662177937322849067994089)
                      ·
                        rfl

theorem cell23_5184573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 4, 1, 3, 2].length) (baseStart_5184573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5184573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5184573 prefixEnd_5184573 := by exact prefixLift 5184573
  have htrace : WordTrace (prefixWord ++ tailWord_5184573) baseStart_5184573 baseEnd_5184573 := by
    simpa [prefixWord, tailWord_5184573, baseEnd_5184573] using wordTrace_append hprefix tailTrace_5184573
  have hstable : (prefixWord ++ tailWord_5184573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5184573).length < 2 ^ (prefixWord ++ tailWord_5184573).sum := by decide
  have hdescent : baseEnd_5184573 < baseStart_5184573 := by decide
  rcases family_descends (prefixWord ++ tailWord_5184573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
